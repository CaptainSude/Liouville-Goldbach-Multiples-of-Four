"""Typeset a short mathematical note from its Markdown source.

ReportLab produces the PDF; Matplotlib's STIX math layout supplies vector glyph
positions. Every equation remains vector text, rather than a raster image.
"""
from __future__ import annotations
import functools
import re
from pathlib import Path
import matplotlib as mpl
from matplotlib.mathtext import MathTextParser
from matplotlib.font_manager import FontProperties
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import SimpleDocTemplate, Flowable, Paragraph, Spacer

PAPER_DIR = Path(__file__).resolve().parents[1]
SOURCE = PAPER_DIR / 'liouville-goldbach-multiples-of-four.md'
OUTPUT = SOURCE.with_suffix('.pdf')
FONT_DIR = Path(mpl.__file__).parent / 'mpl-data/fonts/ttf'
mpl.rcParams['mathtext.fontset'] = 'stix'
mpl.rcParams['font.family'] = 'STIXGeneral'

for name, filename in [('Body', 'STIXGeneral.ttf'), ('Bold', 'STIXGeneralBol.ttf'),
                       ('Italic', 'STIXGeneralItalic.ttf')]:
    pdfmetrics.registerFont(TTFont(name, str(FONT_DIR / filename)))
pdfmetrics.registerFontFamily('Body', normal='Body', bold='Bold', italic='Italic')
PARSER = MathTextParser('path')
REGISTERED_MATH_FONTS = {}

@functools.lru_cache(maxsize=None)
def math_layout(text, size):
    text = text.replace(r'\square', '□')
    return PARSER.parse(text, dpi=72, prop=FontProperties(size=size))

def draw_math(canvas, text, x, baseline, size):
    p = math_layout(text, size)
    for glyph in p.glyphs:
        if len(glyph) == 6:
            font, fontsize, codepoint, _glyph_index, ox, oy = glyph
        else:
            font, fontsize, codepoint, ox, oy = glyph
        path = str(font.fname)
        if path not in REGISTERED_MATH_FONTS:
            fontname = 'Math' + str(len(REGISTERED_MATH_FONTS))
            pdfmetrics.registerFont(TTFont(fontname, path))
            REGISTERED_MATH_FONTS[path] = fontname
        canvas.setFont(REGISTERED_MATH_FONTS[path], fontsize)
        canvas.drawString(x + ox, baseline + oy, chr(codepoint))
    for ox, oy, width, height in p.rects:
        canvas.rect(x + ox, baseline + oy, width, height, stroke=0, fill=1)

def atoms(text, size):
    """Keep punctuation attached to math and wrap only at actual word spaces."""
    result, current = [], []
    def flush():
        nonlocal current
        if current:
            result.append(current)
            current = []
    for part in re.split(r'(\$[^$]+\$|\*\*[^*]+\*\*|\*[^*]+\*)', text):
        if not part:
            continue
        if part.startswith('$'):
            if part == r'$\square$':
                current.append(('qed', '', 7.5, 6.5, 0))
                continue
            p = math_layout(part, size)
            current.append(('math', part, p.width, p.height - p.depth, p.depth))
            continue
        font = 'Body'
        if part.startswith('**'):
            font, part = 'Bold', part[2:-2]
        elif part.startswith('*'):
            font, part = 'Italic', part[1:-1]
        for token in re.split(r'(\s+)', part):
            if token.isspace():
                flush()
            elif token:
                current.append((font, token, pdfmetrics.stringWidth(token, font, size),
                                size * .76, size * .23))
    flush()
    return result

class MathParagraph(Flowable):
    def __init__(self, text='', size=11.65, leading=15.05, lines=None, last=True):
        super().__init__()
        self.text, self.size, self.leading = text, size, leading
        self.fixed_lines, self.last = lines, last
        self.spaceAfter = 5.4
        self.spaceBefore = 0
        self.keepWithNext = False

    def wrap(self, availWidth, availHeight):
        self.width = availWidth
        space = pdfmetrics.stringWidth(' ', 'Body', self.size)
        if self.fixed_lines is None:
            lines, line, width = [], [], 0
            for atom in atoms(self.text, self.size):
                aw = sum(segment[2] for segment in atom)
                if aw > availWidth + .1:
                    raise ValueError(f'Unbreakable text exceeds line: {atom}')
                new_width = width + (space if line else 0) + aw
                if line and new_width > availWidth:
                    lines.append(line)
                    line, width = [], 0
                width += (space if line else 0) + aw
                line.append(atom)
            if line:
                lines.append(line)
            self.lines = lines
        else:
            self.lines = self.fixed_lines
        self.line_heights = [max(self.leading,
            max(s[3] for a in line for s in a) +
            max(s[4] for a in line for s in a) + 2.2) for line in self.lines]
        self.height = sum(self.line_heights)
        return self.width, self.height

    def split(self, availWidth, availHeight):
        self.wrap(availWidth, availHeight)
        total, count = 0, 0
        for h in self.line_heights:
            if total + h > availHeight:
                break
            total += h
            count += 1
        if count < 2:
            return []
        if len(self.lines) - count == 1:
            count -= 1
        if count < 2:
            return []
        a = MathParagraph(size=self.size, leading=self.leading,
                          lines=self.lines[:count], last=False)
        b = MathParagraph(size=self.size, leading=self.leading,
                          lines=self.lines[count:], last=self.last)
        a.spaceAfter = 0
        return [a, b]

    def draw(self):
        c = self.canv
        c.setFillColor(colors.HexColor('#171717'))
        top = self.height
        normal_space = pdfmetrics.stringWidth(' ', 'Body', self.size)
        for index, (line, height) in enumerate(zip(self.lines, self.line_heights)):
            ascent = max(self.size * .78, max(s[3] for a in line for s in a))
            baseline = top - ascent - .4
            content_width = sum(s[2] for a in line for s in a)
            gap = normal_space
            if (index < len(self.lines)-1 or not self.last) and len(line) > 1:
                gap = (self.width - content_width) / (len(line)-1)
            x = 0
            for atom_index, atom in enumerate(line):
                for kind, text, width, _, _ in atom:
                    if kind == 'math':
                        draw_math(c, text, x, baseline, self.size)
                    elif kind == 'qed':
                        c.setLineWidth(.5)
                        c.rect(x+1, baseline+.6, 5.5, 5.5, fill=0, stroke=1)
                    else:
                        c.setFont(kind, self.size)
                        c.drawString(x, baseline, text)
                    x += width
                if atom_index < len(line)-1:
                    c.setFont('Body', self.size)
                    c.drawString(x, baseline, ' ')
                x += gap
            top -= height

class Equation(Flowable):
    def __init__(self, text, number=None):
        super().__init__()
        self.text = '$' + text.strip() + '$'
        self.number = number
        self.size = 12
        self.spaceBefore = 1.2
        self.spaceAfter = 6
        self.keepWithNext = True
    def wrap(self, width, height):
        self.width = width
        self.layout = math_layout(self.text, self.size)
        if self.number == 1:
            self.inner_text = r'$\sum_{n=1}^{m-1}\lambda(n)\lambda(m-n)$'
            self.tail_text = r'$<m-1\qquad(m\geq11).$'
            self.inner = math_layout(self.inner_text, self.size)
            self.tail = math_layout(self.tail_text, self.size)
        self.height = self.layout.height + 5
        if self.layout.width > width - 30:
            raise ValueError('Equation is too wide')
        return width, self.height
    def draw(self):
        self.canv.setFillColor(colors.HexColor('#171717'))
        if self.number == 1:
            self.canv.setStrokeColor(colors.HexColor('#171717'))
            total_width = self.inner.width + self.tail.width + 17
            x = (self.width-total_width)/2
            baseline = self.layout.depth + 2.2
            draw_math(self.canv, self.inner_text, x+5, baseline, self.size)
            right = x + self.inner.width + 10
            self.canv.setLineWidth(.55)
            for bx in (x, right):
                self.canv.line(bx, baseline-self.inner.depth-.6,
                               bx, baseline+self.inner.height-self.inner.depth+.6)
            draw_math(self.canv, self.tail_text, right+7, baseline, self.size)
            self.canv.setFont('Body', 10.5)
            self.canv.drawRightString(self.width, baseline, '(1)')
            return
        draw_math(self.canv, self.text, (self.width-self.layout.width)/2,
                  self.layout.depth + 2.2, self.size)
        if self.number:
            self.canv.setFont('Body', 10.5)
            self.canv.drawRightString(self.width, self.layout.depth+2.2, f'({self.number})')

title_style = ParagraphStyle('Title', fontName='Body', fontSize=20.5, leading=24,
                            alignment=TA_CENTER, textColor=colors.HexColor('#141414'),
                            spaceAfter=19)
heading_style = ParagraphStyle('Heading', fontName='Bold', fontSize=12.0,
                              leading=15, spaceBefore=9, spaceAfter=6, keepWithNext=True)
refs_style = ParagraphStyle('References', fontName='Body', fontSize=9.65, leading=12,
                           spaceAfter=5, leftIndent=15, firstLineIndent=-15,
                           textColor=colors.HexColor('#202020'))

def page(canvas, doc):
    canvas.setTitle("Liouville's Goldbach Problem for Multiples of Four")
    canvas.setAuthor('')
    canvas.setSubject('Shusterman\'s Liouville conjecture for every positive multiple of four')
    canvas.setFont('Body', 10)
    canvas.setFillColor(colors.HexColor('#555555'))
    canvas.drawCentredString(A4[0]/2, 30, str(doc.page))

def reference(text):
    text = re.sub(r'\*\*([^*]+)\*\*', r'<b>\1</b>', text)
    text = re.sub(r'\*([^*]+)\*', r'<i>\1</i>', text)
    text = re.sub(r'(https://\S+)', r'<link href="\1" color="#202020">\1</link>', text)
    return Paragraph(text, refs_style)

def build():
    doc = SimpleDocTemplate(str(OUTPUT), pagesize=A4, rightMargin=70, leftMargin=70,
        topMargin=48, bottomMargin=48, title="Liouville's Goldbach Problem for Multiples of Four",
        author='', pageCompression=1)
    content = SOURCE.read_text(encoding='utf-8')
    story, in_refs, eqnum = [], False, 0
    for block in re.split(r'\n\s*\n', content.strip()):
        if block.startswith('# '):
            story.append(Paragraph("Liouville's Goldbach Problem<br/>for Multiples of Four", title_style))
        elif block.startswith('## '):
            title = block[3:]
            in_refs = title == 'References'
            story.append(Paragraph(title, heading_style))
        elif block.startswith('$$'):
            eqnum += 1
            story.append(Equation(block[2:-2], number=1 if eqnum == 1 else None))
        elif in_refs:
            for ref in block.splitlines():
                if ref.strip():
                    story.append(reference(ref))
        else:
            para = MathParagraph(block.replace('\n', ' '))
            if block.startswith('Since $3$') or block.startswith('are positive integers with'):
                para.keepWithNext = True
            if block.startswith('**Theorem.'):
                para.spaceBefore = 4
                para.spaceAfter = 9
            story.append(para)
    doc.build(story, onFirstPage=page, onLaterPages=page)
    print(OUTPUT)

if __name__ == '__main__':
    build()
