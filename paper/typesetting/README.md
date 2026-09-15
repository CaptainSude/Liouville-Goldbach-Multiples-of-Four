# Rebuilding the paper

The ready-to-read PDF and editable Markdown manuscript are in the parent `paper` folder. Rebuilding the paper is optional and independent of checking the Lean proof.

With Python 3.11 or later installed, run these commands from the repository's top folder:

```text
python -m pip install -r paper/typesetting/requirements.txt
python paper/typesetting/build.py
```

The builder reads `paper/liouville-goldbach-multiples-of-four.md` and regenerates the PDF beside it. It uses ReportLab for the document and Matplotlib's STIX mathematics layout for vector formulas. The title is set in the builder; update it there as well if you rename the paper. The supported manuscript syntax is the small subset used by this paper, not arbitrary Markdown.

The source package versions below match the environment used for the released PDF. STIX fonts are supplied by Matplotlib and retain their bundled license. The builder is Apache 2.0; the paper and manuscript are CC BY 4.0.
