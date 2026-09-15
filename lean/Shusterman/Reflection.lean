import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

namespace Shusterman

/-- The values at positive integers are signs. -/
def SignFunction (f : ℕ → ℤ) : Prop := ∀ n, 0 < n → f n = 1 ∨ f n = -1

/-- Multiplication by `k` reverses signs. -/
def SignFlip (f : ℕ → ℤ) (k : ℕ) : Prop := ∀ n, 0 < n → f (k * n) = -f n

theorem reflection_of_no_negative_pair (f : ℕ → ℤ) (hs : SignFunction f)
    (h2 : SignFlip f 2) (h3 : SignFlip f 3) {m : ℕ} (hm : 1 < m)
    (hodd : Odd m) (hthree : ¬3 ∣ m)
    (hno : ¬∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = 4 * m ∧ f a = -1 ∧ f b = -1) :
    ∀ n, 0 < n → n < m → f n = -f (m - n) := by
  have h4 (n : ℕ) (hn : 0 < n) : f (4 * n) = f n := by
    have ha := h2 n hn
    have hb := h2 (2 * n) (by omega)
    have he : 2 * (2 * n) = 4 * n := by omega
    rw [he, ha] at hb
    simpa using hb
  have noNeg (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = m)
      (hfa : f a = -1) (hfb : f b = -1) : False := by
    apply hno
    refine ⟨4 * a, 4 * b, by omega, by omega, by omega, ?_, ?_⟩
    · rw [h4 a ha, hfa]
    · rw [h4 b hb, hfb]
  have noPos (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 2 * m)
      (hfa : f a = 1) (hfb : f b = 1) : False := by
    apply hno
    refine ⟨2 * a, 2 * b, by omega, by omega, by omega, ?_, ?_⟩
    · rw [h2 a ha, hfa]
    · rw [h2 b hb, hfb]
  have notDiv (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = m)
      (hfa : f a = 1) (hfb : f b = 1) : ¬3 ∣ b := by
    rintro ⟨c, hc⟩
    have hcpos : 0 < c := by omega
    have hcsmall : c < m := by omega
    have hfc : f c = -1 := by
      have := h3 c hcpos
      rw [← hc, hfb] at this
      omega
    have hfmc : f (m - c) = 1 := by
      rcases hs (m - c) (by omega) with h | h
      · exact h
      · exact False.elim (noNeg c (m - c) hcpos (by omega) (by omega) hfc h)
    have hft : f (3 * (m - c)) = -1 := by rw [h3 _ (by omega), hfmc]
    have hfmb : f (m + b) = 1 := by
      rcases hs (m + b) (by omega) with h | h
      · exact h
      · apply False.elim
        apply hno
        exact ⟨3 * (m - c), m + b, by omega, by omega, by omega, hft, h⟩
    exact noPos a (m + b) ha (by omega) (by omega) hfa hfmb
  have ordered : ∀ d : ℕ, ∀ a b : ℕ, 0 < a → a < b → b - a = d →
      a + b = m → f a = 1 → f b = 1 → False := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro a b ha hab hdist hsum hfa hfb
      have hb : 0 < b := by omega
      have hadiv := notDiv b a hb ha (by omega) hfb hfa
      have hbdiv := notDiv a b ha hb hsum hfa hfb
      have hamod : a % 3 ≠ 0 := fun h => hadiv (Nat.dvd_of_mod_eq_zero h)
      have hbmod : b % 3 ≠ 0 := fun h => hbdiv (Nat.dvd_of_mod_eq_zero h)
      have hmmod : m % 3 ≠ 0 := fun h => hthree (Nat.dvd_of_mod_eq_zero h)
      have hares : a % 3 = 1 ∨ a % 3 = 2 := by omega
      have hbres : b % 3 = 1 ∨ b % 3 = 2 := by omega
      have hsum_mod : (a % 3 + b % 3) % 3 = m % 3 := by
        rw [← Nat.add_mod, hsum]
      have hma : (m + a) % 3 = 0 := by
        rw [Nat.add_mod]
        rcases hares with h | h <;> rcases hbres with h' | h' <;>
          simp only [h, h'] at hsum_mod ⊢ <;> omega
      have hmb : (m + b) % 3 = 0 := by
        rw [Nat.add_mod]
        rcases hares with h | h <;> rcases hbres with h' | h' <;>
          simp only [h, h'] at hsum_mod ⊢ <;> omega
      let a' := (m + a) / 3
      let b' := (m + b) / 3
      have heqa : 3 * a' = m + a := by dsimp [a']; omega
      have heqb : 3 * b' = m + b := by dsimp [b']; omega
      have hap : 0 < a' := by omega
      have hbp : 0 < b' := by omega
      have hpa : f (m + a) = -1 := by
        rcases hs (m + a) (by omega) with h | h
        · exact False.elim (noPos b (m + a) hb (by omega) (by omega) hfb h)
        · exact h
      have hpb : f (m + b) = -1 := by
        rcases hs (m + b) (by omega) with h | h
        · exact False.elim (noPos a (m + b) ha (by omega) (by omega) hfa h)
        · exact h
      have hfap : f a' = 1 := by
        have := h3 a' hap
        rw [heqa, hpa] at this
        omega
      have hfbp : f b' = 1 := by
        have := h3 b' hbp
        rw [heqb, hpb] at this
        omega
      exact ih (b' - a') (by omega) a' b' hap (by omega) rfl (by omega) hfap hfbp
  have noPosM (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = m)
      (hfa : f a = 1) (hfb : f b = 1) : False := by
    have hne : a ≠ b := by
      intro heq
      rcases hodd with ⟨k, hk⟩
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ordered (b - a) a b ha hlt rfl hab hfa hfb
    · exact ordered (a - b) b a hb hgt rfl (by omega) hfb hfa
  intro n hn hnm
  rcases hs n hn with ha | ha <;> rcases hs (m - n) (by omega) with hb | hb
  · exact False.elim (noPosM n (m - n) hn (by omega) (by omega) ha hb)
  · omega
  · omega
  · exact False.elim (noNeg n (m - n) hn (by omega) (by omega) ha hb)

end Shusterman
