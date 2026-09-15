import Shusterman.Main
import Shusterman.Liouville
import Shusterman.Reflection

/-!
# Extended Liouville-Goldbach Theorems: Positive Pairs and Duality

This module formalizes the dual sign problem for Shusterman's conjecture:
every multiple of four strictly greater than four is the sum of two positive integers
having positive Liouville value `+1`.

We also prove:
1. Unconditional positive pairs for all multiples of 8 and 12.
2. The sign-duality theorem establishing that negating a sign function preserves the
   `SignFlip` condition, deriving the dual reflection lemma directly from `reflection_of_no_negative_pair`.
3. The sharp boundary exception: `N = 4` has no positive pair (`¬ HasPositivePair 4`),
   making `1 < m` (or `4 < N`) both necessary and optimal.
4. Decidability of `HasNegativePair N` and `HasPositivePair N` via bounded quantification
   over `Finset.Ico 1 N`.
5. A streamlined golfed variant of `negativePair_four_mul_of_equalPair`.
-/

namespace Shusterman

/-- A decomposition into two positive integers having Liouville value `1`. -/
def HasPositivePair (N : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧
    liouville a = 1 ∧ liouville b = 1

/-- Multiples of eight unconditionally possess a positive-positive Liouville pair.
When `liouville d = 1`, `4d + 4d` is positive; when `liouville d = -1`, `3d + 5d` is positive. -/
theorem positivePair_eight_mul {d : ℕ} (hd : 0 < d) :
    HasPositivePair (8 * d) := by
  rcases liouville_sign hd with hpos | hneg
  · refine ⟨4 * d, 4 * d, by omega, by omega, by omega, ?_, ?_⟩ <;>
      simp [liouville_mul, hpos]
  · refine ⟨3 * d, 5 * d, by omega, by omega, by omega, ?_, ?_⟩ <;>
      simp [liouville_mul, hneg]

/-- Multiples of twelve unconditionally possess a positive-positive Liouville pair.
When `liouville d = 1`, `6d + 6d` is positive; when `liouville d = -1`, `5d + 7d` is positive. -/
theorem positivePair_twelve_mul {d : ℕ} (hd : 0 < d) :
    HasPositivePair (12 * d) := by
  rcases liouville_sign hd with hpos | hneg
  · refine ⟨6 * d, 6 * d, by omega, by omega, by omega, ?_, ?_⟩ <;>
      simp [liouville_mul, hpos]
  · refine ⟨5 * d, 7 * d, by omega, by omega, by omega, ?_, ?_⟩ <;>
      simp [liouville_mul, hneg]

/-- Negating a sign function yields a sign function. -/
theorem signFunction_neg {f : ℕ → ℤ} (hs : SignFunction f) :
    SignFunction (-f) := fun n hn => by
  rcases hs n hn with h | h <;> simp [h]

/-- Negating a sign-flipping function preserves the sign-flipping property. -/
theorem signFlip_neg {f : ℕ → ℤ} {k : ℕ} (hk : SignFlip f k) :
    SignFlip (-f) k := fun n hn => by simp [hk n hn]

/-- Dual reflection theorem: if there is no positive pair for `f` at `4 * m`,
then `f` satisfies the exact same reflection identity `f n = -f (m - n)` on `0 < n < m`.
Derived cleanly by applying `reflection_of_no_negative_pair` to the dual sign function `-f`. -/
theorem reflection_of_no_positive_pair (f : ℕ → ℤ) (hs : SignFunction f)
    (h2 : SignFlip f 2) (h3 : SignFlip f 3) {m : ℕ} (hm : 1 < m)
    (hodd : Odd m) (hthree : ¬3 ∣ m)
    (hno : ¬∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = 4 * m ∧ f a = 1 ∧ f b = 1) :
    ∀ n, 0 < n → n < m → f n = -f (m - n) := by
  have hno_neg : ¬∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = 4 * m ∧ (-f) a = -1 ∧ (-f) b = -1 := by
    rintro ⟨a, b, ha, hb, hab, hfa, hfb⟩
    exact hno ⟨a, b, ha, hb, hab, by simpa using hfa, by simpa using hfb⟩
  have hreflect := reflection_of_no_negative_pair (-f) (signFunction_neg hs)
    (signFlip_neg h2) (signFlip_neg h3) hm hodd hthree hno_neg
  intro n hn hnm
  have h := hreflect n hn hnm
  change -f n = - -f (m - n) at h
  omega

/-- The integer 4 has no positive pair, because the only partitions of 4 into positive
integers are `1 + 3` and `2 + 2`, neither of which consists of two `+1` Liouville values.
Thus `N = 4` is the unique exceptional multiple of 4 for positive pairs. -/
theorem not_hasPositivePair_four : ¬ HasPositivePair 4 := by
  rintro ⟨a, b, ha, hb, hab, hfa, hfb⟩
  rcases show a = 1 ∨ a = 2 ∨ a = 3 by omega with rfl | rfl | rfl
  · obtain rfl : b = 3 := by omega
    simp at hfb
  · simp at hfa
  · simp at hfa

theorem positivePair_twenty : HasPositivePair 20 := by
  have h : liouville 10 = 1 := by rw [show (10 : ℕ) = 2 * 5 from rfl, liouville_mul]; simp
  exact ⟨10, 10, by decide, by decide, rfl, h, h⟩

theorem positivePair_twentyEight : HasPositivePair 28 := by
  have h : liouville 14 = 1 := by rw [show (14 : ℕ) = 2 * 7 from rfl, liouville_mul]; simp
  exact ⟨14, 14, by decide, by decide, rfl, h, h⟩

/-- Every multiple of four with `1 < m` has a positive pair, assuming Mangerel's equal-pair theorem.
Note that `1 < m` is necessary and optimal, as `4 * 1 = 4` has no positive pair. -/
theorem positivePair_four_mul_of_equalPair
    (hM : MangerelEqualPair) {m : ℕ} (hm : 1 < m) :
    HasPositivePair (4 * m) := by
  by_cases htwo : 2 ∣ m
  · obtain ⟨d, rfl⟩ := htwo; exact mul_assoc 4 2 d ▸ positivePair_eight_mul (by omega)
  by_cases hthree : 3 ∣ m
  · obtain ⟨d, rfl⟩ := hthree; exact mul_assoc 4 3 d ▸ positivePair_twelve_mul (by omega)
  by_cases hlarge : 11 ≤ m
  · by_contra hno
    have hreflect := reflection_of_no_positive_pair liouville (fun _ => liouville_sign)
      (fun n _ => liouville_two_mul n) (fun n _ => liouville_three_mul n)
      hm (Nat.odd_iff.mpr (by omega)) hthree hno
    obtain ⟨a, b, ha, hb, hab, hequal⟩ := hM m hlarge
    have hopposite := hreflect a ha (by omega)
    rw [show m - a = b by omega] at hopposite
    rcases liouville_sign ha with h | h <;> omega
  · rcases show m = 5 ∨ m = 7 by omega with rfl | rfl
    · exact positivePair_twenty
    · exact positivePair_twentyEight

/-- Streamlined golfed variant of `negativePair_four_mul_of_equalPair` eliminating
redundant modular arithmetic hypotheses and factoring common step proofs. -/
theorem negativePair_four_mul_of_equalPair_golfed
    (hM : MangerelEqualPair) {m : ℕ} (hm : 0 < m) :
    HasNegativePair (4 * m) := by
  by_cases htwo : 2 ∣ m
  · obtain ⟨d, rfl⟩ := htwo; exact mul_assoc 4 2 d ▸ negativePair_eight_mul (by omega)
  by_cases hthree : 3 ∣ m
  · obtain ⟨d, rfl⟩ := hthree; exact mul_assoc 4 3 d ▸ negativePair_twelve_mul (by omega)
  by_cases hlarge : 11 ≤ m
  · by_contra hno
    have hreflect := reflection_of_no_negative_pair liouville (fun _ => liouville_sign)
      (fun n _ => liouville_two_mul n) (fun n _ => liouville_three_mul n)
      (by omega) (Nat.odd_iff.mpr (by omega)) hthree hno
    obtain ⟨a, b, ha, hb, hab, hequal⟩ := hM m hlarge
    have hopposite := hreflect a ha (by omega)
    rw [show m - a = b by omega] at hopposite
    rcases liouville_sign ha with h | h <;> omega
  · rcases show m = 1 ∨ m = 5 ∨ m = 7 by omega with rfl | rfl | rfl
    · exact ⟨2, 2, by decide, by decide, rfl, liouville_two, liouville_two⟩
    · exact ⟨3, 17, by decide, by decide, rfl, liouville_three, liouville_seventeen⟩
    · exact ⟨5, 23, by decide, by decide, rfl, liouville_five, liouville_twentyThree⟩

/-- Every multiple of four strictly greater than 4 has a positive-positive Liouville pair,
assuming Mangerel's nonextremality theorem. -/
theorem shusterman_positive_multiples_of_four
    (hM : MangerelNonextremality) {N : ℕ} (hN : 4 < N) (hfour : 4 ∣ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧
      ArithmeticFunction.liouville a = 1 ∧
      ArithmeticFunction.liouville b = 1 := by
  obtain ⟨m, rfl⟩ := hfour
  exact positivePair_four_mul_of_equalPair hM.equalPair (by omega)

/-- Equivalent formulation requiring `0 < N` and `N ≠ 4`. -/
theorem shusterman_positive_multiples_of_four_of_ne_four
    (hM : MangerelNonextremality) {N : ℕ} (hN : 0 < N) (hne : N ≠ 4) (hfour : 4 ∣ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧
      ArithmeticFunction.liouville a = 1 ∧
      ArithmeticFunction.liouville b = 1 :=
  shusterman_positive_multiples_of_four hM (by obtain ⟨m, rfl⟩ := hfour; omega) hfour

/-- Bounded characterization of `HasNegativePair`: `N` has a negative pair iff
there exists `a ∈ Finset.Ico 1 N` such that `liouville a = -1` and `liouville (N - a) = -1`. -/
theorem hasNegativePair_iff_bex (N : ℕ) :
    HasNegativePair N ↔ ∃ a ∈ Finset.Ico 1 N, liouville a = -1 ∧ liouville (N - a) = -1 := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, hfa, hfb⟩
    exact ⟨a, Finset.mem_Ico.mpr ⟨ha, by omega⟩, hfa, by rwa [show b = N - a by omega] at hfb⟩
  · rintro ⟨a, hmem, hfa, hfb⟩
    rw [Finset.mem_Ico] at hmem
    exact ⟨a, N - a, hmem.1, by omega, by omega, hfa, hfb⟩

instance (N : ℕ) : Decidable (HasNegativePair N) :=
  decidable_of_iff _ (hasNegativePair_iff_bex N).symm

/-- Bounded characterization of `HasPositivePair`: `N` has a positive pair iff
there exists `a ∈ Finset.Ico 1 N` such that `liouville a = 1` and `liouville (N - a) = 1`. -/
theorem hasPositivePair_iff_bex (N : ℕ) :
    HasPositivePair N ↔ ∃ a ∈ Finset.Ico 1 N, liouville a = 1 ∧ liouville (N - a) = 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, hfa, hfb⟩
    exact ⟨a, Finset.mem_Ico.mpr ⟨ha, by omega⟩, hfa, by rwa [show b = N - a by omega] at hfb⟩
  · rintro ⟨a, hmem, hfa, hfb⟩
    rw [Finset.mem_Ico] at hmem
    exact ⟨a, N - a, hmem.1, by omega, by omega, hfa, hfb⟩

instance (N : ℕ) : Decidable (HasPositivePair N) :=
  decidable_of_iff _ (hasPositivePair_iff_bex N).symm

end Shusterman
