import Shusterman.Reflection
import Shusterman.Liouville

/-!
# Shusterman's Liouville conjecture for multiples of four

The only literature input is an explicit parameter for Mangerel's published
nonextremality theorem. The elementary argument and all finite cases are proved
here for Mathlib's actual Liouville function.
-/

namespace Shusterman

/-- A decomposition into two positive integers having Liouville value `-1`. -/
def HasNegativePair (N : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧
    liouville a = -1 ∧ liouville b = -1

theorem negativePair_eight_mul {d : ℕ} (hd : 0 < d) :
    HasNegativePair (8 * d) := by
  rcases liouville_sign hd with hpos | hneg
  · refine ⟨3 * d, 5 * d, by omega, by omega, by omega, ?_, ?_⟩ <;>
      simp [liouville_mul, hpos]
  · refine ⟨4 * d, 4 * d, by omega, by omega, by omega, ?_, ?_⟩ <;>
      simp [liouville_mul, hneg]

theorem negativePair_twelve_mul {d : ℕ} (hd : 0 < d) :
    HasNegativePair (12 * d) := by
  rcases liouville_sign hd with hpos | hneg
  · refine ⟨5 * d, 7 * d, by omega, by omega, by omega, ?_, ?_⟩ <;>
      simp [liouville_mul, hpos]
  · refine ⟨6 * d, 6 * d, by omega, by omega, by omega, ?_, ?_⟩ <;>
      simp [liouville_mul, hneg]

/-- The elementary theorem needs only the equal-sign consequence of Mangerel. -/
theorem negativePair_four_mul_of_equalPair
    (hM : MangerelEqualPair) {m : ℕ} (hm : 0 < m) :
    HasNegativePair (4 * m) := by
  by_cases htwo : 2 ∣ m
  · obtain ⟨d, rfl⟩ := htwo
    have hd : 0 < d := by omega
    have heq : 4 * (2 * d) = 8 * d := by omega
    rw [heq]
    exact negativePair_eight_mul hd
  by_cases hthree : 3 ∣ m
  · obtain ⟨d, rfl⟩ := hthree
    have hd : 0 < d := by omega
    have heq : 4 * (3 * d) = 12 * d := by omega
    rw [heq]
    exact negativePair_twelve_mul hd
  by_cases hlarge : 11 ≤ m
  · by_contra hno
    have hodd : Odd m := by
      exact Nat.odd_iff.mpr (by omega)
    have hreflect := reflection_of_no_negative_pair
      liouville (fun _ hn => liouville_sign hn)
      (fun n _ => liouville_two_mul n)
      (fun n _ => liouville_three_mul n)
      (by omega : 1 < m) hodd hthree hno
    obtain ⟨a, b, ha, hb, hab, hequal⟩ := hM m hlarge
    have hba : m - a = b := by omega
    have hopposite := hreflect a ha (by omega)
    rw [hba] at hopposite
    rcases liouville_sign ha with hpos | hneg <;> omega
  · have htwo' : m % 2 ≠ 0 := by
      simpa only [Nat.dvd_iff_mod_eq_zero] using htwo
    have hthree' : m % 3 ≠ 0 := by
      simpa only [Nat.dvd_iff_mod_eq_zero] using hthree
    have hcases : m = 1 ∨ m = 5 ∨ m = 7 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact ⟨2, 2, by norm_num, by norm_num, by norm_num,
        liouville_two, liouville_two⟩
    · exact ⟨3, 17, by norm_num, by norm_num, by norm_num,
        liouville_three, liouville_seventeen⟩
    · exact ⟨5, 23, by norm_num, by norm_num, by norm_num,
        liouville_five, liouville_twentyThree⟩

/-- Every positive multiple of four has a negative-negative Liouville pair,
assuming the precise unconditional theorem of Mangerel (IMRN 2024, Thm. 1.2).
That published theorem is the sole external mathematical input. -/
theorem shusterman_multiples_of_four
    (hM : MangerelNonextremality) {N : ℕ} (hN : 0 < N) (hfour : 4 ∣ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧
      ArithmeticFunction.liouville a = -1 ∧
      ArithmeticFunction.liouville b = -1 := by
  obtain ⟨m, rfl⟩ := hfour
  exact negativePair_four_mul_of_equalPair hM.equalPair (by omega)

end Shusterman
