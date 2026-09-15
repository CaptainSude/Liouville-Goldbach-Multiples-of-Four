import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Algebra.Ring.Commute
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

/-!
# Liouville values and the external analytic input

`liouville` is an abbreviation for Mathlib's actual Liouville arithmetic function.
The published nonextremality theorem is stated as an explicit proposition, not
as an axiom. The elementary consequence needed by the main proof is verified
below from that proposition.
-/

namespace Shusterman

abbrev liouville : ArithmeticFunction ℤ := ArithmeticFunction.liouville

theorem liouville_sign {n : ℕ} (hn : 0 < n) :
    liouville n = 1 ∨ liouville n = -1 := by
  rw [ArithmeticFunction.liouville_apply (Nat.ne_of_gt hn)]
  exact neg_one_pow_eq_or ℤ _

theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n :=
  ArithmeticFunction.liouville_apply_mul m n

@[simp] theorem liouville_one : liouville 1 = 1 :=
  ArithmeticFunction.liouville_apply_one

theorem liouville_prime {p : ℕ} (hp : p.Prime) : liouville p = -1 := by
  rw [ArithmeticFunction.liouville_apply hp.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp]
  norm_num

@[simp] theorem liouville_two : liouville 2 = -1 := liouville_prime (by decide)
@[simp] theorem liouville_three : liouville 3 = -1 := liouville_prime (by decide)
@[simp] theorem liouville_five : liouville 5 = -1 := liouville_prime (by decide)
@[simp] theorem liouville_seven : liouville 7 = -1 := liouville_prime (by decide)
@[simp] theorem liouville_thirteen : liouville 13 = -1 := liouville_prime (by decide)
@[simp] theorem liouville_seventeen : liouville 17 = -1 := liouville_prime (by decide)
@[simp] theorem liouville_twentyThree : liouville 23 = -1 := liouville_prime (by decide)

@[simp] theorem liouville_two_mul (n : ℕ) : liouville (2 * n) = -liouville n := by
  rw [liouville_mul, liouville_two, neg_one_mul]

@[simp] theorem liouville_three_mul (n : ℕ) : liouville (3 * n) = -liouville n := by
  rw [liouville_mul, liouville_three, neg_one_mul]

@[simp] theorem liouville_four : liouville 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, liouville_mul, liouville_two]
  norm_num

@[simp] theorem liouville_six : liouville 6 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, liouville_mul, liouville_two, liouville_three]
  norm_num

/-- The strict correlation bound in Mangerel, "On a Goldbach-Type Problem for
the Liouville Function", IMRN 2024, Theorem 1.2 (DOI: 10.1093/imrn/rnae149).
It is an explicit input to this development; it is not asserted as an axiom. -/
def MangerelNonextremality : Prop :=
  ∀ m : ℕ, 11 ≤ m →
    |∑ n ∈ Finset.Icc 1 (m - 1), liouville n * liouville (m - n)| < (m : ℤ) - 1

/-- The weaker consequence of nonextremality used by the elementary argument. -/
def MangerelEqualPair : Prop :=
  ∀ m : ℕ, 11 ≤ m → ∃ a b : ℕ,
    0 < a ∧ 0 < b ∧ a + b = m ∧ liouville a = liouville b

theorem MangerelNonextremality.equalPair (h : MangerelNonextremality) :
    MangerelEqualPair := by
  intro m hm
  by_contra hnone
  have hprod : ∀ n ∈ Finset.Icc 1 (m - 1),
      liouville n * liouville (m - n) = -1 := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnm⟩
    have hnpos : 0 < n := by omega
    have hmnp : 0 < m - n := by omega
    have hne : liouville n ≠ liouville (m - n) := by
      intro heq
      apply hnone
      exact ⟨n, m - n, hnpos, hmnp, by omega, heq⟩
    rcases liouville_sign hnpos with ha | ha <;>
      rcases liouville_sign hmnp with hb | hb <;> simp_all
  have hsum :
      (∑ n ∈ Finset.Icc 1 (m - 1), liouville n * liouville (m - n)) =
        -((m : ℤ) - 1) := by
    calc
      _ = ∑ _n ∈ Finset.Icc 1 (m - 1), (-1 : ℤ) :=
        Finset.sum_congr rfl hprod
      _ = -((m : ℤ) - 1) := by
        simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        have hcard : m - 1 + 1 - 1 = m - 1 := by omega
        rw [hcard, Nat.cast_sub (by omega : 1 ≤ m)]
        norm_num
  have hbound := h m hm
  rw [hsum, abs_neg, abs_of_nonneg (by omega : (0 : ℤ) ≤ m - 1)] at hbound
  exact (lt_irrefl _) hbound

end Shusterman
