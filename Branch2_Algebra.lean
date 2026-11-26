import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QCSD.Defs

namespace Branch2Algebra

open QCSD.Defs

/-!
# Section 1: Powers-of-3 Block & DFT Parameters (§2.1)
-/

def minPowExpAux (b target : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | fuel + 1, acc =>
    if target ≤ b ^ acc then acc else minPowExpAux b target fuel (acc + 1)

def minPowExp (b target : ℕ) : ℕ :=
  minPowExpAux b target target 0

lemma self_le_pow_of_two_le {b : ℕ} (hb : 2 ≤ b) : ∀ n : ℕ, n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := self_le_pow_of_two_le hb n
    have hpos : 1 ≤ b ^ n := Nat.one_le_pow n b (by omega)
    calc
      n + 1 ≤ b ^ n + b ^ n := by omega
      _ = 2 * b ^ n := by ring
      _ ≤ b * b ^ n := Nat.mul_le_mul_right (b ^ n) hb
      _ = b ^ (n + 1) := by rw [pow_succ']

lemma minPowExpAux_spec {b target : ℕ} :
    ∀ (fuel acc : ℕ),
      target ≤ b ^ (acc + fuel) →
      (∀ r < acc, b ^ r < target) →
      target ≤ b ^ minPowExpAux b target fuel acc ∧
        ∀ r < minPowExpAux b target fuel acc, b ^ r < target
  | 0, acc, htop, hlow => by
    simpa [minPowExpAux] using And.intro htop hlow
  | fuel + 1, acc, htop, hlow => by
    simp only [minPowExpAux]
    split_ifs with h
    · exact ⟨h, hlow⟩
    · apply minPowExpAux_spec fuel (acc + 1)
      · have heq : (acc + 1) + fuel = acc + (fuel + 1) := by omega
        simpa [heq] using htop
      · intro r hr
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | rfl
        · exact hlow r hlt
        · exact Nat.lt_of_not_ge h

lemma minPowExp_le_pow {b : ℕ} (hb : 2 ≤ b) (target : ℕ) :
    target ≤ b ^ minPowExp b target := by
  have h := minPowExpAux_spec target 0 (by simpa using self_le_pow_of_two_le hb target)
    (by intro r hr; omega)
  exact h.1

lemma lt_of_lt_minPowExp {b : ℕ} (hb : 2 ≤ b) {target r : ℕ}
    (hr : r < minPowExp b target) : b ^ r < target := by
  have h := minPowExpAux_spec target 0 (by simpa using self_le_pow_of_two_le hb target)
    (by intro x hx; omega)
  exact h.2 r hr

lemma minPowExp_min {b : ℕ} (hb : 2 ≤ b) {target r : ℕ} (hr : target ≤ b ^ r) :
    minPowExp b target ≤ r := by
  by_contra hgt
  have hlt : b ^ r < target := lt_of_lt_minPowExp hb (Nat.lt_of_not_ge hgt)
  omega

/-- Exponent `k` such that `J = 3^k` is the smallest power of 3 with `d ≤ J^2`. -/
def paramK (d : ℕ) : ℕ := minPowExp 9 d

/-- Block bit-size `J = 3^k`. -/
def paramJ (d : ℕ) : ℕ := 3 ^ paramK d

/-- Number of input blocks `m = ⌈d / J⌉`. -/
def paramM (d : ℕ) : ℕ := (d + paramJ d - 1) / paramJ d

/-- Exponent `ℓ` such that `L = 3^ℓ` is the smallest power of 3 with `2m - 1 ≤ L`. -/
def paramEll (d : ℕ) : ℕ := minPowExp 3 (2 * paramM d - 1)

/-- Total DFT length `L = 3^ℓ`. -/
def paramL (d : ℕ) : ℕ := 3 ^ paramEll d

/-- Stage-1 transform size `L₁ = 3^{⌊ℓ/2⌋}`. -/
def paramL1 (d : ℕ) : ℕ := 3 ^ (paramEll d / 2)

/-- Stage-2 transform size `L₂ = 3^{⌈ℓ/2⌉}`. -/
def paramL2 (d : ℕ) : ℕ := 3 ^ ((paramEll d + 1) / 2)

lemma paramJ_sq_eq_nine_pow (d : ℕ) : (paramJ d) ^ 2 = 9 ^ paramK d := by
  unfold paramJ
  calc
    (3 ^ paramK d) ^ 2 = (3 ^ 2) ^ paramK d := by rw [← pow_mul, mul_comm, pow_mul]
    _ = 9 ^ paramK d := by norm_num

lemma one_le_paramJ (d : ℕ) : 1 ≤ paramJ d :=
  Nat.one_le_pow (paramK d) 3 (by decide)

lemma paramJ_pos (d : ℕ) : 0 < paramJ d :=
  one_le_paramJ d

lemma le_paramJ_sq (d : ℕ) : d ≤ (paramJ d) ^ 2 := by
  rw [paramJ_sq_eq_nine_pow]
  exact minPowExp_le_pow (by decide) d

lemma paramK_min {d k : ℕ} (hk : d ≤ (3 ^ k) ^ 2) : paramK d ≤ k := by
  apply minPowExp_min (by decide)
  have heq : (3 ^ k) ^ 2 = 9 ^ k := by
    calc
      (3 ^ k) ^ 2 = (3 ^ 2) ^ k := by rw [← pow_mul, mul_comm, pow_mul]
      _ = 9 ^ k := by norm_num
  rwa [← heq]

lemma paramJ_sq_lt_nine_mul {d : ℕ} (hd : 1 ≤ d) : (paramJ d) ^ 2 < 9 * d := by
  rw [paramJ_sq_eq_nine_pow]
  rcases Nat.eq_zero_or_pos (paramK d) with hk0 | hkpos
  · rw [hk0]
    simp only [pow_zero]
    omega
  · have hklt : paramK d - 1 < minPowExp 9 d := by
      change paramK d - 1 < paramK d
      omega
    have hlt : 9 ^ (paramK d - 1) < d :=
      lt_of_lt_minPowExp (b := 9) (by decide) (target := d) hklt
    have hpow : 9 ^ paramK d = 9 * 9 ^ (paramK d - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hkpos, pow_succ']
    omega

lemma one_le_paramM {d : ℕ} (hd : 1 ≤ d) : 1 ≤ paramM d := by
  unfold paramM
  have hJ : 1 ≤ paramJ d := one_le_paramJ d
  exact (Nat.le_div_iff_mul_le hJ).2 (by omega)

lemma le_paramM_mul_paramJ (d : ℕ) : d ≤ paramM d * paramJ d := by
  unfold paramM
  have hJ : 0 < paramJ d := paramJ_pos d
  have hdiv := Nat.div_add_mod (d + paramJ d - 1) (paramJ d)
  have hmod : (d + paramJ d - 1) % paramJ d < paramJ d := Nat.mod_lt _ hJ
  have hmul : paramJ d * ((d + paramJ d - 1) / paramJ d) =
      ((d + paramJ d - 1) / paramJ d) * paramJ d := Nat.mul_comm _ _
  omega

lemma paramM_le_paramJ {d : ℕ} (hd : 1 ≤ d) : paramM d ≤ paramJ d := by
  unfold paramM
  have hJ : 1 ≤ paramJ d := one_le_paramJ d
  have hdJ : d ≤ (paramJ d) ^ 2 := le_paramJ_sq d
  have hlt : d + paramJ d - 1 < (paramJ d + 1) * paramJ d := by
    have hsq : (paramJ d + 1) * paramJ d = (paramJ d) ^ 2 + paramJ d := by ring
    omega
  have hdiv_lt : (d + paramJ d - 1) / paramJ d < paramJ d + 1 :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hlt)
  omega

lemma one_le_paramL (d : ℕ) : 1 ≤ paramL d :=
  Nat.one_le_pow (paramEll d) 3 (by decide)

lemma one_le_paramL1 (d : ℕ) : 1 ≤ paramL1 d :=
  Nat.one_le_pow _ 3 (by decide)

lemma one_le_paramL2 (d : ℕ) : 1 ≤ paramL2 d :=
  Nat.one_le_pow _ 3 (by decide)

lemma two_mul_paramM_sub_one_le_paramL (d : ℕ) : 2 * paramM d - 1 ≤ paramL d :=
  minPowExp_le_pow (by decide) (2 * paramM d - 1)

lemma paramEll_min {d r : ℕ} (hr : 2 * paramM d - 1 ≤ 3 ^ r) : paramEll d ≤ r :=
  minPowExp_min (by decide) hr

lemma paramM_le_paramL {d : ℕ} (hd : 1 ≤ d) : paramM d ≤ paramL d := by
  have hm : 1 ≤ paramM d := one_le_paramM hd
  have hL : 2 * paramM d - 1 ≤ paramL d := two_mul_paramM_sub_one_le_paramL d
  omega

lemma paramEll_le_paramK_succ {d : ℕ} (hd : 1 ≤ d) : paramEll d ≤ paramK d + 1 := by
  apply paramEll_min
  have hm : paramM d ≤ paramJ d := paramM_le_paramJ hd
  have hJ : 1 ≤ paramJ d := one_le_paramJ d
  have hpow : 3 ^ (paramK d + 1) = 3 * paramJ d := by
    unfold paramJ
    rw [pow_succ']
  omega

lemma paramL_le_three_mul_paramJ {d : ℕ} (hd : 1 ≤ d) : paramL d ≤ 3 * paramJ d := by
  have hle : paramEll d ≤ paramK d + 1 := paramEll_le_paramK_succ hd
  calc
    paramL d = 3 ^ paramEll d := rfl
    _ ≤ 3 ^ (paramK d + 1) := Nat.pow_le_pow_right (by decide) hle
    _ = 3 * paramJ d := by unfold paramJ; rw [pow_succ']

lemma paramL_dvd_three_mul_paramJ {d : ℕ} (hd : 1 ≤ d) : paramL d ∣ 3 * paramJ d := by
  have hle : paramEll d ≤ paramK d + 1 := paramEll_le_paramK_succ hd
  have hdvd : 3 ^ paramEll d ∣ 3 ^ (paramK d + 1) := Nat.pow_dvd_pow 3 hle
  have hpow : 3 ^ (paramK d + 1) = 3 * paramJ d := by unfold paramJ; rw [pow_succ']
  rwa [← hpow]

lemma paramL_eq_mul (d : ℕ) : paramL d = paramL1 d * paramL2 d := by
  unfold paramL paramL1 paramL2
  rw [← pow_add]
  congr 1
  omega

lemma paramL1_le_paramL2 (d : ℕ) : paramL1 d ≤ paramL2 d := by
  unfold paramL1 paramL2
  apply Nat.pow_le_pow_right (by decide)
  omega

lemma max_paramL1_paramL2_eq (d : ℕ) : max (paramL1 d) (paramL2 d) = paramL2 d :=
  Nat.max_eq_right (paramL1_le_paramL2 d)

lemma max_paramL1_paramL2_le_three_mul_paramJ {d : ℕ} (hd : 1 ≤ d) :
    max (paramL1 d) (paramL2 d) ≤ 3 * paramJ d := by
  rw [max_paramL1_paramL2_eq]
  have h1 : 1 ≤ paramL1 d := one_le_paramL1 d
  have hmul : paramL2 d ≤ paramL1 d * paramL2 d := Nat.le_mul_of_pos_left _ h1
  rw [← paramL_eq_mul] at hmul
  exact le_trans hmul (paramL_le_three_mul_paramJ hd)

lemma max_paramL1_paramL2_sq_le_nine_mul_paramJ {d : ℕ} (hd : 1 ≤ d) :
    (max (paramL1 d) (paramL2 d)) ^ 2 ≤ 9 * paramJ d := by
  rw [max_paramL1_paramL2_eq]
  have hexp : 2 * ((paramEll d + 1) / 2) ≤ paramEll d + 1 := by omega
  calc
    (paramL2 d) ^ 2 = (3 ^ ((paramEll d + 1) / 2)) ^ 2 := rfl
    _ = 3 ^ (2 * ((paramEll d + 1) / 2)) := by rw [← pow_mul, mul_comm]
    _ ≤ 3 ^ (paramEll d + 1) := Nat.pow_le_pow_right (by decide) hexp
    _ = 3 * paramL d := by unfold paramL; rw [pow_succ']
    _ ≤ 3 * (3 * paramJ d) := Nat.mul_le_mul_left 3 (paramL_le_three_mul_paramJ hd)
    _ = 9 * paramJ d := by ring

lemma mulNet_edge_bound_nat {d : ℕ} (hd : 1 ≤ d) :
    4 * d + 7 * paramL d * (2 * paramJ d) < 382 * d := by
  have hL : paramL d ≤ 3 * paramJ d := paramL_le_three_mul_paramJ hd
  have hJ2 : (paramJ d) ^ 2 < 9 * d := paramJ_sq_lt_nine_mul hd
  have hmid : 7 * paramL d * (2 * paramJ d) ≤ 42 * (paramJ d) ^ 2 := by
    calc
      7 * paramL d * (2 * paramJ d) = 14 * paramJ d * paramL d := by ring
      _ ≤ 14 * paramJ d * (3 * paramJ d) := Nat.mul_le_mul_left _ hL
      _ = 42 * (paramJ d) ^ 2 := by ring
  omega

lemma small_transform_deg_pow4_lt_nat {d : ℕ} (hd : 1 ≤ d) :
    (4 * paramJ d * max (paramL1 d) (paramL2 d)) ^ 4 < 63 ^ 4 * d ^ 3 := by
  set J := paramJ d
  set M := max (paramL1 d) (paramL2 d)
  have hM2 : M ^ 2 ≤ 9 * J := max_paramL1_paramL2_sq_le_nine_mul_paramJ hd
  have hJ2 : J ^ 2 < 9 * d := paramJ_sq_lt_nine_mul hd
  have hsq : (4 * J * M) ^ 2 ≤ 144 * J ^ 3 := by
    calc
      (4 * J * M) ^ 2 = 16 * J ^ 2 * M ^ 2 := by ring
      _ ≤ 16 * J ^ 2 * (9 * J) := Nat.mul_le_mul_left _ hM2
      _ = 144 * J ^ 3 := by ring
  have hpow4 : (4 * J * M) ^ 4 ≤ 20736 * (J ^ 2) ^ 3 := by
    calc
      (4 * J * M) ^ 4 = ((4 * J * M) ^ 2) ^ 2 := by ring
      _ ≤ (144 * J ^ 3) ^ 2 := Nat.pow_le_pow_left hsq 2
      _ = 20736 * (J ^ 2) ^ 3 := by ring
  have hJ6 : (J ^ 2) ^ 3 < (9 * d) ^ 3 := Nat.pow_lt_pow_left hJ2 (by decide)
  have hd3 : 1 ≤ d ^ 3 := Nat.one_le_pow 3 d hd
  calc
    (4 * J * M) ^ 4 ≤ 20736 * (J ^ 2) ^ 3 := hpow4
    _ < 20736 * (9 * d) ^ 3 := (Nat.mul_lt_mul_left (by decide)).2 hJ6
    _ = 15116544 * d ^ 3 := by ring
    _ < 15752961 * d ^ 3 := (Nat.mul_lt_mul_right (by omega)).2 (by decide)
    _ = 63 ^ 4 * d ^ 3 := by norm_num

lemma six_mul_paramJ_pow4_lt_nat {d : ℕ} (hd : 1 ≤ d) :
    (6 * paramJ d) ^ 4 < 63 ^ 4 * d ^ 3 := by
  set J := paramJ d
  have hJ2 : J ^ 2 < 9 * d := paramJ_sq_lt_nine_mul hd
  have hJ4 : (J ^ 2) ^ 2 < (9 * d) ^ 2 := Nat.pow_lt_pow_left hJ2 (by decide)
  have hd23 : d ^ 2 ≤ d ^ 3 := Nat.pow_le_pow_right hd (by decide)
  have hd3 : 1 ≤ d ^ 3 := Nat.one_le_pow 3 d hd
  calc
    (6 * J) ^ 4 = 1296 * (J ^ 2) ^ 2 := by ring
    _ < 1296 * (9 * d) ^ 2 := (Nat.mul_lt_mul_left (by decide)).2 hJ4
    _ = 104976 * d ^ 2 := by ring
    _ ≤ 104976 * d ^ 3 := Nat.mul_le_mul_left _ hd23
    _ < 15752961 * d ^ 3 := (Nat.mul_lt_mul_right (by omega)).2 (by decide)
    _ = 63 ^ 4 * d ^ 3 := by norm_num

private lemma lt_of_pow4_lt_real {x y : ℝ} (hy : 0 ≤ y) (hpow : x ^ 4 < y ^ 4) : x < y := by
  by_contra hge
  have hy_le_x : y ≤ x := le_of_not_gt hge
  have hsq : y * y ≤ x * x := mul_self_le_mul_self hy hy_le_x
  have h4 : (y * y) * (y * y) ≤ (x * x) * (x * x) :=
    mul_self_le_mul_self (mul_nonneg hy hy) hsq
  have h4' : y ^ 4 ≤ x ^ 4 := by linarith [show y ^ 4 = (y * y) * (y * y) by ring,
    show x ^ 4 = (x * x) * (x * x) by ring]
  linarith

lemma small_transform_deg_bound_real {d : ℕ} (hd : 1 ≤ d) :
    ((4 * paramJ d * max (paramL1 d) (paramL2 d) : ℕ) : ℝ) <
      63 * (d : ℝ) ^ ((3 : ℝ) / 4) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hy0 : (0 : ℝ) ≤ 63 * (d : ℝ) ^ ((3 : ℝ) / 4) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hd0 _)
  have hnat : (((4 * paramJ d * max (paramL1 d) (paramL2 d)) ^ 4 : ℕ) : ℝ) <
      ((63 ^ 4 * d ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast small_transform_deg_pow4_lt_nat hd
  apply lt_of_pow4_lt_real hy0
  have hrhs : (63 * (d : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 = ((63 ^ 4 * d ^ 3 : ℕ) : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast ((d : ℝ) ^ ((3 : ℝ) / 4)) 4, ← Real.rpow_mul hd0]
    have hexp : ((3 : ℝ) / 4) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    rw [hexp, Real.rpow_natCast]
    push_cast
    ring
  rw [hrhs]
  simpa only [Nat.cast_pow] using hnat

lemma six_mul_paramJ_bound_real {d : ℕ} (hd : 1 ≤ d) :
    ((6 * paramJ d : ℕ) : ℝ) < 63 * (d : ℝ) ^ ((3 : ℝ) / 4) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hy0 : (0 : ℝ) ≤ 63 * (d : ℝ) ^ ((3 : ℝ) / 4) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hd0 _)
  have hnat : (((6 * paramJ d) ^ 4 : ℕ) : ℝ) < ((63 ^ 4 * d ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast six_mul_paramJ_pow4_lt_nat hd
  apply lt_of_pow4_lt_real hy0
  have hrhs : (63 * (d : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 = ((63 ^ 4 * d ^ 3 : ℕ) : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast ((d : ℝ) ^ ((3 : ℝ) / 4)) 4, ← Real.rpow_mul hd0]
    have hexp : ((3 : ℝ) / 4) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    rw [hexp, Real.rpow_natCast]
    push_cast
    ring
  rw [hrhs]
  simpa only [Nat.cast_pow] using hnat

lemma rpow_three_fourths_le_nine_tenths {d : ℕ} (hd : 1 ≤ d) :
    (63 : ℝ) * (d : ℝ) ^ ((3 : ℝ) / 4) ≤ 63 * ((2 * d : ℝ)) ^ ((9 : ℝ) / 10) := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by linarith
  have h1 : (d : ℝ) ^ ((3 : ℝ) / 4) ≤ (d : ℝ) ^ ((9 : ℝ) / 10) :=
    Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
  have h2 : (d : ℝ) ^ ((9 : ℝ) / 10) ≤ (2 * (d : ℝ)) ^ ((9 : ℝ) / 10) :=
    Real.rpow_le_rpow hd0 (by linarith) (by norm_num)
  nlinarith

/-!
# Section 2: Auxiliary Quotient Ring `A = F_2[Y]/(Y^{2J} + Y^J + 1)` & Orthogonality (§2.1–§2.2)
-/

/-- Concrete `2J`-bit vector representation of elements of `A`. -/
abbrev CoeffVec (J : ℕ) : Type := Fin (2 * J) → ZMod 2

/-- Bool ↔ `ZMod 2` conversion helpers for Boolean tensor network circuits. -/
def boolToZMod2 (b : Bool) : ZMod 2 := if b then 1 else 0

def zmod2ToBool (x : ZMod 2) : Bool := decide (x = 1)

@[simp] lemma zmod2ToBool_boolToZMod2 (b : Bool) : zmod2ToBool (boolToZMod2 b) = b := by
  cases b <;> decide

@[simp] lemma boolToZMod2_zmod2ToBool (x : ZMod 2) : boolToZMod2 (zmod2ToBool x) = x := by
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨_ + 2, hlt⟩ => nomatch hlt

lemma boolToZMod2_xor (a b : Bool) :
    boolToZMod2 (Bool.xor a b) = boolToZMod2 a + boolToZMod2 b := by
  cases a <;> cases b <;> decide

lemma boolToZMod2_and (a b : Bool) :
    boolToZMod2 (a && b) = boolToZMod2 a * boolToZMod2 b := by
  cases a <;> cases b <;> decide

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc
    x + x = 2 * x := (two_mul x).symm
    _ = 0 * x := by rw [h2]
    _ = 0 := zero_mul x

lemma zmod2_neg_eq_self (x : ZMod 2) : -x = x := by
  calc
    -x = -x + (x + x) := by rw [zmod2_add_self, add_zero]
    _ = (-x + x) + x := by rw [add_assoc]
    _ = x := by rw [neg_add_cancel, zero_add]

lemma zmod2_sub_eq_add (x y : ZMod 2) : x - y = x + y := by
  rw [sub_eq_add_neg, zmod2_neg_eq_self]

/-- Modulus polynomial `Y^{2J} + Y^J + 1` over `ZMod 2`. -/
noncomputable def auxModPoly (J : ℕ) : Polynomial (ZMod 2) :=
  Polynomial.X ^ (2 * J) + Polynomial.X ^ J + 1

/-- Quotient ring `A = F_2[Y]/(Y^{2J} + Y^J + 1)`. -/
abbrev AuxRing (J : ℕ) : Type :=
  Polynomial (ZMod 2) ⧸ Ideal.span ({auxModPoly J} : Set (Polynomial (ZMod 2)))

/-- Canonical projection `F_2[Y] →+* A`. -/
noncomputable def toAuxRing (J : ℕ) : Polynomial (ZMod 2) →+* AuxRing J :=
  Ideal.Quotient.mk (Ideal.span ({auxModPoly J} : Set (Polynomial (ZMod 2))))

/-- Image `Y` of `X` in `A`. -/
noncomputable def ringY (J : ℕ) : AuxRing J :=
  toAuxRing J Polynomial.X

lemma auxRing_two_eq_zero (J : ℕ) : (2 : AuxRing J) = 0 := by
  have h2 : (1 + 1 : Polynomial (ZMod 2)) = 0 := by
    ext n
    simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_zero]
    split_ifs <;> decide
  calc
    (2 : AuxRing J) = (1 : AuxRing J) + 1 := one_add_one_eq_two.symm
    _ = toAuxRing J (1 + 1) := by rw [map_add, map_one]
    _ = toAuxRing J 0 := by rw [h2]
    _ = 0 := map_zero _

lemma auxRing_add_self (J : ℕ) (x : AuxRing J) : x + x = 0 := by
  calc
    x + x = 2 * x := (two_mul x).symm
    _ = 0 * x := by rw [auxRing_two_eq_zero]
    _ = 0 := zero_mul x

lemma auxRing_neg_eq_self (J : ℕ) (x : AuxRing J) : -x = x := by
  calc
    -x = -x + (x + x) := by rw [auxRing_add_self, add_zero]
    _ = (-x + x) + x := by rw [add_assoc]
    _ = x := by rw [neg_add_cancel, zero_add]

lemma auxRing_eq_of_add_eq_zero {J : ℕ} {x y : AuxRing J} (h : x + y = 0) : x = y := by
  calc
    x = x + (y + y) := by rw [auxRing_add_self, add_zero]
    _ = (x + y) + y := by rw [add_assoc]
    _ = y := by rw [h, zero_add]

lemma ringY_rel (J : ℕ) : (ringY J) ^ (2 * J) + (ringY J) ^ J + 1 = 0 := by
  have hmem : auxModPoly J ∈ Ideal.span ({auxModPoly J} : Set (Polynomial (ZMod 2))) :=
    Ideal.subset_span rfl
  have hzero : toAuxRing J (auxModPoly J) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simpa [auxModPoly, ringY, map_add, map_pow, map_one] using hzero

lemma ringY_pow_J_rel (J : ℕ) : ((ringY J) ^ J) ^ 2 + (ringY J) ^ J + 1 = 0 := by
  have hpow : ((ringY J) ^ J) ^ 2 = (ringY J) ^ (2 * J) := by
    rw [← pow_mul, mul_comm]
  rw [hpow]
  exact ringY_rel J

lemma ringY_pow_J_cube (J : ℕ) : ((ringY J) ^ J) ^ 3 = 1 := by
  set z : AuxRing J := (ringY J) ^ J
  have hz : z ^ 2 + z + 1 = 0 := ringY_pow_J_rel J
  apply auxRing_eq_of_add_eq_zero
  calc
    z ^ 3 + 1 = (z ^ 2 + z + 1) * (z + 1) - (z ^ 2 + z ^ 2) - (z + z) := by ring
    _ = 0 * (z + 1) - 0 - 0 := by
      rw [hz, auxRing_add_self J (z ^ 2), auxRing_add_self J z]
    _ = 0 := by ring

lemma ringY_pow_three_mul (J : ℕ) : (ringY J) ^ (3 * J) = 1 := by
  calc
    (ringY J) ^ (3 * J) = ((ringY J) ^ J) ^ 3 := by rw [← pow_mul, mul_comm]
    _ = 1 := ringY_pow_J_cube J

lemma auxRing_odd_natCast (J : ℕ) : ∀ m : ℕ, ((2 * m + 1 : ℕ) : AuxRing J) = 1
  | 0 => by simp
  | m + 1 => by
    have ih := auxRing_odd_natCast J m
    have hstep : ((2 * (m + 1) + 1 : ℕ) : AuxRing J) = ((2 * m + 1 : ℕ) : AuxRing J) + 2 := by
      push_cast
      ring
    rw [hstep, ih, auxRing_two_eq_zero, add_zero]

lemma auxRing_three_pow_natCast (J ℓ : ℕ) : ((3 ^ ℓ : ℕ) : AuxRing J) = 1 := by
  have h3 : ((3 : ℕ) : AuxRing J) = 1 := auxRing_odd_natCast J 1
  rw [Nat.cast_pow, h3, one_pow]

/-- Embed a `2J`-bit vector as a polynomial of degree `< 2J`. -/
noncomputable def vecToPoly (J : ℕ) (u : CoeffVec J) : Polynomial (ZMod 2) :=
  Finset.univ.sum (fun i : Fin (2 * J) => Polynomial.monomial i.val (u i))

/-- Map a `2J`-bit vector into the quotient ring `A`. -/
noncomputable def vecToRing (J : ℕ) (u : CoeffVec J) : AuxRing J :=
  toAuxRing J (vecToPoly J u)

lemma vecToPoly_coeff_lt {J : ℕ} (u : CoeffVec J) (i : Fin (2 * J)) :
    (vecToPoly J u).coeff i.val = u i := by
  unfold vecToPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  have hsum : Finset.univ.sum (fun j : Fin (2 * J) => if j.val = i.val then u j else 0) =
      Finset.univ.sum (fun j : Fin (2 * J) => if j = i then u j else 0) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : j = i
    · subst h; simp
    · have hval : j.val ≠ i.val := fun hv => h (Fin.ext hv)
      simp [h, hval]
  rw [hsum]
  simp

lemma vecToPoly_coeff_ge {J : ℕ} (u : CoeffVec J) {k : ℕ} (hk : 2 * J ≤ k) :
    (vecToPoly J u).coeff k = 0 := by
  unfold vecToPoly
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  rw [Polynomial.coeff_monomial]
  have hne : i.val ≠ k := by omega
  simp [hne]

lemma eq_vecToPoly_of_coeff_ge_zero {J : ℕ} (p : Polynomial (ZMod 2))
    (hdeg : ∀ k : ℕ, 2 * J ≤ k → p.coeff k = 0) :
    p = vecToPoly J (fun i => p.coeff i.val) := by
  ext k
  by_cases hk : k < 2 * J
  · exact (vecToPoly_coeff_lt (fun i : Fin (2 * J) => p.coeff i.val) ⟨k, hk⟩).symm
  · rw [hdeg k (by omega), vecToPoly_coeff_ge _ (by omega)]

lemma coeff_X_pow_mul_add (q : Polynomial (ZMod 2)) :
    ∀ k m : ℕ, (Polynomial.X ^ k * q).coeff (k + m) = q.coeff m
  | 0, m => by simp
  | k + 1, m => by
    have heq : Polynomial.X ^ (k + 1) * q = Polynomial.X * (Polynomial.X ^ k * q) := by
      rw [pow_succ', mul_assoc]
    have hidx : k + 1 + m = (k + m) + 1 := by omega
    rw [heq, hidx, Polynomial.coeff_X_mul]
    exact coeff_X_pow_mul_add q k m

/-- Injectivity of `vecToRing J`: distinct `2J`-bit vectors represent distinct elements of `A`. -/
lemma vecToRing_injective {J : ℕ} (hJ : 0 < J) : Function.Injective (vecToRing J) := by
  intro u v huv
  have hmem : vecToPoly J u - vecToPoly J v ∈
      Ideal.span ({auxModPoly J} : Set (Polynomial (ZMod 2))) :=
    Ideal.Quotient.eq.mp huv
  rw [Ideal.mem_span_singleton] at hmem
  rcases hmem with ⟨q, hq⟩
  have hq0 : q = 0 := by
    by_contra hqne
    set m := q.natDegree
    have hlead : q.coeff m ≠ 0 := by
      change q.leadingCoeff ≠ 0
      exact Polynomial.leadingCoeff_ne_zero.mpr hqne
    have hgt1 : q.coeff (J + m) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hgt2 : q.coeff (2 * J + m) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hlhs : (vecToPoly J u - vecToPoly J v).coeff (2 * J + m) = 0 := by
      rw [Polynomial.coeff_sub, vecToPoly_coeff_ge u (by omega),
        vecToPoly_coeff_ge v (by omega), sub_zero]
    have hrhs : (auxModPoly J * q).coeff (2 * J + m) = q.coeff m := by
      unfold auxModPoly
      rw [add_mul, add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_add]
      have hc1 : (Polynomial.X ^ (2 * J) * q).coeff (2 * J + m) = q.coeff m :=
        coeff_X_pow_mul_add q (2 * J) m
      have hc2 : (Polynomial.X ^ J * q).coeff (2 * J + m) = q.coeff (J + m) := by
        have hidx : 2 * J + m = J + (J + m) := by omega
        rw [hidx]
        exact coeff_X_pow_mul_add q J (J + m)
      rw [hc1, hc2, hgt1, hgt2, add_zero, add_zero]
    rw [hq, hrhs] at hlhs
    exact hlead hlhs
  rw [hq0, mul_zero] at hq
  have hp : vecToPoly J u = vecToPoly J v := sub_eq_zero.mp hq
  funext i
  have hi := congrArg (fun p => p.coeff i.val) hp
  simpa [vecToPoly_coeff_lt] using hi

/-- Concrete zero, one, addition, scalar scaling, `Y^m` table, shift-multiply, and ring product. -/
def vecZero (J : ℕ) : CoeffVec J := fun _ => 0

def vecOne (J : ℕ) : CoeffVec J := fun i => if i.val = 0 then 1 else 0

def vecAdd (J : ℕ) (u v : CoeffVec J) : CoeffVec J := fun i => u i + v i

def vecScale (J : ℕ) (c : ZMod 2) (u : CoeffVec J) : CoeffVec J := fun i => c * u i

def monomialModVec (J m : ℕ) (k : Fin (2 * J)) : ZMod 2 :=
  let r := m % (3 * J)
  (if r = k.val then 1 else 0) +
    (if 2 * J ≤ r ∧ r - 2 * J = k.val then 1 else 0) +
    (if 2 * J ≤ r ∧ r - J = k.val then 1 else 0)

def vecMulYExp (J m : ℕ) (u : CoeffVec J) : CoeffVec J :=
  fun k => Finset.univ.sum (fun i : Fin (2 * J) => u i * monomialModVec J (i.val + m) k)

def vecMul (J : ℕ) (u v : CoeffVec J) : CoeffVec J :=
  fun k => Finset.univ.sum (fun i : Fin (2 * J) =>
    Finset.univ.sum (fun j : Fin (2 * J) =>
      (u i * v j) * monomialModVec J (i.val + j.val) k))

lemma vecToRing_zero (J : ℕ) : vecToRing J (vecZero J) = 0 := by
  unfold vecToRing vecToPoly vecZero
  simp

lemma vecToRing_one {J : ℕ} (hJ : 0 < J) : vecToRing J (vecOne J) = 1 := by
  have hp : vecToPoly J (vecOne J) = 1 := by
    ext k
    by_cases hk : k < 2 * J
    · rw [vecToPoly_coeff_lt (vecOne J) ⟨k, hk⟩]
      unfold vecOne
      simp [Polynomial.coeff_one]
    · rw [vecToPoly_coeff_ge (vecOne J) (by omega)]
      have hne : k ≠ 0 := by omega
      simp [Polynomial.coeff_one, hne]
  unfold vecToRing
  rw [hp, map_one]

lemma vecToRing_add (J : ℕ) (u v : CoeffVec J) :
    vecToRing J (vecAdd J u v) = vecToRing J u + vecToRing J v := by
  unfold vecToRing vecToPoly vecAdd
  rw [← map_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact map_add (Polynomial.monomial i.val) (u i) (v i)

lemma vecToRing_finset_sum {J : ℕ} {ι : Type*} (s : Finset ι) (f : ι → CoeffVec J) :
    vecToRing J (fun k => s.sum (fun a => f a k)) = s.sum (fun a => vecToRing J (f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact vecToRing_zero J
  | @insert a s ha ih =>
    have hfun : (fun k => (insert a s).sum (fun b => f b k)) =
        vecAdd J (f a) (fun k => s.sum (fun b => f b k)) := by
      funext k
      simp [vecAdd, Finset.sum_insert ha]
    rw [hfun, vecToRing_add, ih, Finset.sum_insert ha]

lemma vecToRing_scale (J : ℕ) (c : ZMod 2) (u : CoeffVec J) :
    vecToRing J (vecScale J c u) = toAuxRing J (Polynomial.C c) * vecToRing J u := by
  unfold vecToRing vecToPoly vecScale
  rw [← map_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Polynomial.C_mul_monomial]

lemma vecToRing_eq_sum_C_mul_ringY (J : ℕ) (u : CoeffVec J) :
    vecToRing J u = Finset.univ.sum (fun i : Fin (2 * J) =>
      toAuxRing J (Polynomial.C (u i)) * (ringY J) ^ i.val) := by
  unfold vecToRing vecToPoly ringY
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]

private lemma sum_unit_indicator_poly {J r : ℕ} (hr : r < 2 * J) :
    Finset.univ.sum (fun k : Fin (2 * J) =>
      Polynomial.monomial k.val (if r = k.val then (1 : ZMod 2) else 0)) =
      Polynomial.X ^ r := by
  set idx : Fin (2 * J) := ⟨r, hr⟩
  have hsum : Finset.univ.sum (fun k : Fin (2 * J) =>
      Polynomial.monomial k.val (if r = k.val then (1 : ZMod 2) else 0)) =
      Finset.univ.sum (fun k : Fin (2 * J) =>
        if k = idx then Polynomial.monomial k.val (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k = idx
    · subst hk; simp [idx]
    · have hne : r ≠ k.val := fun hv => hk (Fin.ext hv.symm)
      simp [hk, hne]
  rw [hsum]
  simp [idx, Polynomial.X_pow_eq_monomial]

lemma vecToRing_monomialModVec {J : ℕ} (hJ : 0 < J) (m : ℕ) :
    vecToRing J (monomialModVec J m) = (ringY J) ^ m := by
  set r := m % (3 * J)
  have hr3 : r < 3 * J := Nat.mod_lt m (by omega)
  have hrem_pow : (ringY J) ^ m = (ringY J) ^ r := by
    have hdiv := (Nat.div_add_mod m (3 * J)).symm
    conv_lhs => rw [hdiv]
    rw [pow_add, pow_mul, ringY_pow_three_mul J, one_pow, one_mul]
  rw [hrem_pow]
  unfold vecToRing vecToPoly monomialModVec
  dsimp only
  have hsplit : Finset.univ.sum (fun k : Fin (2 * J) =>
      Polynomial.monomial k.val
        ((if r = k.val then (1 : ZMod 2) else 0) +
          (if 2 * J ≤ r ∧ r - 2 * J = k.val then 1 else 0) +
          (if 2 * J ≤ r ∧ r - J = k.val then 1 else 0))) =
      Finset.univ.sum (fun k : Fin (2 * J) =>
        Polynomial.monomial k.val (if r = k.val then (1 : ZMod 2) else 0)) +
      Finset.univ.sum (fun k : Fin (2 * J) =>
        Polynomial.monomial k.val (if 2 * J ≤ r ∧ r - 2 * J = k.val then (1 : ZMod 2) else 0)) +
      Finset.univ.sum (fun k : Fin (2 * J) =>
        Polynomial.monomial k.val (if 2 * J ≤ r ∧ r - J = k.val then (1 : ZMod 2) else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_add, map_add]
  rw [hsplit]
  by_cases hr2 : r < 2 * J
  · have hnot : ¬ (2 * J ≤ r) := by omega
    have hs1 := sum_unit_indicator_poly hr2
    have hs2 : Finset.univ.sum (fun k : Fin (2 * J) =>
        Polynomial.monomial k.val (if 2 * J ≤ r ∧ r - 2 * J = k.val then (1 : ZMod 2) else 0)) = 0 := by
      simp [hnot]
    have hs3 : Finset.univ.sum (fun k : Fin (2 * J) =>
        Polynomial.monomial k.val (if 2 * J ≤ r ∧ r - J = k.val then (1 : ZMod 2) else 0)) = 0 := by
      simp [hnot]
    rw [hs1, hs2, hs3, add_zero, add_zero, map_pow]
    rfl
  · have hge : 2 * J ≤ r := by omega
    have hs1 : Finset.univ.sum (fun k : Fin (2 * J) =>
        Polynomial.monomial k.val (if r = k.val then (1 : ZMod 2) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hne : r ≠ k.val := by omega
      simp [hne]
    have hs2 : Finset.univ.sum (fun k : Fin (2 * J) =>
        Polynomial.monomial k.val (if 2 * J ≤ r ∧ r - 2 * J = k.val then (1 : ZMod 2) else 0)) =
        Polynomial.X ^ (r - 2 * J) := by
      simpa [hge] using sum_unit_indicator_poly (J := J) (r := r - 2 * J) (by omega)
    have hs3 : Finset.univ.sum (fun k : Fin (2 * J) =>
        Polynomial.monomial k.val (if 2 * J ≤ r ∧ r - J = k.val then (1 : ZMod 2) else 0)) =
        Polynomial.X ^ (r - J) := by
      simpa [hge] using sum_unit_indicator_poly (J := J) (r := r - J) (by omega)
    rw [hs1, hs2, hs3, zero_add, map_add, map_pow, map_pow]
    change (ringY J) ^ (r - 2 * J) + (ringY J) ^ (r - J) = (ringY J) ^ r
    have hrJ : r - J = (r - 2 * J) + J := by omega
    have hr2J : r = (r - 2 * J) + 2 * J := by omega
    have hY2J : 1 + (ringY J) ^ J = (ringY J) ^ (2 * J) := by
      apply auxRing_eq_of_add_eq_zero
      calc
        1 + (ringY J) ^ J + (ringY J) ^ (2 * J) =
            (ringY J) ^ (2 * J) + (ringY J) ^ J + 1 := by ring
        _ = 0 := ringY_rel J
    calc
      (ringY J) ^ (r - 2 * J) + (ringY J) ^ (r - J) =
          (ringY J) ^ (r - 2 * J) * (1 + (ringY J) ^ J) := by
        rw [hrJ, pow_add]; ring
      _ = (ringY J) ^ (r - 2 * J) * (ringY J) ^ (2 * J) := by rw [hY2J]
      _ = (ringY J) ^ r := by rw [← pow_add, ← hr2J]

lemma vecToRing_mulYExp {J : ℕ} (hJ : 0 < J) (m : ℕ) (u : CoeffVec J) :
    vecToRing J (vecMulYExp J m u) = (ringY J) ^ m * vecToRing J u := by
  unfold vecMulYExp
  rw [vecToRing_finset_sum]
  calc
    Finset.univ.sum (fun i : Fin (2 * J) =>
        vecToRing J (vecScale J (u i) (monomialModVec J (i.val + m)))) =
      Finset.univ.sum (fun i : Fin (2 * J) =>
        toAuxRing J (Polynomial.C (u i)) * (ringY J) ^ (i.val + m)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [vecToRing_scale, vecToRing_monomialModVec hJ]
    _ = (ringY J) ^ m * Finset.univ.sum (fun i : Fin (2 * J) =>
        toAuxRing J (Polynomial.C (u i)) * (ringY J) ^ i.val) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [pow_add]
      ring
    _ = (ringY J) ^ m * vecToRing J u := by
      rw [← vecToRing_eq_sum_C_mul_ringY]

lemma vecToRing_mul {J : ℕ} (hJ : 0 < J) (u v : CoeffVec J) :
    vecToRing J (vecMul J u v) = vecToRing J u * vecToRing J v := by
  unfold vecMul
  rw [vecToRing_finset_sum]
  calc
    Finset.univ.sum (fun i : Fin (2 * J) =>
        vecToRing J (fun k => Finset.univ.sum (fun j : Fin (2 * J) =>
          (u i * v j) * monomialModVec J (i.val + j.val) k))) =
      Finset.univ.sum (fun i : Fin (2 * J) =>
        Finset.univ.sum (fun j : Fin (2 * J) =>
          (toAuxRing J (Polynomial.C (u i)) * (ringY J) ^ i.val) *
            (toAuxRing J (Polynomial.C (v j)) * (ringY J) ^ j.val))) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [vecToRing_finset_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      change vecToRing J (vecScale J (u i * v j) (monomialModVec J (i.val + j.val))) = _
      rw [vecToRing_scale, vecToRing_monomialModVec hJ, map_mul, map_mul, pow_add]
      ring
    _ = vecToRing J u * vecToRing J v := by
      rw [vecToRing_eq_sum_C_mul_ringY J u, vecToRing_eq_sum_C_mul_ringY J v, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]

lemma vecToRing_surjective {J : ℕ} (hJ : 0 < J) : Function.Surjective (vecToRing J) := by
  intro a
  refine Quotient.inductionOn' a (fun p => ?_)
  change ∃ u, vecToRing J u = toAuxRing J p
  refine Polynomial.induction_on' p ?_ ?_
  · intro p₁ p₂ ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩
    exact ⟨vecAdd J u₁ u₂, by rw [vecToRing_add, hu₁, hu₂, map_add]⟩
  · intro n c
    refine ⟨vecScale J c (monomialModVec J n), ?_⟩
    rw [vecToRing_scale, vecToRing_monomialModVec hJ n]
    unfold ringY
    rw [← map_pow, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]

noncomputable def auxRingEquivVec {J : ℕ} (hJ : 0 < J) : CoeffVec J ≃ AuxRing J :=
  Equiv.ofBijective (vecToRing J) ⟨vecToRing_injective hJ, vecToRing_surjective hJ⟩

/-- Principal `L`-th root of unity `ω = Y^{3J/L}` and its inverse `ω^{-1} = ω^{L-1}` in `A`. -/
noncomputable def omega (J L : ℕ) : AuxRing J :=
  (ringY J) ^ (3 * J / L)

noncomputable def omegaInv (J L : ℕ) : AuxRing J :=
  (omega J L) ^ (L - 1)

lemma omega_pow_L {J L : ℕ} (hdvd : L ∣ 3 * J) : (omega J L) ^ L = 1 := by
  unfold omega
  rw [← pow_mul, Nat.div_mul_cancel hdvd, ringY_pow_three_mul]

lemma omega_mul_omegaInv {J L : ℕ} (hL : 1 ≤ L) (hdvd : L ∣ 3 * J) :
    omega J L * omegaInv J L = 1 := by
  unfold omegaInv
  rw [← pow_succ', Nat.sub_add_cancel hL, omega_pow_L hdvd]

lemma omegaInv_mul_omega {J L : ℕ} (hL : 1 ≤ L) (hdvd : L ∣ 3 * J) :
    omegaInv J L * omega J L = 1 := by
  rw [mul_comm, omega_mul_omegaInv hL hdvd]

lemma omegaInv_pow_L {J L : ℕ} (hdvd : L ∣ 3 * J) : (omegaInv J L) ^ L = 1 := by
  unfold omegaInv
  rw [← pow_mul, mul_comm, pow_mul, omega_pow_L hdvd, one_pow]

/-- Factor out the largest power of 3 dividing `q > 0`: `q = 3^v * u` with `¬ (3 ∣ u)`. -/
lemma factor_three_pow : ∀ {q : ℕ}, 0 < q → ∃ v u : ℕ, q = 3 ^ v * u ∧ ¬ (3 ∣ u) ∧ 0 < u := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq
    by_cases h3 : 3 ∣ q
    · rcases h3 with ⟨q', rfl⟩
      have hq'pos : 0 < q' := by omega
      have hq'lt : q' < 3 * q' := by omega
      rcases ih q' hq'lt hq'pos with ⟨v, u, hqu, hndvd, hupos⟩
      refine ⟨v + 1, u, ?_, hndvd, hupos⟩
      rw [pow_succ', mul_assoc, ← hqu]
    · exact ⟨0, q, by simp, h3, hq⟩

private lemma ringY_pow_J_nondiv3_sum (J : ℕ) {u : ℕ} (hndvd : ¬ (3 ∣ u)) :
    1 + ((ringY J) ^ J) ^ u + ((ringY J) ^ J) ^ (2 * u) = 0 := by
  set z : AuxRing J := (ringY J) ^ J
  have hz3 : z ^ 3 = 1 := ringY_pow_J_cube J
  have hzrel : z ^ 2 + z + 1 = 0 := ringY_pow_J_rel J
  have hmod : ∀ m : ℕ, z ^ m = z ^ (m % 3) := fun m => by
    conv_lhs => rw [← Nat.div_add_mod m 3]
    rw [pow_add, pow_mul, hz3, one_pow, one_mul]
  rw [hmod u, hmod (2 * u)]
  have hrem : u % 3 = 1 ∨ u % 3 = 2 := by omega
  rcases hrem with h1 | h2
  · have h2u : (2 * u) % 3 = 2 := by omega
    rw [h1, h2u, pow_one]
    calc
      1 + z + z ^ 2 = z ^ 2 + z + 1 := by ring
      _ = 0 := hzrel
  · have h2u : (2 * u) % 3 = 1 := by omega
    rw [h2, h2u, pow_one]
    calc
      1 + z ^ 2 + z = z ^ 2 + z + 1 := by ring
      _ = 0 := hzrel

/-- Pure index bijection `(r, k, α) ↦ r + H * (α + 3 * k)` for Lemma `lem:root`. -/
def finThreeBlockEquiv (H v L : ℕ) (hH_pos : 0 < H) (hL_decomp : L = H * (3 * 3 ^ v)) :
    (Fin H × Fin (3 ^ v) × Fin 3) ≃ Fin L where
  toFun := fun ⟨r, k, α⟩ =>
    ⟨r.val + H * (α.val + 3 * k.val), by
      have hr : r.val < H := r.isLt
      have hk : k.val < 3 ^ v := k.isLt
      have hα : α.val < 3 := α.isLt
      have hle1 : α.val + 3 * k.val + 1 ≤ 3 * 3 ^ v := by omega
      have hlt_step : r.val + H * (α.val + 3 * k.val) < H * (α.val + 3 * k.val + 1) := by
        have hmul_succ : H * (α.val + 3 * k.val + 1) = H * (α.val + 3 * k.val) + H := by ring
        omega
      calc
        r.val + H * (α.val + 3 * k.val) < H * (α.val + 3 * k.val + 1) := hlt_step
        _ ≤ H * (3 * 3 ^ v) := Nat.mul_le_mul_left H hle1
        _ = L := hL_decomp.symm⟩
  invFun := fun j =>
    (⟨j.val % H, Nat.mod_lt _ hH_pos⟩,
     ⟨(j.val / H) / 3, by
       have hj : j.val < H * (3 * 3 ^ v) := by simpa [hL_decomp] using j.isLt
       have hj1 : j.val / H < 3 * 3 ^ v := Nat.div_lt_of_lt_mul hj
       exact Nat.div_lt_of_lt_mul hj1⟩,
     ⟨(j.val / H) % 3, Nat.mod_lt _ (by decide)⟩)
  left_inv := fun ⟨r, k, α⟩ => by
    have hr : r.val < H := r.isLt
    have hα : α.val < 3 := α.isLt
    have hmodH : (r.val + H * (α.val + 3 * k.val)) % H = r.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    have hdivH : (r.val + H * (α.val + 3 * k.val)) / H = α.val + 3 * k.val := by
      rw [Nat.add_mul_div_left _ _ hH_pos, Nat.div_eq_of_lt hr, zero_add]
    have hdiv3 : (α.val + 3 * k.val) / 3 = k.val := by
      rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hα, zero_add]
    have hmod3 : (α.val + 3 * k.val) % 3 = α.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hα]
    ext <;> simp [hmodH, hdivH, hdiv3, hmod3]
  right_inv := fun j => by
    ext
    dsimp only
    have h1 := Nat.div_add_mod (j.val / H) 3
    have h2 := Nat.div_add_mod j.val H
    calc
      j.val % H + H * ((j.val / H) % 3 + 3 * ((j.val / H) / 3)) =
          j.val % H + H * (3 * ((j.val / H) / 3) + (j.val / H) % 3) := by ring
      _ = j.val % H + H * (j.val / H) := by rw [h1]
      _ = H * (j.val / H) + j.val % H := by ring
      _ = j.val := h2

@[simp] lemma finThreeBlockEquiv_val (H v L : ℕ) (hH_pos : 0 < H)
    (hL_decomp : L = H * (3 * 3 ^ v)) (r : Fin H) (k : Fin (3 ^ v)) (α : Fin 3) :
    (finThreeBlockEquiv H v L hH_pos hL_decomp (r, k, α)).val =
      r.val + H * (α.val + 3 * k.val) := rfl

/-- **Lemma `lem:root` (Principal Root Orthogonality)**:
For `L = 3^ℓ`, `L ∣ 3J`, and `0 < q < L`, `∑_{j=0}^{L-1} ω^{q j} = 0` in `A`. -/
theorem omega_orthogonality {J ℓ : ℕ} (hdvd : 3 ^ ℓ ∣ 3 * J) {q : ℕ}
    (hq_pos : 0 < q) (hq_lt : q < 3 ^ ℓ) :
    Finset.univ.sum (fun j : Fin (3 ^ ℓ) => (omega J (3 ^ ℓ)) ^ (q * j.val)) = 0 := by
  rcases factor_three_pow hq_pos with ⟨v, u, hqu, hndvd, hupos⟩
  have hv_lt : v < ℓ := by
    by_contra hge
    have hpow : 3 ^ ℓ ≤ 3 ^ v := Nat.pow_le_pow_right (by decide) (by omega)
    have hle : 3 ^ v ≤ 3 ^ v * u := Nat.le_mul_of_pos_right _ hupos
    omega
  set H := 3 ^ (ℓ - (v + 1))
  have hH_pos : 0 < H := Nat.pos_of_ne_zero (by positivity)
  have hL_decomp : 3 ^ ℓ = H * (3 * 3 ^ v) := by
    dsimp [H]
    calc
      3 ^ ℓ = 3 ^ ((ℓ - (v + 1)) + (v + 1)) := by congr 1; omega
      _ = 3 ^ (ℓ - (v + 1)) * 3 ^ (v + 1) := pow_add _ _ _
      _ = 3 ^ (ℓ - (v + 1)) * (3 * 3 ^ v) := by rw [pow_succ']
  have hqH_pow : (omega J (3 ^ ℓ)) ^ (q * H) = ((ringY J) ^ J) ^ u := by
    unfold omega
    rw [← pow_mul, ← pow_mul]
    congr 1
    set K := 3 * J / 3 ^ ℓ
    have hKL : K * 3 ^ ℓ = 3 * J := Nat.div_mul_cancel hdvd
    have h3cancel : 3 * (K * 3 ^ v * H) = 3 * J := by
      calc
        3 * (K * 3 ^ v * H) = K * (H * (3 * 3 ^ v)) := by ring
        _ = K * 3 ^ ℓ := by rw [← hL_decomp]
        _ = 3 * J := hKL
    have hJ_eq : J = K * 3 ^ v * H := by omega
    calc
      K * (q * H) = (K * 3 ^ v * H) * u := by rw [hqu]; ring
      _ = J * u := by rw [← hJ_eq]
  rw [← Equiv.sum_comp (finThreeBlockEquiv H v (3 ^ ℓ) hH_pos hL_decomp)]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro r _
  apply Finset.sum_eq_zero
  intro k _
  rw [Fin.sum_univ_three]
  simp only [finThreeBlockEquiv_val, Fin.val_zero, Fin.val_one, Fin.val_two]
  set base : AuxRing J := (omega J (3 ^ ℓ)) ^ (q * (r.val + 3 * k.val * H))
  set wqH : AuxRing J := (omega J (3 ^ ℓ)) ^ (q * H)
  have ht0 : (omega J (3 ^ ℓ)) ^ (q * (r.val + H * (0 + 3 * k.val))) = base := by
    dsimp [base]
    congr 1
    ring
  have ht1 : (omega J (3 ^ ℓ)) ^ (q * (r.val + H * (1 + 3 * k.val))) = base * wqH := by
    dsimp [base, wqH]
    rw [← pow_add]
    congr 1
    ring
  have ht2 : (omega J (3 ^ ℓ)) ^ (q * (r.val + H * (2 + 3 * k.val))) = base * wqH ^ 2 := by
    dsimp [base, wqH]
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have hwqH1 : wqH = ((ringY J) ^ J) ^ u := hqH_pow
  have hwqH2 : wqH ^ 2 = ((ringY J) ^ J) ^ (2 * u) := by
    rw [hwqH1, ← pow_mul, Nat.mul_comm u 2]
  rw [ht0, ht1, ht2, hwqH2, hwqH1]
  calc
    base + base * ((ringY J) ^ J) ^ u + base * ((ringY J) ^ J) ^ (2 * u) =
        base * (1 + ((ringY J) ^ J) ^ u + ((ringY J) ^ J) ^ (2 * u)) := by ring
    _ = base * 0 := by rw [ringY_pow_J_nondiv3_sum J hndvd]
    _ = 0 := mul_zero _

/-- Fourier transform `DFT_w` over `(AuxRing J)^L`. -/
noncomputable def ringDFT (J L : ℕ) (w : AuxRing J) (x : Fin L → AuxRing J) :
    Fin L → AuxRing J :=
  fun q => Finset.univ.sum (fun j : Fin L => x j * w ^ (j.val * q.val))

private lemma omega_kernel_sum {J ℓ : ℕ} (hdvd : 3 ^ ℓ ∣ 3 * J) (j r : Fin (3 ^ ℓ)) :
    Finset.univ.sum (fun q : Fin (3 ^ ℓ) =>
      (omega J (3 ^ ℓ)) ^ (j.val * q.val) *
        (omegaInv J (3 ^ ℓ)) ^ (q.val * r.val)) =
      if j = r then 1 else 0 := by
  have hL1 : 1 ≤ 3 ^ ℓ := Nat.one_le_pow ℓ 3 (by decide)
  have hw_inv : omega J (3 ^ ℓ) * omegaInv J (3 ^ ℓ) = 1 := omega_mul_omegaInv hL1 hdvd
  have hwL : (omega J (3 ^ ℓ)) ^ (3 ^ ℓ) = 1 := omega_pow_L hdvd
  by_cases hjr : j = r
  · simp only [hjr, ↓reduceIte]
    have h1 : ∀ q : Fin (3 ^ ℓ),
        (omega J (3 ^ ℓ)) ^ (r.val * q.val) * (omegaInv J (3 ^ ℓ)) ^ (q.val * r.val) = 1 :=
      fun q => by
        rw [Nat.mul_comm q.val r.val, ← mul_pow, hw_inv, one_pow]
    simp_rw [h1]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_one]
    exact auxRing_three_pow_natCast J ℓ
  · simp only [hjr, ↓reduceIte]
    have hval_ne : j.val ≠ r.val := fun hv => hjr (Fin.ext hv)
    set d : ℕ := if r.val ≤ j.val then j.val - r.val else 3 ^ ℓ + j.val - r.val
    have hd_pos : 0 < d := by
      dsimp [d]
      split_ifs <;> omega
    have hd_lt : d < 3 ^ ℓ := by
      dsimp [d]
      have hj : j.val < 3 ^ ℓ := j.isLt
      have hr : r.val < 3 ^ ℓ := r.isLt
      split_ifs <;> omega
    have hterm : ∀ q : Fin (3 ^ ℓ),
        (omega J (3 ^ ℓ)) ^ (j.val * q.val) * (omegaInv J (3 ^ ℓ)) ^ (q.val * r.val) =
          (omega J (3 ^ ℓ)) ^ (d * q.val) := fun q => by
      have h1 : (omega J (3 ^ ℓ) * omegaInv J (3 ^ ℓ)) ^ (r.val * q.val) = 1 := by
        rw [hw_inv, one_pow]
      calc
        (omega J (3 ^ ℓ)) ^ (j.val * q.val) * (omegaInv J (3 ^ ℓ)) ^ (q.val * r.val) =
            (omega J (3 ^ ℓ)) ^ (d * q.val) *
              (omega J (3 ^ ℓ) * omegaInv J (3 ^ ℓ)) ^ (r.val * q.val) := by
          rw [mul_pow, ← mul_assoc, ← pow_add, Nat.mul_comm q.val r.val]
          congr 1
          dsimp [d]
          split_ifs with hle
          · have hadd : (j.val - r.val) * q.val + r.val * q.val = j.val * q.val := by
              rw [← add_mul, Nat.sub_add_cancel hle]
            rw [hadd]
          · have hr : r.val < 3 ^ ℓ := r.isLt
            have hadd : (3 ^ ℓ + j.val - r.val) * q.val + r.val * q.val =
                3 ^ ℓ * q.val + j.val * q.val := by
              rw [← add_mul, Nat.sub_add_cancel (by omega), add_mul]
            have hpow_mod : (omega J (3 ^ ℓ)) ^ (3 ^ ℓ * q.val + j.val * q.val) =
                (omega J (3 ^ ℓ)) ^ (j.val * q.val) := by
              rw [pow_add, pow_mul, hwL, one_pow, one_mul]
            rw [hadd, hpow_mod]
        _ = (omega J (3 ^ ℓ)) ^ (d * q.val) := by rw [h1, mul_one]
    simp_rw [hterm]
    exact omega_orthogonality hdvd hd_pos hd_lt

/-- **DFT Inversion (`eq:inverse`)**: `DFT_{ω⁻¹} (DFT_ω x) = x` in `(AuxRing J)^{3^ℓ}`. -/
theorem ringDFT_inv_left {J ℓ : ℕ} (hdvd : 3 ^ ℓ ∣ 3 * J) (x : Fin (3 ^ ℓ) → AuxRing J) :
    ringDFT J (3 ^ ℓ) (omegaInv J (3 ^ ℓ)) (ringDFT J (3 ^ ℓ) (omega J (3 ^ ℓ)) x) = x := by
  funext r
  unfold ringDFT
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ j : Fin (3 ^ ℓ),
      Finset.univ.sum (fun q : Fin (3 ^ ℓ) =>
        x j * (omega J (3 ^ ℓ)) ^ (j.val * q.val) *
          (omegaInv J (3 ^ ℓ)) ^ (q.val * r.val)) =
      if j = r then x j else 0 := fun j => by
    calc
      Finset.univ.sum (fun q : Fin (3 ^ ℓ) =>
          x j * (omega J (3 ^ ℓ)) ^ (j.val * q.val) *
            (omegaInv J (3 ^ ℓ)) ^ (q.val * r.val)) =
        x j * Finset.univ.sum (fun q : Fin (3 ^ ℓ) =>
          (omega J (3 ^ ℓ)) ^ (j.val * q.val) *
            (omegaInv J (3 ^ ℓ)) ^ (q.val * r.val)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        ring
      _ = x j * (if j = r then 1 else 0) := by rw [omega_kernel_sum hdvd j r]
      _ = if j = r then x j else 0 := by split_ifs <;> simp
  simp_rw [hinner]
  simp

/-- Reverse DFT Inversion: `DFT_ω (DFT_{ω⁻¹} y) = y` in `(AuxRing J)^{3^ℓ}`. -/
theorem ringDFT_inv_right {J ℓ : ℕ} (hdvd : 3 ^ ℓ ∣ 3 * J) (y : Fin (3 ^ ℓ) → AuxRing J) :
    ringDFT J (3 ^ ℓ) (omega J (3 ^ ℓ)) (ringDFT J (3 ^ ℓ) (omegaInv J (3 ^ ℓ)) y) = y := by
  funext r
  unfold ringDFT
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ j : Fin (3 ^ ℓ),
      Finset.univ.sum (fun q : Fin (3 ^ ℓ) =>
        y j * (omegaInv J (3 ^ ℓ)) ^ (j.val * q.val) *
          (omega J (3 ^ ℓ)) ^ (q.val * r.val)) =
      if r = j then y j else 0 := fun j => by
    calc
      Finset.univ.sum (fun q : Fin (3 ^ ℓ) =>
          y j * (omegaInv J (3 ^ ℓ)) ^ (j.val * q.val) *
            (omega J (3 ^ ℓ)) ^ (q.val * r.val)) =
        y j * Finset.univ.sum (fun q : Fin (3 ^ ℓ) =>
          (omega J (3 ^ ℓ)) ^ (r.val * q.val) *
            (omegaInv J (3 ^ ℓ)) ^ (q.val * j.val)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [Nat.mul_comm j.val q.val, Nat.mul_comm q.val r.val]
        ring
      _ = y j * (if r = j then 1 else 0) := by rw [omega_kernel_sum hdvd r j]
      _ = if r = j then y j else 0 := by split_ifs <;> simp
  simp_rw [hinner]
  simp

/-!
# Section 3: Concrete Vector DFT & 2-Layer Small Transform Decomposition (§2.3)
-/

/-- Concrete multiplication of `u : CoeffVec J` by `ω^s = Y^{(3J/L) s}`. -/
def vecMulOmegaPow (J L s : ℕ) (u : CoeffVec J) : CoeffVec J :=
  vecMulYExp J ((3 * J / L) * s) u

/-- Concrete multiplication of `u : CoeffVec J` by `(ω^{-1})^s = ω^{(L-1) s}`. -/
def vecMulOmegaInvPow (J L s : ℕ) (u : CoeffVec J) : CoeffVec J :=
  vecMulOmegaPow J L ((L - 1) * s) u

lemma vecToRing_mulOmegaPow {J : ℕ} (hJ : 0 < J) (L s : ℕ) (u : CoeffVec J) :
    vecToRing J (vecMulOmegaPow J L s u) = (omega J L) ^ s * vecToRing J u := by
  unfold vecMulOmegaPow omega
  rw [vecToRing_mulYExp hJ, pow_mul]

lemma vecToRing_mulOmegaInvPow {J : ℕ} (hJ : 0 < J) (L s : ℕ) (u : CoeffVec J) :
    vecToRing J (vecMulOmegaInvPow J L s u) = (omegaInv J L) ^ s * vecToRing J u := by
  unfold vecMulOmegaInvPow omegaInv
  rw [vecToRing_mulOmegaPow hJ, pow_mul]

/-- Concrete 1-layer forward and inverse DFT on `(CoeffVec J)^L`. -/
def vecDFT (J L : ℕ) (x : Fin L → CoeffVec J) (q : Fin L) : CoeffVec J :=
  fun k => Finset.univ.sum (fun j : Fin L => vecMulOmegaPow J L (j.val * q.val) (x j) k)

def vecIDFT (J L : ℕ) (x : Fin L → CoeffVec J) (q : Fin L) : CoeffVec J :=
  fun k => Finset.univ.sum (fun j : Fin L => vecMulOmegaInvPow J L (j.val * q.val) (x j) k)

lemma vecToRing_vecDFT {J : ℕ} (hJ : 0 < J) (L : ℕ) (x : Fin L → CoeffVec J) (q : Fin L) :
    vecToRing J (vecDFT J L x q) = ringDFT J L (omega J L) (fun j => vecToRing J (x j)) q := by
  unfold vecDFT ringDFT
  rw [vecToRing_finset_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [vecToRing_mulOmegaPow hJ, mul_comm]

lemma vecToRing_vecIDFT {J : ℕ} (hJ : 0 < J) (L : ℕ) (x : Fin L → CoeffVec J) (q : Fin L) :
    vecToRing J (vecIDFT J L x q) =
      ringDFT J L (omegaInv J L) (fun j => vecToRing J (x j)) q := by
  unfold vecIDFT ringDFT
  rw [vecToRing_finset_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [vecToRing_mulOmegaInvPow hJ, mul_comm]

theorem vecIDFT_vecDFT {J ℓ : ℕ} (hJ : 0 < J) (hdvd : 3 ^ ℓ ∣ 3 * J)
    (x : Fin (3 ^ ℓ) → CoeffVec J) :
    vecIDFT J (3 ^ ℓ) (vecDFT J (3 ^ ℓ) x) = x := by
  funext r
  apply vecToRing_injective hJ
  rw [vecToRing_vecIDFT hJ]
  have h1 : (fun j => vecToRing J (vecDFT J (3 ^ ℓ) x j)) =
      ringDFT J (3 ^ ℓ) (omega J (3 ^ ℓ)) (fun j => vecToRing J (x j)) := by
    funext j
    exact vecToRing_vecDFT hJ (3 ^ ℓ) x j
  rw [h1]
  exact congrFun (ringDFT_inv_left hdvd (fun j => vecToRing J (x j))) r

theorem vecDFT_vecIDFT {J ℓ : ℕ} (hJ : 0 < J) (hdvd : 3 ^ ℓ ∣ 3 * J)
    (y : Fin (3 ^ ℓ) → CoeffVec J) :
    vecDFT J (3 ^ ℓ) (vecIDFT J (3 ^ ℓ) y) = y := by
  funext r
  apply vecToRing_injective hJ
  rw [vecToRing_vecDFT hJ]
  have h1 : (fun j => vecToRing J (vecIDFT J (3 ^ ℓ) y j)) =
      ringDFT J (3 ^ ℓ) (omegaInv J (3 ^ ℓ)) (fun j => vecToRing J (y j)) := by
    funext j
    exact vecToRing_vecIDFT hJ (3 ^ ℓ) y j
  rw [h1]
  exact congrFun (ringDFT_inv_right hdvd (fun j => vecToRing J (y j))) r

/-- Index helpers for `L = L₁ * L₂`. -/
lemma stage1_idx_lt {L L₁ L₂ : ℕ} (hL : L = L₁ * L₂) (j₁ : Fin L₁) (j₂ : Fin L₂) :
    L₂ * j₁.val + j₂.val < L := by
  have hj1 : j₁.val + 1 ≤ L₁ := j₁.isLt
  have hj2 : j₂.val < L₂ := j₂.isLt
  calc
    L₂ * j₁.val + j₂.val < L₂ * (j₁.val + 1) := by rw [mul_add, mul_one]; omega
    _ ≤ L₂ * L₁ := Nat.mul_le_mul_left L₂ hj1
    _ = L := by rw [mul_comm, ← hL]

lemma stage2_idx_lt {L L₁ L₂ : ℕ} (hL : L = L₁ * L₂) (q₁ : Fin L₁) (q₂ : Fin L₂) :
    q₁.val + L₁ * q₂.val < L := by
  have hq1 : q₁.val < L₁ := q₁.isLt
  have hq2 : q₂.val + 1 ≤ L₂ := q₂.isLt
  calc
    q₁.val + L₁ * q₂.val < L₁ * (q₂.val + 1) := by rw [mul_add, mul_one]; omega
    _ ≤ L₁ * L₂ := Nat.mul_le_mul_left L₁ hq2
    _ = L := hL.symm

/-- Abstract 2-layer Stage-1 and Stage-2 maps over `AuxRing J` (`eq:stage1`–`eq:stage2`). -/
noncomputable def ringStage1 (J L L₁ L₂ : ℕ) (hL : L = L₁ * L₂) (w : AuxRing J)
    (x : Fin L → AuxRing J) (j₂ : Fin L₂) (q₁ : Fin L₁) : AuxRing J :=
  w ^ (j₂.val * q₁.val) *
    Finset.univ.sum (fun j₁ : Fin L₁ =>
      (w ^ L₂) ^ (j₁.val * q₁.val) * x ⟨L₂ * j₁.val + j₂.val, stage1_idx_lt hL j₁ j₂⟩)

noncomputable def ringStage2 (J L₁ L₂ : ℕ) (w : AuxRing J)
    (y : Fin L₂ → Fin L₁ → AuxRing J) (q₁ : Fin L₁) (q₂ : Fin L₂) : AuxRing J :=
  Finset.univ.sum (fun j₂ : Fin L₂ => (w ^ L₁) ^ (j₂.val * q₂.val) * y j₂ q₁)

/-- **2-Layer Small Transform Decomposition (`eq:stage1`–`eq:stage2`)** in `AuxRing J`:
For any `w` with `w^L = 1`, Stage 2 composed with Stage 1 equals `DFT_w` at `q₁ + L₁ q₂`. -/
theorem ringStage2_ringStage1_eq_ringDFT {J L L₁ L₂ : ℕ} (hL : L = L₁ * L₂)
    (hL₂ : 0 < L₂) {w : AuxRing J} (hw : w ^ L = 1)
    (x : Fin L → AuxRing J) (q₁ : Fin L₁) (q₂ : Fin L₂) :
    ringStage2 J L₁ L₂ w (ringStage1 J L L₁ L₂ hL w x) q₁ q₂ =
      ringDFT J L w x ⟨q₁.val + L₁ * q₂.val, stage2_idx_lt hL q₁ q₂⟩ := by
  unfold ringStage2 ringStage1 ringDFT
  let e : Fin L₁ × Fin L₂ ≃ Fin L :=
    { toFun := fun ⟨j₁, j₂⟩ => ⟨L₂ * j₁.val + j₂.val, stage1_idx_lt hL j₁ j₂⟩
      invFun := fun j =>
        (⟨j.val / L₂, by
           have hj : j.val < L₂ * L₁ := by simpa [hL, Nat.mul_comm] using j.isLt
           exact Nat.div_lt_of_lt_mul hj⟩,
         ⟨j.val % L₂, Nat.mod_lt _ hL₂⟩)
      left_inv := fun ⟨j₁, j₂⟩ => by
        have hj2 : j₂.val < L₂ := j₂.isLt
        have hdiv : (L₂ * j₁.val + j₂.val) / L₂ = j₁.val := by
          rw [Nat.mul_comm L₂ j₁.val, Nat.add_comm, Nat.add_mul_div_right _ _ hL₂,
            Nat.div_eq_of_lt hj2, zero_add]
        have hmod : (L₂ * j₁.val + j₂.val) % L₂ = j₂.val := by
          rw [Nat.mul_comm L₂ j₁.val, Nat.add_comm, Nat.add_mul_mod_self_right,
            Nat.mod_eq_of_lt hj2]
        ext <;> simp [hdiv, hmod]
      right_inv := fun j => by
        ext
        dsimp
        exact Nat.div_add_mod j.val L₂ }
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j₂ _ => ?_)
  rw [← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j₁ _ => ?_)
  have hexp : (L₂ * j₁.val + j₂.val) * (q₁.val + L₁ * q₂.val) =
      (L₁ * (j₂.val * q₂.val) + j₂.val * q₁.val + L₂ * (j₁.val * q₁.val)) +
        L * (j₁.val * q₂.val) := by
    rw [hL]
    ring
  have hw_prod : w ^ ((L₂ * j₁.val + j₂.val) * (q₁.val + L₁ * q₂.val)) =
      (w ^ L₁) ^ (j₂.val * q₂.val) * w ^ (j₂.val * q₁.val) *
        (w ^ L₂) ^ (j₁.val * q₁.val) := by
    rw [hexp, pow_add, pow_mul w L, hw, one_pow, mul_one, pow_add, pow_add,
      ← pow_mul, ← pow_mul]
  dsimp [e]
  rw [hw_prod]
  ring

/-- Concrete Stage-1 and Stage-2 small transforms on `CoeffVec J` (`eq:stage1`–`eq:stage2`). -/
def vecDFTStage1 (J L L₁ L₂ : ℕ) (hL : L = L₁ * L₂)
    (x : Fin L → CoeffVec J) (j₂ : Fin L₂) (q₁ : Fin L₁) : CoeffVec J :=
  vecMulOmegaPow J L (j₂.val * q₁.val)
    (fun k => Finset.univ.sum (fun j₁ : Fin L₁ =>
      vecMulOmegaPow J L (L₂ * (j₁.val * q₁.val))
        (x ⟨L₂ * j₁.val + j₂.val, stage1_idx_lt hL j₁ j₂⟩) k))

def vecDFTStage2 (J L L₁ L₂ : ℕ)
    (y : Fin L₂ → Fin L₁ → CoeffVec J) (q₁ : Fin L₁) (q₂ : Fin L₂) : CoeffVec J :=
  fun k => Finset.univ.sum (fun j₂ : Fin L₂ =>
    vecMulOmegaPow J L (L₁ * (j₂.val * q₂.val)) (y j₂ q₁) k)

def vecDFTStage2Flat (J L L₁ L₂ : ℕ) (hL : L = L₁ * L₂) (hL₁ : 0 < L₁)
    (y : Fin L₂ → Fin L₁ → CoeffVec J) (q : Fin L) : CoeffVec J :=
  vecDFTStage2 J L L₁ L₂ y
    ⟨q.val % L₁, Nat.mod_lt _ hL₁⟩
    ⟨q.val / L₁, Nat.div_lt_of_lt_mul (by simpa [hL] using q.isLt)⟩

def vecIDFTStage1 (J L L₁ L₂ : ℕ) (hL : L = L₁ * L₂)
    (x : Fin L → CoeffVec J) (j₂ : Fin L₂) (q₁ : Fin L₁) : CoeffVec J :=
  vecMulOmegaInvPow J L (j₂.val * q₁.val)
    (fun k => Finset.univ.sum (fun j₁ : Fin L₁ =>
      vecMulOmegaInvPow J L (L₂ * (j₁.val * q₁.val))
        (x ⟨L₂ * j₁.val + j₂.val, stage1_idx_lt hL j₁ j₂⟩) k))

def vecIDFTStage2 (J L L₁ L₂ : ℕ)
    (y : Fin L₂ → Fin L₁ → CoeffVec J) (q₁ : Fin L₁) (q₂ : Fin L₂) : CoeffVec J :=
  fun k => Finset.univ.sum (fun j₂ : Fin L₂ =>
    vecMulOmegaInvPow J L (L₁ * (j₂.val * q₂.val)) (y j₂ q₁) k)

def vecIDFTStage2Flat (J L L₁ L₂ : ℕ) (hL : L = L₁ * L₂) (hL₁ : 0 < L₁)
    (y : Fin L₂ → Fin L₁ → CoeffVec J) (q : Fin L) : CoeffVec J :=
  vecIDFTStage2 J L L₁ L₂ y
    ⟨q.val % L₁, Nat.mod_lt _ hL₁⟩
    ⟨q.val / L₁, Nat.div_lt_of_lt_mul (by simpa [hL] using q.isLt)⟩

lemma vecToRing_vecDFTStage1 {J L L₁ L₂ : ℕ} (hJ : 0 < J) (hL : L = L₁ * L₂)
    (x : Fin L → CoeffVec J) (j₂ : Fin L₂) (q₁ : Fin L₁) :
    vecToRing J (vecDFTStage1 J L L₁ L₂ hL x j₂ q₁) =
      ringStage1 J L L₁ L₂ hL (omega J L) (fun j => vecToRing J (x j)) j₂ q₁ := by
  unfold vecDFTStage1 ringStage1
  rw [vecToRing_mulOmegaPow hJ, vecToRing_finset_sum]
  congr 1
  refine Finset.sum_congr rfl (fun j₁ _ => ?_)
  rw [vecToRing_mulOmegaPow hJ, pow_mul]

lemma vecToRing_vecDFTStage2 {J L L₁ L₂ : ℕ} (hJ : 0 < J)
    (y : Fin L₂ → Fin L₁ → CoeffVec J) (q₁ : Fin L₁) (q₂ : Fin L₂) :
    vecToRing J (vecDFTStage2 J L L₁ L₂ y q₁ q₂) =
      ringStage2 J L₁ L₂ (omega J L) (fun j₂ q₁ => vecToRing J (y j₂ q₁)) q₁ q₂ := by
  unfold vecDFTStage2 ringStage2
  rw [vecToRing_finset_sum]
  refine Finset.sum_congr rfl (fun j₂ _ => ?_)
  rw [vecToRing_mulOmegaPow hJ, pow_mul]

lemma vecToRing_vecIDFTStage1 {J L L₁ L₂ : ℕ} (hJ : 0 < J) (hL : L = L₁ * L₂)
    (x : Fin L → CoeffVec J) (j₂ : Fin L₂) (q₁ : Fin L₁) :
    vecToRing J (vecIDFTStage1 J L L₁ L₂ hL x j₂ q₁) =
      ringStage1 J L L₁ L₂ hL (omegaInv J L) (fun j => vecToRing J (x j)) j₂ q₁ := by
  unfold vecIDFTStage1 ringStage1
  rw [vecToRing_mulOmegaInvPow hJ, vecToRing_finset_sum]
  congr 1
  refine Finset.sum_congr rfl (fun j₁ _ => ?_)
  rw [vecToRing_mulOmegaInvPow hJ, pow_mul]

lemma vecToRing_vecIDFTStage2 {J L L₁ L₂ : ℕ} (hJ : 0 < J)
    (y : Fin L₂ → Fin L₁ → CoeffVec J) (q₁ : Fin L₁) (q₂ : Fin L₂) :
    vecToRing J (vecIDFTStage2 J L L₁ L₂ y q₁ q₂) =
      ringStage2 J L₁ L₂ (omegaInv J L) (fun j₂ q₁ => vecToRing J (y j₂ q₁)) q₁ q₂ := by
  unfold vecIDFTStage2 ringStage2
  rw [vecToRing_finset_sum]
  refine Finset.sum_congr rfl (fun j₂ _ => ?_)
  rw [vecToRing_mulOmegaInvPow hJ, pow_mul]

/-- Flattened linear XOR coordinate formulas for Stage-1 forward and inverse transforms,
expressing each output bit directly as a linear combination of input bits. -/
lemma vecDFTStage1_eq_flat_sum {J L L₁ L₂ : ℕ} (hJ : 0 < J) (hL : L = L₁ * L₂)
    (x : Fin L → CoeffVec J) (j₂ : Fin L₂) (q₁ : Fin L₁) :
    vecDFTStage1 J L L₁ L₂ hL x j₂ q₁ =
      fun k => Finset.univ.sum (fun j₁ : Fin L₁ =>
        vecMulOmegaPow J L (j₂.val * q₁.val + L₂ * (j₁.val * q₁.val))
          (x ⟨L₂ * j₁.val + j₂.val, stage1_idx_lt hL j₁ j₂⟩) k) := by
  apply vecToRing_injective hJ
  rw [vecToRing_vecDFTStage1 hJ hL, vecToRing_finset_sum]
  unfold ringStage1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j₁ _ => ?_)
  rw [vecToRing_mulOmegaPow hJ, pow_add, ← pow_mul (omega J L) L₂, mul_assoc]

lemma vecIDFTStage1_eq_flat_sum {J L L₁ L₂ : ℕ} (hJ : 0 < J) (hL : L = L₁ * L₂)
    (x : Fin L → CoeffVec J) (j₂ : Fin L₂) (q₁ : Fin L₁) :
    vecIDFTStage1 J L L₁ L₂ hL x j₂ q₁ =
      fun k => Finset.univ.sum (fun j₁ : Fin L₁ =>
        vecMulOmegaInvPow J L (j₂.val * q₁.val + L₂ * (j₁.val * q₁.val))
          (x ⟨L₂ * j₁.val + j₂.val, stage1_idx_lt hL j₁ j₂⟩) k) := by
  apply vecToRing_injective hJ
  rw [vecToRing_vecIDFTStage1 hJ hL, vecToRing_finset_sum]
  unfold ringStage1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j₁ _ => ?_)
  rw [vecToRing_mulOmegaInvPow hJ, pow_add, ← pow_mul (omegaInv J L) L₂, mul_assoc]

/-- Concrete 2-layer forward decomposition equals `vecDFT`. -/
theorem vecDFTStage2_vecDFTStage1_eq_vecDFT {J L L₁ L₂ : ℕ} (hJ : 0 < J)
    (hL : L = L₁ * L₂) (hL₂ : 0 < L₂) (hdvd : L ∣ 3 * J)
    (x : Fin L → CoeffVec J) (q₁ : Fin L₁) (q₂ : Fin L₂) :
    vecDFTStage2 J L L₁ L₂ (vecDFTStage1 J L L₁ L₂ hL x) q₁ q₂ =
      vecDFT J L x ⟨q₁.val + L₁ * q₂.val, stage2_idx_lt hL q₁ q₂⟩ := by
  apply vecToRing_injective hJ
  rw [vecToRing_vecDFTStage2 hJ, vecToRing_vecDFT hJ]
  have hs1 : (fun j₂ q₁ => vecToRing J (vecDFTStage1 J L L₁ L₂ hL x j₂ q₁)) =
      ringStage1 J L L₁ L₂ hL (omega J L) (fun j => vecToRing J (x j)) := by
    funext j₂ q₁'
    exact vecToRing_vecDFTStage1 hJ hL x j₂ q₁'
  rw [hs1]
  exact ringStage2_ringStage1_eq_ringDFT hL hL₂ (omega_pow_L hdvd) _ q₁ q₂

theorem vecDFTStage2Flat_vecDFTStage1_eq_vecDFT {J L L₁ L₂ : ℕ} (hJ : 0 < J)
    (hL : L = L₁ * L₂) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hdvd : L ∣ 3 * J)
    (x : Fin L → CoeffVec J) :
    vecDFTStage2Flat J L L₁ L₂ hL hL₁ (vecDFTStage1 J L L₁ L₂ hL x) = vecDFT J L x := by
  funext q
  unfold vecDFTStage2Flat
  rw [vecDFTStage2_vecDFTStage1_eq_vecDFT hJ hL hL₂ hdvd]
  congr 1
  ext
  dsimp
  rw [Nat.add_comm, Nat.div_add_mod]

/-- Concrete 2-layer inverse decomposition equals `vecIDFT`. -/
theorem vecIDFTStage2_vecIDFTStage1_eq_vecIDFT {J L L₁ L₂ : ℕ} (hJ : 0 < J)
    (hL : L = L₁ * L₂) (hL₂ : 0 < L₂) (hdvd : L ∣ 3 * J)
    (x : Fin L → CoeffVec J) (q₁ : Fin L₁) (q₂ : Fin L₂) :
    vecIDFTStage2 J L L₁ L₂ (vecIDFTStage1 J L L₁ L₂ hL x) q₁ q₂ =
      vecIDFT J L x ⟨q₁.val + L₁ * q₂.val, stage2_idx_lt hL q₁ q₂⟩ := by
  apply vecToRing_injective hJ
  rw [vecToRing_vecIDFTStage2 hJ, vecToRing_vecIDFT hJ]
  have hs1 : (fun j₂ q₁ => vecToRing J (vecIDFTStage1 J L L₁ L₂ hL x j₂ q₁)) =
      ringStage1 J L L₁ L₂ hL (omegaInv J L) (fun j => vecToRing J (x j)) := by
    funext j₂ q₁'
    exact vecToRing_vecIDFTStage1 hJ hL x j₂ q₁'
  rw [hs1]
  exact ringStage2_ringStage1_eq_ringDFT hL hL₂ (omegaInv_pow_L hdvd) _ q₁ q₂

theorem vecIDFTStage2Flat_vecIDFTStage1_eq_vecIDFT {J L L₁ L₂ : ℕ} (hJ : 0 < J)
    (hL : L = L₁ * L₂) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hdvd : L ∣ 3 * J)
    (x : Fin L → CoeffVec J) :
    vecIDFTStage2Flat J L L₁ L₂ hL hL₁ (vecIDFTStage1 J L L₁ L₂ hL x) = vecIDFT J L x := by
  funext q
  unfold vecIDFTStage2Flat
  rw [vecIDFTStage2_vecIDFTStage1_eq_vecIDFT hJ hL hL₂ hdvd]
  congr 1
  ext
  dsimp
  rw [Nat.add_comm, Nat.div_add_mod]

/-!
# Section 4: Carryless Block Convolution, Overlap-XOR, and Cyclic Folding (§3.1 & §4.1)
-/

/-- Exact integer-index carryless convolution `c_full u = ∑_{i + j = u} a i * b j`. -/
def polyFullConv (d : ℕ) (a b : Fin d → ZMod 2) (u : Fin (2 * d)) : ZMod 2 :=
  (Finset.univ.filter (fun p : Fin d × Fin d => p.1.val + p.2.val = u.val)).sum
    (fun p => a p.1 * b p.2)

/-- Polynomial representation of a degree-`< d` bit vector. -/
noncomputable def inputToPoly (d : ℕ) (a : Fin d → ZMod 2) : Polynomial (ZMod 2) :=
  Finset.univ.sum (fun i : Fin d => Polynomial.monomial i.val (a i))

lemma inputToPoly_coeff {d : ℕ} (a : Fin d → ZMod 2) (k : ℕ) :
    (inputToPoly d a).coeff k = if hk : k < d then a ⟨k, hk⟩ else 0 := by
  unfold inputToPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hk : k < d
  · simp only [hk, ↓reduceDIte]
    set idx : Fin d := ⟨k, hk⟩
    have hsum : Finset.univ.sum (fun i : Fin d => if i.val = k then a i else 0) =
        Finset.univ.sum (fun i : Fin d => if i = idx then a i else 0) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : i = idx
      · subst hi; simp [idx]
      · have hne : i.val ≠ k := fun hv => hi (Fin.ext hv)
        simp [hi, hne]
    rw [hsum]
    simp [idx]
  · simp only [hk, ↓reduceDIte]
    apply Finset.sum_eq_zero
    intro i _
    have hne : i.val ≠ k := by omega
    simp [hne]

lemma inputToPoly_mul_coeff {d : ℕ} (a b : Fin d → ZMod 2) (k : ℕ) :
    (inputToPoly d a * inputToPoly d b).coeff k =
      (Finset.univ.filter (fun p : Fin d × Fin d => p.1.val + p.2.val = k)).sum
        (fun p => a p.1 * b p.2) := by
  unfold inputToPoly
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, Polynomial.monomial_mul_monomial]
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_filter]
  exact (Fintype.sum_prod_type (fun p : Fin d × Fin d =>
    if p.1.val + p.2.val = k then a p.1 * b p.2 else 0)).symm

lemma polyFullConv_eq_mul_coeff {d : ℕ} (a b : Fin d → ZMod 2) (u : Fin (2 * d)) :
    polyFullConv d a b u = (inputToPoly d a * inputToPoly d b).coeff u.val :=
  (inputToPoly_mul_coeff a b u.val).symm

/-- Slice `a : Fin d → ZMod 2` into `L` blocks in `CoeffVec J`, zero-padded above `< J` and `< m`. -/
def sliceBlocks (d J L : ℕ) (a : Fin d → ZMod 2) (i : Fin L) (t : Fin (2 * J)) : ZMod 2 :=
  if _ : t.val < J then
    if hidx : J * i.val + t.val < d then
      a ⟨J * i.val + t.val, hidx⟩
    else 0
  else 0

lemma sliceBlocks_eq_zero_of_ge_J {d J L : ℕ} (a : Fin d → ZMod 2)
    (i : Fin L) {t : Fin (2 * J)} (ht : J ≤ t.val) :
    sliceBlocks d J L a i t = 0 := by
  unfold sliceBlocks
  have hnot : ¬ (t.val < J) := by omega
  simp [hnot]

lemma sliceBlocks_eq_zero_of_ge_m {d J L m : ℕ} (hdm : d ≤ m * J) (a : Fin d → ZMod 2)
    {i : Fin L} (hi : m ≤ i.val) :
    sliceBlocks d J L a i = vecZero J := by
  funext t
  unfold sliceBlocks vecZero
  have hge : d ≤ J * i.val + t.val := by
    have hmul : m * J ≤ J * i.val := by
      rw [Nat.mul_comm J i.val]
      exact Nat.mul_le_mul_right J hi
    omega
  have hnot : ¬ (J * i.val + t.val < d) := by omega
  split_ifs <;> simp_all

lemma vecToPoly_sliceBlocks_coeff_ge_J {d J L : ℕ} (a : Fin d → ZMod 2)
    (i : Fin L) {k : ℕ} (hk : J ≤ k) :
    (vecToPoly J (sliceBlocks d J L a i)).coeff k = 0 := by
  by_cases hk2 : k < 2 * J
  · rw [vecToPoly_coeff_lt (sliceBlocks d J L a i) ⟨k, hk2⟩]
    exact sliceBlocks_eq_zero_of_ge_J a i hk
  · exact vecToPoly_coeff_ge (sliceBlocks d J L a i) (by omega)

lemma vecToPoly_sliceBlocks_eq_zero_of_ge_m {d J L m : ℕ} (hdm : d ≤ m * J)
    (a : Fin d → ZMod 2) {i : Fin L} (hi : m ≤ i.val) :
    vecToPoly J (sliceBlocks d J L a i) = 0 := by
  rw [sliceBlocks_eq_zero_of_ge_m hdm a hi]
  unfold vecToPoly vecZero
  simp

lemma coeff_mul_X_pow (p : Polynomial (ZMod 2)) (K M : ℕ) :
    (p * Polynomial.X ^ K).coeff M = if K ≤ M then p.coeff (M - K) else 0 := by
  rw [mul_comm]
  by_cases h : K ≤ M
  · simp only [h, ↓reduceIte]
    have hM : M = K + (M - K) := (Nat.add_sub_of_le h).symm
    conv_lhs => rw [hM]
    exact coeff_X_pow_mul_add p K (M - K)
  · simp only [h, ↓reduceIte]
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro uv huv
    rw [Finset.mem_antidiagonal] at huv
    rw [Polynomial.coeff_X_pow]
    have hne : uv.1 ≠ K := by omega
    simp [hne]

/-- Block decomposition `a(X) = ∑_{i=0}^{L-1} a_i(X) X^{Ji}` (`eq:blocks`). -/
lemma inputToPoly_eq_sum_sliceBlocks {d J L : ℕ} (hJ : 0 < J) (hdL : d ≤ L * J)
    (a : Fin d → ZMod 2) :
    inputToPoly d a =
      Finset.univ.sum (fun i : Fin L =>
        vecToPoly J (sliceBlocks d J L a i) * Polynomial.X ^ (J * i.val)) := by
  ext k
  rw [inputToPoly_coeff, Polynomial.finsetSum_coeff]
  simp_rw [coeff_mul_X_pow]
  set q := k / J
  set rem := k % J
  have hrem_lt : rem < J := Nat.mod_lt k hJ
  have hk_eq : k = J * q + rem := (Nat.div_add_mod k J).symm
  have hterm : ∀ i : Fin L,
      (if J * i.val ≤ k then
        (vecToPoly J (sliceBlocks d J L a i)).coeff (k - J * i.val) else 0) =
      if i.val = q then (if hk : k < d then a ⟨k, hk⟩ else 0) else 0 := fun i => by
    by_cases hiq : i.val = q
    · simp only [hiq, ↓reduceIte]
      have hle : J * q ≤ k := by omega
      have hsub : k - J * q = rem := by omega
      simp only [hle, ↓reduceIte, hsub]
      have hrem2 : rem < 2 * J := by omega
      rw [vecToPoly_coeff_lt (sliceBlocks d J L a i) ⟨rem, hrem2⟩]
      unfold sliceBlocks
      dsimp only
      simp only [hrem_lt, ↓reduceDIte, hiq]
      have hji : J * q + rem = k := hk_eq.symm
      by_cases hk : k < d
      · have hidx : J * q + rem < d := by omega
        simp only [hidx, hk, ↓reduceDIte]
        congr 1
        ext
        exact hji
      · have hidx : ¬ (J * q + rem < d) := by omega
        simp only [hidx, hk, ↓reduceDIte]
    · simp only [hiq, ↓reduceIte]
      by_cases hle : J * i.val ≤ k
      · simp only [hle, ↓reduceIte]
        have hilt : i.val < q := by
          by_contra hge
          have h1 : q + 1 ≤ i.val := by omega
          have h2 : J * (q + 1) ≤ J * i.val := Nat.mul_le_mul_left J h1
          have h3 : J * (q + 1) = J * q + J := by ring
          omega
        have hsub_ge : J ≤ k - J * i.val := by
          have h1 : i.val + 1 ≤ q := hilt
          have h2 : J * (i.val + 1) ≤ J * q := Nat.mul_le_mul_left J h1
          have h3 : J * (i.val + 1) = J * i.val + J := by ring
          omega
        exact vecToPoly_sliceBlocks_coeff_ge_J a i hsub_ge
      · simp only [hle, ↓reduceIte]
  simp_rw [hterm]
  by_cases hk : k < d
  · simp only [hk, ↓reduceDIte]
    have hq_lt : q < L := by
      have hkLJ : k < J * L := by simpa [Nat.mul_comm] using lt_of_lt_of_le hk hdL
      exact Nat.div_lt_of_lt_mul hkLJ
    set idx : Fin L := ⟨q, hq_lt⟩
    have hsum : Finset.univ.sum (fun i : Fin L => if i.val = q then a ⟨k, hk⟩ else 0) =
        Finset.univ.sum (fun i : Fin L => if i = idx then a ⟨k, hk⟩ else 0) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : i = idx
      · subst hi; simp [idx]
      · have hne : i.val ≠ q := fun hv => hi (Fin.ext hv)
        simp [hi, hne]
    rw [hsum]
    simp [idx]
  · simp only [hk, ↓reduceDIte]
    simp

/-- Cyclic convolution of length `L` over `AuxRing J`. -/
noncomputable def ringCycConv (J L : ℕ) (A B : Fin L → AuxRing J) (r : Fin L) : AuxRing J :=
  (Finset.univ.filter (fun p : Fin L × Fin L => (p.1.val + p.2.val) % L = r.val)).sum
    (fun p => A p.1 * B p.2)

/-- Convolution theorem in `AuxRing J`: `DFT_ω (A ⊛ B) = DFT_ω A · DFT_ω B`. -/
lemma ringDFT_cycConv {J L : ℕ} (hL_pos : 0 < L) (hdvd : L ∣ 3 * J)
    (A B : Fin L → AuxRing J) (q : Fin L) :
    ringDFT J L (omega J L) (ringCycConv J L A B) q =
      ringDFT J L (omega J L) A q * ringDFT J L (omega J L) B q := by
  have hwL : (omega J L) ^ L = 1 := omega_pow_L hdvd
  unfold ringDFT ringCycConv
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  have hrhs_prod :
      Finset.univ.sum (fun i : Fin L =>
        Finset.univ.sum (fun j : Fin L =>
          A i * (omega J L) ^ (i.val * q.val) * (B j * (omega J L) ^ (j.val * q.val)))) =
      Finset.univ.sum (fun p : Fin L × Fin L =>
        A p.1 * (omega J L) ^ (p.1.val * q.val) * (B p.2 * (omega J L) ^ (p.2.val * q.val))) :=
    (Fintype.sum_prod_type (fun p : Fin L × Fin L =>
      A p.1 * (omega J L) ^ (p.1.val * q.val) *
        (B p.2 * (omega J L) ^ (p.2.val * q.val)))).symm
  rw [hrhs_prod]
  simp_rw [Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  set r0 : Fin L := ⟨(p.1.val + p.2.val) % L, Nat.mod_lt _ hL_pos⟩
  have hsum : Finset.univ.sum (fun r : Fin L =>
      if (p.1.val + p.2.val) % L = r.val then
        A p.1 * B p.2 * (omega J L) ^ (r.val * q.val) else 0) =
      Finset.univ.sum (fun r : Fin L =>
        if r = r0 then A p.1 * B p.2 * (omega J L) ^ (r0.val * q.val) else 0) := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    by_cases hr : r = r0
    · subst hr; simp [r0]
    · have hne : (p.1.val + p.2.val) % L ≠ r.val := fun hv => hr (Fin.ext hv.symm)
      simp [hr, hne]
  rw [hsum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hpow : (omega J L) ^ (p.1.val * q.val) * (omega J L) ^ (p.2.val * q.val) =
      (omega J L) ^ (r0.val * q.val) := by
    rw [← pow_add, ← add_mul]
    conv_lhs => rw [← Nat.div_add_mod (p.1.val + p.2.val) L]
    rw [add_mul, pow_add, mul_assoc, pow_mul, hwL, one_pow, one_mul]
  calc
    A p.1 * B p.2 * (omega J L) ^ (r0.val * q.val) =
        A p.1 * B p.2 * ((omega J L) ^ (p.1.val * q.val) * (omega J L) ^ (p.2.val * q.val)) := by
      rw [hpow]
    _ = A p.1 * (omega J L) ^ (p.1.val * q.val) * (B p.2 * (omega J L) ^ (p.2.val * q.val)) := by
      ring

lemma ringIDFT_pointwise_mul_eq_cycConv {J ℓ : ℕ} (hdvd : 3 ^ ℓ ∣ 3 * J)
    (A B : Fin (3 ^ ℓ) → AuxRing J) :
    ringDFT J (3 ^ ℓ) (omegaInv J (3 ^ ℓ))
      (fun q => ringDFT J (3 ^ ℓ) (omega J (3 ^ ℓ)) A q *
        ringDFT J (3 ^ ℓ) (omega J (3 ^ ℓ)) B q) =
      ringCycConv J (3 ^ ℓ) A B := by
  have hL_pos : 0 < 3 ^ ℓ := Nat.pos_of_ne_zero (by positivity)
  have hpt : (fun q => ringDFT J (3 ^ ℓ) (omega J (3 ^ ℓ)) A q *
      ringDFT J (3 ^ ℓ) (omega J (3 ^ ℓ)) B q) =
      ringDFT J (3 ^ ℓ) (omega J (3 ^ ℓ)) (ringCycConv J (3 ^ ℓ) A B) := by
    funext q
    exact (ringDFT_cycConv hL_pos hdvd A B q).symm
  rw [hpt]
  exact ringDFT_inv_left hdvd _

/-- Exact non-modular block convolution polynomial `c_r(Y) = ∑_{i + j = r} a_i(Y) b_j(Y)`. -/
noncomputable def exactBlockConvPoly (d J L : ℕ) (a b : Fin d → ZMod 2) (r : Fin L) :
    Polynomial (ZMod 2) :=
  (Finset.univ.filter (fun p : Fin L × Fin L => p.1.val + p.2.val = r.val)).sum
    (fun p => vecToPoly J (sliceBlocks d J L a p.1) * vecToPoly J (sliceBlocks d J L b p.2))

/-- **Degree Bound (`deg c_r ≤ 2J - 2 < 2J`)**: in characteristic 2, carryless block sums do not
increase degree, so all coefficients at `k ≥ 2J - 1` (and in particular `k ≥ 2J`) vanish. -/
lemma exactBlockConvPoly_coeff_ge_two_J_sub_one {d J L : ℕ} (hJ : 0 < J)
    (a b : Fin d → ZMod 2) (r : Fin L) {k : ℕ} (hk : 2 * J - 1 ≤ k) :
    (exactBlockConvPoly d J L a b r).coeff k = 0 := by
  unfold exactBlockConvPoly
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro p _
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro uv huv
  rw [Finset.mem_antidiagonal] at huv
  by_cases huv1 : J ≤ uv.1
  · rw [vecToPoly_sliceBlocks_coeff_ge_J a p.1 huv1, zero_mul]
  · have huv2 : J ≤ uv.2 := by omega
    rw [vecToPoly_sliceBlocks_coeff_ge_J b p.2 huv2, mul_zero]

lemma exactBlockConvPoly_eq_zero_of_ge_two_m_sub_one {d J L m : ℕ} (hdm : d ≤ m * J)
    (hm : 1 ≤ m) (a b : Fin d → ZMod 2) {r : Fin L} (hr : 2 * m - 1 ≤ r.val) :
    exactBlockConvPoly d J L a b r = 0 := by
  unfold exactBlockConvPoly
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter] at hp
  by_cases hp1 : m ≤ p.1.val
  · rw [vecToPoly_sliceBlocks_eq_zero_of_ge_m hdm a hp1, zero_mul]
  · have hp2 : m ≤ p.2.val := by omega
    rw [vecToPoly_sliceBlocks_eq_zero_of_ge_m hdm b hp2, mul_zero]

lemma exactBlockConvPoly_coeff_ge_two_d_sub_one {d J L : ℕ} (hd : 1 ≤ d)
    (a b : Fin d → ZMod 2) (r : Fin L) {t : ℕ} (ht : 2 * d - 1 ≤ J * r.val + t) :
    (exactBlockConvPoly d J L a b r).coeff t = 0 := by
  unfold exactBlockConvPoly
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro uv huv
  rw [Finset.mem_antidiagonal] at huv
  by_cases huv1 : J ≤ uv.1
  · rw [vecToPoly_sliceBlocks_coeff_ge_J a p.1 huv1, zero_mul]
  · by_cases huv2 : J ≤ uv.2
    · rw [vecToPoly_sliceBlocks_coeff_ge_J b p.2 huv2, mul_zero]
    · have huv1_lt : uv.1 < J := by omega
      have huv2_lt : uv.2 < J := by omega
      have hu1 : uv.1 < 2 * J := by omega
      have hu2 : uv.2 < 2 * J := by omega
      rw [vecToPoly_coeff_lt _ ⟨uv.1, hu1⟩, vecToPoly_coeff_lt _ ⟨uv.2, hu2⟩]
      unfold sliceBlocks
      dsimp only
      simp only [huv1_lt, huv2_lt, ↓reduceDIte]
      have hsum_idx : (J * p.1.val + uv.1) + (J * p.2.val + uv.2) = J * r.val + t := by
        calc
          (J * p.1.val + uv.1) + (J * p.2.val + uv.2) =
              J * (p.1.val + p.2.val) + (uv.1 + uv.2) := by ring
          _ = J * r.val + t := by rw [hp.2, huv]
      by_cases ha : J * p.1.val + uv.1 < d
      · have hb_not : ¬ (J * p.2.val + uv.2 < d) := by omega
        simp only [hb_not, ↓reduceDIte, mul_zero]
      · simp only [ha, ↓reduceDIte, zero_mul]

/-- No block-index or degree wrap-around: inverse DFT of pointwise products equals exact
polynomial block convolution `exactBlockConvPoly`. -/
theorem vecIDFT_pointwise_mul_eq_exactBlockConv {d J ℓ m : ℕ} (hJ : 0 < J)
    (hm : 1 ≤ m) (hdm : d ≤ m * J) (hLm : 2 * m - 1 ≤ 3 ^ ℓ) (hdvd : 3 ^ ℓ ∣ 3 * J)
    (a b : Fin d → ZMod 2) (r : Fin (3 ^ ℓ)) (t : Fin (2 * J)) :
    vecIDFT J (3 ^ ℓ)
      (fun q => vecMul J
        (vecDFT J (3 ^ ℓ) (sliceBlocks d J (3 ^ ℓ) a) q)
        (vecDFT J (3 ^ ℓ) (sliceBlocks d J (3 ^ ℓ) b) q)) r t =
      (exactBlockConvPoly d J (3 ^ ℓ) a b r).coeff t.val := by
  suffices hvec : vecIDFT J (3 ^ ℓ)
      (fun q => vecMul J
        (vecDFT J (3 ^ ℓ) (sliceBlocks d J (3 ^ ℓ) a) q)
        (vecDFT J (3 ^ ℓ) (sliceBlocks d J (3 ^ ℓ) b) q)) r =
      fun s : Fin (2 * J) => (exactBlockConvPoly d J (3 ^ ℓ) a b r).coeff s.val by
    exact congrFun hvec t
  apply vecToRing_injective hJ
  have hlhs : vecToRing J (vecIDFT J (3 ^ ℓ)
      (fun q => vecMul J
        (vecDFT J (3 ^ ℓ) (sliceBlocks d J (3 ^ ℓ) a) q)
        (vecDFT J (3 ^ ℓ) (sliceBlocks d J (3 ^ ℓ) b) q)) r) =
      ringCycConv J (3 ^ ℓ)
        (fun i => vecToRing J (sliceBlocks d J (3 ^ ℓ) a i))
        (fun j => vecToRing J (sliceBlocks d J (3 ^ ℓ) b j)) r := by
    rw [vecToRing_vecIDFT hJ]
    have hmul_eq : (fun q => vecToRing J (vecMul J
        (vecDFT J (3 ^ ℓ) (sliceBlocks d J (3 ^ ℓ) a) q)
        (vecDFT J (3 ^ ℓ) (sliceBlocks d J (3 ^ ℓ) b) q))) =
        (fun q => ringDFT J (3 ^ ℓ) (omega J (3 ^ ℓ))
          (fun i => vecToRing J (sliceBlocks d J (3 ^ ℓ) a i)) q *
          ringDFT J (3 ^ ℓ) (omega J (3 ^ ℓ))
            (fun j => vecToRing J (sliceBlocks d J (3 ^ ℓ) b j)) q) := by
      funext q
      rw [vecToRing_mul hJ, vecToRing_vecDFT hJ, vecToRing_vecDFT hJ]
    rw [hmul_eq]
    exact congrFun (ringIDFT_pointwise_mul_eq_cycConv hdvd _ _) r
  have hnowr : ringCycConv J (3 ^ ℓ)
      (fun i => vecToRing J (sliceBlocks d J (3 ^ ℓ) a i))
      (fun j => vecToRing J (sliceBlocks d J (3 ^ ℓ) b j)) r =
      toAuxRing J (exactBlockConvPoly d J (3 ^ ℓ) a b r) := by
    unfold ringCycConv exactBlockConvPoly
    rw [map_sum, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp1 : m ≤ p.1.val
    · have hz : vecToRing J (sliceBlocks d J (3 ^ ℓ) a p.1) = 0 := by
        rw [sliceBlocks_eq_zero_of_ge_m hdm a hp1, vecToRing_zero]
      have hzp : vecToPoly J (sliceBlocks d J (3 ^ ℓ) a p.1) = 0 :=
        vecToPoly_sliceBlocks_eq_zero_of_ge_m hdm a hp1
      simp [hz, hzp]
    · by_cases hp2 : m ≤ p.2.val
      · have hz : vecToRing J (sliceBlocks d J (3 ^ ℓ) b p.2) = 0 := by
          rw [sliceBlocks_eq_zero_of_ge_m hdm b hp2, vecToRing_zero]
        have hzp : vecToPoly J (sliceBlocks d J (3 ^ ℓ) b p.2) = 0 :=
          vecToPoly_sliceBlocks_eq_zero_of_ge_m hdm b hp2
        simp [hz, hzp]
      · have hsum_lt : p.1.val + p.2.val < 3 ^ ℓ := by omega
        rw [Nat.mod_eq_of_lt hsum_lt]
        split_ifs with heq
        · rw [map_mul]
          rfl
        · rfl
  have hrhs : vecToRing J
      (fun s : Fin (2 * J) => (exactBlockConvPoly d J (3 ^ ℓ) a b r).coeff s.val) =
      toAuxRing J (exactBlockConvPoly d J (3 ^ ℓ) a b r) := by
    unfold vecToRing
    rw [← eq_vecToPoly_of_coeff_ge_zero (exactBlockConvPoly d J (3 ^ ℓ) a b r)
      (fun k hk => exactBlockConvPoly_coeff_ge_two_J_sub_one hJ a b r (by omega))]
  rw [hlhs, hnowr, hrhs]

/-- Low `J`-bit half, high `J`-bit half, overlap-XOR (`eq:overlap`), and full `2d`-bit product. -/
def blockLo (J L : ℕ) (c_blk : Fin L → CoeffVec J) (r : ℕ) (t : Fin J) : ZMod 2 :=
  if hr : r < L then c_blk ⟨r, hr⟩ ⟨t.val, by omega⟩ else 0

def blockHi (J L : ℕ) (c_blk : Fin L → CoeffVec J) (r : ℕ) (t : Fin J) : ZMod 2 :=
  if hr : r < L then c_blk ⟨r, hr⟩ ⟨J + t.val, by omega⟩ else 0

def overlapBlock (J L : ℕ) (c_blk : Fin L → CoeffVec J) (r : ℕ) (t : Fin J) : ZMod 2 :=
  blockLo J L c_blk r t + (if r = 0 then 0 else blockHi J L c_blk (r - 1) t)

def reconstructFull (d J L : ℕ) (hJ : 0 < J) (c_blk : Fin L → CoeffVec J) :
    Fin (2 * d) → ZMod 2 :=
  fun u => overlapBlock J L c_blk (u.val / J) ⟨u.val % J, Nat.mod_lt _ hJ⟩

lemma inputToPoly_mul_eq_sum_exactBlockConvPoly {d J L m : ℕ} (hJ : 0 < J)
    (hm : 1 ≤ m) (hdm : d ≤ m * J) (hLm : 2 * m - 1 ≤ L) (a b : Fin d → ZMod 2) :
    inputToPoly d a * inputToPoly d b =
      Finset.univ.sum (fun r : Fin L =>
        exactBlockConvPoly d J L a b r * Polynomial.X ^ (J * r.val)) := by
  have hmL : m ≤ L := by omega
  have hdL : d ≤ L * J := le_trans hdm (Nat.mul_le_mul_right J hmL)
  rw [inputToPoly_eq_sum_sliceBlocks hJ hdL a, inputToPoly_eq_sum_sliceBlocks hJ hdL b]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  have hlhs_prod :
      Finset.univ.sum (fun i : Fin L =>
        Finset.univ.sum (fun j : Fin L =>
          vecToPoly J (sliceBlocks d J L a i) * Polynomial.X ^ (J * i.val) *
            (vecToPoly J (sliceBlocks d J L b j) * Polynomial.X ^ (J * j.val)))) =
      Finset.univ.sum (fun p : Fin L × Fin L =>
        vecToPoly J (sliceBlocks d J L a p.1) * Polynomial.X ^ (J * p.1.val) *
          (vecToPoly J (sliceBlocks d J L b p.2) * Polynomial.X ^ (J * p.2.val))) :=
    (Fintype.sum_prod_type (fun p : Fin L × Fin L =>
      vecToPoly J (sliceBlocks d J L a p.1) * Polynomial.X ^ (J * p.1.val) *
        (vecToPoly J (sliceBlocks d J L b p.2) * Polynomial.X ^ (J * p.2.val)))).symm
  rw [hlhs_prod]
  unfold exactBlockConvPoly
  simp_rw [Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hp1 : m ≤ p.1.val
  · rw [vecToPoly_sliceBlocks_eq_zero_of_ge_m hdm a hp1]
    simp
  · by_cases hp2 : m ≤ p.2.val
    · rw [vecToPoly_sliceBlocks_eq_zero_of_ge_m hdm b hp2]
      simp
    · have hsum_lt : p.1.val + p.2.val < L := by omega
      set r0 : Fin L := ⟨p.1.val + p.2.val, hsum_lt⟩
      have hsum : Finset.univ.sum (fun r : Fin L =>
          if p.1.val + p.2.val = r.val then
            vecToPoly J (sliceBlocks d J L a p.1) * vecToPoly J (sliceBlocks d J L b p.2) *
              Polynomial.X ^ (J * r.val)
          else 0) =
          Finset.univ.sum (fun r : Fin L =>
            if r = r0 then
              (vecToPoly J (sliceBlocks d J L a p.1) * vecToPoly J (sliceBlocks d J L b p.2)) *
                Polynomial.X ^ (J * r0.val)
            else 0) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        by_cases hr : r = r0
        · subst hr; simp [r0]
        · have hne : p.1.val + p.2.val ≠ r.val := fun hv => hr (Fin.ext hv.symm)
          simp [hr, hne]
      rw [hsum]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hexp : J * r0.val = J * p.1.val + J * p.2.val := by dsimp [r0]; ring
      rw [hexp, pow_add]
      ring

/-- **Overlap-XOR Reconstruction (`eq:overlap`)**: `z_r = lo_r + hi_{r-1}` recovers the exact
integer-index convolution `polyFullConv d a b`. -/
theorem reconstructFull_eq_polyFullConv {d J L m : ℕ} (hJ : 0 < J)
    (hm : 1 ≤ m) (hdm : d ≤ m * J) (hLm : 2 * m - 1 ≤ L)
    (a b : Fin d → ZMod 2) (c_blk : Fin L → CoeffVec J)
    (hc : ∀ (r : Fin L) (t : Fin (2 * J)),
      c_blk r t = (exactBlockConvPoly d J L a b r).coeff t.val) :
    reconstructFull d J L hJ c_blk = polyFullConv d a b := by
  funext u
  rw [polyFullConv_eq_mul_coeff, inputToPoly_mul_eq_sum_exactBlockConvPoly hJ hm hdm hLm a b]
  rw [Polynomial.finsetSum_coeff]
  simp_rw [coeff_mul_X_pow]
  unfold reconstructFull overlapBlock blockLo blockHi
  set q := u.val / J
  set rem := u.val % J
  have hrem_lt : rem < J := Nat.mod_lt u.val hJ
  have hu_eq : u.val = J * q + rem := (Nat.div_add_mod u.val J).symm
  have hterm : ∀ r : Fin L,
      (if J * r.val ≤ u.val then
        (exactBlockConvPoly d J L a b r).coeff (u.val - J * r.val) else 0) =
      (if r.val = q then c_blk r ⟨rem, by omega⟩ else 0) +
        (if q ≠ 0 ∧ r.val = q - 1 then c_blk r ⟨J + rem, by omega⟩ else 0) := fun r => by
    by_cases hrq : r.val = q
    · have hJr : J * r.val = J * q := congrArg (J * ·) hrq
      have hle : J * r.val ≤ u.val := by omega
      have hsub : u.val - J * r.val = rem := by omega
      have hnot2 : ¬ (q ≠ 0 ∧ r.val = q - 1) := by
        rintro ⟨hq0, hreq⟩
        have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq0
        have hq1 : q = r.val + 1 := by rw [hreq]; exact (Nat.sub_add_cancel hq_pos).symm
        omega
      simp only [hle, ↓reduceIte]
      rw [hsub]
      simp only [hnot2, ↓reduceIte, add_zero]
      simp only [hrq, ↓reduceIte]
      rw [hc]
    · by_cases hrq1 : q ≠ 0 ∧ r.val = q - 1
      · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hrq1.1
        have hq1 : q = r.val + 1 := by
          rw [hrq1.2]
          exact (Nat.sub_add_cancel hq_pos).symm
        have hJq : J * q = J * r.val + J := by rw [hq1]; ring
        have hle : J * r.val ≤ u.val := by omega
        have hsub : u.val - J * r.val = J + rem := by omega
        simp only [hle, ↓reduceIte]
        rw [hsub]
        simp only [hrq, ↓reduceIte, zero_add]
        rcases hrq1 with ⟨hq_ne0, hr_eq⟩
        simp only [hq_ne0, hr_eq, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        rw [hc]
      · simp only [hrq, hrq1, ↓reduceIte, add_zero]
        by_cases hle : J * r.val ≤ u.val
        · simp only [hle, ↓reduceIte]
          have hr_le_q : r.val ≤ q := by
            by_contra hgt
            have h1 : q + 1 ≤ r.val := by omega
            have h2 : J * (q + 1) ≤ J * r.val := Nat.mul_le_mul_left J h1
            have h3 : J * (q + 1) = J * q + J := by ring
            omega
          have hr2 : r.val + 2 ≤ q := by omega
          have hsub_ge : 2 * J ≤ u.val - J * r.val := by
            have h1 : J * (r.val + 2) ≤ J * q := Nat.mul_le_mul_left J hr2
            have h2 : J * (r.val + 2) = J * r.val + 2 * J := by ring
            omega
          exact exactBlockConvPoly_coeff_ge_two_J_sub_one hJ a b r (by omega)
        · simp only [hle, ↓reduceIte]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases hq : q < L
    · simp only [hq, ↓reduceDIte]
      set idx : Fin L := ⟨q, hq⟩
      have hsum : Finset.univ.sum (fun r : Fin L =>
          if r.val = q then c_blk r ⟨rem, by omega⟩ else 0) =
          Finset.univ.sum (fun r : Fin L =>
            if r = idx then c_blk idx ⟨rem, by omega⟩ else 0) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        by_cases hr : r = idx
        · subst hr; simp [idx]
        · have hne : r.val ≠ q := fun hv => hr (Fin.ext hv)
          simp [hr, hne]
      rw [hsum]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rfl
    · simp only [hq, ↓reduceDIte]
      symm
      apply Finset.sum_eq_zero
      intro r _
      have hne : r.val ≠ q := by omega
      simp [hne]
  · by_cases hq0 : q = 0
    · simp [hq0]
    · simp only [hq0, ↓reduceIte]
      by_cases hq1 : q - 1 < L
      · simp only [hq1, ↓reduceDIte]
        set idx : Fin L := ⟨q - 1, hq1⟩
        have hsum : Finset.univ.sum (fun r : Fin L =>
            if q ≠ 0 ∧ r.val = q - 1 then c_blk r ⟨J + rem, by omega⟩ else 0) =
            Finset.univ.sum (fun r : Fin L =>
              if r = idx then c_blk idx ⟨J + rem, by omega⟩ else 0) := by
          refine Finset.sum_congr rfl (fun r _ => ?_)
          by_cases hr : r = idx
          · subst hr; simp [idx, hq0]
          · have hne : r.val ≠ q - 1 := fun hv => hr (Fin.ext hv)
            simp [hr, hne]
        rw [hsum]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rfl
      · simp only [hq1, ↓reduceDIte]
        symm
        apply Finset.sum_eq_zero
        intro r _
        have hne : r.val ≠ q - 1 := by omega
        simp [hne]

/-- Cyclic folding operation `(ab mod (X^n - 1))_k = c_k + c_{k+n}` (`eq:fold`). -/
def cycFold (n : ℕ) (c_full : Fin (2 * n) → ZMod 2) : Fin n → ZMod 2 :=
  fun k => c_full ⟨k.val, by omega⟩ + c_full ⟨k.val + n, by omega⟩

/-- **Cyclic Folding Theorem (`eq:fold`)**:
For all `n : ℕ`, `a b : Fin n → ZMod 2`, and `k : Fin n`,
`QCSD_cycMul n a b k = polyFullConv n a b k + polyFullConv n a b (k + n)`. -/
theorem QCSD_cycMul_eq_polyFullConv_fold (n : ℕ) (a b : Fin n → ZMod 2) (k : Fin n) :
    QCSD_cycMul n a b k =
      polyFullConv n a b ⟨k.val, by omega⟩ + polyFullConv n a b ⟨k.val + n, by omega⟩ := by
  have hk_lt : k.val < n := k.isLt
  have hn : 0 < n := by omega
  unfold QCSD_cycMul polyFullConv
  simp only [Finset.sum_filter]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  set j0 : Fin n := QCSD_subIdx n k i
  by_cases hik : i.val ≤ k.val
  · have hj0_val : j0.val = k.val - i.val := by
      dsimp [j0, QCSD_subIdx]
      simp only [hn, ↓reduceDIte]
      have hrew : k.val + n - i.val = (k.val - i.val) + 1 * n := by omega
      rw [hrew, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have hs1 : Finset.univ.sum (fun j : Fin n =>
        if i.val + j.val = k.val then a i * b j else 0) = a i * b j0 := by
      have hcongr : Finset.univ.sum (fun j : Fin n =>
          if i.val + j.val = k.val then a i * b j else 0) =
          Finset.univ.sum (fun j : Fin n => if j = j0 then a i * b j0 else 0) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hj : j = j0
        · subst hj
          have : i.val + j0.val = k.val := by omega
          simp [this]
        · have hne : i.val + j.val ≠ k.val := by
            intro heq
            apply hj
            ext
            omega
          simp [hj, hne]
      rw [hcongr]
      simp
    have hs2 : Finset.univ.sum (fun j : Fin n =>
        if i.val + j.val = k.val + n then a i * b j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hj_lt : j.val < n := j.isLt
      have hne : i.val + j.val ≠ k.val + n := by omega
      simp [hne]
    rw [hs1, hs2, add_zero]
  · have hj0_val : j0.val = k.val + n - i.val := by
      dsimp [j0, QCSD_subIdx]
      simp only [hn, ↓reduceDIte]
      have hi_lt : i.val < n := i.isLt
      exact Nat.mod_eq_of_lt (by omega)
    have hs1 : Finset.univ.sum (fun j : Fin n =>
        if i.val + j.val = k.val then a i * b j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hne : i.val + j.val ≠ k.val := by omega
      simp [hne]
    have hs2 : Finset.univ.sum (fun j : Fin n =>
        if i.val + j.val = k.val + n then a i * b j else 0) = a i * b j0 := by
      have hcongr : Finset.univ.sum (fun j : Fin n =>
          if i.val + j.val = k.val + n then a i * b j else 0) =
          Finset.univ.sum (fun j : Fin n => if j = j0 then a i * b j0 else 0) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hj : j = j0
        · subst hj
          have hi_lt : i.val < n := i.isLt
          have : i.val + j0.val = k.val + n := by omega
          simp [this]
        · have hne : i.val + j.val ≠ k.val + n := by
            intro heq
            apply hj
            ext
            omega
          simp [hj, hne]
      rw [hcongr]
      simp
    rw [hs1, hs2, zero_add]

theorem cycFold_polyFullConv_eq_QCSD_cycMul (n : ℕ) (a b : Fin n → ZMod 2) :
    cycFold n (polyFullConv n a b) = QCSD_cycMul n a b := by
  funext k
  exact (QCSD_cycMul_eq_polyFullConv_fold n a b k).symm

/-!
# Section 5: Parameter-Specialized Concrete Pipeline & Master Unique-Wire Theorems (§3.1 & §4.1)
-/

def paramSliceBlocks (d : ℕ) (a : Fin d → ZMod 2) : Fin (paramL d) → CoeffVec (paramJ d) :=
  sliceBlocks d (paramJ d) (paramL d) a

def paramDFTStage1 (d : ℕ) (x : Fin (paramL d) → CoeffVec (paramJ d)) :
    Fin (paramL2 d) → Fin (paramL1 d) → CoeffVec (paramJ d) :=
  vecDFTStage1 (paramJ d) (paramL d) (paramL1 d) (paramL2 d) (paramL_eq_mul d) x

def paramDFTStage2 (d : ℕ)
    (y : Fin (paramL2 d) → Fin (paramL1 d) → CoeffVec (paramJ d)) :
    Fin (paramL d) → CoeffVec (paramJ d) :=
  vecDFTStage2Flat (paramJ d) (paramL d) (paramL1 d) (paramL2 d)
    (paramL_eq_mul d) (one_le_paramL1 d) y

def paramPointwiseMul (d : ℕ) (u v : Fin (paramL d) → CoeffVec (paramJ d)) :
    Fin (paramL d) → CoeffVec (paramJ d) :=
  fun q => vecMul (paramJ d) (u q) (v q)

def paramIDFTStage1 (d : ℕ) (x : Fin (paramL d) → CoeffVec (paramJ d)) :
    Fin (paramL2 d) → Fin (paramL1 d) → CoeffVec (paramJ d) :=
  vecIDFTStage1 (paramJ d) (paramL d) (paramL1 d) (paramL2 d) (paramL_eq_mul d) x

def paramIDFTStage2 (d : ℕ)
    (y : Fin (paramL2 d) → Fin (paramL1 d) → CoeffVec (paramJ d)) :
    Fin (paramL d) → CoeffVec (paramJ d) :=
  vecIDFTStage2Flat (paramJ d) (paramL d) (paramL1 d) (paramL2 d)
    (paramL_eq_mul d) (one_le_paramL1 d) y

def paramReconstructFull (d : ℕ) (c_blk : Fin (paramL d) → CoeffVec (paramJ d)) :
    Fin (2 * d) → ZMod 2 :=
  reconstructFull d (paramJ d) (paramL d) (paramJ_pos d) c_blk

/-- Canonical inverse-DFT output blocks `c_blk` for inputs `a, b : Fin d → ZMod 2`. -/
def paramConvBlocks (d : ℕ) (a b : Fin d → ZMod 2) : Fin (paramL d) → CoeffVec (paramJ d) :=
  let ya := paramDFTStage1 d (paramSliceBlocks d a)
  let a_hat := paramDFTStage2 d ya
  let yb := paramDFTStage1 d (paramSliceBlocks d b)
  let b_hat := paramDFTStage2 d yb
  let c_hat := paramPointwiseMul d a_hat b_hat
  let yc := paramIDFTStage1 d c_hat
  paramIDFTStage2 d yc

lemma paramConvBlocks_eq_exactBlockConvPoly_coeff {d : ℕ} (hd : 1 ≤ d)
    (a b : Fin d → ZMod 2) (r : Fin (paramL d)) (t : Fin (2 * paramJ d)) :
    paramConvBlocks d a b r t =
      (exactBlockConvPoly d (paramJ d) (paramL d) a b r).coeff t.val := by
  have hJ : 0 < paramJ d := paramJ_pos d
  have hL : paramL d = paramL1 d * paramL2 d := paramL_eq_mul d
  have hL1 : 0 < paramL1 d := one_le_paramL1 d
  have hL2 : 0 < paramL2 d := one_le_paramL2 d
  have hdvd : paramL d ∣ 3 * paramJ d := paramL_dvd_three_mul_paramJ hd
  unfold paramConvBlocks paramIDFTStage2 paramIDFTStage1 paramPointwiseMul
    paramDFTStage2 paramDFTStage1 paramSliceBlocks
  rw [vecIDFTStage2Flat_vecIDFTStage1_eq_vecIDFT hJ hL hL1 hL2 hdvd]
  rw [vecDFTStage2Flat_vecDFTStage1_eq_vecDFT hJ hL hL1 hL2 hdvd]
  rw [vecDFTStage2Flat_vecDFTStage1_eq_vecDFT hJ hL hL1 hL2 hdvd]
  exact vecIDFT_pointwise_mul_eq_exactBlockConv (ℓ := paramEll d) hJ
    (one_le_paramM hd) (le_paramM_mul_paramJ d) (two_mul_paramM_sub_one_le_paramL d)
    hdvd a b r t

/-- Boundary-zero guarantees on `paramConvBlocks d a b` (`§3.1`, lines 204, 208, 220). -/
lemma paramConvBlocks_eq_zero_of_ge_two_m_sub_one {d : ℕ} (hd : 1 ≤ d)
    (a b : Fin d → ZMod 2) {r : Fin (paramL d)} (hr : 2 * paramM d - 1 ≤ r.val) :
    paramConvBlocks d a b r = vecZero (paramJ d) := by
  funext t
  rw [paramConvBlocks_eq_exactBlockConvPoly_coeff hd]
  rw [exactBlockConvPoly_eq_zero_of_ge_two_m_sub_one (le_paramM_mul_paramJ d)
    (one_le_paramM hd) a b hr]
  simp [vecZero]

lemma paramConvBlocks_eq_zero_of_ge_two_d_sub_one {d : ℕ} (hd : 1 ≤ d)
    (a b : Fin d → ZMod 2) (r : Fin (paramL d)) (t : Fin (2 * paramJ d))
    (ht : 2 * d - 1 ≤ paramJ d * r.val + t.val) :
    paramConvBlocks d a b r t = 0 := by
  rw [paramConvBlocks_eq_exactBlockConvPoly_coeff hd]
  exact exactBlockConvPoly_coeff_ge_two_d_sub_one hd a b r ht

/-- **End-to-End 2-Layer Carryless Polynomial Multiplication Theorem (`§3.1`)**. -/
theorem paramReconstructFull_paramConvBlocks_eq_polyFullConv {d : ℕ} (hd : 1 ≤ d)
    (a b : Fin d → ZMod 2) :
    paramReconstructFull d (paramConvBlocks d a b) = polyFullConv d a b := by
  unfold paramReconstructFull
  exact reconstructFull_eq_polyFullConv (paramJ_pos d) (one_le_paramM hd)
    (le_paramM_mul_paramJ d) (two_mul_paramM_sub_one_le_paramL d) a b
    (paramConvBlocks d a b) (paramConvBlocks_eq_exactBlockConvPoly_coeff hd a b)

/-- Type of all 7 internal ring-element wire arrays (`ya, a_hat, yb, b_hat, c_hat, yc, c_blk`)
in `lem:multiplication` (defined via `abbrev` over `×`, zero custom `structure`/`inductive`s). -/
abbrev StageInterArray (d : ℕ) : Type :=
  Fin (paramL2 d) → Fin (paramL1 d) → CoeffVec (paramJ d)

abbrev RingElemArray (d : ℕ) : Type :=
  Fin (paramL d) → CoeffVec (paramJ d)

abbrev MulNetWires (d : ℕ) : Type :=
  StageInterArray d × RingElemArray d × StageInterArray d × RingElemArray d ×
    RingElemArray d × StageInterArray d × RingElemArray d

/-- Canonical intermediate wire assignment for `lem:multiplication` on inputs `(a, b)`. -/
def canonicalMulNetWires (d : ℕ) (a b : Fin d → ZMod 2) : MulNetWires d :=
  let ya := paramDFTStage1 d (paramSliceBlocks d a)
  let a_hat := paramDFTStage2 d ya
  let yb := paramDFTStage1 d (paramSliceBlocks d b)
  let b_hat := paramDFTStage2 d yb
  let c_hat := paramPointwiseMul d a_hat b_hat
  let yc := paramIDFTStage1 d c_hat
  let c_blk := paramIDFTStage2 d yc
  (ya, a_hat, yb, b_hat, c_hat, yc, c_blk)

/-- Local vertex constraints of the multiplication network (`lem:multiplication`), including
Stage-1/Stage-2 forward DFTs, pointwise `A`-multiplications, Stage-1/Stage-2 inverse DFT,
boundary-zero checks above `2d - 2`, and overlap-XOR output equality `z = reconstruct(c_blk)`. -/
def mulNetLocalConstraints (d : ℕ) (a b : Fin d → ZMod 2) (z : Fin (2 * d) → ZMod 2)
    (w : MulNetWires d) : Prop :=
  let (ya, a_hat, yb, b_hat, c_hat, yc, c_blk) := w
  ya = paramDFTStage1 d (paramSliceBlocks d a) ∧
  a_hat = paramDFTStage2 d ya ∧
  yb = paramDFTStage1 d (paramSliceBlocks d b) ∧
  b_hat = paramDFTStage2 d yb ∧
  c_hat = paramPointwiseMul d a_hat b_hat ∧
  yc = paramIDFTStage1 d c_hat ∧
  c_blk = paramIDFTStage2 d yc ∧
  (∀ (r : Fin (paramL d)) (t : Fin (2 * paramJ d)),
    2 * d - 1 ≤ paramJ d * r.val + t.val → c_blk r t = 0) ∧
  z = paramReconstructFull d c_blk

/-- **Solution-Preserving Unique Extension for `lem:multiplication`**:
For any `d ≥ 1`, `a, b : Fin d → ZMod 2`, and `z : Fin (2 * d) → ZMod 2`, there exists a
unique intermediate wire tuple `w : MulNetWires d` satisfying all local constraints iff
`z = polyFullConv d a b`. -/
theorem mulNet_unique_wires_iff {d : ℕ} (hd : 1 ≤ d)
    (a b : Fin d → ZMod 2) (z : Fin (2 * d) → ZMod 2) :
    (∃! w : MulNetWires d, mulNetLocalConstraints d a b z w) ↔
      z = polyFullConv d a b := by
  constructor
  · rintro ⟨⟨ya, a_hat, yb, b_hat, c_hat, yc, c_blk⟩, hw, _⟩
    rcases hw with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, rfl⟩
    exact paramReconstructFull_paramConvBlocks_eq_polyFullConv hd a b
  · rintro rfl
    refine ⟨canonicalMulNetWires d a b, ?_, ?_⟩
    · unfold canonicalMulNetWires mulNetLocalConstraints
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · intro r t ht
        exact paramConvBlocks_eq_zero_of_ge_two_d_sub_one hd a b r t ht
      · exact (paramReconstructFull_paramConvBlocks_eq_polyFullConv hd a b).symm
    · rintro ⟨ya, a_hat, yb, b_hat, c_hat, yc, c_blk⟩ hw
      rcases hw with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, _⟩
      rfl

/-- Full QCSD syndrome-network intermediate wire tuple (`MulNetWires n × (Fin (2 * n) → ZMod 2)`),
containing all 7 internal ring-element arrays plus the reconstructed `2n`-bit product `c_full`. -/
abbrev QCSDSyndromeWires (n : ℕ) : Type :=
  MulNetWires n × (Fin (2 * n) → ZMod 2)

def canonicalQCSDSyndromeWires (n : ℕ) (h e₁ : Fin n → ZMod 2) : QCSDSyndromeWires n :=
  let w := canonicalMulNetWires n h e₁
  (w, paramReconstructFull n w.2.2.2.2.2.2)

/-- Local deterministic functional and syndrome constraints (`eq:syndrome-bits`) for QCSD (`§4.1`). -/
def qcsdSyndromeLocalConstraints (n : ℕ) (h s e₀ e₁ : Fin n → ZMod 2)
    (wires : QCSDSyndromeWires n) : Prop :=
  mulNetLocalConstraints n h e₁ wires.2 wires.1 ∧
  ∀ k : Fin n,
    e₀ k + wires.2 ⟨k.val, by omega⟩ + wires.2 ⟨k.val + n, by omega⟩ = s k

/-- **Master Algebraic Theorem for QCSD Syndrome Network (`§3.1` & `§4.1`)**:
For any `n ≥ 1` (in particular `n ≥ 2`), fixed public `h, s : Fin n → ZMod 2`, and any candidate
error pair `(e₀, e₁)`, there exists a **unique** assignment to all intermediate DFT, product,
and overlap-XOR reconstruction bit wires satisfying the local constraints iff
`∀ k : Fin n, e₀ k + QCSD_cycMul n h e₁ k = s k`. -/
theorem qcsdSyndrome_unique_wires_iff {n : ℕ} (hn : 1 ≤ n)
    (h s e₀ e₁ : Fin n → ZMod 2) :
    (∃! wires : QCSDSyndromeWires n, qcsdSyndromeLocalConstraints n h s e₀ e₁ wires) ↔
      (∀ k : Fin n, e₀ k + QCSD_cycMul n h e₁ k = s k) := by
  constructor
  · rintro ⟨⟨w, c_full⟩, ⟨hmul, hsyn⟩, _⟩
    have huniq := (mulNet_unique_wires_iff hn h e₁ c_full).mp ⟨w, hmul, fun w' hw' => by
      rcases w with ⟨ya, a_hat, yb, b_hat, c_hat, yc, c_blk⟩
      rcases w' with ⟨ya', a_hat', yb', b_hat', c_hat', yc', c_blk'⟩
      rcases hmul with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, _⟩
      rcases hw' with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, _⟩
      rfl⟩
    subst huniq
    intro k
    have hfold := QCSD_cycMul_eq_polyFullConv_fold n h e₁ k
    have hk := hsyn k
    calc
      e₀ k + QCSD_cycMul n h e₁ k =
          e₀ k + (polyFullConv n h e₁ ⟨k.val, by omega⟩ +
            polyFullConv n h e₁ ⟨k.val + n, by omega⟩) := by rw [hfold]
      _ = e₀ k + polyFullConv n h e₁ ⟨k.val, by omega⟩ +
            polyFullConv n h e₁ ⟨k.val + n, by omega⟩ := by ring
      _ = s k := hk
  · intro hsol
    have hmul_ex := (mulNet_unique_wires_iff hn h e₁ (polyFullConv n h e₁)).mpr rfl
    rcases hmul_ex with ⟨w0, hw0, hw0_uniq⟩
    refine ⟨(w0, polyFullConv n h e₁), ⟨hw0, ?_⟩, ?_⟩
    · intro k
      have hfold := QCSD_cycMul_eq_polyFullConv_fold n h e₁ k
      calc
        e₀ k + polyFullConv n h e₁ ⟨k.val, by omega⟩ +
            polyFullConv n h e₁ ⟨k.val + n, by omega⟩ =
          e₀ k + (polyFullConv n h e₁ ⟨k.val, by omega⟩ +
            polyFullConv n h e₁ ⟨k.val + n, by omega⟩) := by ring
        _ = e₀ k + QCSD_cycMul n h e₁ k := by rw [← hfold]
        _ = s k := hsol k
    · rintro ⟨w', c_full'⟩ ⟨hw', _⟩
      have hc_eq : c_full' = polyFullConv n h e₁ := by
        rcases w' with ⟨ya, a_hat, yb, b_hat, c_hat, yc, c_blk⟩
        rcases hw' with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, rfl⟩
        exact paramReconstructFull_paramConvBlocks_eq_polyFullConv hn h e₁
      subst hc_eq
      have hw_eq : w' = w0 := hw0_uniq w' hw'
      subst hw_eq
      rfl

/-- Constant-`h` variant of the QCSD syndrome wire tuple where `h_hat = DFT_ω(h)` is baked into
vertex predicates as a public constant, leaving `(yb, b_hat, c_hat, yc, c_blk, c_full)` as wires. -/
abbrev QCSDSyndromeConstHWires (n : ℕ) : Type :=
  StageInterArray n × RingElemArray n × RingElemArray n ×
    StageInterArray n × RingElemArray n × (Fin (2 * n) → ZMod 2)

def qcsdSyndromeConstHLocalConstraints (n : ℕ) (h s e₀ e₁ : Fin n → ZMod 2)
    (wires : QCSDSyndromeConstHWires n) : Prop :=
  let (yb, b_hat, c_hat, yc, c_blk, c_full) := wires
  let h_hat := paramDFTStage2 n (paramDFTStage1 n (paramSliceBlocks n h))
  yb = paramDFTStage1 n (paramSliceBlocks n e₁) ∧
  b_hat = paramDFTStage2 n yb ∧
  c_hat = paramPointwiseMul n h_hat b_hat ∧
  yc = paramIDFTStage1 n c_hat ∧
  c_blk = paramIDFTStage2 n yc ∧
  (∀ (r : Fin (paramL n)) (t : Fin (2 * paramJ n)),
    2 * n - 1 ≤ paramJ n * r.val + t.val → c_blk r t = 0) ∧
  c_full = paramReconstructFull n c_blk ∧
  ∀ k : Fin n,
    e₀ k + c_full ⟨k.val, by omega⟩ + c_full ⟨k.val + n, by omega⟩ = s k

theorem qcsdSyndromeConstH_unique_wires_iff {n : ℕ} (hn : 1 ≤ n)
    (h s e₀ e₁ : Fin n → ZMod 2) :
    (∃! wires : QCSDSyndromeConstHWires n,
      qcsdSyndromeConstHLocalConstraints n h s e₀ e₁ wires) ↔
      (∀ k : Fin n, e₀ k + QCSD_cycMul n h e₁ k = s k) := by
  constructor
  · rintro ⟨⟨yb, b_hat, c_hat, yc, c_blk, c_full⟩, hw, _⟩
    rcases hw with ⟨rfl, rfl, rfl, rfl, rfl, _, rfl, hsyn⟩
    have hc : paramReconstructFull n (paramConvBlocks n h e₁) = polyFullConv n h e₁ :=
      paramReconstructFull_paramConvBlocks_eq_polyFullConv hn h e₁
    intro k
    have hfold := QCSD_cycMul_eq_polyFullConv_fold n h e₁ k
    have hk := hsyn k
    change e₀ k + paramReconstructFull n (paramConvBlocks n h e₁) ⟨k.val, _⟩ +
      paramReconstructFull n (paramConvBlocks n h e₁) ⟨k.val + n, _⟩ = s k at hk
    simp only [hc] at hk
    calc
      e₀ k + QCSD_cycMul n h e₁ k =
          e₀ k + (polyFullConv n h e₁ ⟨k.val, by omega⟩ +
            polyFullConv n h e₁ ⟨k.val + n, by omega⟩) := by rw [hfold]
      _ = e₀ k + polyFullConv n h e₁ ⟨k.val, by omega⟩ +
            polyFullConv n h e₁ ⟨k.val + n, by omega⟩ := by ring
      _ = s k := hk
  · intro hsol
    let h_hat := paramDFTStage2 n (paramDFTStage1 n (paramSliceBlocks n h))
    let yb := paramDFTStage1 n (paramSliceBlocks n e₁)
    let b_hat := paramDFTStage2 n yb
    let c_hat := paramPointwiseMul n h_hat b_hat
    let yc := paramIDFTStage1 n c_hat
    let c_blk := paramIDFTStage2 n yc
    refine ⟨(yb, b_hat, c_hat, yc, c_blk, polyFullConv n h e₁), ?_, ?_⟩
    · refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · intro r t ht
        exact paramConvBlocks_eq_zero_of_ge_two_d_sub_one hn h e₁ r t ht
      · exact (paramReconstructFull_paramConvBlocks_eq_polyFullConv hn h e₁).symm
      · intro k
        have hfold := QCSD_cycMul_eq_polyFullConv_fold n h e₁ k
        calc
          e₀ k + polyFullConv n h e₁ ⟨k.val, by omega⟩ +
              polyFullConv n h e₁ ⟨k.val + n, by omega⟩ =
            e₀ k + (polyFullConv n h e₁ ⟨k.val, by omega⟩ +
              polyFullConv n h e₁ ⟨k.val + n, by omega⟩) := by ring
          _ = e₀ k + QCSD_cycMul n h e₁ k := by rw [← hfold]
          _ = s k := hsol k
    · rintro ⟨yb', b_hat', c_hat', yc', c_blk', c_full'⟩ hw'
      rcases hw' with ⟨rfl, rfl, rfl, rfl, rfl, _, rfl, _⟩
      have hc : paramReconstructFull n c_blk = polyFullConv n h e₁ :=
        paramReconstructFull_paramConvBlocks_eq_polyFullConv hn h e₁
      rw [hc]

end Branch2Algebra
