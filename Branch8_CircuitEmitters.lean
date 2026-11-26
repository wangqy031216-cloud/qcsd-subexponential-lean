import Branch6_EncoderMacros
import Branch7_EncodeNetSpec

namespace Branch8CircuitEmit

open QCSD.Defs
open Branch5PadAndSep
open Branch6Encoder
open Branch7EncodeSpec

/-!
## Section 1: Exact `Branch3` Parameters, Matrices, Vertex Offsets, and Polynomial Bounds

All definitions in this section are structurally (`rfl`) identical to `Branch3_Network.lean`,
using only `def`, `abbrev`, `lemma`, and `theorem` over standard types.
-/

def paramK (d : ℕ) : ℕ := minPowExp 9 d
def paramJ (d : ℕ) : ℕ := 3 ^ paramK d
def paramM (d : ℕ) : ℕ := (d + paramJ d - 1) / paramJ d
def paramEll (d : ℕ) : ℕ := minPowExp 3 (2 * paramM d - 1)
def paramL (d : ℕ) : ℕ := 3 ^ paramEll d
def paramL1 (d : ℕ) : ℕ := 3 ^ (paramEll d / 2)
def paramL2 (d : ℕ) : ℕ := 3 ^ ((paramEll d + 1) / 2)
def paramOmegaExp (d : ℕ) : ℕ := 3 ^ (paramK d + 1 - paramEll d)
def paramInvOmegaExp (d : ℕ) : ℕ := 3 * paramJ d - paramOmegaExp d

def treeLog (N_bits : ℕ) : ℕ := max 1 (minPowExp 2 N_bits)
def treeM (N_bits : ℕ) : ℕ := 2 ^ treeLog N_bits

def treeVertOff (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | j + 1 => treeVertOff r j + (j + 1) * 2 ^ (r - j)

def decodeTreeVertAux (r rem : ℕ) : ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, j => (j, 0, 0)
  | fuel + 1, j =>
    let blk := (j + 1) * 2 ^ (r - j)
    if rem < blk then (j, rem / (j + 1), rem % (j + 1))
    else decodeTreeVertAux r (rem - blk) fuel (j + 1)

def decodeTreeVert (r locV : ℕ) : ℕ × ℕ × ℕ :=
  decodeTreeVertAux r locV r 1

def coeffPowY (J m p : ℕ) : Bool :=
  decide (m % (3 * J) = p ∨ m % (3 * J) = 2 * J + p % J)

def ringMulTensor (J : ℕ) (p t1 t2 : ℕ) : Bool :=
  coeffPowY J (t1 + t2) p

def fwdSt1InIndices (n J L2 j2 : ℕ) : List ℕ :=
  (List.range n).filter (fun idx => decide ((idx / J) % L2 = j2))

def fwdSt1Mat (J L1 wExp : ℕ) (inIndices : List ℕ) (outIdx inK : ℕ) : Bool :=
  let q1 := outIdx / (2 * J)
  let p := outIdx % (2 * J)
  let idx := inIndices.getD inK 0
  let r := idx / J
  let u := idx % J
  decide (q1 < L1) && coeffPowY J (wExp * r * q1 + u) p

def fullSt1Mat (J L1 L2 wExp j2 : ℕ) (outIdx inIdx : ℕ) : Bool :=
  let q1 := outIdx / (2 * J)
  let p := outIdx % (2 * J)
  let j1 := inIdx / (2 * J)
  let t := inIdx % (2 * J)
  let r := L2 * j1 + j2
  decide (q1 < L1 ∧ j1 < L1) && coeffPowY J (wExp * r * q1 + t) p

def st2Mat (J L1 L2 wExp : ℕ) (outIdx inIdx : ℕ) : Bool :=
  let q2 := outIdx / (2 * J)
  let p := outIdx % (2 * J)
  let j2 := inIdx / (2 * J)
  let t := inIdx % (2 * J)
  decide (q2 < L2 ∧ j2 < L2) && coeffPowY J (wExp * L1 * j2 * q2 + t) p

def ovlTargetBit (J blk p : ℕ) : ℕ :=
  if p < J then blk * J + p else (blk + 1) * J + (p - J)

def ovlInLocal (J L tk : ℕ) : List ℕ :=
  (if 0 < tk / J ∧ tk / J - 1 < L then [(tk / J - 1) * (2 * J) + (J + tk % J)] else []) ++
  (if tk / J < L then [(tk / J) * (2 * J) + tk % J] else [])

def zmod2ToBool (z : ZMod 2) : Bool := decide (z = (1 : ZMod 2))

def netV0 (_n : ℕ) : ℕ := 0
def netV1 (n : ℕ) : ℕ := 2 * n
def netV2 (n : ℕ) : ℕ := 4 * n
def netV3 (n : ℕ) : ℕ := 5 * n
def netV4 (n : ℕ) : ℕ := 5 * n + paramL2 n
def netV5 (n : ℕ) : ℕ := 5 * n + paramL2 n + paramL1 n
def netV6 (n : ℕ) : ℕ := 5 * n + 2 * paramL2 n + paramL1 n
def netV7 (n : ℕ) : ℕ := 5 * n + 2 * paramL2 n + 2 * paramL1 n
def netV8 (n : ℕ) : ℕ := netV7 n + paramL n
def netV9 (n : ℕ) : ℕ := netV8 n + paramL2 n
def netV10 (n : ℕ) : ℕ := netV9 n + paramL1 n
def netV11 (n : ℕ) : ℕ := netV10 n + 2 * paramJ n * paramL n
def netV12 (n : ℕ) : ℕ := netV11 n + 2 * n
def netV13 (n : ℕ) : ℕ := netV12 n + n
def netV14 (n : ℕ) : ℕ := netV13 n + (treeM n - n)
def netV15 (n : ℕ) : ℕ := netV14 n + (treeM n - n)
def netV16 (n : ℕ) : ℕ := netV15 n + treeVertOff (treeLog n + 1) (treeLog n + 2)
def netV17 (n : ℕ) : ℕ := netV16 n + 1
def netV18 (n : ℕ) : ℕ := netV17 n + (treeLog n + 2)
def netVertCount (n : ℕ) : ℕ := netV18 n + 1

/-- Exact `Branch3.rawPred` (`mode = 0` Exact, `mode = 1` Le, `mode = 2` Sep). -/
def rawPred (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) (v : ℕ) :
    QCSD_BoolCircuit :=
  let J := paramJ n
  let L := paramL n
  let L1 := paramL1 n
  let L2 := paramL2 n
  let r := treeLog n + 1
  let W := treeLog n + 2
  if v < netV1 n then
    pinBitCircuit (if v < pre.length then some (pre.getD v false) else none)
  else if v < netV2 n then
    linearMapCheckCircuit 1 2 (fun _ _ => true)
  else if v < netV3 n then
    let idx := v - netV2 n
    pinBitCircuit (some (if hlt : idx < n then zmod2ToBool (h ⟨idx, hlt⟩) else false))
  else if v < netV4 n then
    let inList := fwdSt1InIndices n J L2 (v - netV3 n)
    linearMapCheckCircuit inList.length (2 * J * L1) (fwdSt1Mat J L1 (paramOmegaExp n) inList)
  else if v < netV5 n then
    linearMapCheckCircuit (2 * J * L2) (2 * J * L2) (st2Mat J L1 L2 (paramOmegaExp n))
  else if v < netV6 n then
    let inList := fwdSt1InIndices n J L2 (v - netV5 n)
    linearMapCheckCircuit inList.length (2 * J * L1) (fwdSt1Mat J L1 (paramOmegaExp n) inList)
  else if v < netV7 n then
    linearMapCheckCircuit (2 * J * L2) (2 * J * L2) (st2Mat J L1 L2 (paramOmegaExp n))
  else if v < netV8 n then
    bilinearMapCheckCircuit (2 * J) (2 * J) (2 * J) (ringMulTensor J)
  else if v < netV9 n then
    linearMapCheckCircuit (2 * J * L1) (2 * J * L1)
      (fullSt1Mat J L1 L2 (paramInvOmegaExp n) (v - netV8 n))
  else if v < netV10 n then
    linearMapCheckCircuit (2 * J * L2) (2 * J * L2) (st2Mat J L1 L2 (paramInvOmegaExp n))
  else if v < netV11 n then
    let k := v - netV10 n
    constCircuit (if ovlTargetBit J (k / (2 * J)) (k % (2 * J)) < 2 * n then 0 else 1) true
  else if v < netV12 n then
    let dIn := (ovlInLocal J L (v - netV11 n)).length
    linearMapCheckCircuit dIn 1 (fun _ _ => true)
  else if v < netV13 n then
    let i := v - netV12 n
    synCheckCircuit (if hlt : i < n then zmod2ToBool (s ⟨i, hlt⟩) else false)
  else if v < netV14 n then
    pinBitCircuit (some false)
  else if v < netV15 n then
    pinBitCircuit (some false)
  else if v < netV16 n then
    let tv := decodeTreeVert r (v - netV15 n)
    let j := tv.1; let u := tv.2.2
    if u = 0 then pinBitCircuit (some false)
    else
      let b := u - 1
      if mode = 2 ∧ j = r then
        sepFullAdderCircuit (decide (t0 < 2 ^ r ∧ t1 < 2 ^ r)) (t0.testBit b) (t1.testBit b)
      else fullAdderCircuit
  else if v < netV17 n then
    pinBitCircuit (some false)
  else if v < netV18 n then
    let b := v - netV17 n
    if mode = 0 then exactCmpStepCircuit (decide (t0 < 2 ^ W)) (t0.testBit b)
    else if mode = 1 then borrowStepCircuit (t0.testBit b)
    else sepCmpStepCircuit
  else
    if mode = 1 ∧ ¬(t0 < 2 ^ W) then constCircuit 1 true
    else pinBitCircuit (some false)

/-! ### 1.1 Parameter Positivity and Polynomial Bounds (Valid for ALL `d : ℕ`) -/

lemma le_of_pow_le_pow {a b k : ℕ} (hk : k ≠ 0) (h : a ^ k ≤ b ^ k) : a ≤ b := by
  by_contra hgt
  have hlt : b ^ k < a ^ k := Nat.pow_lt_pow_left (Nat.lt_of_not_ge hgt) hk
  omega

lemma paramJ_pos (d : ℕ) : 0 < paramJ d := Nat.one_le_pow (paramK d) 3 (by decide)
lemma one_le_paramJ (d : ℕ) : 1 ≤ paramJ d := paramJ_pos d
lemma one_le_paramL (d : ℕ) : 1 ≤ paramL d := Nat.one_le_pow (paramEll d) 3 (by decide)
lemma one_le_paramL1 (d : ℕ) : 1 ≤ paramL1 d := Nat.one_le_pow _ 3 (by decide)
lemma one_le_paramL2 (d : ℕ) : 1 ≤ paramL2 d := Nat.one_le_pow _ 3 (by decide)
lemma one_le_treeLog (d : ℕ) : 1 ≤ treeLog d := le_max_left 1 _

lemma paramJ_sq_eq_nine_pow (d : ℕ) : (paramJ d) ^ 2 = 9 ^ paramK d := by
  unfold paramJ
  calc
    (3 ^ paramK d) ^ 2 = (3 ^ 2) ^ paramK d := by rw [← pow_mul, mul_comm, pow_mul]
    _ = 9 ^ paramK d := by norm_num

lemma le_paramJ_sq (d : ℕ) : d ≤ (paramJ d) ^ 2 := by
  rw [paramJ_sq_eq_nine_pow]; exact minPowExp_le_pow (by decide) d

lemma paramJ_sq_le_nine (d : ℕ) : (paramJ d) ^ 2 ≤ 9 * (d + 1) := by
  rw [paramJ_sq_eq_nine_pow]
  rcases Nat.eq_zero_or_pos (paramK d) with hk0 | hkpos
  · rw [hk0]; simp only [pow_zero]; omega
  · have hklt : paramK d - 1 < minPowExp 9 d := by unfold paramK at hkpos ⊢; omega
    have hlt : 9 ^ (paramK d - 1) < d :=
      lt_of_lt_minPowExp (b := 9) (by decide) (target := d) hklt
    have hpow : 9 ^ paramK d = 9 * 9 ^ (paramK d - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hkpos, pow_succ']
    omega

lemma paramJ_le_three (d : ℕ) : paramJ d ≤ 3 * (d + 1) := by
  apply le_of_pow_le_pow (by decide : 2 ≠ 0)
  have h1 := paramJ_sq_le_nine d
  have h2 : 9 * (d + 1) ≤ (3 * (d + 1)) ^ 2 := by
    have : (3 * (d + 1)) ^ 2 = 9 * (d + 1) * (d + 1) := by ring
    rw [this]
    exact Nat.le_mul_of_pos_right _ (by omega)
  exact h1.trans h2

lemma paramM_le_paramJ (d : ℕ) : paramM d ≤ paramJ d := by
  unfold paramM
  have hJ : 1 ≤ paramJ d := one_le_paramJ d
  have hdJ : d ≤ (paramJ d) ^ 2 := le_paramJ_sq d
  have hlt : d + paramJ d - 1 < (paramJ d + 1) * paramJ d := by
    have hsq : (paramJ d + 1) * paramJ d = (paramJ d) ^ 2 + paramJ d := by ring
    omega
  have hdiv_lt : (d + paramJ d - 1) / paramJ d < paramJ d + 1 :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hlt)
  omega

lemma paramEll_le_paramK_succ (d : ℕ) : paramEll d ≤ paramK d + 1 := by
  apply minPowExp_min (by decide)
  have hm := paramM_le_paramJ d
  have hJ := one_le_paramJ d
  have hpow : 3 ^ (paramK d + 1) = 3 * paramJ d := by unfold paramJ; rw [pow_succ']
  omega

lemma paramL_le_three_J (d : ℕ) : paramL d ≤ 3 * paramJ d := by
  calc
    paramL d = 3 ^ paramEll d := rfl
    _ ≤ 3 ^ (paramK d + 1) := Nat.pow_le_pow_right (by decide) (paramEll_le_paramK_succ d)
    _ = 3 * paramJ d := by unfold paramJ; rw [pow_succ']

lemma paramL_eq_mul (d : ℕ) : paramL d = paramL1 d * paramL2 d := by
  unfold paramL paramL1 paramL2
  rw [← pow_add]; congr 1; omega

lemma paramL1_le_paramL2 (d : ℕ) : paramL1 d ≤ paramL2 d :=
  Nat.pow_le_pow_right (by decide) (by omega)

lemma paramL2_sq_le_nine_J (d : ℕ) : (paramL2 d) ^ 2 ≤ 9 * paramJ d := by
  have hexp : 2 * ((paramEll d + 1) / 2) ≤ paramEll d + 1 := by omega
  calc
    (paramL2 d) ^ 2 = 3 ^ (2 * ((paramEll d + 1) / 2)) := by
      unfold paramL2; rw [← pow_mul, mul_comm]
    _ ≤ 3 ^ (paramEll d + 1) := Nat.pow_le_pow_right (by decide) hexp
    _ = 3 * paramL d := by unfold paramL; rw [pow_succ']
    _ ≤ 3 * (3 * paramJ d) := Nat.mul_le_mul_left 3 (paramL_le_three_J d)
    _ = 9 * paramJ d := by ring

lemma paramOmegaExp_le_three_J (d : ℕ) : paramOmegaExp d ≤ 3 * paramJ d := by
  calc
    paramOmegaExp d = 3 ^ (paramK d + 1 - paramEll d) := rfl
    _ ≤ 3 ^ (paramK d + 1) := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    _ = 3 * paramJ d := by unfold paramJ; rw [pow_succ']

lemma paramInvOmegaExp_le_three_J (d : ℕ) : paramInvOmegaExp d ≤ 3 * paramJ d :=
  Nat.sub_le _ _

/-- Key linear bound: `paramJ d * paramL2 d ≤ 16 * (d + 1)` via 4th-power comparison. -/
lemma paramJ_mul_L2_le (d : ℕ) : paramJ d * paramL2 d ≤ 16 * (d + 1) := by
  apply le_of_pow_le_pow (by decide : 4 ≠ 0)
  have hJ2 := paramJ_sq_le_nine d
  have hL2 := paramL2_sq_le_nine_J d
  have hL4 : (paramL2 d) ^ 4 ≤ 81 * (paramJ d) ^ 2 := by
    calc
      (paramL2 d) ^ 4 = ((paramL2 d) ^ 2) ^ 2 := by ring
      _ ≤ (9 * paramJ d) ^ 2 := Nat.pow_le_pow_left hL2 2
      _ = 81 * (paramJ d) ^ 2 := by ring
  have hJ4 : (paramJ d) ^ 4 ≤ 81 * (d + 1) ^ 2 := by
    calc
      (paramJ d) ^ 4 = ((paramJ d) ^ 2) ^ 2 := by ring
      _ ≤ (9 * (d + 1)) ^ 2 := Nat.pow_le_pow_left hJ2 2
      _ = 81 * (d + 1) ^ 2 := by ring
  calc
    (paramJ d * paramL2 d) ^ 4 = (paramJ d) ^ 4 * (paramL2 d) ^ 4 := by ring
    _ ≤ (81 * (d + 1) ^ 2) * (81 * (paramJ d) ^ 2) := Nat.mul_le_mul hJ4 hL4
    _ ≤ (81 * (d + 1) ^ 2) * (81 * (9 * (d + 1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 81 hJ2)
    _ = 59049 * (d + 1) ^ 3 := by ring
    _ ≤ 59049 * (d + 1) ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by decide))
    _ ≤ 65536 * (d + 1) ^ 4 := Nat.mul_le_mul_right _ (by decide)
    _ = (16 * (d + 1)) ^ 4 := by ring

lemma paramJ_mul_L_le (d : ℕ) : paramJ d * paramL d ≤ 27 * (d + 1) := by
  calc
    paramJ d * paramL d ≤ paramJ d * (3 * paramJ d) :=
      Nat.mul_le_mul_left _ (paramL_le_three_J d)
    _ = 3 * (paramJ d) ^ 2 := by ring
    _ ≤ 3 * (9 * (d + 1)) := Nat.mul_le_mul_left 3 (paramJ_sq_le_nine d)
    _ = 27 * (d + 1) := by ring

lemma paramL2_le (d : ℕ) : paramL2 d ≤ 16 * (d + 1) := by
  calc
    paramL2 d = 1 * paramL2 d := (Nat.one_mul _).symm
    _ ≤ paramJ d * paramL2 d := Nat.mul_le_mul_right _ (one_le_paramJ d)
    _ ≤ 16 * (d + 1) := paramJ_mul_L2_le d

lemma paramL_le (d : ℕ) : paramL d ≤ 27 * (d + 1) := by
  calc
    paramL d = 1 * paramL d := (Nat.one_mul _).symm
    _ ≤ paramJ d * paramL d := Nat.mul_le_mul_right _ (one_le_paramJ d)
    _ ≤ 27 * (d + 1) := paramJ_mul_L_le d

/-- Key quadratic matrix-entry count bound: `L2 * (J * L2)^2 ≤ 1300 * (d + 1)^2` via 4th powers. -/
lemma paramL2_mul_JL2_sq_le (d : ℕ) :
    paramL2 d * (paramJ d * paramL2 d) ^ 2 ≤ 1300 * (d + 1) ^ 2 := by
  apply le_of_pow_le_pow (by decide : 4 ≠ 0)
  have hJ2 := paramJ_sq_le_nine d
  have hL2 := paramL2_sq_le_nine_J d
  have hL12 : (paramL2 d) ^ 12 ≤ (9 ^ 6) * (paramJ d) ^ 6 := by
    calc
      (paramL2 d) ^ 12 = ((paramL2 d) ^ 2) ^ 6 := by ring
      _ ≤ (9 * paramJ d) ^ 6 := Nat.pow_le_pow_left hL2 6
      _ = (9 ^ 6) * (paramJ d) ^ 6 := by ring
  have hJ8 : (paramJ d) ^ 8 ≤ (9 ^ 4) * (d + 1) ^ 4 := by
    calc
      (paramJ d) ^ 8 = ((paramJ d) ^ 2) ^ 4 := by ring
      _ ≤ (9 * (d + 1)) ^ 4 := Nat.pow_le_pow_left hJ2 4
      _ = (9 ^ 4) * (d + 1) ^ 4 := by ring
  have hJ6 : (paramJ d) ^ 6 ≤ (9 ^ 3) * (d + 1) ^ 3 := by
    calc
      (paramJ d) ^ 6 = ((paramJ d) ^ 2) ^ 3 := by ring
      _ ≤ (9 * (d + 1)) ^ 3 := Nat.pow_le_pow_left hJ2 3
      _ = (9 ^ 3) * (d + 1) ^ 3 := by ring
  calc
    (paramL2 d * (paramJ d * paramL2 d) ^ 2) ^ 4
        = (paramJ d) ^ 8 * (paramL2 d) ^ 12 := by ring
    _ ≤ ((9 ^ 4) * (d + 1) ^ 4) * ((9 ^ 6) * (paramJ d) ^ 6) := Nat.mul_le_mul hJ8 hL12
    _ ≤ ((9 ^ 4) * (d + 1) ^ 4) * ((9 ^ 6) * ((9 ^ 3) * (d + 1) ^ 3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hJ6)
    _ = (9 ^ 13) * (d + 1) ^ 7 := by ring
    _ ≤ (9 ^ 13) * (d + 1) ^ 8 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by decide))
    _ ≤ (1300 ^ 4) * (d + 1) ^ 8 := Nat.mul_le_mul_right _ (by decide)
    _ = (1300 * (d + 1) ^ 2) ^ 4 := by ring

lemma le_treeM (d : ℕ) : d ≤ treeM d := by
  unfold treeM treeLog
  exact le_trans (minPowExp_le_pow (by decide) d)
    (Nat.pow_le_pow_right (by decide) (le_max_right 1 _))

lemma treeM_le (d : ℕ) : treeM d ≤ 2 * (d + 1) := by
  unfold treeM treeLog
  rcases Nat.eq_zero_or_pos (minPowExp 2 d) with h0 | hpos
  · rw [h0]; simp
  · have hmax : max 1 (minPowExp 2 d) = minPowExp 2 d := max_eq_right hpos
    rw [hmax]
    have hlt : 2 ^ (minPowExp 2 d - 1) < d :=
      lt_of_lt_minPowExp (b := 2) (by decide) (target := d) (by omega)
    have hpow : 2 ^ minPowExp 2 d = 2 * 2 ^ (minPowExp 2 d - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hpos, pow_succ']
    omega

lemma treeLog_le (d : ℕ) : treeLog d ≤ d + 1 := by
  unfold treeLog
  have hm := minPowExp_le_self (b := 2) (by decide) d
  omega

/-! ### 1.2 Algebraic Simplifications: `ovlTargetBit`, `coeffPowY`, `fwdSt1InIndices`, `dftUnifiedMat` -/

theorem ovlTargetBit_eq (J blk p : ℕ) : ovlTargetBit J blk p = blk * J + p := by
  unfold ovlTargetBit
  split_ifs with h
  · rfl
  · have : (blk + 1) * J = blk * J + J := by ring
    omega

theorem coeffPowY_mod_mul (J a b u p : ℕ) :
    coeffPowY J (((a % (3 * J)) * b + u)) p = coeffPowY J (a * b + u) p := by
  unfold coeffPowY
  have hmod : ((a % (3 * J)) * b + u) % (3 * J) = (a * b + u) % (3 * J) := by
    conv_rhs => rw [Nat.add_mod, Nat.mul_mod]
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  rw [hmod]

def fwdIdx (J L2 j2 k : ℕ) : ℕ :=
  ((k / J) * L2 + j2) * J + k % J

lemma fwdIdx_div_mod {J : ℕ} (hJ : 0 < J) (L2 j2 k : ℕ) :
    fwdIdx J L2 j2 k / J = (k / J) * L2 + j2 ∧ fwdIdx J L2 j2 k % J = k % J := by
  unfold fwdIdx
  have hlt : k % J < J := Nat.mod_lt k hJ
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hJ, Nat.div_eq_of_lt hlt, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

lemma fwdIdx_strictMono {J L2 j2 : ℕ} (hJ : 0 < J) (hj2 : j2 < L2)
    {k1 k2 : ℕ} (hlt : k1 < k2) : fwdIdx J L2 j2 k1 < fwdIdx J L2 j2 k2 := by
  unfold fwdIdx
  have h1 := Nat.div_add_mod k1 J
  have h2 := Nat.div_add_mod k2 J
  have hr1 : k1 % J < J := Nat.mod_lt k1 hJ
  have hr2 : k2 % J < J := Nat.mod_lt k2 hJ
  by_cases hq : k1 / J = k2 / J
  · rw [hq] at h1 ⊢
    omega
  · have hqlt : k1 / J < k2 / J := by
      rcases lt_trichotomy (k1 / J) (k2 / J) with h | h | h
      · exact h
      · exact absurd h hq
      · have hle : J * (k2 / J + 1) ≤ J * (k1 / J) := Nat.mul_le_mul_left J h
        have hexp : J * (k2 / J + 1) = J * (k2 / J) + J := by ring
        omega
    have hblk : (k1 / J) * L2 + j2 + 1 ≤ (k2 / J) * L2 + j2 := by
      have hm : (k1 / J + 1) * L2 ≤ (k2 / J) * L2 := Nat.mul_le_mul_right L2 hqlt
      have hexp : (k1 / J + 1) * L2 = (k1 / J) * L2 + L2 := by ring
      omega
    have hmul : ((k1 / J) * L2 + j2 + 1) * J ≤ ((k2 / J) * L2 + j2) * J :=
      Nat.mul_le_mul_right J hblk
    have hexp2 : ((k1 / J) * L2 + j2 + 1) * J = ((k1 / J) * L2 + j2) * J + J := by ring
    omega

lemma fwdIdx_ge_self {J L2 j2 : ℕ} (hj2 : j2 < L2) (k : ℕ) :
    k ≤ fwdIdx J L2 j2 k := by
  unfold fwdIdx
  have hL2 : 1 ≤ L2 := by omega
  have hq : k / J ≤ (k / J) * L2 + j2 := by
    have : (k / J) * 1 ≤ (k / J) * L2 := Nat.mul_le_mul_left _ hL2
    omega
  have hmul : (k / J) * J ≤ ((k / J) * L2 + j2) * J := Nat.mul_le_mul_right J hq
  have hdm := Nat.div_add_mod k J
  have hc : J * (k / J) = (k / J) * J := Nat.mul_comm _ _
  omega

lemma filter_range_downward_closed (P : ℕ → Bool)
    (hdown : ∀ a b, a < b → P b = true → P a = true) :
    ∀ n : ℕ, (List.range n).filter P = List.range (((List.range n).filter P).length)
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.filter_append]
    cases hm : P m with
    | false =>
      have htail : [m].filter P = [] := by simp [List.filter, hm]
      rw [htail, List.append_nil]
      exact filter_range_downward_closed P hdown m
    | true =>
      have hall : (List.range m).filter P = List.range m := by
        rw [List.filter_eq_self]
        intro a ha
        exact hdown a m (List.mem_range.mp ha) hm
      have htail : [m].filter P = [m] := by simp [List.filter, hm]
      rw [htail, hall, ← List.range_succ, List.length_range]

lemma eq_of_pairwise_lt_iff :
    ∀ {l1 l2 : List ℕ},
      l1.Pairwise (· < ·) → l2.Pairwise (· < ·) → (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: bs, _, _, hiff => absurd ((hiff b).mpr List.mem_cons_self) (by simp)
  | a :: as, [], _, _, hiff => absurd ((hiff a).mp List.mem_cons_self) (by simp)
  | a :: as, b :: bs, hp1, hp2, hiff => by
    rw [List.pairwise_cons] at hp1 hp2
    have hab : a = b := by
      have ha : a ∈ b :: bs := (hiff a).mp List.mem_cons_self
      have hb : b ∈ a :: as := (hiff b).mpr List.mem_cons_self
      rcases List.mem_cons.mp ha with rfl | habs
      · rfl
      · rcases List.mem_cons.mp hb with rfl | hbas
        · rfl
        · have h1 := hp2.1 a habs
          have h2 := hp1.1 b hbas
          omega
    subst hab
    congr 1
    refine eq_of_pairwise_lt_iff hp1.2 hp2.2 (fun x => ?_)
    constructor
    · intro hx
      have hax : a < x := hp1.1 x hx
      rcases List.mem_cons.mp ((hiff x).mp (List.mem_cons_of_mem a hx)) with rfl | hxbs
      · omega
      · exact hxbs
    · intro hx
      have hax : a < x := hp2.1 x hx
      rcases List.mem_cons.mp ((hiff x).mpr (List.mem_cons_of_mem a hx)) with rfl | hxas
      · omega
      · exact hxas

theorem fwdSt1InIndices_eq_map (n J L2 j2 : ℕ) (hJ : 0 < J) (hj2 : j2 < L2) :
    let cnt := (fwdSt1InIndices n J L2 j2).length
    fwdSt1InIndices n J L2 j2 = (List.range cnt).map (fwdIdx J L2 j2) := by
  set P : ℕ → Bool := fun k => decide (fwdIdx J L2 j2 k < n)
  have hdown : ∀ a b, a < b → P b = true → P a = true := by
    intro a b hab hPb
    simp only [P, decide_eq_true_eq] at hPb ⊢
    exact lt_trans (fwdIdx_strictMono hJ hj2 hab) hPb
  set l0 := (List.range n).filter P
  have hl0_eq : l0 = List.range l0.length := filter_range_downward_closed P hdown n
  have hmap_eq : (List.range l0.length).map (fwdIdx J L2 j2) = fwdSt1InIndices n J L2 j2 := by
    apply eq_of_pairwise_lt_iff
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun {a b} hab => fwdIdx_strictMono hJ hj2 hab) List.pairwise_lt_range
    · exact List.Pairwise.filter _ List.pairwise_lt_range
    · intro idx
      rw [← hl0_eq]
      simp only [l0, P, fwdSt1InIndices, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨k, ⟨_, hfn⟩, rfl⟩
        refine ⟨hfn, ?_⟩
        rw [(fwdIdx_div_mod hJ L2 j2 k).1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj2]
      · rintro ⟨hidx_lt, hmod_eq⟩
        set k := ((idx / J) / L2) * J + idx % J
        have hkm : idx % J < J := Nat.mod_lt idx hJ
        have hk_div : k / J = (idx / J) / L2 := by
          dsimp only [k]
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hJ, Nat.div_eq_of_lt hkm, Nat.zero_add]
        have hk_mod : k % J = idx % J := by
          dsimp only [k]
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hkm]
        have hfk : fwdIdx J L2 j2 k = idx := by
          unfold fwdIdx
          rw [hk_div, hk_mod]
          have hd1 := Nat.div_add_mod (idx / J) L2
          have hc1 : L2 * ((idx / J) / L2) = ((idx / J) / L2) * L2 := Nat.mul_comm _ _
          have hr_eq : ((idx / J) / L2) * L2 + j2 = idx / J := by omega
          rw [hr_eq]
          have hd2 := Nat.div_add_mod idx J
          have hc2 : J * (idx / J) = (idx / J) * J := Nat.mul_comm _ _
          omega
        refine ⟨k, ⟨?_, ?_⟩, hfk⟩
        · exact lt_of_le_of_lt (fwdIdx_ge_self hj2 k) (by rw [hfk]; exact hidx_lt)
        · rw [hfk]; exact hidx_lt
  have hlen : (fwdSt1InIndices n J L2 j2).length = l0.length := by
    rw [← hmap_eq, List.length_map, List.length_range]
  dsimp only
  rw [hlen, hmap_eq]

lemma fwdSt1InIndices_length_le_n (n J L2 j2 : ℕ) :
    (fwdSt1InIndices n J L2 j2).length ≤ n := by
  unfold fwdSt1InIndices
  exact (List.length_filter_le _ _).trans (by simp)

lemma fwdSt1InIndices_length_le_JL1 (n : ℕ) (j2 : ℕ) :
    (fwdSt1InIndices n (paramJ n) (paramL2 n) j2).length ≤ 2 * paramJ n * paramL2 n := by
  by_cases hj2 : j2 < paramL2 n
  · have hmap := fwdSt1InIndices_eq_map n (paramJ n) (paramL2 n) j2 (paramJ_pos n) hj2
    set cnt := (fwdSt1InIndices n (paramJ n) (paramL2 n) j2).length
    rcases Nat.eq_zero_or_pos cnt with h0 | hpos
    · omega
    · have hmem : fwdIdx (paramJ n) (paramL2 n) j2 (cnt - 1) ∈
          fwdSt1InIndices n (paramJ n) (paramL2 n) j2 := by
        rw [hmap, List.mem_map]
        exact ⟨cnt - 1, List.mem_range.mpr (by omega), rfl⟩
      simp only [fwdSt1InIndices, List.mem_filter, List.mem_range] at hmem
      have hlt_n : fwdIdx (paramJ n) (paramL2 n) j2 (cnt - 1) < n := hmem.1
      have hn_le : n ≤ paramM n * paramJ n := by
        unfold paramM
        have hJ : 0 < paramJ n := paramJ_pos n
        have hdiv := Nat.div_add_mod (n + paramJ n - 1) (paramJ n)
        have hmod : (n + paramJ n - 1) % paramJ n < paramJ n := Nat.mod_lt _ hJ
        have hmul : paramJ n * ((n + paramJ n - 1) / paramJ n) =
            ((n + paramJ n - 1) / paramJ n) * paramJ n := Nat.mul_comm _ _
        omega
      have hM_le_L : paramM n ≤ paramL n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn_pos
        · simp [paramM, paramJ, paramK, minPowExp, minPowExpAux]
        · have hM1 : 1 ≤ paramM n :=
            (Nat.le_div_iff_mul_le (one_le_paramJ n)).2 (by omega)
          have h2M : 2 * paramM n - 1 ≤ paramL n := minPowExp_le_pow (by decide) _
          omega
      have hlt_LJ : fwdIdx (paramJ n) (paramL2 n) j2 (cnt - 1) < (paramL1 n * paramL2 n) * paramJ n := by
        calc
          fwdIdx (paramJ n) (paramL2 n) j2 (cnt - 1) < n := hlt_n
          _ ≤ paramM n * paramJ n := hn_le
          _ ≤ paramL n * paramJ n := Nat.mul_le_mul_right _ hM_le_L
          _ = (paramL1 n * paramL2 n) * paramJ n := by rw [paramL_eq_mul]
      have hdiv1 : ((cnt - 1) / paramJ n) * paramL2 n + j2 < paramL1 n * paramL2 n := by
        have h1 := (fwdIdx_div_mod (paramJ_pos n) (paramL2 n) j2 (cnt - 1)).1
        rw [← h1]
        exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hlt_LJ)
      have hdiv2 : (cnt - 1) / paramJ n < paramL1 n := by
        by_contra hge
        have hle : paramL1 n * paramL2 n ≤ ((cnt - 1) / paramJ n) * paramL2 n :=
          Nat.mul_le_mul_right _ (Nat.le_of_not_lt hge)
        omega
      have hcnt_lt : cnt - 1 < paramL1 n * paramJ n := by
        have hdm := Nat.div_add_mod (cnt - 1) (paramJ n)
        have hmod : (cnt - 1) % paramJ n < paramJ n := Nat.mod_lt _ (paramJ_pos n)
        have hle : ((cnt - 1) / paramJ n + 1) * paramJ n ≤ paramL1 n * paramJ n :=
          Nat.mul_le_mul_right _ hdiv2
        have hexp : ((cnt - 1) / paramJ n + 1) * paramJ n =
            paramJ n * ((cnt - 1) / paramJ n) + paramJ n := by ring
        omega
      have hL12 : paramL1 n ≤ paramL2 n := paramL1_le_paramL2 n
      have hJL12 : paramL1 n * paramJ n ≤ 2 * paramJ n * paramL2 n := by
        calc
          paramL1 n * paramJ n = paramJ n * paramL1 n := Nat.mul_comm _ _
          _ ≤ paramJ n * paramL2 n := Nat.mul_le_mul_left _ hL12
          _ ≤ 2 * (paramJ n * paramL2 n) := Nat.le_mul_of_pos_left _ (by decide)
          _ = 2 * paramJ n * paramL2 n := by ring
      omega
  · have hemp : fwdSt1InIndices n (paramJ n) (paramL2 n) j2 = [] := by
      unfold fwdSt1InIndices
      rw [List.filter_eq_nil_iff]
      intro idx _
      have hmod : (idx / paramJ n) % paramL2 n < paramL2 n := Nat.mod_lt _ (one_le_paramL2 n)
      simp [show (idx / paramJ n) % paramL2 n ≠ j2 by omega]
    rw [hemp]; simp

def dftUnifiedMat (J wExp inStep stride off : ℕ) (outIdx inIdx : ℕ) : Bool :=
  let qOut := outIdx / (2 * J)
  let pOut := outIdx % (2 * J)
  let qIn := inIdx / inStep
  let uIn := inIdx % inStep
  coeffPowY J (wExp * (stride * qIn + off) * qOut + uIn) pOut

theorem linearMapCheckCircuit_congr (numIn numOut : ℕ) (mat1 mat2 : ℕ → ℕ → Bool)
    (h : ∀ j < numOut, ∀ i < numIn, mat1 j i = mat2 j i) :
    linearMapCheckCircuit numIn numOut mat1 = linearMapCheckCircuit numIn numOut mat2 := by
  have hspecs :
      (List.range numOut).map (fun j => (numIn + j, (List.range numIn).filter (fun i => mat1 j i))) =
      (List.range numOut).map (fun j => (numIn + j, (List.range numIn).filter (fun i => mat2 j i))) := by
    refine List.map_congr_left (fun j hj => ?_)
    congr 1
    exact List.filter_congr (fun i hi => h j (List.mem_range.mp hj) i (List.mem_range.mp hi))
  unfold linearMapCheckCircuit
  dsimp only
  rw [hspecs]

theorem st2Mat_circuit_eq_unified (J L1 L2 wExp : ℕ) :
    linearMapCheckCircuit (2 * J * L2) (2 * J * L2) (st2Mat J L1 L2 wExp) =
      linearMapCheckCircuit (2 * J * L2) (2 * J * L2) (dftUnifiedMat J wExp (2 * J) L1 0) := by
  apply linearMapCheckCircuit_congr
  intro outIdx hout inIdx hin
  have hq2 : outIdx / (2 * J) < L2 :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hout)
  have hj2 : inIdx / (2 * J) < L2 :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hin)
  unfold st2Mat dftUnifiedMat
  simp [hq2, hj2, Nat.mul_assoc]

theorem fullSt1Mat_circuit_eq_unified (J L1 L2 wExp j2 : ℕ) :
    linearMapCheckCircuit (2 * J * L1) (2 * J * L1) (fullSt1Mat J L1 L2 wExp j2) =
      linearMapCheckCircuit (2 * J * L1) (2 * J * L1) (dftUnifiedMat J wExp (2 * J) L2 j2) := by
  apply linearMapCheckCircuit_congr
  intro outIdx hout inIdx hin
  have hq1 : outIdx / (2 * J) < L1 :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hout)
  have hj1 : inIdx / (2 * J) < L1 :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hin)
  unfold fullSt1Mat dftUnifiedMat
  simp [hq1, hj1]

theorem fwdSt1Mat_circuit_eq_unified (n J L1 L2 wExp j2 : ℕ) (hJ : 0 < J) (hj2 : j2 < L2) :
    let inList := fwdSt1InIndices n J L2 j2
    linearMapCheckCircuit inList.length (2 * J * L1) (fwdSt1Mat J L1 wExp inList) =
      linearMapCheckCircuit inList.length (2 * J * L1) (dftUnifiedMat J wExp J L2 j2) := by
  dsimp only
  apply linearMapCheckCircuit_congr
  intro outIdx hout inK hinK
  have hq1 : outIdx / (2 * J) < L1 :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hout)
  have hmap := fwdSt1InIndices_eq_map n J L2 j2 hJ hj2
  have hget : (fwdSt1InIndices n J L2 j2).getD inK 0 = fwdIdx J L2 j2 inK := by
    rw [hmap, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hinK]
    rfl
  unfold fwdSt1Mat dftUnifiedMat
  dsimp only
  rw [hget, (fwdIdx_div_mod hJ L2 j2 inK).1, (fwdIdx_div_mod hJ L2 j2 inK).2]
  have hcomm : (inK / J) * L2 = L2 * (inK / J) := Nat.mul_comm _ _
  rw [hcomm]
  simp [hq1]

/-! ### 1.3 Monotonicity & Upper Bounds on `prefixHits` and `parityRowStart` -/

lemma prefixHits_mono (pred : ℕ → Bool) : ∀ {a b : ℕ}, a ≤ b → prefixHits pred a ≤ prefixHits pred b := by
  intro a b hab
  induction hab with
  | refl => exact le_rfl
  | @step m _ ih =>
    rw [prefixHits_succ]
    omega

lemma prefixHits_succ_le_of_pos {pred : ℕ → Bool} {k M : ℕ} (hk : k < M) (hp : pred k = true) :
    prefixHits pred k + 1 ≤ prefixHits pred M := by
  have h1 : prefixHits pred k + 1 = prefixHits pred (k + 1) := by
    rw [prefixHits_succ, hp]; simp
  rw [h1]
  exact prefixHits_mono pred hk

lemma parityRowStart_mono (base M : ℕ) (active : ℕ → ℕ → Bool) :
    ∀ {a b : ℕ}, a ≤ b → parityRowStart base M active a ≤ parityRowStart base M active b := by
  intro a b hab
  induction hab with
  | refl => exact le_rfl
  | @step m _ ih =>
    rw [parityRowStart_succ]
    omega

lemma parityRowStart_le_bound (base M R : ℕ) (active : ℕ → ℕ → Bool) :
    parityRowStart base M active R ≤ base + R * (7 + 5 * M) := by
  induction R with
  | zero => simp
  | succ r ih =>
    rw [parityRowStart_succ]
    have hhits : parityRowHits M active r ≤ M := prefixHits_le (active r) M
    have hexp : (r + 1) * (7 + 5 * M) = r * (7 + 5 * M) + 7 + 5 * M := by ring
    omega

/-!
## Section 2: Master 19-Block Stream Decomposition of `rawPred`
-/

lemma range_add_flatMap {α : Type*} (a b : ℕ) (f : ℕ → List α) :
    (List.range (a + b)).flatMap f =
      (List.range a).flatMap f ++ (List.range b).flatMap (fun i => f (a + i)) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]

lemma range_sub_split_flatMap {α : Type*} {lo hi : ℕ} (hle : lo ≤ hi) (f : ℕ → List α) :
    (List.range hi).flatMap f =
      (List.range lo).flatMap f ++ (List.range (hi - lo)).flatMap (fun i => f (lo + i)) := by
  have heq : hi = lo + (hi - lo) := (Nat.add_sub_of_le hle).symm
  conv_lhs => rw [heq]
  exact range_add_flatMap lo (hi - lo) f

lemma treeVertOff_mono (r : ℕ) : ∀ {a b : ℕ}, a ≤ b → treeVertOff r a ≤ treeVertOff r b := by
  intro a b hab
  induction hab with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    cases m with
    | zero => exact ih
    | succ m' =>
      change treeVertOff r a ≤ treeVertOff r (m' + 2)
      have h : treeVertOff r (m' + 2) = treeVertOff r (m' + 1) + (m' + 2) * 2 ^ (r - (m' + 1)) := rfl
      omega

lemma decodeTreeVertAux_spec (r : ℕ) :
    ∀ (fuel j rem : ℕ),
      1 ≤ j →
      j + fuel = r + 1 →
      treeVertOff r j + rem < treeVertOff r (r + 1) →
      let t := decodeTreeVertAux r rem fuel j
      1 ≤ t.1 ∧ t.1 ≤ r ∧ t.2.1 < 2 ^ (r - t.1) ∧ t.2.2 < t.1 + 1 ∧
      treeVertOff r j + rem = treeVertOff r t.1 + t.2.1 * (t.1 + 1) + t.2.2
  | 0, j, rem, _, hjf, hlt => by
    have : j = r + 1 := by omega
    subst this; omega
  | fuel + 1, j, rem, hj1, hjf, hlt => by
    simp only [decodeTreeVertAux]
    set blk := (j + 1) * 2 ^ (r - j)
    split_ifs with hrem
    · dsimp only
      have hdiv : rem / (j + 1) < 2 ^ (r - j) := Nat.div_lt_of_lt_mul hrem
      have hmod : rem % (j + 1) < j + 1 := Nat.mod_lt _ (by omega)
      have hdm := Nat.div_add_mod rem (j + 1)
      have hcomm : (j + 1) * (rem / (j + 1)) = (rem / (j + 1)) * (j + 1) := Nat.mul_comm _ _
      exact ⟨hj1, by omega, hdiv, hmod, by omega⟩
    · have hstep : treeVertOff r (j + 1) = treeVertOff r j + blk := by
        cases j with | zero => omega | succ _ => rfl
      have hrec := decodeTreeVertAux_spec r fuel (j + 1) (rem - blk)
        (by omega) (by omega) (by omega)
      exact ⟨hrec.1, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1, by have := hrec.2.2.2.2; omega⟩

lemma encodeTreeVert_lt {r j node u : ℕ}
    (hj1 : 1 ≤ j) (hjr : j ≤ r) (hnode : node < 2 ^ (r - j)) (hu : u < j + 1) :
    treeVertOff r j + node * (j + 1) + u < treeVertOff r (r + 1) := by
  have h1 : node * (j + 1) + u < (node + 1) * (j + 1) := by
    have : (node + 1) * (j + 1) = node * (j + 1) + (j + 1) := by ring
    omega
  have h2 : (node + 1) * (j + 1) ≤ 2 ^ (r - j) * (j + 1) := Nat.mul_le_mul_right _ hnode
  have h3 : treeVertOff r (j + 1) = treeVertOff r j + (j + 1) * 2 ^ (r - j) := by
    cases j with | zero => omega | succ _ => rfl
  have h4 : treeVertOff r (j + 1) ≤ treeVertOff r (r + 1) := treeVertOff_mono r (by omega)
  have hcomm : 2 ^ (r - j) * (j + 1) = (j + 1) * 2 ^ (r - j) := Nat.mul_comm _ _
  omega

lemma encodeTreeVert_inj {r j1 n1 u1 j2 n2 u2 : ℕ}
    (hj1_lo : 1 ≤ j1) (hn1 : n1 < 2 ^ (r - j1)) (hu1 : u1 < j1 + 1)
    (hj2_lo : 1 ≤ j2) (hn2 : n2 < 2 ^ (r - j2)) (hu2 : u2 < j2 + 1)
    (heq : treeVertOff r j1 + n1 * (j1 + 1) + u1 =
           treeVertOff r j2 + n2 * (j2 + 1) + u2) :
    j1 = j2 ∧ n1 = n2 ∧ u1 = u2 := by
  have hj_eq : j1 = j2 := by
    rcases lt_trichotomy j1 j2 with hlt | rfl | hgt
    · have hb1 : treeVertOff r j1 + n1 * (j1 + 1) + u1 < treeVertOff r (j1 + 1) := by
        have hstep : treeVertOff r (j1 + 1) = treeVertOff r j1 + (j1 + 1) * 2 ^ (r - j1) := by
          cases j1 with | zero => omega | succ _ => rfl
        have hmul : (n1 + 1) * (j1 + 1) ≤ 2 ^ (r - j1) * (j1 + 1) := Nat.mul_le_mul_right _ hn1
        have hcomm : 2 ^ (r - j1) * (j1 + 1) = (j1 + 1) * 2 ^ (r - j1) := Nat.mul_comm _ _
        have hlin : (n1 + 1) * (j1 + 1) = n1 * (j1 + 1) + (j1 + 1) := by ring
        omega
      have hb2 : treeVertOff r (j1 + 1) ≤ treeVertOff r j2 := treeVertOff_mono r hlt
      omega
    · rfl
    · have hb2 : treeVertOff r j2 + n2 * (j2 + 1) + u2 < treeVertOff r (j2 + 1) := by
        have hstep : treeVertOff r (j2 + 1) = treeVertOff r j2 + (j2 + 1) * 2 ^ (r - j2) := by
          cases j2 with | zero => omega | succ _ => rfl
        have hmul : (n2 + 1) * (j2 + 1) ≤ 2 ^ (r - j2) * (j2 + 1) := Nat.mul_le_mul_right _ hn2
        have hcomm : 2 ^ (r - j2) * (j2 + 1) = (j2 + 1) * 2 ^ (r - j2) := Nat.mul_comm _ _
        have hlin : (n2 + 1) * (j2 + 1) = n2 * (j2 + 1) + (j2 + 1) := by ring
        omega
      have hb1 : treeVertOff r (j2 + 1) ≤ treeVertOff r j1 := treeVertOff_mono r hgt
      omega
  subst hj_eq
  have hsub : n1 * (j1 + 1) + u1 = n2 * (j1 + 1) + u2 := by omega
  have hu_eq : u1 = u2 := by
    have hm := congrArg (· % (j1 + 1)) hsub
    simpa [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hu1, Nat.mod_eq_of_lt hu2] using hm
  subst hu_eq
  have hn_mul : n1 * (j1 + 1) = n2 * (j1 + 1) := by omega
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega) hn_mul, rfl⟩

lemma decodeTreeVert_encode {r j node u : ℕ}
    (hj1 : 1 ≤ j) (hjr : j ≤ r) (hnode : node < 2 ^ (r - j)) (hu : u < j + 1) :
    decodeTreeVert r (treeVertOff r j + node * (j + 1) + u) = (j, node, u) := by
  have hlt := encodeTreeVert_lt hj1 hjr hnode hu
  have hsp := decodeTreeVertAux_spec r r 1 (treeVertOff r j + node * (j + 1) + u)
    (by omega) (by omega) (by simpa [treeVertOff] using hlt)
  set t := decodeTreeVert r (treeVertOff r j + node * (j + 1) + u)
  have ht_eq : decodeTreeVertAux r (treeVertOff r j + node * (j + 1) + u) r 1 = t := rfl
  rw [ht_eq] at hsp
  have h0 : treeVertOff r 1 = 0 := rfl
  rw [h0, Nat.zero_add] at hsp
  obtain ⟨e1, e2, e3⟩ := encodeTreeVert_inj hsp.1 hsp.2.2.1 hsp.2.2.2.1 hj1 hnode hu hsp.2.2.2.2.symm
  rcases t with ⟨tj, tn, tu⟩
  dsimp only at e1 e2 e3
  rw [e1, e2, e3]

lemma range_treeVertOff_flatMap {α : Type*} (r : ℕ) (f : ℕ → List α) :
    ∀ k : ℕ,
      (List.range (treeVertOff r (k + 1))).flatMap f =
        (List.range k).flatMap (fun j0 =>
          let j := j0 + 1
          (List.range (2 ^ (r - j))).flatMap (fun node =>
            (List.range (j + 1)).flatMap (fun u =>
              f (treeVertOff r j + node * (j + 1) + u))))
  | 0 => rfl
  | k + 1 => by
    have hstep : treeVertOff r (k + 2) =
        treeVertOff r (k + 1) + 2 ^ (r - (k + 1)) * (k + 2) := by
      change treeVertOff r (k + 1) + (k + 2) * 2 ^ (r - (k + 1)) = _
      rw [Nat.mul_comm]
    rw [hstep, range_add_flatMap, range_treeVertOff_flatMap r f k,
        List.range_succ, List.flatMap_append, List.flatMap_singleton]
    congr 1
    rw [range_mul_eq_flatMap (2 ^ (r - (k + 1))) (k + 2), flatMap_flatMap_eq]
    refine List.flatMap_congr (fun node _ => ?_)
    rw [List.flatMap_map]
    refine List.flatMap_congr (fun u _ => ?_)
    have hassoc : treeVertOff r (k + 1) + (node * (k + 2) + u) =
        treeVertOff r (k + 1) + node * (k + 2) + u := by omega
    rw [hassoc]

/-! ### Closed-Form Per-Block Bit-Stream Definitions (`blockStream0 .. blockStream18`) -/

def pinBitNoneBits : List Bool := [true, false, true, false, false, false, true]
def pinBitTrueBits : List Bool := [true, false, true, false, false, false, false, false]
def pinBitFalseBits : List Bool :=
  [true, false, true, true, false, false, false, false, false, false, true, true, false]
def const0TrueBits : List Bool := [false, true, false, false, false, true]
def const1TrueBits : List Bool := [true, false, true, false, false, false, true]
def sepCmpBits : List Bool :=
  [true, true, true, false, true, true, false, false, false, false, true, true, false,
   false, true, true, false]

def blockStream0 (n : ℕ) (pre : List Bool) : List Bool :=
  (List.range (2 * n)).flatMap (fun v =>
    if v < pre.length then
      if pre.getD v false then pinBitTrueBits else pinBitFalseBits
    else pinBitNoneBits)

def blockStream1 (n : ℕ) : List Bool :=
  (List.range (2 * n)).flatMap (fun _ => ecopyBits)

def blockStream2 (n : ℕ) (h : Fin n → ZMod 2) : List Bool :=
  (List.range n).flatMap (fun idx =>
    if hlt : idx < n then
      if zmod2ToBool (h ⟨idx, hlt⟩) then pinBitTrueBits else pinBitFalseBits
    else pinBitFalseBits)

def blockStream3 (n : ℕ) : List Bool :=
  let J := paramJ n; let L1 := paramL1 n; let L2 := paramL2 n; let wExp := paramOmegaExp n
  (List.range L2).flatMap (fun j2 =>
    let numIn := (fwdSt1InIndices n J L2 j2).length
    QCSD_encodeCircuit (linearMapCheckCircuit numIn (2 * J * L1) (dftUnifiedMat J wExp J L2 j2)))

def blockStream4 (n : ℕ) : List Bool :=
  let J := paramJ n; let L1 := paramL1 n; let L2 := paramL2 n; let wExp := paramOmegaExp n
  (List.range L1).flatMap (fun _ =>
    QCSD_encodeCircuit (linearMapCheckCircuit (2 * J * L2) (2 * J * L2)
      (dftUnifiedMat J wExp (2 * J) L1 0)))

def blockStream5 (n : ℕ) : List Bool := blockStream3 n
def blockStream6 (n : ℕ) : List Bool := blockStream4 n

def blockStream7 (n : ℕ) : List Bool :=
  let J := paramJ n; let L := paramL n
  (List.range L).flatMap (fun _ =>
    QCSD_encodeCircuit (bilinearMapCheckCircuit (2 * J) (2 * J) (2 * J) (ringMulTensor J)))

def blockStream8 (n : ℕ) : List Bool :=
  let J := paramJ n; let L1 := paramL1 n; let L2 := paramL2 n; let invW := paramInvOmegaExp n
  (List.range L2).flatMap (fun j2 =>
    QCSD_encodeCircuit (linearMapCheckCircuit (2 * J * L1) (2 * J * L1)
      (dftUnifiedMat J invW (2 * J) L2 j2)))

def blockStream9 (n : ℕ) : List Bool :=
  let J := paramJ n; let L1 := paramL1 n; let L2 := paramL2 n; let invW := paramInvOmegaExp n
  (List.range L1).flatMap (fun _ =>
    QCSD_encodeCircuit (linearMapCheckCircuit (2 * J * L2) (2 * J * L2)
      (dftUnifiedMat J invW (2 * J) L1 0)))

def blockStream10 (n : ℕ) : List Bool :=
  let J := paramJ n; let L := paramL n
  (List.range L).flatMap (fun blk =>
    (List.range (2 * J)).flatMap (fun p =>
      if blk * J + p < 2 * n then const0TrueBits else const1TrueBits))

def blockStream11 (n : ℕ) : List Bool :=
  let J := paramJ n; let L := paramL n
  (List.range (2 * n)).flatMap (fun tk =>
    let q := tk / J
    let dIn := (if 0 < q ∧ q - 1 < L then 1 else 0) + (if q < L then 1 else 0)
    if dIn = 0 then ovl0Bits else if dIn = 1 then ovl1Bits else ovl2Bits)

def blockStream12 (n : ℕ) (s : Fin n → ZMod 2) : List Bool :=
  (List.range n).flatMap (fun i =>
    synCheckBits (if hlt : i < n then zmod2ToBool (s ⟨i, hlt⟩) else false))

def blockStream13 (n : ℕ) : List Bool :=
  (List.range (treeM n - n)).flatMap (fun _ => pinBitFalseBits)

def blockStream14 (n : ℕ) : List Bool := blockStream13 n

def blockStream15 (mode n t0 t1 : ℕ) : List Bool :=
  let r := treeLog n + 1
  (List.range r).flatMap (fun j0 =>
    let j := j0 + 1
    (List.range (2 ^ (r - j))).flatMap (fun _ =>
      pinBitFalseBits ++
      (List.range j).flatMap (fun b =>
        if mode = 2 ∧ j = r then
          sepFullAdderBits (decide (t0 < 2 ^ r ∧ t1 < 2 ^ r)) (t0.testBit b) (t1.testBit b)
        else fullAdderBits)))

def blockStream16 : List Bool := pinBitFalseBits

def blockStream17 (mode n t0 : ℕ) : List Bool :=
  let W := treeLog n + 2
  (List.range W).flatMap (fun b =>
    if mode = 0 then exactCmpStepBits (decide (t0 < 2 ^ W)) (t0.testBit b)
    else if mode = 1 then borrowStepBits (t0.testBit b)
    else sepCmpBits)

def blockStream18 (mode n t0 : ℕ) : List Bool :=
  let W := treeLog n + 2
  if mode = 1 ∧ ¬(t0 < 2 ^ W) then const1TrueBits else pinBitFalseBits

lemma netV_chain (n : ℕ) :
    netV0 n ≤ netV1 n ∧ netV1 n ≤ netV2 n ∧ netV2 n ≤ netV3 n ∧ netV3 n ≤ netV4 n ∧
    netV4 n ≤ netV5 n ∧ netV5 n ≤ netV6 n ∧ netV6 n ≤ netV7 n ∧ netV7 n ≤ netV8 n ∧
    netV8 n ≤ netV9 n ∧ netV9 n ≤ netV10 n ∧ netV10 n ≤ netV11 n ∧ netV11 n ≤ netV12 n ∧
    netV12 n ≤ netV13 n ∧ netV13 n ≤ netV14 n ∧ netV14 n ≤ netV15 n ∧ netV15 n ≤ netV16 n ∧
    netV16 n ≤ netV17 n ∧ netV17 n ≤ netV18 n ∧ netV18 n ≤ netVertCount n := by
  simp only [netV0, netV1, netV2, netV3, netV4, netV5, netV6, netV7, netV8, netV9,
             netV10, netV11, netV12, netV13, netV14, netV15, netV16, netV17, netV18, netVertCount]
  omega

/-! ### Per-Block `rawPred` Lemmas (`rawPred_V0 .. rawPred_V18`) for Instant Elaboration -/

lemma rawPred_V0 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hhi : v < netV1 n) :
    rawPred mode n h s t0 t1 pre v =
      pinBitCircuit (if v < pre.length then some (pre.getD v false) else none) := by
  unfold rawPred; dsimp only; simp only [hhi, ↓reduceIte]

lemma rawPred_V1 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV1 n ≤ v) (hhi : v < netV2 n) :
    rawPred mode n h s t0 t1 pre v = linearMapCheckCircuit 1 2 (fun _ _ => true) := by
  unfold rawPred; dsimp only; simp only [show ¬(v < netV1 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V2 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV2 n ≤ v) (hhi : v < netV3 n) :
    rawPred mode n h s t0 t1 pre v =
      pinBitCircuit (some (if hlt : v - netV2 n < n then zmod2ToBool (h ⟨v - netV2 n, hlt⟩) else false)) := by
  rcases netV_chain n with ⟨_, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V3 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV3 n ≤ v) (hhi : v < netV4 n) :
    rawPred mode n h s t0 t1 pre v =
      (let inList := fwdSt1InIndices n (paramJ n) (paramL2 n) (v - netV3 n)
       linearMapCheckCircuit inList.length (2 * paramJ n * paramL1 n)
         (fwdSt1Mat (paramJ n) (paramL1 n) (paramOmegaExp n) inList)) := by
  rcases netV_chain n with ⟨_, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V4 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV4 n ≤ v) (hhi : v < netV5 n) :
    rawPred mode n h s t0 t1 pre v =
      linearMapCheckCircuit (2 * paramJ n * paramL2 n) (2 * paramJ n * paramL2 n)
        (st2Mat (paramJ n) (paramL1 n) (paramL2 n) (paramOmegaExp n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V5 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV5 n ≤ v) (hhi : v < netV6 n) :
    rawPred mode n h s t0 t1 pre v =
      (let inList := fwdSt1InIndices n (paramJ n) (paramL2 n) (v - netV5 n)
       linearMapCheckCircuit inList.length (2 * paramJ n * paramL1 n)
         (fwdSt1Mat (paramJ n) (paramL1 n) (paramOmegaExp n) inList)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V6 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV6 n ≤ v) (hhi : v < netV7 n) :
    rawPred mode n h s t0 t1 pre v =
      linearMapCheckCircuit (2 * paramJ n * paramL2 n) (2 * paramJ n * paramL2 n)
        (st2Mat (paramJ n) (paramL1 n) (paramL2 n) (paramOmegaExp n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V7 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV7 n ≤ v) (hhi : v < netV8 n) :
    rawPred mode n h s t0 t1 pre v =
      bilinearMapCheckCircuit (2 * paramJ n) (2 * paramJ n) (2 * paramJ n) (ringMulTensor (paramJ n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V8 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV8 n ≤ v) (hhi : v < netV9 n) :
    rawPred mode n h s t0 t1 pre v =
      linearMapCheckCircuit (2 * paramJ n * paramL1 n) (2 * paramJ n * paramL1 n)
        (fullSt1Mat (paramJ n) (paramL1 n) (paramL2 n) (paramInvOmegaExp n) (v - netV8 n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V9 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV9 n ≤ v) (hhi : v < netV10 n) :
    rawPred mode n h s t0 t1 pre v =
      linearMapCheckCircuit (2 * paramJ n * paramL2 n) (2 * paramJ n * paramL2 n)
        (st2Mat (paramJ n) (paramL1 n) (paramL2 n) (paramInvOmegaExp n)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V10 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV10 n ≤ v) (hhi : v < netV11 n) :
    rawPred mode n h s t0 t1 pre v =
      (let k := v - netV10 n
       constCircuit (if ovlTargetBit (paramJ n) (k / (2 * paramJ n)) (k % (2 * paramJ n)) < 2 * n
                     then 0 else 1) true) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V11 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV11 n ≤ v) (hhi : v < netV12 n) :
    rawPred mode n h s t0 t1 pre v =
      linearMapCheckCircuit (ovlInLocal (paramJ n) (paramL n) (v - netV11 n)).length 1 (fun _ _ => true) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V12 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV12 n ≤ v) (hhi : v < netV13 n) :
    rawPred mode n h s t0 t1 pre v =
      synCheckCircuit (if hlt : v - netV12 n < n then zmod2ToBool (s ⟨v - netV12 n, hlt⟩) else false) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V13_15 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV13 n ≤ v) (hhi : v < netV15 n) :
    rawPred mode n h s t0 t1 pre v = pinBitCircuit (some false) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  by_cases h14 : v < netV14 n
  · simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
               show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
               show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
               show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
               show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
               show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
               show ¬(v < netV13 n) by omega, h14, ↓reduceIte]
  · simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
               show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
               show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
               show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
               show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
               show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
               show ¬(v < netV13 n) by omega, h14, hhi, ↓reduceIte]

lemma rawPred_V15 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    {v j node u : ℕ} (hlo : netV15 n ≤ v) (hhi : v < netV16 n)
    (hdec : decodeTreeVert (treeLog n + 1) (v - netV15 n) = (j, node, u)) :
    rawPred mode n h s t0 t1 pre v =
      (let r := treeLog n + 1
       if u = 0 then pinBitCircuit (some false)
       else
         let b := u - 1
         if mode = 2 ∧ j = r then
           sepFullAdderCircuit (decide (t0 < 2 ^ r ∧ t1 < 2 ^ r)) (t0.testBit b) (t1.testBit b)
         else fullAdderCircuit) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, hhi, ↓reduceIte, hdec]

lemma rawPred_V16 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV16 n ≤ v) (hhi : v < netV17 n) :
    rawPred mode n h s t0 t1 pre v = pinBitCircuit (some false) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, show ¬(v < netV16 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V17 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV17 n ≤ v) (hhi : v < netV18 n) :
    rawPred mode n h s t0 t1 pre v =
      (let b := v - netV17 n
       let W := treeLog n + 2
       if mode = 0 then exactCmpStepCircuit (decide (t0 < 2 ^ W)) (t0.testBit b)
       else if mode = 1 then borrowStepCircuit (t0.testBit b)
       else sepCmpStepCircuit) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, show ¬(v < netV16 n) by omega,
             show ¬(v < netV17 n) by omega, hhi, ↓reduceIte]

lemma rawPred_V18 (mode n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool) {v : ℕ}
    (hlo : netV18 n ≤ v) :
    rawPred mode n h s t0 t1 pre v =
      (if mode = 1 ∧ ¬(t0 < 2 ^ (treeLog n + 2)) then constCircuit 1 true
       else pinBitCircuit (some false)) := by
  rcases netV_chain n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold rawPred; dsimp only
  simp only [show ¬(v < netV1 n) by omega, show ¬(v < netV2 n) by omega,
             show ¬(v < netV3 n) by omega, show ¬(v < netV4 n) by omega,
             show ¬(v < netV5 n) by omega, show ¬(v < netV6 n) by omega,
             show ¬(v < netV7 n) by omega, show ¬(v < netV8 n) by omega,
             show ¬(v < netV9 n) by omega, show ¬(v < netV10 n) by omega,
             show ¬(v < netV11 n) by omega, show ¬(v < netV12 n) by omega,
             show ¬(v < netV13 n) by omega, show ¬(v < netV14 n) by omega,
             show ¬(v < netV15 n) by omega, show ¬(v < netV16 n) by omega,
             show ¬(v < netV17 n) by omega, show ¬(v < netV18 n) by omega, ↓reduceIte]

/-- **Master 19-Block Stream Decomposition Theorem**. -/
theorem encodeAllVertices_eq_blocks (mode n : ℕ) (h s : Fin n → ZMod 2)
    (t0 t1 : ℕ) (pre : List Bool) :
    (List.range (netVertCount n)).flatMap
      (fun v => QCSD_encodeCircuit (rawPred mode n h s t0 t1 pre v)) =
    blockStream0 n pre ++
    blockStream1 n ++
    blockStream2 n h ++
    blockStream3 n ++
    blockStream4 n ++
    blockStream5 n ++
    blockStream6 n ++
    blockStream7 n ++
    blockStream8 n ++
    blockStream9 n ++
    blockStream10 n ++
    blockStream11 n ++
    blockStream12 n s ++
    blockStream13 n ++
    blockStream14 n ++
    blockStream15 mode n t0 t1 ++
    blockStream16 ++
    blockStream17 mode n t0 ++
    blockStream18 mode n t0 := by
  set F := fun v => QCSD_encodeCircuit (rawPred mode n h s t0 t1 pre v)
  rcases netV_chain n with
    ⟨_, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10,
     hv11, hv12, hv13, hv14, hv15, hv16, hv17, hv18⟩
  rw [range_sub_split_flatMap hv18 F,
      range_sub_split_flatMap hv17 F,
      range_sub_split_flatMap hv16 F,
      range_sub_split_flatMap hv15 F,
      range_sub_split_flatMap hv14 F,
      range_sub_split_flatMap hv13 F,
      range_sub_split_flatMap hv12 F,
      range_sub_split_flatMap hv11 F,
      range_sub_split_flatMap hv10 F,
      range_sub_split_flatMap hv9 F,
      range_sub_split_flatMap hv8 F,
      range_sub_split_flatMap hv7 F,
      range_sub_split_flatMap hv6 F,
      range_sub_split_flatMap hv5 F,
      range_sub_split_flatMap hv4 F,
      range_sub_split_flatMap hv3 F,
      range_sub_split_flatMap hv2 F,
      range_sub_split_flatMap hv1 F]
  have hb0 : (List.range (netV1 n)).flatMap F = blockStream0 n pre := by
    change (List.range (2 * n)).flatMap F = blockStream0 n pre
    unfold blockStream0
    refine List.flatMap_congr (fun v hv => ?_)
    have hvlt : v < netV1 n := List.mem_range.mp hv
    dsimp only [F]; rw [rawPred_V0 _ _ _ _ _ _ _ hvlt]
    by_cases hpre : v < pre.length
    · simp only [hpre, ↓reduceIte]
      cases pre.getD v false <;> rfl
    · simp only [hpre, ↓reduceIte]; rfl
  have hb1 : (List.range (netV2 n - netV1 n)).flatMap (fun i => F (netV1 n + i)) = blockStream1 n := by
    have hd : netV2 n - netV1 n = 2 * n := by simp [netV2, netV1]; omega
    rw [hd]; unfold blockStream1
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < 2 * n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V1 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV1, netV2]; omega), encodeCircuit_ecopy]
  have hb2 : (List.range (netV3 n - netV2 n)).flatMap (fun i => F (netV2 n + i)) = blockStream2 n h := by
    have hd : netV3 n - netV2 n = n := by simp [netV3, netV2]; omega
    rw [hd]; unfold blockStream2
    refine List.flatMap_congr (fun idx hi => ?_)
    have hilt : idx < n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V2 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV2, netV3]; omega)]
    simp only [Nat.add_sub_cancel_left, hilt, ↓reduceDIte]
    cases zmod2ToBool (h ⟨idx, hilt⟩) <;> rfl
  have hb3 : (List.range (netV4 n - netV3 n)).flatMap (fun i => F (netV3 n + i)) = blockStream3 n := by
    have hd : netV4 n - netV3 n = paramL2 n := by simp [netV4, netV3]
    rw [hd]; unfold blockStream3; dsimp only
    refine List.flatMap_congr (fun j2 hj2 => ?_)
    have hj2lt : j2 < paramL2 n := List.mem_range.mp hj2
    dsimp only [F]
    rw [rawPred_V3 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV3, netV4]; omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [fwdSt1Mat_circuit_eq_unified n (paramJ n) (paramL1 n) (paramL2 n) (paramOmegaExp n) j2
          (paramJ_pos n) hj2lt]
  have hb4 : (List.range (netV5 n - netV4 n)).flatMap (fun i => F (netV4 n + i)) = blockStream4 n := by
    have hd : netV5 n - netV4 n = paramL1 n := by simp [netV5, netV4]
    rw [hd]; unfold blockStream4; dsimp only
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < paramL1 n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V4 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV4, netV5]; omega),
        st2Mat_circuit_eq_unified]
  have hb5 : (List.range (netV6 n - netV5 n)).flatMap (fun i => F (netV5 n + i)) = blockStream5 n := by
    have hd : netV6 n - netV5 n = paramL2 n := by simp [netV6, netV5]; omega
    rw [hd]; unfold blockStream5 blockStream3; dsimp only
    refine List.flatMap_congr (fun j2 hj2 => ?_)
    have hj2lt : j2 < paramL2 n := List.mem_range.mp hj2
    dsimp only [F]
    rw [rawPred_V5 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV5, netV6]; omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [fwdSt1Mat_circuit_eq_unified n (paramJ n) (paramL1 n) (paramL2 n) (paramOmegaExp n) j2
          (paramJ_pos n) hj2lt]
  have hb6 : (List.range (netV7 n - netV6 n)).flatMap (fun i => F (netV6 n + i)) = blockStream6 n := by
    have hd : netV7 n - netV6 n = paramL1 n := by simp [netV7, netV6]; omega
    rw [hd]; unfold blockStream6 blockStream4; dsimp only
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < paramL1 n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V6 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV6, netV7]; omega),
        st2Mat_circuit_eq_unified]
  have hb7 : (List.range (netV8 n - netV7 n)).flatMap (fun i => F (netV7 n + i)) = blockStream7 n := by
    have hd : netV8 n - netV7 n = paramL n := by simp [netV8]
    rw [hd]; unfold blockStream7; dsimp only
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < paramL n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V7 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV8]; omega)]
  have hb8 : (List.range (netV9 n - netV8 n)).flatMap (fun i => F (netV8 n + i)) = blockStream8 n := by
    have hd : netV9 n - netV8 n = paramL2 n := by simp [netV9]
    rw [hd]; unfold blockStream8; dsimp only
    refine List.flatMap_congr (fun j2 hj2 => ?_)
    have hj2lt : j2 < paramL2 n := List.mem_range.mp hj2
    dsimp only [F]
    rw [rawPred_V8 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV9]; omega)]
    simp only [Nat.add_sub_cancel_left, fullSt1Mat_circuit_eq_unified]
  have hb9 : (List.range (netV10 n - netV9 n)).flatMap (fun i => F (netV9 n + i)) = blockStream9 n := by
    have hd : netV10 n - netV9 n = paramL1 n := by simp [netV10]
    rw [hd]; unfold blockStream9; dsimp only
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < paramL1 n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V9 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV10]; omega),
        st2Mat_circuit_eq_unified]
  have hb10 : (List.range (netV11 n - netV10 n)).flatMap (fun i => F (netV10 n + i)) = blockStream10 n := by
    have hd : netV11 n - netV10 n = paramL n * (2 * paramJ n) := by simp [netV11]; ring
    rw [hd, range_mul_eq_flatMap (paramL n) (2 * paramJ n), flatMap_flatMap_eq]
    unfold blockStream10; dsimp only
    have h2J : 0 < 2 * paramJ n := by have := paramJ_pos n; omega
    refine List.flatMap_congr (fun blk hblk => ?_)
    rw [List.flatMap_map]
    refine List.flatMap_congr (fun p hp => ?_)
    have hblt : blk < paramL n := List.mem_range.mp hblk
    have hplt : p < 2 * paramJ n := List.mem_range.mp hp
    set k := blk * (2 * paramJ n) + p
    have hklt : k < 2 * paramJ n * paramL n := by
      have h1 : (blk + 1) * (2 * paramJ n) ≤ paramL n * (2 * paramJ n) := Nat.mul_le_mul_right _ hblt
      have h2 : (blk + 1) * (2 * paramJ n) = blk * (2 * paramJ n) + 2 * paramJ n := by ring
      have h3 : paramL n * (2 * paramJ n) = 2 * paramJ n * paramL n := Nat.mul_comm _ _
      omega
    dsimp only [F]
    rw [rawPred_V10 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV11]; omega)]
    simp only [Nat.add_sub_cancel_left]
    have hk_div : k / (2 * paramJ n) = blk := by
      dsimp only [k]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ h2J, Nat.div_eq_of_lt hplt, Nat.zero_add]
    have hk_mod : k % (2 * paramJ n) = p := by
      dsimp only [k]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hplt]
    rw [hk_div, hk_mod, ovlTargetBit_eq]
    split_ifs <;> rfl
  have hb11 : (List.range (netV12 n - netV11 n)).flatMap (fun i => F (netV11 n + i)) = blockStream11 n := by
    have hd : netV12 n - netV11 n = 2 * n := by simp [netV12]
    rw [hd]; unfold blockStream11; dsimp only
    refine List.flatMap_congr (fun tk htk => ?_)
    have htklt : tk < 2 * n := List.mem_range.mp htk
    dsimp only [F]
    rw [rawPred_V11 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV12]; omega)]
    simp only [Nat.add_sub_cancel_left]
    unfold ovlInLocal
    by_cases hc1 : 0 < tk / paramJ n ∧ tk / paramJ n - 1 < paramL n <;>
    by_cases hc2 : tk / paramJ n < paramL n
    · simp only [hc1, hc2, and_self, ↓reduceIte, List.length_append, List.length_singleton]
      exact encodeCircuit_ovl2
    · simp only [hc1, hc2, and_self, ↓reduceIte, List.length_append, List.length_singleton, List.length_nil]
      exact encodeCircuit_ovl1
    · simp only [hc1, hc2, ↓reduceIte, List.length_append, List.length_singleton, List.length_nil]
      exact encodeCircuit_ovl1
    · simp only [hc1, hc2, ↓reduceIte, List.length_append, List.length_nil]
      exact encodeCircuit_ovl0
  have hb12 : (List.range (netV13 n - netV12 n)).flatMap (fun i => F (netV12 n + i)) = blockStream12 n s := by
    have hd : netV13 n - netV12 n = n := by simp [netV13]
    rw [hd]; unfold blockStream12
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V12 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV13]; omega)]
    simp only [Nat.add_sub_cancel_left, encodeCircuit_synCheckCircuit]
  have hb13 : (List.range (netV14 n - netV13 n)).flatMap (fun i => F (netV13 n + i)) = blockStream13 n := by
    have hd : netV14 n - netV13 n = treeM n - n := by simp [netV14]
    rw [hd]; unfold blockStream13
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < treeM n - n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V13_15 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV14, netV15]; omega)]
    rfl
  have hb14 : (List.range (netV15 n - netV14 n)).flatMap (fun i => F (netV14 n + i)) = blockStream14 n := by
    have hd : netV15 n - netV14 n = treeM n - n := by simp [netV15]
    rw [hd]; unfold blockStream14 blockStream13
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < treeM n - n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V13_15 _ _ _ _ _ _ _ (by omega) (by simp [netV15]; omega)]
    rfl
  have hb15 : (List.range (netV16 n - netV15 n)).flatMap (fun i => F (netV15 n + i)) =
      blockStream15 mode n t0 t1 := by
    have hd : netV16 n - netV15 n = treeVertOff (treeLog n + 1) ((treeLog n + 1) + 1) := by
      simp [netV16]
    rw [hd, range_treeVertOff_flatMap (treeLog n + 1) (fun i => F (netV15 n + i)) (treeLog n + 1)]
    unfold blockStream15; dsimp only
    refine List.flatMap_congr (fun j0 hj0 => ?_)
    have hj0lt : j0 < treeLog n + 1 := List.mem_range.mp hj0
    refine List.flatMap_congr (fun node hnode => ?_)
    have hnodelt : node < 2 ^ (treeLog n + 1 - (j0 + 1)) := List.mem_range.mp hnode
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    congr 1
    · set loc0 := treeVertOff (treeLog n + 1) (j0 + 1) + node * (j0 + 2) + 0
      have hloc0 : loc0 < treeVertOff (treeLog n + 1) (treeLog n + 2) :=
        encodeTreeVert_lt (by omega) (by omega) hnodelt (by omega)
      have hdec0 : decodeTreeVert (treeLog n + 1) loc0 = (j0 + 1, node, 0) :=
        decodeTreeVert_encode (by omega) (by omega) hnodelt (by omega)
      dsimp only [F]
      rw [rawPred_V15 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV16]; omega)
            (by simpa [Nat.add_sub_cancel_left] using hdec0)]
      rfl
    · refine List.flatMap_congr (fun b hb => ?_)
      have hblt : b < j0 + 1 := List.mem_range.mp hb
      set locB := treeVertOff (treeLog n + 1) (j0 + 1) + node * (j0 + 2) + (b + 1)
      have hlocB : locB < treeVertOff (treeLog n + 1) (treeLog n + 2) :=
        encodeTreeVert_lt (by omega) (by omega) hnodelt (by omega)
      have hdecB : decodeTreeVert (treeLog n + 1) locB = (j0 + 1, node, b + 1) :=
        decodeTreeVert_encode (by omega) (by omega) hnodelt (by omega)
      dsimp only [F]
      rw [rawPred_V15 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV16]; omega)
            (by simpa [Nat.add_sub_cancel_left] using hdecB)]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      split_ifs
      · exact encodeCircuit_sepFullAdderCircuit _ _ _
      · exact encodeCircuit_fullAdderCircuit
  have hb16 : (List.range (netV17 n - netV16 n)).flatMap (fun i => F (netV16 n + i)) = blockStream16 := by
    have hd : netV17 n - netV16 n = 1 := by simp [netV17]
    rw [hd]; simp only [List.range_one, List.flatMap_singleton, Nat.add_zero]
    dsimp only [F]; rw [rawPred_V16 _ _ _ _ _ _ _ le_rfl (by simp [netV17])]; rfl
  have hb17 : (List.range (netV18 n - netV17 n)).flatMap (fun i => F (netV17 n + i)) =
      blockStream17 mode n t0 := by
    have hd : netV18 n - netV17 n = treeLog n + 2 := by simp [netV18]
    rw [hd]; unfold blockStream17; dsimp only
    refine List.flatMap_congr (fun b hb => ?_)
    have hblt : b < treeLog n + 2 := List.mem_range.mp hb
    dsimp only [F]
    rw [rawPred_V17 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV18]; omega)]
    simp only [Nat.add_sub_cancel_left]
    split_ifs
    · exact encodeCircuit_exactCmpStepCircuit _ _
    · exact encodeCircuit_borrowStepCircuit _
    · exact encodeCircuit_sepCmpStepCircuit
  have hb18 : (List.range (netVertCount n - netV18 n)).flatMap (fun i => F (netV18 n + i)) =
      blockStream18 mode n t0 := by
    have hd : netVertCount n - netV18 n = 1 := by simp [netVertCount]
    rw [hd]; simp only [List.range_one, List.flatMap_singleton, Nat.add_zero]
    dsimp only [F]; rw [rawPred_V18 _ _ _ _ _ _ _ le_rfl]
    unfold blockStream18; dsimp only
    split_ifs <;> rfl
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10,
      hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18]

/-!
## Section 3: Compositional `RMBlock` Combinators, Register Tiers, and Circuit Gadgets
-/

/-- Compositional register-machine block `(program, entryState)`. -/
abbrev RMBlock (R : ℕ) (Q : Type) : Type := RMProg R Q × Q

/-- Halting execution specification for an `RMBlock`, abstracting away internal exit state `q₁`. -/
def RMBlockExec {R : ℕ} {Q : Type} (B : RMBlock R Q) (Vmax : ℕ) (inp : List Bool)
    (reg₀ reg₁ : RegState R) (emitted : List Bool) (steps : ℕ) : Prop :=
  ∃ q₁ : Q, RMExec B.1 Vmax inp B.2 reg₀ q₁ reg₁ emitted steps

lemma RMBlockExec.weaken {R : ℕ} {Q : Type} {B : RMBlock R Q} {V₁ V₂ : ℕ} {inp : List Bool}
    {reg₀ reg₁ : RegState R} {out : List Bool} {T₁ T₂ : ℕ}
    (h : RMBlockExec B V₁ inp reg₀ reg₁ out T₁) (hV : V₁ ≤ V₂) (hT : T₁ ≤ T₂) :
    RMBlockExec B V₂ inp reg₀ reg₁ out T₂ := by
  rcases h with ⟨q₁, he⟩
  exact ⟨q₁, he.weaken hV hT⟩

lemma RMBlockExec.congr_out_steps {R : ℕ} {Q : Type} {B : RMBlock R Q}
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ : RegState R} {out₁ out₂ : List Bool} {T₁ T₂ : ℕ}
    (h : RMBlockExec B V inp reg₀ reg₁ out₁ T₁) (hout : out₁ = out₂) (hT : T₁ ≤ T₂) :
    RMBlockExec B V inp reg₀ reg₁ out₂ T₂ := by
  subst hout; exact h.weaken le_rfl hT

lemma RMBlockExec.reg₀_le {R : ℕ} {Q : Type} {B : RMBlock R Q} {V : ℕ} {inp : List Bool}
    {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (h : RMBlockExec B V inp reg₀ reg₁ out T) : ∀ i, reg₀ i ≤ V := by
  rcases h with ⟨_, he⟩
  exact he.reg₀_le

lemma RMBlockExec.reg₁_le {R : ℕ} {Q : Type} {B : RMBlock R Q} {V : ℕ} {inp : List Bool}
    {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (h : RMBlockExec B V inp reg₀ reg₁ out T) : ∀ i, reg₁ i ≤ V := by
  rcases h with ⟨_, he⟩
  exact he.reg₁_le

def blkSeq {R : ℕ} {Q₁ Q₂ : Type} (B₁ : RMBlock R Q₁) (B₂ : RMBlock R Q₂) :
    RMBlock R (Q₁ ⊕ Q₂) :=
  (rmChain B₁.1 B₂.1 B₂.2, rmChainEntry B₁.1 B₁.2 B₂.2)

infixr:60 " ;; " => blkSeq

theorem blkSeq_spec {R : ℕ} {Q₁ Q₂ : Type}
    {B₁ : RMBlock R Q₁} {B₂ : RMBlock R Q₂}
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ reg₂ : RegState R}
    {out₁ out₂ : List Bool} {T₁ T₂ : ℕ}
    (h₁ : RMBlockExec B₁ V inp reg₀ reg₁ out₁ T₁)
    (h₂ : RMBlockExec B₂ V inp reg₁ reg₂ out₂ T₂) :
    RMBlockExec (B₁ ;; B₂) V inp reg₀ reg₂ (out₁ ++ out₂) (T₁ + T₂) := by
  rcases h₁ with ⟨q₁, e₁⟩
  rcases h₂ with ⟨q₂, e₂⟩
  refine ⟨Sum.inr q₂, ?_⟩
  dsimp only [blkSeq]
  simpa [max_self] using rmChain_spec e₁ e₂

theorem blkSeq_nil_left {R : ℕ} {Q₁ Q₂ : Type}
    {B₁ : RMBlock R Q₁} {B₂ : RMBlock R Q₂}
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ reg₂ : RegState R}
    {out₂ : List Bool} {T₁ T₂ : ℕ}
    (h₁ : RMBlockExec B₁ V inp reg₀ reg₁ [] T₁)
    (h₂ : RMBlockExec B₂ V inp reg₁ reg₂ out₂ T₂) :
    RMBlockExec (B₁ ;; B₂) V inp reg₀ reg₂ out₂ (T₁ + T₂) := by
  simpa using blkSeq_spec h₁ h₂

theorem blkSeq_nil_right {R : ℕ} {Q₁ Q₂ : Type}
    {B₁ : RMBlock R Q₁} {B₂ : RMBlock R Q₂}
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ reg₂ : RegState R}
    {out₁ : List Bool} {T₁ T₂ : ℕ}
    (h₁ : RMBlockExec B₁ V inp reg₀ reg₁ out₁ T₁)
    (h₂ : RMBlockExec B₂ V inp reg₁ reg₂ [] T₂) :
    RMBlockExec (B₁ ;; B₂) V inp reg₀ reg₂ out₁ (T₁ + T₂) := by
  simpa using blkSeq_spec h₁ h₂

def blkIfZero {R : ℕ} {Qz Qnz : Type} (r : Fin R)
    (Bz : RMBlock R Qz) (Bnz : RMBlock R Qnz) :
    RMBlock R (Option Bool ⊕ (Qz ⊕ (Bool ⊕ Qnz))) :=
  (rmIfZero r Bz.1 Bnz.1 Bz.2 Bnz.2, rmIfZeroEntry)

theorem blkIfZero_zero_spec {R : ℕ} {Qz Qnz : Type} (r : Fin R)
    {Bz : RMBlock R Qz} (Bnz : RMBlock R Qnz)
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (hr : reg₀ r = 0)
    (hz : RMBlockExec Bz V inp reg₀ reg₁ out T) :
    RMBlockExec (blkIfZero r Bz Bnz) V inp reg₀ reg₁ out (2 + T) := by
  rcases hz with ⟨qz₁, ez⟩
  exact ⟨_, rmIfZero_zero_spec r Bnz.1 Bnz.2 hr ez⟩

theorem blkIfZero_pos_spec {R : ℕ} {Qz Qnz : Type} (r : Fin R)
    (Bz : RMBlock R Qz) {Bnz : RMBlock R Qnz}
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (hr : reg₀ r ≠ 0)
    (hnz : RMBlockExec Bnz V inp reg₀ reg₁ out T) :
    RMBlockExec (blkIfZero r Bz Bnz) V inp reg₀ reg₁ out (2 + T) := by
  rcases hnz with ⟨qnz₁, enz⟩
  exact ⟨_, rmIfZero_pos_spec r Bz.1 Bz.2 hr enz⟩

def blkIfReadIn {R : ℕ} {Qf Qt : Type} (rIdx : Fin R)
    (Bf : RMBlock R Qf) (Bt : RMBlock R Qt) :
    RMBlock R (Option Bool ⊕ (Qf ⊕ Qt)) :=
  (rmIfReadIn rIdx Bf.1 Bt.1 Bf.2 Bt.2, rmIfReadInEntry)

theorem blkIfReadIn_false_spec {R : ℕ} {Qf Qt : Type} (rIdx : Fin R)
    {Bf : RMBlock R Qf} (Bt : RMBlock R Qt)
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (hb : inp.getD (reg₀ rIdx) false = false)
    (hf : RMBlockExec Bf V inp reg₀ reg₁ out T) :
    RMBlockExec (blkIfReadIn rIdx Bf Bt) V inp reg₀ reg₁ out (1 + T) := by
  rcases hf with ⟨qf₁, ef⟩
  exact ⟨_, rmIfReadIn_false_spec rIdx Bt.1 Bt.2 hb ef⟩

theorem blkIfReadIn_true_spec {R : ℕ} {Qf Qt : Type} (rIdx : Fin R)
    (Bf : RMBlock R Qf) {Bt : RMBlock R Qt}
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (hb : inp.getD (reg₀ rIdx) false = true)
    (ht : RMBlockExec Bt V inp reg₀ reg₁ out T) :
    RMBlockExec (blkIfReadIn rIdx Bf Bt) V inp reg₀ reg₁ out (1 + T) := by
  rcases ht with ⟨qt₁, et⟩
  exact ⟨_, rmIfReadIn_true_spec rIdx Bf.1 Bf.2 hb et⟩

def blkForRange {R : ℕ} {Q : Type} (rIdx rRem rCount : Fin R) (body : RMBlock R Q) :
    RMBlock R (RMForRangeQ Q) :=
  (rmForRange rIdx rRem rCount body.1 body.2, rmForRangeEntry)

theorem blkForRange_spec {R : ℕ} {Q : Type} (rIdx rRem rCount : Fin R)
    (hir : rIdx ≠ rRem) (hic : rIdx ≠ rCount)
    (body : RMBlock R Q) (V T_step : ℕ) (inp : List Bool) (reg₀ : RegState R)
    (Inv : ℕ → RegState R → Prop) (emitFn : ℕ → List Bool)
    (hreg₀ : ∀ j, reg₀ j ≤ V)
    (hInv_init : Inv 0 (regUpd (regUpd reg₀ rIdx 0) rRem (reg₀ rCount)))
    (hInv_le : ∀ i reg, Inv i reg → ∀ j, reg j ≤ V)
    (hInv_idx : ∀ i reg, Inv i reg → reg rIdx = i)
    (hInv_rem : ∀ i reg v, v ≤ V → Inv i reg → Inv i (regUpd reg rRem v))
    (hstep_spec : ∀ i reg, i < reg₀ rCount → Inv i reg →
      ∃ reg₁,
        reg₁ rIdx = i ∧
        reg₁ rRem = reg rRem ∧
        Inv (i + 1) (regUpd reg₁ rIdx (i + 1)) ∧
        RMBlockExec body V inp reg reg₁ (emitFn i) T_step) :
    ∃ reg_end : RegState R,
      reg_end rIdx = reg₀ rCount ∧
      reg_end rRem = 0 ∧
      Inv (reg₀ rCount) reg_end ∧
      RMBlockExec (blkForRange rIdx rRem rCount body) V inp reg₀ reg_end
        ((List.range (reg₀ rCount)).flatMap emitFn)
        (reg₀ rCount * (T_step + 2) + 3) := by
  rcases rmForRange_spec rIdx rRem rCount hir hic body.1 body.2 V T_step inp reg₀ Inv emitFn
      hreg₀ hInv_init hInv_le hInv_idx hInv_rem
      (fun i reg hi hI => by
        rcases hstep_spec i reg hi hI with ⟨reg₁, h1, h2, h3, q₁, hex⟩
        exact ⟨q₁, reg₁, h1, h2, h3, hex⟩)
    with ⟨reg_end, he1, he2, he3, hexec⟩
  exact ⟨reg_end, he1, he2, he3, rmForRangeExit, hexec⟩

theorem blkForRange_frame_spec {R : ℕ} {Q : Type} (rIdx rRem rCount : Fin R)
    (hir : rIdx ≠ rRem) (hic : rIdx ≠ rCount)
    (keep : Fin R → Prop) (hk_idx : ¬ keep rIdx) (hk_rem : ¬ keep rRem)
    (body : RMBlock R Q) (V T_step : ℕ) (inp : List Bool) (reg₀ : RegState R)
    (emitFn : ℕ → List Bool)
    (hreg₀ : ∀ j, reg₀ j ≤ V)
    (hbody : ∀ i reg, i < reg₀ rCount →
      reg rIdx = i → (∀ j, reg j ≤ V) → (∀ r, keep r → reg r = reg₀ r) →
      ∃ reg₁,
        reg₁ rIdx = i ∧
        reg₁ rRem = reg rRem ∧
        (∀ r, keep r → reg₁ r = reg₀ r) ∧
        RMBlockExec body V inp reg reg₁ (emitFn i) T_step) :
    ∃ reg_end : RegState R,
      (∀ r, keep r → reg_end r = reg₀ r) ∧
      RMBlockExec (blkForRange rIdx rRem rCount body) V inp reg₀ reg_end
        ((List.range (reg₀ rCount)).flatMap emitFn)
        (reg₀ rCount * (T_step + 2) + 3) := by
  have hne_rem : ∀ r, keep r → r ≠ rRem := fun r hkr heq => by subst heq; exact hk_rem hkr
  have hne_idx : ∀ r, keep r → r ≠ rIdx := fun r hkr heq => by subst heq; exact hk_idx hkr
  set Inv : ℕ → RegState R → Prop := fun i reg =>
    reg rIdx = i ∧ (∀ j, reg j ≤ V) ∧ (∀ r, keep r → reg r = reg₀ r)
  rcases blkForRange_spec rIdx rRem rCount hir hic body V T_step inp reg₀ Inv emitFn
      hreg₀
      ⟨by rw [regUpd_ne _ hir, regUpd_self],
       regUpd_le (regUpd_le hreg₀ rIdx (Nat.zero_le V)) rRem (hreg₀ rCount),
       fun r hkr => by rw [regUpd_ne _ (hne_rem r hkr), regUpd_ne _ (hne_idx r hkr)]⟩
      (fun _ _ hI => hI.2.1)
      (fun _ _ hI => hI.1)
      (fun i reg v hv hI =>
        ⟨by rw [regUpd_ne _ hir, hI.1],
         regUpd_le hI.2.1 rRem hv,
         fun r hkr => by rw [regUpd_ne _ (hne_rem r hkr), hI.2.2 r hkr]⟩)
      (fun i reg hi hI => by
        have hcV : reg₀ rCount ≤ V := hreg₀ rCount
        rcases hbody i reg hi hI.1 hI.2.1 hI.2.2 with ⟨reg₁, h1, h2, h3, hex⟩
        refine ⟨reg₁, h1, h2, ?_, hex⟩
        exact ⟨regUpd_self _ _ _,
               regUpd_le hex.reg₁_le rIdx (by omega),
               fun r hkr => by rw [regUpd_ne _ (hne_idx r hkr), h3 r hkr]⟩)
    with ⟨reg_end, _, _, hInv_end, hex_end⟩
  exact ⟨reg_end, hInv_end.2.2, hex_end⟩

def blkLift {R₁ R₂ : ℕ} {Q : Type} (g : Fin R₁ → Fin R₂) (B : RMBlock R₁ Q) :
    RMBlock R₂ Q :=
  (rmLift g B.1, B.2)

theorem blkLift_spec {R₁ R₂ : ℕ} {Q : Type} (g : Fin R₁ → Fin R₂) (hg : Function.Injective g)
    (B : RMBlock R₁ Q) (V : ℕ) (inp : List Bool)
    (reg₀ : RegState R₂) (reg₁' : RegState R₁) (out : List Bool) (T : ℕ)
    (hbound : ∀ i : Fin R₂, (∀ j : Fin R₁, g j ≠ i) → reg₀ i ≤ V)
    (hexec : RMBlockExec B V inp (fun j => reg₀ (g j)) reg₁' out T) :
    ∃ reg₁ : RegState R₂,
      (∀ j : Fin R₁, reg₁ (g j) = reg₁' j) ∧
      (∀ i : Fin R₂, (∀ j : Fin R₁, g j ≠ i) → reg₁ i = reg₀ i) ∧
      RMBlockExec (blkLift g B) V inp reg₀ reg₁ out T := by
  rcases hexec with ⟨q₁, he⟩
  rcases rmLift_spec g hg B.1 V V inp B.2 q₁ reg₀ reg₁' out T hbound he
    with ⟨reg₁, ha, hf, hl⟩
  refine ⟨reg₁, ha, hf, q₁, ?_⟩
  dsimp only [blkLift]
  simpa [max_self] using hl

/-! ### Opaque-State Atomic & Arithmetic `RMBlock` Wrappers (Zero `regUpd` Unfolding!) -/

def blkNop {R : ℕ} : RMBlock R Unit := (rmNop, ())
def blkZero {R : ℕ} (r : Fin R) : RMBlock R Bool := (rmZero r, false)
def blkInc {R : ℕ} (r : Fin R) : RMBlock R Bool := (rmInc r, false)
def blkDec1 {R : ℕ} (r : Fin R) : RMBlock R Bool := (rmDec1 r, false)
def blkCopy {R : ℕ} (dst src : Fin R) : RMBlock R Bool := (rmCopy dst src, false)
def blkAddConst {R : ℕ} (r : Fin R) (c : ℕ) : RMBlock R (Fin (c + 1)) :=
  (rmAddConst r c, ⟨0, by omega⟩)
def blkSetConst {R : ℕ} (r : Fin R) (c : ℕ) : RMBlock R (RMSetConstQ c) :=
  (rmSetConst r c, rmSetConstEntry)
def blkAdd {R : ℕ} (dst src tmp : Fin R) : RMBlock R RMAddQ :=
  (rmAdd dst src tmp, rmAddEntry)
def blkSub {R : ℕ} (dst src tmp : Fin R) : RMBlock R RMSubQ :=
  (rmSub dst src tmp, rmSubEntry)
def blkCmpLt {R : ℕ} (flag a b tA tB : Fin R) : RMBlock R (Fin 8) :=
  (rmCmpLt flag a b tA tB, 0)
def blkMul {R : ℕ} (dst a b t1 t2 : Fin R) : RMBlock R RMMulQ :=
  (rmMul dst a b t1 t2, rmMulEntry)
def blkDivMod {R : ℕ} (qOut rOut a b flag tA tB : Fin R) : RMBlock R RMDivModQ :=
  (rmDivMod qOut rOut a b flag tA tB, rmDivModEntry)
def blkPow {R : ℕ} (dst base exp tE tP t1 t2 : Fin R) : RMBlock R RMPowQ :=
  (rmPow dst base exp tE tP t1 t2, rmPowEntry)
def blkMinPow {R : ℕ} (dst base target powReg flag tP t1 t2 : Fin R) : RMBlock R RMMinPowExpQ :=
  (rmMinPowExp dst base target powReg flag tP t1 t2, rmMinPowExpEntry)
def blkEmitBits {R : ℕ} (bs : List Bool) : RMBlock R (Fin (bs.length + 1)) :=
  (rmEmitBits bs, ⟨0, by omega⟩)
def blkEmitBits3 {R : ℕ} (b0 b1 b2 : Bool) : RMBlock R (Fin 4) :=
  (rmEmitBits3 b0 b1 b2, 0)
def blkEmitUnary {R : ℕ} (r tmp : Fin R) : RMBlock R RMEmitUnaryQ :=
  (rmEmitUnary r tmp, rmEmitUnaryEntry)

theorem blkNop_spec {R : ℕ} (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V) :
    RMBlockExec blkNop V inp reg reg [] 0 :=
  ⟨(), rmNop_spec V inp reg hreg⟩

theorem blkZero_clean {R : ℕ} (r : Fin R) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ r = 0 ∧
      (∀ i, i ≠ r → reg₁ i = reg i) ∧
      RMBlockExec (blkZero r) V inp reg reg₁ [] 1 :=
  ⟨regUpd reg r 0, regUpd_self _ _ _, fun _ hi => regUpd_ne reg hi 0, true, rmZero_spec r V inp reg hreg⟩

theorem blkInc_clean {R : ℕ} (r : Fin R) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) (hle : reg r + 1 ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ r = reg r + 1 ∧
      (∀ i, i ≠ r → reg₁ i = reg i) ∧
      RMBlockExec (blkInc r) V inp reg reg₁ [] 1 :=
  ⟨regUpd reg r (reg r + 1), regUpd_self _ _ _, fun _ hi => regUpd_ne reg hi _,
   true, rmInc_spec r V inp reg hreg hle⟩

theorem blkDec1_clean {R : ℕ} (r : Fin R) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ r = reg r - 1 ∧
      (∀ i, i ≠ r → reg₁ i = reg i) ∧
      RMBlockExec (blkDec1 r) V inp reg reg₁ [] 1 :=
  ⟨regUpd reg r (reg r - 1), regUpd_self _ _ _, fun _ hi => regUpd_ne reg hi _,
   true, rmDec1_spec r V inp reg hreg⟩

theorem blkCopy_clean {R : ℕ} (dst src : Fin R) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ dst = reg src ∧
      (∀ i, i ≠ dst → reg₁ i = reg i) ∧
      RMBlockExec (blkCopy dst src) V inp reg reg₁ [] 1 :=
  ⟨regUpd reg dst (reg src), regUpd_self _ _ _, fun _ hi => regUpd_ne reg hi _,
   true, rmCopy_spec dst src V inp reg hreg⟩

theorem blkAddConst_clean {R : ℕ} (r : Fin R) (c V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) (hle : reg r + c ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ r = reg r + c ∧
      (∀ i, i ≠ r → reg₁ i = reg i) ∧
      RMBlockExec (blkAddConst r c) V inp reg reg₁ [] c :=
  ⟨regUpd reg r (reg r + c), regUpd_self _ _ _, fun _ hi => regUpd_ne reg hi _,
   ⟨c, by omega⟩, rmAddConst_spec r c V inp reg hreg hle⟩

theorem blkSetConst_clean {R : ℕ} (r : Fin R) (c V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) (hc : c ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ r = c ∧
      (∀ i, i ≠ r → reg₁ i = reg i) ∧
      RMBlockExec (blkSetConst r c) V inp reg reg₁ [] (1 + c) :=
  ⟨regUpd reg r c, regUpd_self _ _ _, fun _ hi => regUpd_ne reg hi _,
   rmSetConstExit, rmSetConst_spec r c V inp reg hreg hc⟩

theorem blkAdd_clean {R : ℕ} (dst src tmp : Fin R) (hdt : dst ≠ tmp) (hst : src ≠ tmp)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V)
    (hle : reg dst + reg src ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ dst = reg dst + reg src ∧
      (∀ i, i ≠ dst → i ≠ tmp → reg₁ i = reg i) ∧
      RMBlockExec (blkAdd dst src tmp) V inp reg reg₁ [] (2 * V + 2) := by
  have hs := hreg src
  refine ⟨regUpd (regUpd reg dst (reg dst + reg src)) tmp 0,
    by rw [regUpd_ne _ hdt, regUpd_self],
    fun i hid hit => by rw [regUpd_ne _ hit, regUpd_ne _ hid],
    rmAddExit, (rmAdd_spec dst src tmp hdt hst V inp reg hreg hle).weaken le_rfl (by omega)⟩

theorem blkSub_clean {R : ℕ} (dst src tmp : Fin R) (hdt : dst ≠ tmp)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ dst = reg dst - reg src ∧
      (∀ i, i ≠ dst → i ≠ tmp → reg₁ i = reg i) ∧
      RMBlockExec (blkSub dst src tmp) V inp reg reg₁ [] (2 * V + 2) := by
  have hs := hreg src
  refine ⟨regUpd (regUpd reg dst (reg dst - reg src)) tmp 0,
    by rw [regUpd_ne _ hdt, regUpd_self],
    fun i hid hit => by rw [regUpd_ne _ hit, regUpd_ne _ hid],
    rmSubExit, (rmSub_spec dst src tmp hdt V inp reg hreg).weaken le_rfl (by omega)⟩

theorem blkCmpLt_clean {R : ℕ} (flag a b tA tB : Fin R)
    (hAB : tA ≠ tB) (hfA : flag ≠ tA) (hfB : flag ≠ tB) (hbA : b ≠ tA)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V) (h1 : 1 ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ flag = (if reg a < reg b then 1 else 0) ∧
      (∀ i, i ≠ flag → i ≠ tA → i ≠ tB → reg₁ i = reg i) ∧
      RMBlockExec (blkCmpLt flag a b tA tB) V inp reg reg₁ [] (2 * V + 6) := by
  rcases rmCmpLt_spec flag a b tA tB hAB hfA hfB hbA V inp reg hreg h1
    with ⟨reg₁, hf, hfr, hex⟩
  have hm : min (reg a) (reg b) ≤ V := le_trans (Nat.min_le_left _ _) (hreg a)
  exact ⟨reg₁, hf, hfr, 7, hex.weaken le_rfl (by omega)⟩

theorem blkMul_clean {R : ℕ} (dst a b t1 t2 : Fin R)
    (hda : dst ≠ a) (hdb : dst ≠ b) (hdt1 : dst ≠ t1) (hdt2 : dst ≠ t2)
    (hbt1 : b ≠ t1) (hbt2 : b ≠ t2) (ht12 : t1 ≠ t2)
    (B V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) (haB : reg a ≤ B) (hbB : reg b ≤ B) (hle : reg a * reg b ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ dst = reg a * reg b ∧
      (∀ i, i ≠ dst → i ≠ t1 → i ≠ t2 → reg₁ i = reg i) ∧
      RMBlockExec (blkMul dst a b t1 t2) V inp reg reg₁ [] (B * (2 * B + 3) + 3) := by
  rcases rmMul_spec dst a b t1 t2 hda hdb hdt1 hdt2 hbt1 hbt2 ht12 V inp reg hreg hle
    with ⟨reg₁, hd, hfr, hex⟩
  have hT : reg a * (2 * reg b + 3) + 3 ≤ B * (2 * B + 3) + 3 := by
    have hm : reg a * (2 * reg b + 3) ≤ B * (2 * B + 3) := Nat.mul_le_mul haB (by omega)
    omega
  exact ⟨reg₁, hd, hfr, rmMulExit, hex.weaken le_rfl hT⟩

theorem blkDivMod_clean {R : ℕ} (qOut rOut a b flag tA tB : Fin R)
    (hqr : qOut ≠ rOut) (hqa : qOut ≠ a) (hqb : qOut ≠ b) (hqf : qOut ≠ flag)
    (hqA : qOut ≠ tA) (hqB : qOut ≠ tB)
    (hrb : rOut ≠ b) (hrf : rOut ≠ flag) (hrA : rOut ≠ tA) (hrB : rOut ≠ tB)
    (hbf : b ≠ flag) (hbA : b ≠ tA) (hbB : b ≠ tB)
    (hfA : flag ≠ tA) (hfB : flag ≠ tB) (hAB : tA ≠ tB)
    (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hbpos : 0 < reg b) (hreg : ∀ i, reg i ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ qOut = reg a / reg b ∧
      reg₁ rOut = reg a % reg b ∧
      (∀ i, i ≠ qOut → i ≠ rOut → i ≠ flag → i ≠ tA → i ≠ tB → reg₁ i = reg i) ∧
      RMBlockExec (blkDivMod qOut rOut a b flag tA tB) V inp reg reg₁ [] (17 * V + 10) := by
  have hbV : reg b ≤ V := hreg b
  have haV : reg a ≤ V := hreg a
  rcases rmDivMod_spec qOut rOut a b flag tA tB hqr hqa hqb hqf hqA hqB hrb hrf hrA hrB
      hbf hbA hbB hfA hfB hAB V inp reg hbpos hreg (by omega)
    with ⟨reg₁, hq, hr, hfr, hex⟩
  exact ⟨reg₁, hq, hr, hfr, rmDivModExit, hex.weaken le_rfl (by omega)⟩

theorem blkPow_clean {R : ℕ} (dst base exp tE tP t1 t2 : Fin R)
    (hdb : dst ≠ base) (hde : dst ≠ exp) (hdE : dst ≠ tE) (hdP : dst ≠ tP)
    (hd1 : dst ≠ t1) (hd2 : dst ≠ t2)
    (hbE : base ≠ tE) (hbP : base ≠ tP) (hb1 : base ≠ t1) (hb2 : base ≠ t2)
    (hEP : tE ≠ tP) (hE1 : tE ≠ t1) (hE2 : tE ≠ t2)
    (hP1 : tP ≠ t1) (hP2 : tP ≠ t2) (h12 : t1 ≠ t2)
    (E B V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) (h1 : 1 ≤ V) (heE : reg exp ≤ E) (hbB : reg base ≤ B)
    (hpow : reg base ^ reg exp ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ dst = reg base ^ reg exp ∧
      (∀ i, i ≠ dst → i ≠ tE → i ≠ tP → i ≠ t1 → i ≠ t2 → reg₁ i = reg i) ∧
      RMBlockExec (blkPow dst base exp tE tP t1 t2) V inp reg reg₁ []
        (E * (V * (2 * B + 3) + 5) + 4) := by
  rcases rmPow_spec dst base exp tE tP t1 t2 hdb hde hdE hdP hd1 hd2 hbE hbP hb1 hb2
      hEP hE1 hE2 hP1 hP2 h12 V inp reg hreg h1 hpow
    with ⟨reg₁, hd, hfr, hex⟩
  have hT : reg exp * (V * (2 * reg base + 3) + 5) + 4 ≤ E * (V * (2 * B + 3) + 5) + 4 := by
    have hm1 : V * (2 * reg base + 3) ≤ V * (2 * B + 3) := Nat.mul_le_mul_left V (by omega)
    have hm2 : reg exp * (V * (2 * reg base + 3) + 5) ≤ E * (V * (2 * B + 3) + 5) :=
      Nat.mul_le_mul heE (by omega)
    omega
  exact ⟨reg₁, hd, hfr, rmPowExit, hex.weaken le_rfl hT⟩

theorem blkEmitBits_spec {R : ℕ} (bs : List Bool) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    RMBlockExec (blkEmitBits bs) V inp reg reg bs bs.length :=
  ⟨⟨bs.length, by omega⟩, rmEmitBits_spec bs V inp reg hreg⟩

theorem blkEmitBits3_spec {R : ℕ} (b0 b1 b2 : Bool) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    RMBlockExec (blkEmitBits3 b0 b1 b2) V inp reg reg [b0, b1, b2] 3 :=
  ⟨3, rmEmitBits3_spec b0 b1 b2 V inp reg hreg⟩

theorem blkEmitUnary_clean {R : ℕ} (r tmp : Fin R) (hrt : r ≠ tmp)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V) :
    ∃ reg₁ : RegState R,
      (∀ i, i ≠ tmp → reg₁ i = reg i) ∧
      RMBlockExec (blkEmitUnary r tmp) V inp reg reg₁ (QCSD_natToUnary (reg r)) (2 * V + 3) := by
  have hrV : reg r ≤ V := hreg r
  exact ⟨regUpd reg tmp 0, fun _ hi => regUpd_ne reg hi 0,
    rmEmitUnaryExit, (rmEmitUnary_spec r tmp hrt V inp reg hreg).weaken le_rfl (by omega)⟩

/-! ### Tiered 42-Register Architecture (`R_emit = 42`) -/

abbrev R_emit : ℕ := 42

-- Tier 0 (0..14): Read-Only Input & Network Parameter Registers
def rN       : Fin R_emit := 0
def rHOff    : Fin R_emit := 1
def rSOff    : Fin R_emit := 2
def rPreOff  : Fin R_emit := 3
def rPreLen  : Fin R_emit := 4
def rT0      : Fin R_emit := 5
def rT1      : Fin R_emit := 6
def rJ       : Fin R_emit := 7
def rL       : Fin R_emit := 8
def rL1      : Fin R_emit := 9
def rL2      : Fin R_emit := 10
def rWExp    : Fin R_emit := 11
def rInvWExp : Fin R_emit := 12
def rTreeLog : Fin R_emit := 13
def rTreeM   : Fin R_emit := 14

-- Tier 1 (15..19): Outer Vertex-Block Loop Registers
def rBlkCnt  : Fin R_emit := 15
def rBlkIdx  : Fin R_emit := 16
def rBlkRem  : Fin R_emit := 17
def rBlkAux1 : Fin R_emit := 18
def rBlkAux2 : Fin R_emit := 19

-- Tier 2 (20..30): Circuit-Level & Parity-Matrix Loop Registers
def rNumIn    : Fin R_emit := 20
def rNumOut   : Fin R_emit := 21
def rTotalIn  : Fin R_emit := 22
def rPairBase : Fin R_emit := 23
def rMatCols  : Fin R_emit := 24
def rAllBase  : Fin R_emit := 25
def rCurWire  : Fin R_emit := 26
def rRowJ     : Fin R_emit := 27
def rRowRem   : Fin R_emit := 28
def rColK     : Fin R_emit := 29
def rColRem   : Fin R_emit := 30

-- Tier 3 (31..34): Matrix Entry & Wire Operand Registers
def rMatHit  : Fin R_emit := 31
def rWArg1   : Fin R_emit := 32
def rWArg2   : Fin R_emit := 33
def rThreeJ  : Fin R_emit := 34

-- Tier 4 (35..41): Leaf Arithmetic / Gadget Scratch Registers
def s0 : Fin R_emit := 35
def s1 : Fin R_emit := 36
def s2 : Fin R_emit := 37
def s3 : Fin R_emit := 38
def s4 : Fin R_emit := 39
def s5 : Fin R_emit := 40
def s6 : Fin R_emit := 41

lemma ne_of_lt_val {R : ℕ} {i r : Fin R} (h : i.val < r.val) : i ≠ r := by
  intro heq; subst heq; omega

/-! ### Multi-Gate Gadget Blocks (`blkEmitXorAt`, `blkEmitEqAt`, `blkEqTest`, `blkCoeffPowY`) -/

def blkEmitXorHalf1 (rO rA rB : Fin R_emit) :=
  blkEmitBits3 false true true ;;
  blkEmitUnary rB s1 ;;
  blkEmitBits3 true false false ;;
  blkEmitUnary rA s1 ;;
  blkEmitUnary rO s1 ;;
  blkEmitBits3 false true true ;;
  blkEmitUnary rA s1 ;;
  blkCopy s0 rO ;;
  blkAddConst s0 2

def blkEmitXorHalf2 (rO rB : Fin R_emit) :=
  blkEmitBits3 true false false ;;
  blkEmitUnary s0 s1 ;;
  blkEmitUnary rB s1 ;;
  blkCopy s0 rO ;;
  blkAddConst s0 1 ;;
  blkEmitBits3 true false true ;;
  blkEmitUnary s0 s1 ;;
  blkAddConst s0 2 ;;
  blkEmitUnary s0 s1

def blkEmitXorAt (rO rA rB : Fin R_emit) :=
  blkEmitXorHalf1 rO rA rB ;; blkEmitXorHalf2 rO rB

theorem blkEmitXorAt_spec (rO rA rB : Fin R_emit)
    (hO : rO.val < 35) (hA : rA.val < 35) (hB : rB.val < 35)
    (V : ℕ) (inp : List Bool) (reg : RegState R_emit)
    (hreg : ∀ i, reg i ≤ V) (hO3 : reg rO + 3 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 35 → reg₁ i = reg i) ∧
      RMBlockExec (blkEmitXorAt rO rA rB) V inp reg reg₁
        (encodeXorAt (reg rO) (reg rA) (reg rB)) (16 * V + 60) := by
  have hOs1 : rO ≠ s1 := ne_of_lt_val (by change rO.val < 36; omega)
  have hAs1 : rA ≠ s1 := ne_of_lt_val (by change rA.val < 36; omega)
  have hBs1 : rB ≠ s1 := ne_of_lt_val (by change rB.val < 36; omega)
  have e1 := blkEmitBits3_spec false true true V inp reg hreg
  rcases blkEmitUnary_clean rB s1 hBs1 V inp reg hreg with ⟨g1, f1, e2⟩
  have e3 := blkEmitBits3_spec true false false V inp g1 e2.reg₁_le
  rcases blkEmitUnary_clean rA s1 hAs1 V inp g1 e2.reg₁_le with ⟨g2, f2, e4⟩
  rw [f1 rA hAs1] at e4
  rcases blkEmitUnary_clean rO s1 hOs1 V inp g2 e4.reg₁_le with ⟨g3, f3, e5⟩
  rw [f2 rO hOs1, f1 rO hOs1] at e5
  have e6 := blkEmitBits3_spec false true true V inp g3 e5.reg₁_le
  rcases blkEmitUnary_clean rA s1 hAs1 V inp g3 e5.reg₁_le with ⟨g4, f4, e7⟩
  rw [f3 rA hAs1, f2 rA hAs1, f1 rA hAs1] at e7
  have fg4 : ∀ i : Fin R_emit, i.val < 35 → g4 i = reg i := fun i hi => by
    have his1 : i ≠ s1 := ne_of_lt_val (by change i.val < 36; omega)
    rw [f4 i his1, f3 i his1, f2 i his1, f1 i his1]
  rcases blkCopy_clean s0 rO V inp g4 e7.reg₁_le with ⟨g5, vs5, f5, e8⟩
  rw [fg4 rO hO] at vs5
  rcases blkAddConst_clean s0 2 V inp g5 e8.reg₁_le (by rw [vs5]; omega) with ⟨g6, vs6, f6, e9⟩
  rw [vs5] at vs6
  have hcomb1 : RMBlockExec (blkEmitXorHalf1 rO rA rB) V inp reg g6
      ([false, true, true] ++
       (QCSD_natToUnary (reg rB) ++
        ([true, false, false] ++
         (QCSD_natToUnary (reg rA) ++
          (QCSD_natToUnary (reg rO) ++
           ([false, true, true] ++ QCSD_natToUnary (reg rA)))))))
      (8 * V + 25) :=
    (blkSeq_spec e1 (blkSeq_spec e2 (blkSeq_spec e3 (blkSeq_spec e4 (blkSeq_spec e5
      (blkSeq_spec e6 (blkSeq_nil_right e7 (blkSeq_nil_left e8 e9)))))))).weaken le_rfl (by omega)
  have e10 := blkEmitBits3_spec true false false V inp g6 e9.reg₁_le
  rcases blkEmitUnary_clean s0 s1 (by decide) V inp g6 e9.reg₁_le with ⟨g7, f7, e11⟩
  rw [vs6] at e11
  have fg7 : ∀ i : Fin R_emit, i.val < 35 → g7 i = reg i := fun i hi => by
    have his0 : i ≠ s0 := ne_of_lt_val (by change i.val < 35; exact hi)
    have his1 : i ≠ s1 := ne_of_lt_val (by change i.val < 36; omega)
    rw [f7 i his1, f6 i his0, f5 i his0, fg4 i hi]
  rcases blkEmitUnary_clean rB s1 hBs1 V inp g7 e11.reg₁_le with ⟨g8, f8, e12⟩
  rw [fg7 rB hB] at e12
  rcases blkCopy_clean s0 rO V inp g8 e12.reg₁_le with ⟨g9, vs9, f9, e13⟩
  rw [f8 rO hOs1, fg7 rO hO] at vs9
  rcases blkAddConst_clean s0 1 V inp g9 e13.reg₁_le (by rw [vs9]; omega) with ⟨g10, vs10, f10, e14⟩
  rw [vs9] at vs10
  have e15 := blkEmitBits3_spec true false true V inp g10 e14.reg₁_le
  rcases blkEmitUnary_clean s0 s1 (by decide) V inp g10 e14.reg₁_le with ⟨g11, f11, e16⟩
  rw [vs10] at e16
  have hg11_s0 : g11 s0 = reg rO + 1 := by rw [f11 s0 (by decide), vs10]
  rcases blkAddConst_clean s0 2 V inp g11 e16.reg₁_le (by rw [hg11_s0]; omega) with ⟨g12, vs12, f12, e17⟩
  have hg12_s0 : g12 s0 = reg rO + 3 := by rw [vs12, hg11_s0]
  rcases blkEmitUnary_clean s0 s1 (by decide) V inp g12 e17.reg₁_le with ⟨g13, f13, e18⟩
  rw [hg12_s0] at e18
  have hcomb2 : RMBlockExec (blkEmitXorHalf2 rO rB) V inp g6 g13
      ([true, false, false] ++
       (QCSD_natToUnary (reg rO + 2) ++
        (QCSD_natToUnary (reg rB) ++
         ([true, false, true] ++
          (QCSD_natToUnary (reg rO + 1) ++ QCSD_natToUnary (reg rO + 3))))))
      (8 * V + 35) :=
    (blkSeq_spec e10 (blkSeq_spec e11 (blkSeq_spec e12 (blkSeq_nil_left e13
      (blkSeq_nil_left e14 (blkSeq_spec e15 (blkSeq_spec e16
        (blkSeq_nil_left e17 e18)))))))).weaken le_rfl (by omega)
  have hcomb := blkSeq_spec hcomb1 hcomb2
  have hout :
      ([false, true, true] ++
       (QCSD_natToUnary (reg rB) ++
        ([true, false, false] ++
         (QCSD_natToUnary (reg rA) ++
          (QCSD_natToUnary (reg rO) ++
           ([false, true, true] ++ QCSD_natToUnary (reg rA))))))) ++
      ([true, false, false] ++
       (QCSD_natToUnary (reg rO + 2) ++
        (QCSD_natToUnary (reg rB) ++
         ([true, false, true] ++
          (QCSD_natToUnary (reg rO + 1) ++ QCSD_natToUnary (reg rO + 3)))))) =
      encodeXorAt (reg rO) (reg rA) (reg rB) := by
    simp [encodeXorAt, List.append_assoc]
  rw [hout] at hcomb
  refine ⟨g13, ?_, hcomb.weaken le_rfl (by omega)⟩
  intro i hi
  have his0 : i ≠ s0 := ne_of_lt_val (by change i.val < 35; exact hi)
  have his1 : i ≠ s1 := ne_of_lt_val (by change i.val < 36; omega)
  rw [f13 i his1, f12 i his0, f11 i his1, f10 i his0, f9 i his0, f8 i his1, fg7 i hi]

def blkEmitEqAt (rO rA rB : Fin R_emit) :=
  blkEmitXorAt rO rA rB ;;
  blkCopy s0 rO ;;
  blkAddConst s0 4 ;;
  blkEmitBits3 false true true ;;
  blkEmitUnary s0 s1

theorem blkEmitEqAt_spec (rO rA rB : Fin R_emit)
    (hO : rO.val < 35) (hA : rA.val < 35) (hB : rB.val < 35)
    (V : ℕ) (inp : List Bool) (reg : RegState R_emit)
    (hreg : ∀ i, reg i ≤ V) (hO4 : reg rO + 4 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 35 → reg₁ i = reg i) ∧
      RMBlockExec (blkEmitEqAt rO rA rB) V inp reg reg₁
        (encodeEqAt (reg rO) (reg rA) (reg rB)) (18 * V + 80) := by
  rcases blkEmitXorAt_spec rO rA rB hO hA hB V inp reg hreg (by omega)
    with ⟨g1, fg1, exor⟩
  rcases blkCopy_clean s0 rO V inp g1 exor.reg₁_le with ⟨g2, vs2, fg2, ecp⟩
  rw [fg1 rO hO] at vs2
  rcases blkAddConst_clean s0 4 V inp g2 ecp.reg₁_le (by rw [vs2]; omega) with ⟨g3, vs3, fg3, eadd⟩
  rw [vs2] at vs3
  have eb3 := blkEmitBits3_spec false true true V inp g3 eadd.reg₁_le
  rcases blkEmitUnary_clean s0 s1 (by decide) V inp g3 eadd.reg₁_le with ⟨g4, fg4, eun⟩
  rw [vs3] at eun
  have hcomb := blkSeq_spec exor (blkSeq_nil_left ecp (blkSeq_nil_left eadd (blkSeq_spec eb3 eun)))
  have hout :
      encodeXorAt (reg rO) (reg rA) (reg rB) ++ ([false, true, true] ++ QCSD_natToUnary (reg rO + 4)) =
      encodeEqAt (reg rO) (reg rA) (reg rB) := by
    simp [encodeEqAt, List.append_assoc]
  rw [hout] at hcomb
  refine ⟨g4, ?_, hcomb.weaken le_rfl (by omega)⟩
  intro i hi
  have his0 : i ≠ s0 := ne_of_lt_val (by change i.val < 35; exact hi)
  have his1 : i ≠ s1 := ne_of_lt_val (by change i.val < 36; omega)
  rw [fg4 i his1, fg3 i his0, fg2 i his0, fg1 i hi]

def blkEqTest (rRes rA rB : Fin R_emit) :=
  blkCmpLt s3 rA rB s5 s6 ;;
  blkCmpLt s4 rB rA s5 s6 ;;
  blkAdd s3 s4 s5 ;;
  blkIfZero s3 (blkSetConst rRes 1) (blkZero rRes)

theorem blkEqTest_spec (rRes rA rB : Fin R_emit)
    (_hRes : rRes.val < 38) (hA : rA.val < 38) (hB : rB.val < 38)
    (V : ℕ) (inp : List Bool) (reg : RegState R_emit)
    (hreg : ∀ i, reg i ≤ V) (h1 : 1 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      reg₁ rRes = (if reg rA = reg rB then 1 else 0) ∧
      (∀ i : Fin R_emit, i ≠ rRes → i.val < 38 → reg₁ i = reg i) ∧
      RMBlockExec (blkEqTest rRes rA rB) V inp reg reg₁ [] (6 * V + 25) := by
  rcases blkCmpLt_clean s3 rA rB s5 s6 (by decide) (by decide) (by decide)
      (ne_of_lt_val (by change rB.val < 40; omega)) V inp reg hreg h1
    with ⟨g1, vs3_1, fg1, ec1⟩
  have g1A : g1 rA = reg rA := fg1 rA
    (ne_of_lt_val hA) (ne_of_lt_val (by change rA.val < 40; omega)) (ne_of_lt_val (by change rA.val < 41; omega))
  have g1B : g1 rB = reg rB := fg1 rB
    (ne_of_lt_val hB) (ne_of_lt_val (by change rB.val < 40; omega)) (ne_of_lt_val (by change rB.val < 41; omega))
  rcases blkCmpLt_clean s4 rB rA s5 s6 (by decide) (by decide) (by decide)
      (ne_of_lt_val (by change rA.val < 40; omega)) V inp g1 ec1.reg₁_le h1
    with ⟨g2, vs4_2, fg2, ec2⟩
  rw [g1A, g1B] at vs4_2
  have vs3_2 : g2 s3 = (if reg rA < reg rB then 1 else 0) := by
    rw [fg2 s3 (by decide) (by decide) (by decide), vs3_1]
  have hsum : g2 s3 + g2 s4 ≤ V := by rw [vs3_2, vs4_2]; split_ifs <;> omega
  rcases blkAdd_clean s3 s4 s5 (by decide) (by decide) V inp g2 ec2.reg₁_le hsum
    with ⟨g3, vs3_3, fg3, eadd⟩
  rw [vs3_2, vs4_2] at vs3_3
  have fg3_38 : ∀ i : Fin R_emit, i.val < 38 → g3 i = reg i := fun i hi => by
    rw [fg3 i (ne_of_lt_val (by change i.val < 38; exact hi))
          (ne_of_lt_val (by change i.val < 40; omega)),
        fg2 i (ne_of_lt_val (by change i.val < 39; omega))
          (ne_of_lt_val (by change i.val < 40; omega)) (ne_of_lt_val (by change i.val < 41; omega)),
        fg1 i (ne_of_lt_val (by change i.val < 38; exact hi))
          (ne_of_lt_val (by change i.val < 40; omega)) (ne_of_lt_val (by change i.val < 41; omega))]
  by_cases heq : reg rA = reg rB
  · have hs0 : g3 s3 = 0 := by rw [vs3_3]; simp [heq]
    rcases blkSetConst_clean rRes 1 V inp g3 eadd.reg₁_le h1 with ⟨g4, vres, fg4, eset⟩
    have ebr := blkIfZero_zero_spec s3 (blkZero rRes) hs0 eset
    have hcomb := blkSeq_nil_left ec1 (blkSeq_nil_left ec2 (blkSeq_nil_left eadd ebr))
    refine ⟨g4, by simp [heq, vres], fun i hiR hi38 => by rw [fg4 i hiR, fg3_38 i hi38],
      hcomb.weaken le_rfl (by omega)⟩
  · have hsne : g3 s3 ≠ 0 := by
      rw [vs3_3]
      rcases lt_trichotomy (reg rA) (reg rB) with h | h | h
      · simp [h, Nat.not_lt.mpr (le_of_lt h)]
      · exact absurd h heq
      · simp [h, Nat.not_lt.mpr (le_of_lt h)]
    rcases blkZero_clean rRes V inp g3 eadd.reg₁_le with ⟨g4, vres, fg4, ez⟩
    have ebr := blkIfZero_pos_spec s3 (blkSetConst rRes 1) hsne ez
    have hcomb := blkSeq_nil_left ec1 (blkSeq_nil_left ec2 (blkSeq_nil_left eadd ebr))
    refine ⟨g4, by simp [heq, vres], fun i hiR hi38 => by rw [fg4 i hiR, fg3_38 i hi38],
      hcomb.weaken le_rfl (by omega)⟩

def blkCoeffPowY (rRes rM rP : Fin R_emit) :=
  blkCopy rThreeJ rJ ;;
  blkAdd rThreeJ rJ s0 ;;
  blkAdd rThreeJ rJ s0 ;;
  blkDivMod s0 s1 rM rThreeJ s4 s5 s6 ;;
  blkEqTest rRes s1 rP ;;
  blkDivMod s0 s2 rP rJ s4 s5 s6 ;;
  blkAdd s2 rJ s5 ;;
  blkAdd s2 rJ s5 ;;
  blkCmpLt s3 s1 s2 s5 s6 ;;
  blkCmpLt s4 s2 s1 s5 s6 ;;
  blkAdd s3 s4 s5 ;;
  blkIfZero s3 (blkSetConst rRes 1) blkNop

theorem blkCoeffPowY_spec (rRes rM rP : Fin R_emit)
    (hResJ : rRes ≠ rJ) (hResP : rRes ≠ rP)
    (hRes34 : rRes.val < 34) (hM34 : rM.val < 34) (hP34 : rP.val < 34)
    (V : ℕ) (inp : List Bool) (reg : RegState R_emit)
    (hJpos : 0 < reg rJ) (hreg : ∀ i, reg i ≤ V) (h3J : 3 * reg rJ ≤ V) :
    ∃ reg₁ : RegState R_emit,
      reg₁ rRes = (if coeffPowY (reg rJ) (reg rM) (reg rP) then 1 else 0) ∧
      (∀ i : Fin R_emit, i ≠ rRes → i.val < 34 → reg₁ i = reg i) ∧
      RMBlockExec (blkCoeffPowY rRes rM rP) V inp reg reg₁ [] (60 * V + 100) := by
  have h1 : 1 ≤ V := by omega
  rcases blkCopy_clean rThreeJ rJ V inp reg hreg with ⟨g1, v1, f1, e1⟩
  have g1J : g1 rJ = reg rJ := f1 rJ (by decide)
  rcases blkAdd_clean rThreeJ rJ s0 (by decide) (by decide) V inp g1 e1.reg₁_le
    (by rw [v1, g1J]; omega) with ⟨g2, v2, f2, e2⟩
  have v2' : g2 rThreeJ = 2 * reg rJ := by rw [v2, v1, g1J]; omega
  have g2J : g2 rJ = reg rJ := by rw [f2 rJ (by decide) (by decide), g1J]
  rcases blkAdd_clean rThreeJ rJ s0 (by decide) (by decide) V inp g2 e2.reg₁_le
    (by rw [v2', g2J]; omega) with ⟨g3, v3, f3, e3⟩
  have v3' : g3 rThreeJ = 3 * reg rJ := by rw [v3, v2', g2J]; omega
  have fg3 : ∀ i : Fin R_emit, i.val < 34 → g3 i = reg i := fun i hi => by
    have hi34 : i ≠ rThreeJ := ne_of_lt_val hi
    have his0 : i ≠ s0 := ne_of_lt_val (by change i.val < 35; omega)
    rw [f3 i hi34 his0, f2 i hi34 his0, f1 i hi34]
  rcases blkDivMod_clean s0 s1 rM rThreeJ s4 s5 s6
      (by decide) (ne_of_lt_val (by change rM.val < 35; omega)).symm (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      V inp g3 (by rw [v3']; omega) e3.reg₁_le
    with ⟨g4, _, vs1_4, f4, ediv1⟩
  rw [fg3 rM hM34, v3'] at vs1_4
  have fg4 : ∀ i : Fin R_emit, i.val < 34 → g4 i = reg i := fun i hi => by
    rw [f4 i (ne_of_lt_val (by change i.val < 35; omega))
          (ne_of_lt_val (by change i.val < 36; omega))
          (ne_of_lt_val (by change i.val < 39; omega))
          (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega)),
        fg3 i hi]
  rcases blkEqTest_spec rRes s1 rP (by omega) (by decide) (by omega) V inp g4 ediv1.reg₁_le h1
    with ⟨g5, vres_5, f5, eeq1⟩
  rw [vs1_4, fg4 rP hP34] at vres_5
  have g5_s1 : g5 s1 = reg rM % (3 * reg rJ) := by
    rw [f5 s1 (ne_of_lt_val (by change rRes.val < 36; omega)).symm (by decide), vs1_4]
  have g5_P : g5 rP = reg rP := by rw [f5 rP hResP.symm (by omega), fg4 rP hP34]
  have g5_J : g5 rJ = reg rJ := by rw [f5 rJ hResJ.symm (by decide), fg4 rJ (by decide)]
  rcases blkDivMod_clean s0 s2 rP rJ s4 s5 s6
      (by decide) (ne_of_lt_val (by change rP.val < 35; omega)).symm (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      V inp g5 (by rw [g5_J]; exact hJpos) eeq1.reg₁_le
    with ⟨g6, _, vs2_6, f6, ediv2⟩
  rw [g5_P, g5_J] at vs2_6
  have g6_s1 : g6 s1 = reg rM % (3 * reg rJ) := by
    rw [f6 s1 (by decide) (by decide) (by decide) (by decide) (by decide), g5_s1]
  have g6_J : g6 rJ = reg rJ := by
    rw [f6 rJ (by decide) (by decide) (by decide) (by decide) (by decide), g5_J]
  have hmodP : reg rP % reg rJ < reg rJ := Nat.mod_lt _ hJpos
  rcases blkAdd_clean s2 rJ s5 (by decide) (by decide) V inp g6 ediv2.reg₁_le
    (by rw [vs2_6, g6_J]; omega) with ⟨g7, vs2_7, f7, ea1⟩
  have vs2_7' : g7 s2 = reg rP % reg rJ + reg rJ := by rw [vs2_7, vs2_6, g6_J]
  have g7_J : g7 rJ = reg rJ := by rw [f7 rJ (by decide) (by decide), g6_J]
  rcases blkAdd_clean s2 rJ s5 (by decide) (by decide) V inp g7 ea1.reg₁_le
    (by rw [vs2_7', g7_J]; omega) with ⟨g8, vs2_8, f8, ea2⟩
  have vs2_8' : g8 s2 = 2 * reg rJ + reg rP % reg rJ := by rw [vs2_8, vs2_7', g7_J]; omega
  have g8_s1 : g8 s1 = reg rM % (3 * reg rJ) := by
    rw [f8 s1 (by decide) (by decide), f7 s1 (by decide) (by decide), g6_s1]
  rcases blkCmpLt_clean s3 s1 s2 s5 s6 (by decide) (by decide) (by decide) (by decide)
      V inp g8 ea2.reg₁_le h1 with ⟨g9, vs3_9, f9, ecmp1⟩
  have g9_s1 : g9 s1 = reg rM % (3 * reg rJ) := by rw [f9 s1 (by decide) (by decide) (by decide), g8_s1]
  have g9_s2 : g9 s2 = 2 * reg rJ + reg rP % reg rJ := by
    rw [f9 s2 (by decide) (by decide) (by decide), vs2_8']
  rcases blkCmpLt_clean s4 s2 s1 s5 s6 (by decide) (by decide) (by decide) (by decide)
      V inp g9 ecmp1.reg₁_le h1 with ⟨g10, vs4_10, f10, ecmp2⟩
  rw [g9_s2, g9_s1] at vs4_10
  have g10_s3 : g10 s3 = (if reg rM % (3 * reg rJ) < 2 * reg rJ + reg rP % reg rJ then 1 else 0) := by
    rw [f10 s3 (by decide) (by decide) (by decide), vs3_9, g8_s1, vs2_8']
  have hsum2 : g10 s3 + g10 s4 ≤ V := by rw [g10_s3, vs4_10]; split_ifs <;> omega
  rcases blkAdd_clean s3 s4 s5 (by decide) (by decide) V inp g10 ecmp2.reg₁_le hsum2
    with ⟨g11, vs3_11, f11, ea3⟩
  rw [g10_s3, vs4_10] at vs3_11
  have fg11_from_g5 : ∀ i : Fin R_emit, i.val < 35 → g11 i = g5 i := fun i hi => by
    rw [f11 i (ne_of_lt_val (by change i.val < 38; omega)) (ne_of_lt_val (by change i.val < 40; omega)),
        f10 i (ne_of_lt_val (by change i.val < 39; omega)) (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega)),
        f9 i (ne_of_lt_val (by change i.val < 38; omega)) (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega)),
        f8 i (ne_of_lt_val (by change i.val < 37; omega)) (ne_of_lt_val (by change i.val < 40; omega)),
        f7 i (ne_of_lt_val (by change i.val < 37; omega)) (ne_of_lt_val (by change i.val < 40; omega)),
        f6 i (ne_of_lt_val hi) (ne_of_lt_val (by change i.val < 37; omega))
          (ne_of_lt_val (by change i.val < 39; omega)) (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega))]
  have fg11_34 : ∀ i : Fin R_emit, i ≠ rRes → i.val < 34 → g11 i = reg i := fun i hiR hi34 => by
    rw [fg11_from_g5 i (by omega), f5 i hiR (by omega), fg4 i hi34]
  have g11_res : g11 rRes = (if reg rM % (3 * reg rJ) = reg rP then 1 else 0) := by
    rw [fg11_from_g5 rRes (by omega), vres_5]
  by_cases heq2 : reg rM % (3 * reg rJ) = 2 * reg rJ + reg rP % reg rJ
  · have hs0 : g11 s3 = 0 := by rw [vs3_11]; simp [heq2]
    rcases blkSetConst_clean rRes 1 V inp g11 ea3.reg₁_le h1 with ⟨g12, vr12, f12, eset⟩
    have ebr := blkIfZero_zero_spec s3 blkNop hs0 eset
    have hcomb :=
      blkSeq_nil_left e1 (blkSeq_nil_left e2 (blkSeq_nil_left e3
        (blkSeq_nil_left ediv1 (blkSeq_nil_left eeq1 (blkSeq_nil_left ediv2
          (blkSeq_nil_left ea1 (blkSeq_nil_left ea2 (blkSeq_nil_left ecmp1
            (blkSeq_nil_left ecmp2 (blkSeq_nil_left ea3 ebr))))))))))
    refine ⟨g12, by simp [coeffPowY, heq2, vr12],
      fun i hiR hi34 => by rw [f12 i hiR, fg11_34 i hiR hi34],
      hcomb.weaken le_rfl (by omega)⟩
  · have hsne : g11 s3 ≠ 0 := by
      rw [vs3_11]
      rcases lt_trichotomy (reg rM % (3 * reg rJ)) (2 * reg rJ + reg rP % reg rJ) with h | h | h
      · simp [h, Nat.not_lt.mpr (le_of_lt h)]
      · exact absurd h heq2
      · simp [h, Nat.not_lt.mpr (le_of_lt h)]
    have ebr := blkIfZero_pos_spec s3 (blkSetConst rRes 1) hsne (blkNop_spec V inp g11 ea3.reg₁_le)
    have hcomb :=
      blkSeq_nil_left e1 (blkSeq_nil_left e2 (blkSeq_nil_left e3
        (blkSeq_nil_left ediv1 (blkSeq_nil_left eeq1 (blkSeq_nil_left ediv2
          (blkSeq_nil_left ea1 (blkSeq_nil_left ea2 (blkSeq_nil_left ecmp1
            (blkSeq_nil_left ecmp2 (blkSeq_nil_left ea3 ebr))))))))))
    refine ⟨g11, ?_, fg11_34, hcomb.weaken le_rfl (by omega)⟩
    rw [g11_res]; unfold coeffPowY
    by_cases heq1 : reg rM % (3 * reg rJ) = reg rP <;> simp [heq1, heq2]

/-!
## Section 4: Unified DFT Matrix Oracle, Generic `linearMapCheckCircuit`, and `bilinearMapCheckCircuit` Emitters
-/

/-- Unified DFT matrix-entry oracle: sets `rMatHit := if dftUnifiedMat ... outIdx inIdx then 1 else 0`
in `O(V)` steps while preserving ALL registers `< 31`. -/
def blkDftUnifiedMat (rWExpParam rInStep rStride rOff : Fin R_emit) :=
  blkCopy rThreeJ rJ ;;
  blkAdd rThreeJ rJ s0 ;;
  blkDivMod rWArg1 rWArg2 rRowJ rThreeJ s4 s5 s6 ;;
  blkDivMod s0 s1 rColK rInStep s4 s5 s6 ;;
  blkMul s2 rStride s0 s5 s6 ;;
  blkAdd s2 rOff s5 ;;
  blkMul s3 rWExpParam s2 s5 s6 ;;
  blkAdd rThreeJ rJ s5 ;;
  blkDivMod s0 s2 s3 rThreeJ s4 s5 s6 ;;
  blkMul rMatHit s2 rWArg1 s5 s6 ;;
  blkAdd rMatHit s1 s5 ;;
  blkCopy rWArg1 rMatHit ;;
  blkCoeffPowY rMatHit rWArg1 rWArg2

theorem blkDftUnifiedMat_spec (rWExpParam rInStep rStride rOff : Fin R_emit)
    (hW20 : rWExpParam.val < 20) (hIS20 : rInStep.val < 20)
    (hSt20 : rStride.val < 20) (hOf20 : rOff.val < 20)
    (V : ℕ) (inp : List Bool) (reg : RegState R_emit)
    (hreg : ∀ i, reg i ≤ V)
    (hJpos : 0 < reg rJ)
    (hISpos : 0 < reg rInStep) (hIS_le : reg rInStep ≤ 2 * reg rJ)
    (hW_le : reg rWExpParam ≤ 3 * reg rJ)
    (hSt_le : reg rStride ≤ 3 * reg rJ)
    (hqOut_le : reg rRowJ / (2 * reg rJ) ≤ 3 * reg rJ)
    (hqIn_le : reg rColK / reg rInStep ≤ 3 * reg rJ)
    (hr_le : reg rStride * (reg rColK / reg rInStep) + reg rOff ≤ 3 * reg rJ)
    (h12J2 : 12 * (reg rJ) ^ 2 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      reg₁ rMatHit = (if dftUnifiedMat (reg rJ) (reg rWExpParam) (reg rInStep)
                        (reg rStride) (reg rOff) (reg rRowJ) (reg rColK) then 1 else 0) ∧
      (∀ i : Fin R_emit, i.val < 31 → reg₁ i = reg i) ∧
      RMBlockExec (blkDftUnifiedMat rWExpParam rInStep rStride rOff) V inp reg reg₁ []
        (160 * V + 250) := by
  have h3J_V : 3 * reg rJ ≤ V := by
    have : reg rJ ≤ (reg rJ) ^ 2 := by
      have : reg rJ * 1 ≤ reg rJ * reg rJ := Nat.mul_le_mul_left _ hJpos
      simpa [pow_two] using this
    omega
  have h9J2_3V : (3 * reg rJ) * (2 * (3 * reg rJ) + 3) + 3 ≤ 3 * V + 3 := by
    have hJ1 : reg rJ ≤ (reg rJ) ^ 2 := by
      have : reg rJ * 1 ≤ reg rJ * reg rJ := Nat.mul_le_mul_left _ hJpos
      simpa [pow_two] using this
    have hexp : (3 * reg rJ) * (2 * (3 * reg rJ) + 3) = 18 * (reg rJ) ^ 2 + 9 * reg rJ := by ring
    omega
  rcases blkCopy_clean rThreeJ rJ V inp reg hreg with ⟨g1, v1, f1, e1⟩
  have g1J : g1 rJ = reg rJ := f1 rJ (by decide)
  rcases blkAdd_clean rThreeJ rJ s0 (by decide) (by decide) V inp g1 e1.reg₁_le
    (by rw [v1, g1J]; omega) with ⟨g2, v2, f2, e2⟩
  have v2' : g2 rThreeJ = 2 * reg rJ := by rw [v2, v1, g1J]; omega
  have fg2 : ∀ i : Fin R_emit, i.val < 34 → g2 i = reg i := fun i hi => by
    rw [f2 i (ne_of_lt_val hi) (ne_of_lt_val (by change i.val < 35; omega)), f1 i (ne_of_lt_val hi)]
  rcases blkDivMod_clean rWArg1 rWArg2 rRowJ rThreeJ s4 s5 s6
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      V inp g2 (by rw [v2']; omega) e2.reg₁_le
    with ⟨g3, vqOut, vpOut, f3, ediv1⟩
  rw [fg2 rRowJ (by decide), v2'] at vqOut vpOut
  have fg3_32 : ∀ i : Fin R_emit, i.val < 32 → g3 i = reg i := fun i hi => by
    rw [f3 i (ne_of_lt_val hi) (ne_of_lt_val (by change i.val < 33; omega))
          (ne_of_lt_val (by change i.val < 39; omega)) (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega)),
        fg2 i (by omega)]
  have g3_3J : g3 rThreeJ = 2 * reg rJ := by
    rw [f3 rThreeJ (by decide) (by decide) (by decide) (by decide) (by decide), v2']
  rcases blkDivMod_clean s0 s1 rColK rInStep s4 s5 s6
      (by decide) (by decide) (ne_of_lt_val (by change rInStep.val < 35; omega)).symm
      (by decide) (by decide) (by decide)
      (ne_of_lt_val (by change rInStep.val < 36; omega)).symm (by decide) (by decide) (by decide)
      (ne_of_lt_val (by change rInStep.val < 39; omega))
      (ne_of_lt_val (by change rInStep.val < 40; omega))
      (ne_of_lt_val (by change rInStep.val < 41; omega))
      (by decide) (by decide) (by decide)
      V inp g3 (by rw [fg3_32 rInStep (by omega)]; exact hISpos) ediv1.reg₁_le
    with ⟨g4, vqIn, vuIn, f4, ediv2⟩
  rw [fg3_32 rColK (by decide), fg3_32 rInStep (by omega)] at vqIn vuIn
  have fg4_35 : ∀ i : Fin R_emit, i.val < 35 → g4 i = g3 i := fun i hi =>
    f4 i (ne_of_lt_val hi) (ne_of_lt_val (by change i.val < 36; omega))
      (ne_of_lt_val (by change i.val < 39; omega)) (ne_of_lt_val (by change i.val < 40; omega))
      (ne_of_lt_val (by change i.val < 41; omega))
  have g4_St : g4 rStride = reg rStride := by rw [fg4_35 rStride (by omega), fg3_32 rStride (by omega)]
  rcases blkMul_clean s2 rStride s0 s5 s6
      (ne_of_lt_val (by change rStride.val < 37; omega)).symm (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (3 * reg rJ) V inp g4 ediv2.reg₁_le
      (by rw [g4_St]; exact hSt_le) (by rw [vqIn]; exact hqIn_le)
      (by rw [g4_St, vqIn]; omega)
    with ⟨g5, vs2_5, f5, emul1⟩
  rw [g4_St, vqIn] at vs2_5
  have g5_Off : g5 rOff = reg rOff := by
    rw [f5 rOff (ne_of_lt_val (by change rOff.val < 37; omega))
          (ne_of_lt_val (by change rOff.val < 40; omega))
          (ne_of_lt_val (by change rOff.val < 41; omega)),
        fg4_35 rOff (by omega), fg3_32 rOff (by omega)]
  rcases blkAdd_clean s2 rOff s5 (by decide) (ne_of_lt_val (by change rOff.val < 40; omega))
      V inp g5 emul1.reg₁_le (by rw [vs2_5, g5_Off]; omega)
    with ⟨g6, vs2_6, f6, eadd1⟩
  rw [vs2_5, g5_Off] at vs2_6
  have g6_W : g6 rWExpParam = reg rWExpParam := by
    rw [f6 rWExpParam (ne_of_lt_val (by change rWExpParam.val < 37; omega))
          (ne_of_lt_val (by change rWExpParam.val < 40; omega)),
        f5 rWExpParam (ne_of_lt_val (by change rWExpParam.val < 37; omega))
          (ne_of_lt_val (by change rWExpParam.val < 40; omega))
          (ne_of_lt_val (by change rWExpParam.val < 41; omega)),
        fg4_35 rWExpParam (by omega), fg3_32 rWExpParam (by omega)]
  have hprod2_V : g6 rWExpParam * g6 s2 ≤ V := by
    rw [g6_W, vs2_6]
    calc
      reg rWExpParam * (reg rStride * (reg rColK / reg rInStep) + reg rOff)
          ≤ (3 * reg rJ) * (3 * reg rJ) := Nat.mul_le_mul hW_le hr_le
      _ = 9 * (reg rJ) ^ 2 := by ring
      _ ≤ V := by omega
  rcases blkMul_clean s3 rWExpParam s2 s5 s6
      (ne_of_lt_val (by change rWExpParam.val < 38; omega)).symm (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (3 * reg rJ) V inp g6 eadd1.reg₁_le
      (by rw [g6_W]; exact hW_le) (by rw [vs2_6]; exact hr_le) hprod2_V
    with ⟨g7, vs3_7, f7, emul2⟩
  rw [g6_W, vs2_6] at vs3_7
  have fg7_37 : ∀ i : Fin R_emit, i.val < 37 → g7 i = g4 i := fun i hi => by
    have his2 : i ≠ s2 := ne_of_lt_val (by change i.val < 37; exact hi)
    rw [f7 i (ne_of_lt_val (by change i.val < 38; omega))
          (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega)),
        f6 i his2 (ne_of_lt_val (by change i.val < 40; omega)),
        f5 i his2 (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega))]
  have g7_3J : g7 rThreeJ = 2 * reg rJ := by rw [fg7_37 rThreeJ (by decide), fg4_35 rThreeJ (by decide), g3_3J]
  have g7_J : g7 rJ = reg rJ := by rw [fg7_37 rJ (by decide), fg4_35 rJ (by decide), fg3_32 rJ (by decide)]
  rcases blkAdd_clean rThreeJ rJ s5 (by decide) (by decide) V inp g7 emul2.reg₁_le
    (by rw [g7_3J, g7_J]; omega) with ⟨g8, v3J_8, f8, eadd2⟩
  have v3J_8' : g8 rThreeJ = 3 * reg rJ := by rw [v3J_8, g7_3J, g7_J]; omega
  have g8_s3 : g8 s3 = reg rWExpParam * (reg rStride * (reg rColK / reg rInStep) + reg rOff) := by
    rw [f8 s3 (by decide) (by decide), vs3_7]
  rcases blkDivMod_clean s0 s2 s3 rThreeJ s4 s5 s6
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      V inp g8 (by rw [v3J_8']; omega) eadd2.reg₁_le
    with ⟨g9, _, vs2_9, f9, ediv3⟩
  rw [g8_s3, v3J_8'] at vs2_9
  have g9_qOut : g9 rWArg1 = reg rRowJ / (2 * reg rJ) := by
    rw [f9 rWArg1 (by decide) (by decide) (by decide) (by decide) (by decide),
        f8 rWArg1 (by decide) (by decide), fg7_37 rWArg1 (by decide), fg4_35 rWArg1 (by decide), vqOut]
  have g9_pOut : g9 rWArg2 = reg rRowJ % (2 * reg rJ) := by
    rw [f9 rWArg2 (by decide) (by decide) (by decide) (by decide) (by decide),
        f8 rWArg2 (by decide) (by decide), fg7_37 rWArg2 (by decide), fg4_35 rWArg2 (by decide), vpOut]
  have g9_uIn : g9 s1 = reg rColK % reg rInStep := by
    rw [f9 s1 (by decide) (by decide) (by decide) (by decide) (by decide),
        f8 s1 (by decide) (by decide), fg7_37 s1 (by decide), vuIn]
  have fg9_32 : ∀ i : Fin R_emit, i.val < 32 → g9 i = reg i := fun i hi => by
    rw [f9 i (ne_of_lt_val (by change i.val < 35; omega))
          (ne_of_lt_val (by change i.val < 37; omega))
          (ne_of_lt_val (by change i.val < 39; omega))
          (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega)),
        f8 i (ne_of_lt_val (by change i.val < 34; omega))
          (ne_of_lt_val (by change i.val < 40; omega)),
        fg7_37 i (by omega), fg4_35 i (by omega), fg3_32 i hi]
  have hmod_lt3J : g9 s2 < 3 * reg rJ := by rw [vs2_9]; exact Nat.mod_lt _ (by omega)
  have huIn_lt2J : reg rColK % reg rInStep < 2 * reg rJ :=
    lt_of_lt_of_le (Nat.mod_lt _ hISpos) hIS_le
  have hprod3_le9J2 : g9 s2 * g9 rWArg1 ≤ 9 * (reg rJ) ^ 2 := by
    rw [g9_qOut]
    calc
      g9 s2 * (reg rRowJ / (2 * reg rJ)) ≤ (3 * reg rJ) * (3 * reg rJ) :=
        Nat.mul_le_mul (le_of_lt hmod_lt3J) hqOut_le
      _ = 9 * (reg rJ) ^ 2 := by ring
  have hJ_le_J2 : reg rJ ≤ (reg rJ) ^ 2 := by
    have : reg rJ * 1 ≤ reg rJ * reg rJ := Nat.mul_le_mul_left _ hJpos
    simpa [pow_two] using this
  rcases blkMul_clean rMatHit s2 rWArg1 s5 s6
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (3 * reg rJ) V inp g9 ediv3.reg₁_le
      (le_of_lt hmod_lt3J) (by rw [g9_qOut]; exact hqOut_le) (by omega)
    with ⟨g10, vhit_10, f10, emul3⟩
  have g10_s1 : g10 s1 = reg rColK % reg rInStep := by
    rw [f10 s1 (by decide) (by decide) (by decide), g9_uIn]
  rcases blkAdd_clean rMatHit s1 s5 (by decide) (by decide) V inp g10 emul3.reg₁_le
    (by rw [vhit_10, g10_s1]; omega) with ⟨g11, vhit_11, f11, eadd3⟩
  rcases blkCopy_clean rWArg1 rMatHit V inp g11 eadd3.reg₁_le with ⟨g12, vw1_12, f12, ecp⟩
  have g12_w1 : g12 rWArg1 =
      ((reg rWExpParam * (reg rStride * (reg rColK / reg rInStep) + reg rOff)) % (3 * reg rJ)) *
      (reg rRowJ / (2 * reg rJ)) + reg rColK % reg rInStep := by
    rw [vw1_12, vhit_11, vhit_10, g10_s1, vs2_9, g9_qOut]
  have g12_w2 : g12 rWArg2 = reg rRowJ % (2 * reg rJ) := by
    rw [f12 rWArg2 (by decide), f11 rWArg2 (by decide) (by decide),
        f10 rWArg2 (by decide) (by decide) (by decide), g9_pOut]
  have fg12_31 : ∀ i : Fin R_emit, i.val < 31 → g12 i = reg i := fun i hi => by
    rw [f12 i (ne_of_lt_val (by change i.val < 32; omega)),
        f11 i (ne_of_lt_val hi) (ne_of_lt_val (by change i.val < 40; omega)),
        f10 i (ne_of_lt_val hi) (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega)),
        fg9_32 i (by omega)]
  rcases blkCoeffPowY_spec rMatHit rWArg1 rWArg2 (by decide) (by decide)
      (by decide) (by decide) (by decide)
      V inp g12 (by rw [fg12_31 rJ (by decide)]; exact hJpos) ecp.reg₁_le
      (by rw [fg12_31 rJ (by decide)]; exact h3J_V)
    with ⟨g13, vres_13, f13, ecoeff⟩
  rw [fg12_31 rJ (by decide), g12_w1, g12_w2, coeffPowY_mod_mul] at vres_13
  have hcomb :=
    blkSeq_nil_left e1 (blkSeq_nil_left e2 (blkSeq_nil_left ediv1 (blkSeq_nil_left ediv2
      (blkSeq_nil_left (emul1.weaken le_rfl h9J2_3V) (blkSeq_nil_left eadd1
        (blkSeq_nil_left (emul2.weaken le_rfl h9J2_3V) (blkSeq_nil_left eadd2
          (blkSeq_nil_left ediv3 (blkSeq_nil_left (emul3.weaken le_rfl h9J2_3V)
            (blkSeq_nil_left eadd3 (blkSeq_nil_left ecp ecoeff)))))))))))
  refine ⟨g13, vres_13, fun i hi => by
    rw [f13 i (ne_of_lt_val hi) (by omega), fg12_31 i hi],
    hcomb.weaken le_rfl (by omega)⟩

/-- Ring-multiplication tensor entry oracle (`ringMulTensor J j (k / (2 * J)) (k % (2 * J))`),
where `rBlkAux1` holds `2 * J`. Preserves all registers `< 31`. -/
def blkRingMulActive :=
  blkDivMod rWArg1 s0 rColK rBlkAux1 s4 s5 s6 ;;
  blkAdd rWArg1 s0 s5 ;;
  blkCopy rWArg2 rRowJ ;;
  blkCoeffPowY rMatHit rWArg1 rWArg2

theorem blkRingMulActive_spec (V : ℕ) (inp : List Bool) (reg : RegState R_emit)
    (hreg : ∀ i, reg i ≤ V) (hJpos : 0 < reg rJ)
    (hAux : reg rBlkAux1 = 2 * reg rJ)
    (hk_lt : reg rColK < (2 * reg rJ) * (2 * reg rJ))
    (h4J_V : 4 * reg rJ ≤ V) :
    ∃ reg₁ : RegState R_emit,
      reg₁ rMatHit = (if ringMulTensor (reg rJ) (reg rRowJ)
                        (reg rColK / (2 * reg rJ)) (reg rColK % (2 * reg rJ)) then 1 else 0) ∧
      (∀ i : Fin R_emit, i.val < 31 → reg₁ i = reg i) ∧
      RMBlockExec blkRingMulActive V inp reg reg₁ [] (80 * V + 120) := by
  rcases blkDivMod_clean rWArg1 s0 rColK rBlkAux1 s4 s5 s6
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      V inp reg (by rw [hAux]; omega) hreg
    with ⟨g1, vq, vr, f1, ediv⟩
  rw [hAux] at vq vr
  have hq_lt : reg rColK / (2 * reg rJ) < 2 * reg rJ := Nat.div_lt_of_lt_mul hk_lt
  have hr_lt : reg rColK % (2 * reg rJ) < 2 * reg rJ := Nat.mod_lt _ (by omega)
  rcases blkAdd_clean rWArg1 s0 s5 (by decide) (by decide) V inp g1 ediv.reg₁_le
    (by rw [vq, vr]; omega) with ⟨g2, vsum, f2, eadd⟩
  rw [vq, vr] at vsum
  rcases blkCopy_clean rWArg2 rRowJ V inp g2 eadd.reg₁_le with ⟨g3, vw2, f3, ecp⟩
  have fg3_31 : ∀ i : Fin R_emit, i.val < 31 → g3 i = reg i := fun i hi => by
    rw [f3 i (ne_of_lt_val (by change i.val < 33; omega)),
        f2 i (ne_of_lt_val (by change i.val < 32; omega))
          (ne_of_lt_val (by change i.val < 40; omega)),
        f1 i (ne_of_lt_val (by change i.val < 32; omega))
          (ne_of_lt_val (by change i.val < 35; omega))
          (ne_of_lt_val (by change i.val < 39; omega))
          (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega))]
  have g3_w2 : g3 rWArg2 = reg rRowJ := by
    rw [vw2, f2 rRowJ (by decide) (by decide),
        f1 rRowJ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have g3_w1 : g3 rWArg1 = reg rColK / (2 * reg rJ) + reg rColK % (2 * reg rJ) := by
    rw [f3 rWArg1 (by decide), vsum]
  rcases blkCoeffPowY_spec rMatHit rWArg1 rWArg2 (by decide) (by decide)
      (by decide) (by decide) (by decide)
      V inp g3 (by rw [fg3_31 rJ (by decide)]; exact hJpos) ecp.reg₁_le
      (by rw [fg3_31 rJ (by decide)]; omega)
    with ⟨g4, vres, f4, ecoeff⟩
  rw [fg3_31 rJ (by decide), g3_w1, g3_w2] at vres
  have hcomb := blkSeq_nil_left ediv (blkSeq_nil_left eadd (blkSeq_nil_left ecp ecoeff))
  refine ⟨g4, vres, fun i hi => by rw [f4 i (ne_of_lt_val hi) (by omega), fg3_31 i hi],
    hcomb.weaken le_rfl (by omega)⟩

/-! ### Shared Generic Parity-Circuit Emitters (`blkEmitInitInputs`, `blkCountAllBase`, `blkEmitParityRows`, `blkEmitAllConjs`) -/

def blkEmitInitInputs :=
  blkForRange rRowJ rRowRem rTotalIn
    (blkEmitBits3 false false false ;; blkEmitUnary rRowJ s1)

theorem blkEmitInitInputs_spec (V : ℕ) (inp : List Bool) (reg₀ : RegState R_emit)
    (hreg₀ : ∀ i, reg₀ i ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 27 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitInitInputs V inp reg₀ reg₁
        ((List.range (reg₀ rTotalIn)).flatMap (fun i => [false, false, false] ++ QCSD_natToUnary i))
        (reg₀ rTotalIn * (2 * V + 8) + 3) := by
  rcases blkForRange_frame_spec rRowJ rRowRem rTotalIn (by decide) (by decide)
      (fun r => r.val < 27) (by decide) (by decide)
      (blkEmitBits3 false false false ;; blkEmitUnary rRowJ s1)
      V (2 * V + 6) inp reg₀
      (fun i => [false, false, false] ++ QCSD_natToUnary i)
      hreg₀
      (fun i reg _ hidx hreg hkeep => by
        have eb := blkEmitBits3_spec false false false V inp reg hreg
        rcases blkEmitUnary_clean rRowJ s1 (by decide) V inp reg hreg with ⟨g1, fg1, eu⟩
        rw [hidx] at eu
        exact ⟨g1,
          by rw [fg1 rRowJ (by decide), hidx],
          fg1 rRowRem (by decide),
          fun r hr => by rw [fg1 r (ne_of_lt_val (by change r.val < 36; omega)), hkeep r hr],
          (blkSeq_spec eb eu).weaken le_rfl (by omega)⟩)
    with ⟨reg_end, hfr, hex⟩
  exact ⟨reg_end, hfr, hex⟩

def blkCountAllBase {Q : Type} (B_act : RMBlock R_emit Q) :=
  blkCopy rCurWire rPairBase ;;
  blkForRange rRowJ rRowRem rNumOut
    (blkAddConst rCurWire 7 ;;
     blkForRange rColK rColRem rMatCols
       (B_act ;; blkIfZero rMatHit blkNop (blkAddConst rCurWire 5))) ;;
  blkCopy rAllBase rCurWire

theorem blkCountAllBase_spec {Q : Type} (B_act : RMBlock R_emit Q)
    (active : ℕ → ℕ → Bool) (V T_act : ℕ) (inp : List Bool) (reg₀ : RegState R_emit)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hall_le : parityRowStart (reg₀ rPairBase) (reg₀ rMatCols) active (reg₀ rNumOut) ≤ V)
    (hact : ∀ j k reg,
      j < reg₀ rNumOut → k < reg₀ rMatCols →
      reg rRowJ = j → reg rColK = k →
      (∀ i : Fin R_emit, i.val < 26 → reg i = reg₀ i) →
      (∀ i, reg i ≤ V) →
      ∃ reg₁,
        reg₁ rMatHit = (if active j k then 1 else 0) ∧
        (∀ i : Fin R_emit, i.val < 31 → reg₁ i = reg i) ∧
        RMBlockExec B_act V inp reg reg₁ [] T_act) :
    ∃ reg₁ : RegState R_emit,
      reg₁ rAllBase = parityRowStart (reg₀ rPairBase) (reg₀ rMatCols) active (reg₀ rNumOut) ∧
      (∀ i : Fin R_emit, i.val < 25 → reg₁ i = reg₀ i) ∧
      RMBlockExec (blkCountAllBase B_act) V inp reg₀ reg₁ []
        (reg₀ rNumOut * (reg₀ rMatCols * (T_act + 9) + 12) + 5) := by
  set base := reg₀ rPairBase
  set M := reg₀ rMatCols
  set nOut := reg₀ rNumOut
  rcases blkCopy_clean rCurWire rPairBase V inp reg₀ hreg₀ with ⟨g0, vc0, fg0, ecp0⟩
  have hg0_nOut : g0 rNumOut = nOut := fg0 rNumOut (by decide)
  set InvOut : ℕ → RegState R_emit → Prop := fun j reg =>
    reg rRowJ = j ∧
    reg rCurWire = parityRowStart base M active j ∧
    (∀ i, reg i ≤ V) ∧
    (∀ i : Fin R_emit, i.val < 26 → reg i = reg₀ i)
  rcases blkForRange_spec rRowJ rRowRem rNumOut (by decide) (by decide)
      _ V (M * (T_act + 9) + 10) inp g0 InvOut (fun _ => [])
      ecp0.reg₁_le
      ⟨by rw [regUpd_ne _ (by decide), regUpd_self],
       by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), vc0]; rfl,
       regUpd_le (regUpd_le ecp0.reg₁_le rRowJ (Nat.zero_le V)) rRowRem (ecp0.reg₁_le rNumOut),
       fun i hi => by
         rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 28; omega)),
             regUpd_ne _ (ne_of_lt_val (by change i.val < 27; omega)),
             fg0 i (ne_of_lt_val (by change i.val < 26; exact hi))]⟩
      (fun _ _ hI => hI.2.2.1)
      (fun _ _ hI => hI.1)
      (fun j reg v hv hI =>
        ⟨by rw [regUpd_ne _ (by decide), hI.1],
         by rw [regUpd_ne _ (by decide), hI.2.1],
         regUpd_le hI.2.2.1 rRowRem hv,
         fun i hi => by rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 28; omega)), hI.2.2.2 i hi]⟩)
      (fun j reg hj hI => by
        rw [hg0_nOut] at hj
        have hrow_end_le : parityRowStart base M active (j + 1) ≤ V :=
          le_trans (parityRowStart_mono base M active hj) hall_le
        have hcur7 : reg rCurWire + 7 ≤ V := by
          rw [hI.2.1]; rw [parityRowStart_succ] at hrow_end_le; omega
        rcases blkAddConst_clean rCurWire 7 V inp reg hI.2.2.1 hcur7 with ⟨r1, vr1, fr1, ea7⟩
        have hr1_cols : r1 rMatCols = M := by rw [fr1 rMatCols (by decide), hI.2.2.2 rMatCols (by decide)]
        set InvIn : ℕ → RegState R_emit → Prop := fun k rg =>
          rg rColK = k ∧
          rg rRowJ = j ∧
          rg rRowRem = reg rRowRem ∧
          rg rCurWire = parityRowStart base M active j + 7 + 5 * prefixHits (active j) k ∧
          (∀ i, rg i ≤ V) ∧
          (∀ i : Fin R_emit, i.val < 26 → rg i = reg₀ i)
        rcases blkForRange_spec rColK rColRem rMatCols (by decide) (by decide)
            (B_act ;; blkIfZero rMatHit blkNop (blkAddConst rCurWire 5))
            V (T_act + 7) inp r1 InvIn (fun _ => [])
            ea7.reg₁_le
            ⟨by rw [regUpd_ne _ (by decide), regUpd_self],
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), fr1 rRowJ (by decide), hI.1],
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), fr1 rRowRem (by decide)],
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), vr1, hI.2.1]; simp,
             regUpd_le (regUpd_le ea7.reg₁_le rColK (Nat.zero_le V)) rColRem (ea7.reg₁_le rMatCols),
             fun i hi => by
               rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 30; omega)),
                   regUpd_ne _ (ne_of_lt_val (by change i.val < 29; omega)),
                   fr1 i (ne_of_lt_val (by change i.val < 26; exact hi)), hI.2.2.2 i hi]⟩
            (fun _ _ hJ => hJ.2.2.2.2.1)
            (fun _ _ hJ => hJ.1)
            (fun k rg v hv hJ =>
              ⟨by rw [regUpd_ne _ (by decide), hJ.1],
               by rw [regUpd_ne _ (by decide), hJ.2.1],
               by rw [regUpd_ne _ (by decide), hJ.2.2.1],
               by rw [regUpd_ne _ (by decide), hJ.2.2.2.1],
               regUpd_le hJ.2.2.2.2.1 rColRem hv,
               fun i hi => by rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 30; omega)), hJ.2.2.2.2.2 i hi]⟩)
            (fun k rg hk hJ => by
              rw [hr1_cols] at hk
              rcases hact j k rg hj hk hJ.2.1 hJ.1 hJ.2.2.2.2.2 hJ.2.2.2.2.1
                with ⟨rg1, vhit, frg1, eact⟩
              cases hjk : active j k with
              | false =>
                rw [hjk] at vhit
                have ebr := (blkIfZero_zero_spec rMatHit (blkAddConst rCurWire 5) vhit
                  (blkNop_spec V inp rg1 eact.reg₁_le)).weaken le_rfl (by omega : 2 + 0 ≤ 7)
                refine ⟨rg1,
                  by rw [frg1 rColK (by decide), hJ.1],
                  frg1 rColRem (by decide),
                  ⟨regUpd_self _ _ _,
                   by rw [regUpd_ne _ (by decide), frg1 rRowJ (by decide), hJ.2.1],
                   by rw [regUpd_ne _ (by decide), frg1 rRowRem (by decide), hJ.2.2.1],
                   by rw [regUpd_ne _ (by decide), frg1 rCurWire (by decide), hJ.2.2.2.1,
                          prefixHits_succ, hjk]; simp,
                   regUpd_le eact.reg₁_le rColK (by have := hreg₀ rMatCols; omega),
                   fun i hi => by
                     rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 29; omega)),
                         frg1 i (by omega), hJ.2.2.2.2.2 i hi]⟩,
                  blkSeq_nil_left eact ebr⟩
              | true =>
                rw [hjk] at vhit
                have hpk1 : prefixHits (active j) k + 1 ≤ parityRowHits M active j :=
                  prefixHits_succ_le_of_pos hk hjk
                have hcur5 : rg1 rCurWire + 5 ≤ V := by
                  rw [frg1 rCurWire (by decide), hJ.2.2.2.1]
                  rw [parityRowStart_succ] at hrow_end_le
                  dsimp only [parityRowHits] at hpk1 hrow_end_le
                  omega
                rcases blkAddConst_clean rCurWire 5 V inp rg1 eact.reg₁_le hcur5
                  with ⟨rg2, vcur2, frg2, ea5⟩
                have ebr := blkIfZero_pos_spec rMatHit blkNop (by simp [vhit]) ea5
                refine ⟨rg2,
                  by rw [frg2 rColK (by decide), frg1 rColK (by decide), hJ.1],
                  by rw [frg2 rColRem (by decide), frg1 rColRem (by decide)],
                  ⟨regUpd_self _ _ _,
                   by rw [regUpd_ne _ (by decide), frg2 rRowJ (by decide), frg1 rRowJ (by decide), hJ.2.1],
                   by rw [regUpd_ne _ (by decide), frg2 rRowRem (by decide), frg1 rRowRem (by decide), hJ.2.2.1],
                   by rw [regUpd_ne _ (by decide), vcur2, frg1 rCurWire (by decide), hJ.2.2.2.1,
                          prefixHits_succ, hjk]; simp; omega,
                   regUpd_le ea5.reg₁_le rColK (by have := hreg₀ rMatCols; omega),
                   fun i hi => by
                     rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 29; omega)),
                         frg2 i (ne_of_lt_val (by change i.val < 26; exact hi)),
                         frg1 i (by omega), hJ.2.2.2.2.2 i hi]⟩,
                  blkSeq_nil_left eact ebr⟩)
          with ⟨rg_end, _, _, hIn_end, ein_exec⟩
        have hnil : (List.range (r1 rMatCols)).flatMap (fun _ => ([] : List Bool)) = [] := by simp
        rw [hnil, hr1_cols] at ein_exec
        rw [hr1_cols] at hIn_end
        have hT_in : 7 + (M * (T_act + 7 + 2) + 3) ≤ M * (T_act + 9) + 10 := by
          have : 7 + (M * (T_act + 7 + 2) + 3) = M * (T_act + 9) + 10 := by ring
          omega
        have hstep_comb := (blkSeq_nil_left ea7 ein_exec).weaken le_rfl hT_in
        refine ⟨rg_end, hIn_end.2.1, hIn_end.2.2.1,
          ⟨regUpd_self _ _ _,
           by rw [regUpd_ne _ (by decide), hIn_end.2.2.2.1]; rfl,
           regUpd_le hIn_end.2.2.2.2.1 rRowJ (by have := hreg₀ rNumOut; omega),
           fun i hi => by
             rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 27; omega)), hIn_end.2.2.2.2.2 i hi]⟩,
          hstep_comb⟩)
    with ⟨g_mid, _, _, hOut_end, eout_exec⟩
  have hnil_out : (List.range (g0 rNumOut)).flatMap (fun _ => ([] : List Bool)) = [] := by simp
  rw [hnil_out, hg0_nOut] at eout_exec
  rw [hg0_nOut] at hOut_end
  rcases blkCopy_clean rAllBase rCurWire V inp g_mid hOut_end.2.2.1 with ⟨g_fin, vfin, ffin, ecp_fin⟩
  rw [hOut_end.2.1] at vfin
  have hcomb := blkSeq_nil_left ecp0 (blkSeq_nil_left eout_exec ecp_fin)
  have hT_out : 1 + ((nOut * ((M * (T_act + 9) + 10) + 2) + 3) + 1) ≤
      nOut * (M * (T_act + 9) + 12) + 5 := by
    have : 1 + ((nOut * ((M * (T_act + 9) + 10) + 2) + 3) + 1) =
        nOut * (M * (T_act + 9) + 12) + 5 := by ring
    omega
  refine ⟨g_fin, vfin,
    fun i hi => by
      rw [ffin i (ne_of_lt_val (by change i.val < 25; exact hi)), hOut_end.2.2.2 i (by omega)],
    hcomb.weaken le_rfl hT_out⟩

def blkParityHitStep (useInOff : Bool) (rInOff : Fin R_emit) :=
  blkCopy rWArg1 rCurWire ;; blkDec1 rWArg1 ;;
  (if useInOff then blkCopy rWArg2 rInOff else blkZero rWArg2) ;;
  blkAdd rWArg2 rColK s0 ;;
  blkEmitXorAt rCurWire rWArg1 rWArg2 ;;
  blkAddConst rCurWire 5

def blkEmitParityRows {Q : Type} (useInOff : Bool) (rOutOff rInOff : Fin R_emit)
    (B_act : RMBlock R_emit Q) :=
  blkCopy rCurWire rPairBase ;;
  blkForRange rRowJ rRowRem rNumOut
    (blkEmitBits3 false true false ;;
     blkInc rCurWire ;;
     blkForRange rColK rColRem rMatCols
       (B_act ;; blkIfZero rMatHit blkNop (blkParityHitStep useInOff rInOff)) ;;
     blkCopy rWArg1 rOutOff ;; blkAdd rWArg1 rRowJ s0 ;;
     blkCopy rWArg2 rCurWire ;; blkDec1 rWArg2 ;;
     blkEmitEqAt rCurWire rWArg1 rWArg2 ;;
     blkAddConst rCurWire 6)

theorem blkEmitParityRows_spec {Q : Type} (useInOff : Bool) (rOutOff rInOff : Fin R_emit)
    (hOut26 : rOutOff.val < 26) (hIn26 : rInOff.val < 26)
    (B_act : RMBlock R_emit Q)
    (active : ℕ → ℕ → Bool) (V T_act : ℕ) (inp : List Bool) (reg₀ : RegState R_emit)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hout_le : reg₀ rOutOff + reg₀ rNumOut ≤ V)
    (hin_le : (if useInOff then reg₀ rInOff else 0) + reg₀ rMatCols ≤ V)
    (hall_le : parityRowStart (reg₀ rPairBase) (reg₀ rMatCols) active (reg₀ rNumOut) ≤ V)
    (hact : ∀ j k reg,
      j < reg₀ rNumOut → k < reg₀ rMatCols →
      reg rRowJ = j → reg rColK = k →
      (∀ i : Fin R_emit, i.val < 26 → reg i = reg₀ i) →
      (∀ i, reg i ≤ V) →
      ∃ reg₁,
        reg₁ rMatHit = (if active j k then 1 else 0) ∧
        (∀ i : Fin R_emit, i.val < 31 → reg₁ i = reg i) ∧
        RMBlockExec B_act V inp reg reg₁ [] T_act) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 26 → reg₁ i = reg₀ i) ∧
      RMBlockExec (blkEmitParityRows useInOff rOutOff rInOff B_act) V inp reg₀ reg₁
        ((List.range (reg₀ rNumOut)).flatMap (fun j =>
          encodeParityRow (reg₀ rPairBase) (reg₀ rMatCols)
            (fun r => reg₀ rOutOff + r)
            (fun k => if useInOff then reg₀ rInOff + k else k)
            active j))
        (reg₀ rNumOut * (reg₀ rMatCols * (T_act + 18 * V + 80) + 20 * V + 110) + 5) := by
  set base := reg₀ rPairBase
  set M := reg₀ rMatCols
  set nOut := reg₀ rNumOut
  set inWire : ℕ → ℕ := fun k => if useInOff then reg₀ rInOff + k else k
  set outWire : ℕ → ℕ := fun r => reg₀ rOutOff + r
  rcases blkCopy_clean rCurWire rPairBase V inp reg₀ hreg₀ with ⟨g0, vc0, fg0, ecp0⟩
  have hg0_nOut : g0 rNumOut = nOut := fg0 rNumOut (by decide)
  set InvOut : ℕ → RegState R_emit → Prop := fun j reg =>
    reg rRowJ = j ∧
    reg rCurWire = parityRowStart base M active j ∧
    (∀ i, reg i ≤ V) ∧
    (∀ i : Fin R_emit, i.val < 26 → reg i = reg₀ i)
  rcases blkForRange_spec rRowJ rRowRem rNumOut (by decide) (by decide)
      _ V (M * (T_act + 18 * V + 80) + 20 * V + 108) inp g0 InvOut
      (fun j => encodeParityRow base M outWire inWire active j)
      ecp0.reg₁_le
      ⟨by rw [regUpd_ne _ (by decide), regUpd_self],
       by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), vc0]; rfl,
       regUpd_le (regUpd_le ecp0.reg₁_le rRowJ (Nat.zero_le V)) rRowRem (ecp0.reg₁_le rNumOut),
       fun i hi => by
         rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 28; omega)),
             regUpd_ne _ (ne_of_lt_val (by change i.val < 27; omega)),
             fg0 i (ne_of_lt_val hi)]⟩
      (fun _ _ hI => hI.2.2.1)
      (fun _ _ hI => hI.1)
      (fun j reg v hv hI =>
        ⟨by rw [regUpd_ne _ (by decide), hI.1],
         by rw [regUpd_ne _ (by decide), hI.2.1],
         regUpd_le hI.2.2.1 rRowRem hv,
         fun i hi => by rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 28; omega)), hI.2.2.2 i hi]⟩)
      (fun j reg hj hI => by
        rw [hg0_nOut] at hj
        have hrow_end_le : parityRowStart base M active (j + 1) ≤ V :=
          le_trans (parityRowStart_mono base M active hj) hall_le
        have hff := blkEmitBits3_spec false true false V inp reg hI.2.2.1
        have hcur1 : reg rCurWire + 1 ≤ V := by
          rw [hI.2.1]; rw [parityRowStart_succ] at hrow_end_le; omega
        rcases blkInc_clean rCurWire V inp reg hI.2.2.1 hcur1 with ⟨r1, vr1, fr1, einc⟩
        have hr1_cols : r1 rMatCols = M := by rw [fr1 rMatCols (by decide), hI.2.2.2 rMatCols (by decide)]
        set rBase := parityRowStart base M active j
        set InvIn : ℕ → RegState R_emit → Prop := fun k rg =>
          rg rColK = k ∧
          rg rRowJ = j ∧
          rg rRowRem = reg rRowRem ∧
          rg rCurWire = rBase + 1 + 5 * prefixHits (active j) k ∧
          (∀ i, rg i ≤ V) ∧
          (∀ i : Fin R_emit, i.val < 26 → rg i = reg₀ i)
        rcases blkForRange_spec rColK rColRem rMatCols (by decide) (by decide)
            (B_act ;; blkIfZero rMatHit blkNop (blkParityHitStep useInOff rInOff))
            V (T_act + (18 * V + 78)) inp r1 InvIn
            (fun k => if active j k then
                let acc := rBase + 5 * prefixHits (active j) k
                encodeXorAt (acc + 1) acc (inWire k)
              else [])
            einc.reg₁_le
            ⟨by rw [regUpd_ne _ (by decide), regUpd_self],
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), fr1 rRowJ (by decide), hI.1],
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), fr1 rRowRem (by decide)],
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), vr1, hI.2.1]; simp [rBase],
             regUpd_le (regUpd_le einc.reg₁_le rColK (Nat.zero_le V)) rColRem (einc.reg₁_le rMatCols),
             fun i hi => by
               rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 30; omega)),
                   regUpd_ne _ (ne_of_lt_val (by change i.val < 29; omega)),
                   fr1 i (ne_of_lt_val hi), hI.2.2.2 i hi]⟩
            (fun _ _ hJ => hJ.2.2.2.2.1)
            (fun _ _ hJ => hJ.1)
            (fun k rg v hv hJ =>
              ⟨by rw [regUpd_ne _ (by decide), hJ.1],
               by rw [regUpd_ne _ (by decide), hJ.2.1],
               by rw [regUpd_ne _ (by decide), hJ.2.2.1],
               by rw [regUpd_ne _ (by decide), hJ.2.2.2.1],
               regUpd_le hJ.2.2.2.2.1 rColRem hv,
               fun i hi => by rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 30; omega)), hJ.2.2.2.2.2 i hi]⟩)
            (fun k rg hk hJ => by
              rw [hr1_cols] at hk
              rcases hact j k rg hj hk hJ.2.1 hJ.1 hJ.2.2.2.2.2 hJ.2.2.2.2.1
                with ⟨rg1, vhit, frg1, eact⟩
              cases hjk : active j k with
              | false =>
                rw [hjk] at vhit
                have ebr := (blkIfZero_zero_spec rMatHit (blkParityHitStep useInOff rInOff) (by simpa using vhit)
                  (blkNop_spec V inp rg1 eact.reg₁_le)).weaken le_rfl (by omega : 2 + 0 ≤ 18 * V + 78)
                refine ⟨rg1,
                  by rw [frg1 rColK (by decide), hJ.1],
                  frg1 rColRem (by decide),
                  ⟨regUpd_self _ _ _,
                   by rw [regUpd_ne _ (by decide), frg1 rRowJ (by decide), hJ.2.1],
                   by rw [regUpd_ne _ (by decide), frg1 rRowRem (by decide), hJ.2.2.1],
                   by rw [regUpd_ne _ (by decide), frg1 rCurWire (by decide), hJ.2.2.2.1,
                          prefixHits_succ, hjk]; simp,
                   regUpd_le eact.reg₁_le rColK (by have := hreg₀ rMatCols; omega),
                   fun i hi => by
                     rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 29; omega)),
                         frg1 i (by omega), hJ.2.2.2.2.2 i hi]⟩,
                  blkSeq_nil_left eact ebr⟩
              | true =>
                rw [hjk] at vhit
                set acc := rBase + 5 * prefixHits (active j) k
                have hrg1_cur : rg1 rCurWire = acc + 1 := by
                  rw [frg1 rCurWire (by decide), hJ.2.2.2.1]; dsimp only [acc]; omega
                have hpk1 : prefixHits (active j) k + 1 ≤ parityRowHits M active j :=
                  prefixHits_succ_le_of_pos hk hjk
                have hacc5 : acc + 6 ≤ V := by
                  dsimp only [acc, rBase]
                  rw [parityRowStart_succ] at hrow_end_le
                  dsimp only [parityRowHits] at hpk1 hrow_end_le
                  omega
                rcases blkCopy_clean rWArg1 rCurWire V inp rg1 eact.reg₁_le with ⟨rg2, vw1_2, frg2, ec1⟩
                rcases blkDec1_clean rWArg1 V inp rg2 ec1.reg₁_le with ⟨rg3, vw1_3, frg3, ed1⟩
                have hrg3_w1 : rg3 rWArg1 = acc := by rw [vw1_3, vw1_2, hrg1_cur]; omega
                have hin_init : ∃ rg4a : RegState R_emit,
                    rg4a rWArg2 = (if useInOff then reg₀ rInOff else 0) ∧
                    (∀ i : Fin R_emit, i ≠ rWArg2 → rg4a i = rg3 i) ∧
                    RMBlockExec (if useInOff then blkCopy rWArg2 rInOff else blkZero rWArg2)
                      V inp rg3 rg4a [] 1 := by
                  cases useInOff with
                  | false =>
                    rcases blkZero_clean rWArg2 V inp rg3 ed1.reg₁_le with ⟨rg4a, vz, fz, ez⟩
                    exact ⟨rg4a, vz, fz, ez⟩
                  | true =>
                    rcases blkCopy_clean rWArg2 rInOff V inp rg3 ed1.reg₁_le with ⟨rg4a, vcp, fcp, ecp⟩
                    have hrg3_in : rg3 rInOff = reg₀ rInOff := by
                      rw [frg3 rInOff (ne_of_lt_val (by change rInOff.val < 32; omega)),
                          frg2 rInOff (ne_of_lt_val (by change rInOff.val < 32; omega)),
                          frg1 rInOff (by omega), hJ.2.2.2.2.2 rInOff hIn26]
                    rw [hrg3_in] at vcp
                    exact ⟨rg4a, vcp, fcp, ecp⟩
                rcases hin_init with ⟨rg4a, vw2_a, frg4a, ein_a⟩
                have hrg4a_k : rg4a rColK = k := by
                  rw [frg4a rColK (by decide), frg3 rColK (by decide),
                      frg2 rColK (by decide), frg1 rColK (by decide), hJ.1]
                rcases blkAdd_clean rWArg2 rColK s0 (by decide) (by decide) V inp rg4a ein_a.reg₁_le
                  (by rw [vw2_a, hrg4a_k]; omega) with ⟨rg4, vw2_4, frg4_add, eaddk⟩
                have hrg4_w2 : rg4 rWArg2 = inWire k := by
                  rw [vw2_4, vw2_a, hrg4a_k]; dsimp only [inWire]; cases useInOff <;> simp
                have frg4 : ∀ i : Fin R_emit, i ≠ rWArg2 → i ≠ s0 → rg4 i = rg3 i :=
                  fun i h1 h2 => by rw [frg4_add i h1 h2, frg4a i h1]
                have ein_w2 := blkSeq_nil_left ein_a eaddk
                have hrg4_cur : rg4 rCurWire = acc + 1 := by
                  rw [frg4 rCurWire (by decide) (by decide), frg3 rCurWire (by decide),
                      frg2 rCurWire (by decide), hrg1_cur]
                have hrg4_w1 : rg4 rWArg1 = acc := by
                  rw [frg4 rWArg1 (by decide) (by decide), hrg3_w1]
                rcases blkEmitXorAt_spec rCurWire rWArg1 rWArg2 (by decide) (by decide) (by decide)
                    V inp rg4 ein_w2.reg₁_le (by rw [hrg4_cur]; omega)
                  with ⟨rg5, frg5, exor⟩
                rw [hrg4_cur, hrg4_w1, hrg4_w2] at exor
                have hrg5_cur : rg5 rCurWire = acc + 1 := by rw [frg5 rCurWire (by decide), hrg4_cur]
                rcases blkAddConst_clean rCurWire 5 V inp rg5 exor.reg₁_le
                  (by rw [hrg5_cur]; omega) with ⟨rg6, vcur6, frg6, ea5⟩
                have hnz_body : RMBlockExec (blkParityHitStep useInOff rInOff) V inp rg1 rg6
                    (encodeXorAt (acc + 1) acc (inWire k))
                    (1 + (1 + (1 + ((2 * V + 2) + (16 * V + 60 + 5))))) :=
                  blkSeq_nil_left ec1 (blkSeq_nil_left ed1
                    (blkSeq_nil_left ein_a (blkSeq_nil_left eaddk (blkSeq_nil_right exor ea5))))
                have ebr := (blkIfZero_pos_spec rMatHit blkNop (by simp [vhit]) hnz_body).weaken
                  le_rfl (by omega : 2 + (1 + (1 + (1 + ((2 * V + 2) + (16 * V + 60 + 5))))) ≤ 18 * V + 78)
                have frg6_31 : ∀ i : Fin R_emit, i ≠ rCurWire → i.val < 31 → rg6 i = rg i :=
                  fun i hic hi31 => by
                    rw [frg6 i hic, frg5 i (by omega),
                        frg4 i (ne_of_lt_val (by change i.val < 33; omega))
                          (ne_of_lt_val (by change i.val < 35; omega)),
                        frg3 i (ne_of_lt_val (by change i.val < 32; omega)),
                        frg2 i (ne_of_lt_val (by change i.val < 32; omega)),
                        frg1 i hi31]
                refine ⟨rg6,
                  by rw [frg6_31 rColK (by decide) (by decide), hJ.1],
                  frg6_31 rColRem (by decide) (by decide),
                  ⟨regUpd_self _ _ _,
                   by rw [regUpd_ne _ (by decide), frg6_31 rRowJ (by decide) (by decide), hJ.2.1],
                   by rw [regUpd_ne _ (by decide), frg6_31 rRowRem (by decide) (by decide), hJ.2.2.1],
                   by rw [regUpd_ne _ (by decide), vcur6, hrg5_cur, prefixHits_succ, hjk]; dsimp only [acc]; simp; omega,
                   regUpd_le ea5.reg₁_le rColK (by have := hreg₀ rMatCols; omega),
                   fun i hi => by
                     rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 29; omega)),
                         frg6_31 i (ne_of_lt_val hi) (by omega), hJ.2.2.2.2.2 i hi]⟩,
                  blkSeq_nil_left eact ebr⟩)
          with ⟨rg_end, _, _, hIn_end, ein_exec⟩
        rw [hr1_cols] at ein_exec hIn_end
        set endXorAcc := rBase + 5 * parityRowHits M active j
        have hrg_cur : rg_end rCurWire = endXorAcc + 1 := by
          rw [hIn_end.2.2.2.1]; dsimp only [endXorAcc, parityRowHits]; omega
        rcases blkCopy_clean rWArg1 rOutOff V inp rg_end hIn_end.2.2.2.2.1 with ⟨q1, vq1, fq1, eqc1⟩
        have hq1_j : q1 rRowJ = j := by rw [fq1 rRowJ (by decide), hIn_end.2.1]
        have hq1_out : q1 rWArg1 = reg₀ rOutOff := by rw [vq1, hIn_end.2.2.2.2.2 rOutOff hOut26]
        rcases blkAdd_clean rWArg1 rRowJ s0 (by decide) (by decide) V inp q1 eqc1.reg₁_le
          (by rw [hq1_out, hq1_j]; omega) with ⟨q2, vq2, fq2, eqadd⟩
        have hq2_w1 : q2 rWArg1 = outWire j := by rw [vq2, hq1_out, hq1_j]
        have hq2_cur : q2 rCurWire = endXorAcc + 1 := by
          rw [fq2 rCurWire (by decide) (by decide), fq1 rCurWire (by decide), hrg_cur]
        rcases blkCopy_clean rWArg2 rCurWire V inp q2 eqadd.reg₁_le with ⟨q3, vq3, fq3, eqc2⟩
        rcases blkDec1_clean rWArg2 V inp q3 eqc2.reg₁_le with ⟨q4, vq4, fq4, eqdec⟩
        have hq4_w2 : q4 rWArg2 = endXorAcc := by rw [vq4, vq3, hq2_cur]; omega
        have hq4_w1 : q4 rWArg1 = outWire j := by rw [fq4 rWArg1 (by decide), fq3 rWArg1 (by decide), hq2_w1]
        have hq4_cur : q4 rCurWire = endXorAcc + 1 := by
          rw [fq4 rCurWire (by decide), fq3 rCurWire (by decide), hq2_cur]
        have heq_cur4 : q4 rCurWire + 4 ≤ V := by
          rw [hq4_cur]; dsimp only [endXorAcc, rBase]; rw [parityRowStart_succ] at hrow_end_le
          dsimp only [parityRowHits] at hrow_end_le; omega
        rcases blkEmitEqAt_spec rCurWire rWArg1 rWArg2 (by decide) (by decide) (by decide)
            V inp q4 eqdec.reg₁_le heq_cur4
          with ⟨q5, fq5, eeq_at⟩
        rw [hq4_cur, hq4_w1, hq4_w2] at eeq_at
        have hq5_cur : q5 rCurWire = endXorAcc + 1 := by rw [fq5 rCurWire (by decide), hq4_cur]
        have hcur6 : q5 rCurWire + 6 ≤ V := by
          rw [hq5_cur]; dsimp only [endXorAcc, rBase]; rw [parityRowStart_succ] at hrow_end_le
          dsimp only [parityRowHits] at hrow_end_le; omega
        rcases blkAddConst_clean rCurWire 6 V inp q5 eeq_at.reg₁_le hcur6 with ⟨q6, vq6, fq6, ea6⟩
        have hrow_comb :=
          blkSeq_spec hff (blkSeq_nil_left einc (blkSeq_spec ein_exec
            (blkSeq_nil_left eqc1 (blkSeq_nil_left eqadd (blkSeq_nil_left eqc2
              (blkSeq_nil_left eqdec (blkSeq_nil_right eeq_at ea6)))))))
        have hrow_out :
            [false, true, false] ++
            (((List.range M).flatMap fun k =>
                if active j k then
                  let acc := rBase + 5 * prefixHits (active j) k
                  encodeXorAt (acc + 1) acc (inWire k)
                else []) ++
              encodeEqAt (endXorAcc + 1) (outWire j) endXorAcc) =
            encodeParityRow base M outWire inWire active j := by
          unfold encodeParityRow; dsimp only [rBase, endXorAcc]; simp only [List.append_assoc]
        rw [hrow_out] at hrow_comb
        have fq6_31 : ∀ i : Fin R_emit, i ≠ rCurWire → i.val < 31 → q6 i = rg_end i :=
          fun i hic hi31 => by
            rw [fq6 i hic, fq5 i (by omega),
                fq4 i (ne_of_lt_val (by change i.val < 33; omega)),
                fq3 i (ne_of_lt_val (by change i.val < 33; omega)),
                fq2 i (ne_of_lt_val (by change i.val < 32; omega))
                  (ne_of_lt_val (by change i.val < 35; omega)),
                fq1 i (ne_of_lt_val (by change i.val < 32; omega))]
        have hT_row :
            3 + (1 + ((M * ((T_act + (18 * V + 78)) + 2) + 3) +
              (1 + ((2 * V + 2) + (1 + (1 + ((18 * V + 80) + 6))))))) ≤
            M * (T_act + 18 * V + 80) + 20 * V + 108 := by
          have hl :
              3 + (1 + ((M * ((T_act + (18 * V + 78)) + 2) + 3) +
                (1 + ((2 * V + 2) + (1 + (1 + ((18 * V + 80) + 6))))))) =
              M * (T_act + 18 * V + 80) + 20 * V + 98 := by ring
          omega
        refine ⟨q6,
          by rw [fq6_31 rRowJ (by decide) (by decide), hIn_end.2.1],
          by rw [fq6_31 rRowRem (by decide) (by decide), hIn_end.2.2.1],
          ⟨regUpd_self _ _ _,
           by rw [regUpd_ne _ (by decide), vq6, hq5_cur]; dsimp only [endXorAcc, rBase]; rw [parityRowStart_succ]; omega,
           regUpd_le ea6.reg₁_le rRowJ (by have := hreg₀ rNumOut; omega),
           fun i hi => by
             rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 27; omega)),
                 fq6_31 i (ne_of_lt_val hi) (by omega), hIn_end.2.2.2.2.2 i hi]⟩,
          hrow_comb.weaken le_rfl hT_row⟩)
    with ⟨g_end, _, _, hOut_end, eout_exec⟩
  rw [hg0_nOut] at eout_exec hOut_end
  have hT_all :
      1 + (nOut * ((M * (T_act + 18 * V + 80) + 20 * V + 108) + 2) + 3) ≤
      nOut * (M * (T_act + 18 * V + 80) + 20 * V + 110) + 5 := by
    have hl :
        1 + (nOut * ((M * (T_act + 18 * V + 80) + 20 * V + 108) + 2) + 3) =
        nOut * (M * (T_act + 18 * V + 80) + 20 * V + 110) + 4 := by ring
    omega
  exact ⟨g_end, hOut_end.2.2.2, (blkSeq_nil_left ecp0 eout_exec).weaken le_rfl hT_all⟩

def blkEmitAllConjs {Q : Type} (B_act : RMBlock R_emit Q) :=
  blkEmitBits3 false false true ;;
  blkCopy rCurWire rPairBase ;;
  blkForRange rRowJ rRowRem rNumOut
    (blkForRange rColK rColRem rMatCols
       (B_act ;; blkIfZero rMatHit blkNop (blkAddConst rCurWire 5)) ;;
     blkAddConst rCurWire 6 ;;
     blkCopy rWArg1 rAllBase ;; blkAdd rWArg1 rRowJ s0 ;;
     blkEmitBits3 true false false ;;
     blkEmitUnary rWArg1 s1 ;;
     blkEmitUnary rCurWire s1 ;;
     blkInc rCurWire)

theorem blkEmitAllConjs_spec {Q : Type} (B_act : RMBlock R_emit Q)
    (active : ℕ → ℕ → Bool) (V T_act : ℕ) (inp : List Bool) (reg₀ : RegState R_emit)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hall_eq : reg₀ rAllBase = parityRowStart (reg₀ rPairBase) (reg₀ rMatCols) active (reg₀ rNumOut))
    (hall_V : reg₀ rAllBase + reg₀ rNumOut ≤ V)
    (hact : ∀ j k reg,
      j < reg₀ rNumOut → k < reg₀ rMatCols →
      reg rRowJ = j → reg rColK = k →
      (∀ i : Fin R_emit, i.val < 26 → reg i = reg₀ i) →
      (∀ i, reg i ≤ V) →
      ∃ reg₁,
        reg₁ rMatHit = (if active j k then 1 else 0) ∧
        (∀ i : Fin R_emit, i.val < 31 → reg₁ i = reg i) ∧
        RMBlockExec B_act V inp reg reg₁ [] T_act) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 26 → reg₁ i = reg₀ i) ∧
      RMBlockExec (blkEmitAllConjs B_act) V inp reg₀ reg₁
        ([false, false, true] ++
         (List.range (reg₀ rNumOut)).flatMap (fun j =>
           [true, false, false] ++
           QCSD_natToUnary (reg₀ rAllBase + j) ++
           QCSD_natToUnary (parityEqWire (reg₀ rPairBase) (reg₀ rMatCols) active j)))
        (reg₀ rNumOut * (reg₀ rMatCols * (T_act + 9) + 6 * V + 26) + 10) := by
  set base := reg₀ rPairBase
  set M := reg₀ rMatCols
  set nOut := reg₀ rNumOut
  have ett := blkEmitBits3_spec false false true V inp reg₀ hreg₀
  rcases blkCopy_clean rCurWire rPairBase V inp reg₀ hreg₀ with ⟨g0, vc0, fg0, ecp0⟩
  have hg0_nOut : g0 rNumOut = nOut := fg0 rNumOut (by decide)
  set InvOut : ℕ → RegState R_emit → Prop := fun j reg =>
    reg rRowJ = j ∧
    reg rCurWire = parityRowStart base M active j ∧
    (∀ i, reg i ≤ V) ∧
    (∀ i : Fin R_emit, i.val < 26 → reg i = reg₀ i)
  rcases blkForRange_spec rRowJ rRowRem rNumOut (by decide) (by decide)
      _ V (M * (T_act + 9) + 6 * V + 24) inp g0 InvOut
      (fun j =>
        [true, false, false] ++
        QCSD_natToUnary (reg₀ rAllBase + j) ++
        QCSD_natToUnary (parityEqWire base M active j))
      ecp0.reg₁_le
      ⟨by rw [regUpd_ne _ (by decide), regUpd_self],
       by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), vc0]; rfl,
       regUpd_le (regUpd_le ecp0.reg₁_le rRowJ (Nat.zero_le V)) rRowRem (ecp0.reg₁_le rNumOut),
       fun i hi => by
         rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 28; omega)),
             regUpd_ne _ (ne_of_lt_val (by change i.val < 27; omega)),
             fg0 i (ne_of_lt_val hi)]⟩
      (fun _ _ hI => hI.2.2.1)
      (fun _ _ hI => hI.1)
      (fun j reg v hv hI =>
        ⟨by rw [regUpd_ne _ (by decide), hI.1],
         by rw [regUpd_ne _ (by decide), hI.2.1],
         regUpd_le hI.2.2.1 rRowRem hv,
         fun i hi => by rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 28; omega)), hI.2.2.2 i hi]⟩)
      (fun j reg hj hI => by
        rw [hg0_nOut] at hj
        have hrow_end_le : parityRowStart base M active (j + 1) ≤ V := by
          have hm := parityRowStart_mono base M active (show j + 1 ≤ nOut by omega)
          have hv : parityRowStart base M active nOut + nOut ≤ V := by rw [← hall_eq]; exact hall_V
          omega
        have hreg_cols : reg rMatCols = M := hI.2.2.2 rMatCols (by decide)
        set rBase := parityRowStart base M active j
        set InvIn : ℕ → RegState R_emit → Prop := fun k rg =>
          rg rColK = k ∧
          rg rRowJ = j ∧
          rg rRowRem = reg rRowRem ∧
          rg rCurWire = rBase + 5 * prefixHits (active j) k ∧
          (∀ i, rg i ≤ V) ∧
          (∀ i : Fin R_emit, i.val < 26 → rg i = reg₀ i)
        rcases blkForRange_spec rColK rColRem rMatCols (by decide) (by decide)
            (B_act ;; blkIfZero rMatHit blkNop (blkAddConst rCurWire 5))
            V (T_act + 7) inp reg InvIn (fun _ => [])
            hI.2.2.1
            ⟨by rw [regUpd_ne _ (by decide), regUpd_self],
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hI.1],
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide)],
             by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), hI.2.1]; simp [rBase],
             regUpd_le (regUpd_le hI.2.2.1 rColK (Nat.zero_le V)) rColRem (hI.2.2.1 rMatCols),
             fun i hi => by
               rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 30; omega)),
                   regUpd_ne _ (ne_of_lt_val (by change i.val < 29; omega)), hI.2.2.2 i hi]⟩
            (fun _ _ hJ => hJ.2.2.2.2.1)
            (fun _ _ hJ => hJ.1)
            (fun k rg v hv hJ =>
              ⟨by rw [regUpd_ne _ (by decide), hJ.1],
               by rw [regUpd_ne _ (by decide), hJ.2.1],
               by rw [regUpd_ne _ (by decide), hJ.2.2.1],
               by rw [regUpd_ne _ (by decide), hJ.2.2.2.1],
               regUpd_le hJ.2.2.2.2.1 rColRem hv,
               fun i hi => by rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 30; omega)), hJ.2.2.2.2.2 i hi]⟩)
            (fun k rg hk hJ => by
              rw [hreg_cols] at hk
              rcases hact j k rg hj hk hJ.2.1 hJ.1 hJ.2.2.2.2.2 hJ.2.2.2.2.1
                with ⟨rg1, vhit, frg1, eact⟩
              cases hjk : active j k with
              | false =>
                rw [hjk] at vhit
                have ebr := (blkIfZero_zero_spec rMatHit (blkAddConst rCurWire 5) vhit
                  (blkNop_spec V inp rg1 eact.reg₁_le)).weaken le_rfl (by omega : 2 + 0 ≤ 7)
                refine ⟨rg1,
                  by rw [frg1 rColK (by decide), hJ.1],
                  frg1 rColRem (by decide),
                  ⟨regUpd_self _ _ _,
                   by rw [regUpd_ne _ (by decide), frg1 rRowJ (by decide), hJ.2.1],
                   by rw [regUpd_ne _ (by decide), frg1 rRowRem (by decide), hJ.2.2.1],
                   by rw [regUpd_ne _ (by decide), frg1 rCurWire (by decide), hJ.2.2.2.1,
                          prefixHits_succ, hjk]; simp,
                   regUpd_le eact.reg₁_le rColK (by have := hreg₀ rMatCols; omega),
                   fun i hi => by
                     rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 29; omega)),
                         frg1 i (by omega), hJ.2.2.2.2.2 i hi]⟩,
                  blkSeq_nil_left eact ebr⟩
              | true =>
                rw [hjk] at vhit
                have hpk1 : prefixHits (active j) k + 1 ≤ parityRowHits M active j :=
                  prefixHits_succ_le_of_pos hk hjk
                have hcur5 : rg1 rCurWire + 5 ≤ V := by
                  rw [frg1 rCurWire (by decide), hJ.2.2.2.1]; dsimp only [rBase]
                  rw [parityRowStart_succ] at hrow_end_le
                  dsimp only [parityRowHits] at hpk1 hrow_end_le; omega
                rcases blkAddConst_clean rCurWire 5 V inp rg1 eact.reg₁_le hcur5
                  with ⟨rg2, vcur2, frg2, ea5⟩
                have ebr := blkIfZero_pos_spec rMatHit blkNop (by simp [vhit]) ea5
                refine ⟨rg2,
                  by rw [frg2 rColK (by decide), frg1 rColK (by decide), hJ.1],
                  by rw [frg2 rColRem (by decide), frg1 rColRem (by decide)],
                  ⟨regUpd_self _ _ _,
                   by rw [regUpd_ne _ (by decide), frg2 rRowJ (by decide), frg1 rRowJ (by decide), hJ.2.1],
                   by rw [regUpd_ne _ (by decide), frg2 rRowRem (by decide), frg1 rRowRem (by decide), hJ.2.2.1],
                   by rw [regUpd_ne _ (by decide), vcur2, frg1 rCurWire (by decide), hJ.2.2.2.1,
                          prefixHits_succ, hjk]; simp; omega,
                   regUpd_le ea5.reg₁_le rColK (by have := hreg₀ rMatCols; omega),
                   fun i hi => by
                     rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 29; omega)),
                         frg2 i (ne_of_lt_val hi), frg1 i (by omega), hJ.2.2.2.2.2 i hi]⟩,
                  blkSeq_nil_left eact ebr⟩)
          with ⟨rg_end, _, _, hIn_end, ein_exec⟩
        have hnil : (List.range (reg rMatCols)).flatMap (fun _ => ([] : List Bool)) = [] := by simp
        rw [hnil, hreg_cols] at ein_exec
        rw [hreg_cols] at hIn_end
        have hcur6 : rg_end rCurWire + 6 ≤ V := by
          rw [hIn_end.2.2.2.1]; dsimp only [rBase]; rw [parityRowStart_succ] at hrow_end_le
          dsimp only [parityRowHits] at hrow_end_le; omega
        rcases blkAddConst_clean rCurWire 6 V inp rg_end hIn_end.2.2.2.2.1 hcur6 with ⟨q1, vq1, fq1, ea6⟩
        have hq1_eqW : q1 rCurWire = parityEqWire base M active j := by
          rw [vq1, hIn_end.2.2.2.1]; unfold parityEqWire parityRowHits; dsimp only [rBase]; omega
        rcases blkCopy_clean rWArg1 rAllBase V inp q1 ea6.reg₁_le with ⟨q2, vq2, fq2, ecpA⟩
        have hq2_w1 : q2 rWArg1 = reg₀ rAllBase := by
          rw [vq2, fq1 rAllBase (by decide), hIn_end.2.2.2.2.2 rAllBase (by decide)]
        have hq2_j : q2 rRowJ = j := by
          rw [fq2 rRowJ (by decide), fq1 rRowJ (by decide), hIn_end.2.1]
        rcases blkAdd_clean rWArg1 rRowJ s0 (by decide) (by decide) V inp q2 ecpA.reg₁_le
          (by rw [hq2_w1, hq2_j]; omega) with ⟨q3, vq3, fq3, eaddj⟩
        have hq3_w1 : q3 rWArg1 = reg₀ rAllBase + j := by rw [vq3, hq2_w1, hq2_j]
        have hq3_cur : q3 rCurWire = parityEqWire base M active j := by
          rw [fq3 rCurWire (by decide) (by decide), fq2 rCurWire (by decide), hq1_eqW]
        have eb3 := blkEmitBits3_spec true false false V inp q3 eaddj.reg₁_le
        rcases blkEmitUnary_clean rWArg1 s1 (by decide) V inp q3 eaddj.reg₁_le with ⟨q4, fq4, eu1⟩
        rw [hq3_w1] at eu1
        have hq4_cur : q4 rCurWire = parityEqWire base M active j := by
          rw [fq4 rCurWire (by decide), hq3_cur]
        rcases blkEmitUnary_clean rCurWire s1 (by decide) V inp q4 eu1.reg₁_le with ⟨q5, fq5, eu2⟩
        rw [hq4_cur] at eu2
        have hq5_cur : q5 rCurWire = parityEqWire base M active j := by
          rw [fq5 rCurWire (by decide), hq4_cur]
        have hcur_inc : q5 rCurWire + 1 ≤ V := by
          rw [hq5_cur, parityEqWire_add_one]; exact hrow_end_le
        rcases blkInc_clean rCurWire V inp q5 eu2.reg₁_le hcur_inc with ⟨q6, vq6, fq6, einc⟩
        have hstep_comb :=
          blkSeq_nil_left ein_exec (blkSeq_nil_left ea6 (blkSeq_nil_left ecpA
            (blkSeq_nil_left eaddj (blkSeq_spec eb3 (blkSeq_spec eu1 (blkSeq_nil_right eu2 einc))))))
        simp only [List.append_assoc] at hstep_comb ⊢
        have fq6_31 : ∀ i : Fin R_emit, i ≠ rCurWire → i.val < 31 → q6 i = rg_end i :=
          fun i hic hi31 => by
            rw [fq6 i hic, fq5 i (ne_of_lt_val (by change i.val < 36; omega)),
                fq4 i (ne_of_lt_val (by change i.val < 36; omega)),
                fq3 i (ne_of_lt_val (by change i.val < 32; omega))
                  (ne_of_lt_val (by change i.val < 35; omega)),
                fq2 i (ne_of_lt_val (by change i.val < 32; omega)),
                fq1 i hic]
        have hT_row :
            (M * ((T_act + 7) + 2) + 3) +
              (6 + (1 + ((2 * V + 2) + (3 + ((2 * V + 3) + ((2 * V + 3) + 1)))))) ≤
            M * (T_act + 9) + 6 * V + 24 := by
          have hl :
              (M * ((T_act + 7) + 2) + 3) +
                (6 + (1 + ((2 * V + 2) + (3 + ((2 * V + 3) + ((2 * V + 3) + 1)))))) =
              M * (T_act + 9) + 6 * V + 22 := by ring
          omega
        refine ⟨q6,
          by rw [fq6_31 rRowJ (by decide) (by decide), hIn_end.2.1],
          by rw [fq6_31 rRowRem (by decide) (by decide), hIn_end.2.2.1],
          ⟨regUpd_self _ _ _,
           by rw [regUpd_ne _ (by decide), vq6, hq5_cur, parityEqWire_add_one],
           regUpd_le einc.reg₁_le rRowJ (by have := hreg₀ rNumOut; omega),
           fun i hi => by
             rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 27; omega)),
                 fq6_31 i (ne_of_lt_val hi) (by omega), hIn_end.2.2.2.2.2 i hi]⟩,
          hstep_comb.weaken le_rfl hT_row⟩)
    with ⟨g_end, _, _, hOut_end, eout_exec⟩
  rw [hg0_nOut] at eout_exec hOut_end
  have hcomb := blkSeq_spec ett (blkSeq_nil_left ecp0 eout_exec)
  simp only [List.append_assoc] at hcomb ⊢
  have hT_all :
      3 + (1 + (nOut * ((M * (T_act + 9) + 6 * V + 24) + 2) + 3)) ≤
      nOut * (M * (T_act + 9) + 6 * V + 26) + 10 := by
    have hl :
        3 + (1 + (nOut * ((M * (T_act + 9) + 6 * V + 24) + 2) + 3)) =
        nOut * (M * (T_act + 9) + 6 * V + 26) + 7 := by ring
    omega
  exact ⟨g_end, hOut_end.2.2.2, hcomb.weaken le_rfl hT_all⟩

def blkEmitLinearSetup {Q : Type} (B_mat : RMBlock R_emit Q) :=
  blkCopy rTotalIn rNumIn ;; blkAdd rTotalIn rNumOut s0 ;;
  blkCopy rPairBase rTotalIn ;;
  blkCopy rMatCols rNumIn ;;
  blkCountAllBase B_mat

def blkEmitLinearBody {Q : Type} (B_mat : RMBlock R_emit Q) :=
  blkEmitUnary rTotalIn s1 ;;
  blkCopy rWArg1 rAllBase ;; blkInc rWArg1 ;; blkAdd rWArg1 rNumOut s0 ;;
  blkEmitUnary rWArg1 s1 ;;
  blkEmitInitInputs ;;
  blkEmitParityRows false rNumIn rNumIn B_mat ;;
  blkEmitAllConjs B_mat

private lemma linearMap_step_bound (numIn numOut T_mat V : ℕ) :
    (2 * V + 10 + numOut * (numIn * (T_mat + 9) + 12)) +
    ((2 * V + 3) + (1 + (1 + ((2 * V + 2) + ((2 * V + 3) +
    (((numIn + numOut) * (2 * V + 8) + 3) +
    ((numOut * (numIn * (T_mat + 18 * V + 80) + 20 * V + 110) + 5) +
    (numOut * (numIn * (T_mat + 9) + 6 * V + 26) + 10)))))))) ≤
    (numOut + 1) * ((numIn + 1) * (3 * T_mat + 20 * V + 100) + 30 * V + 160) := by
  have hrhs :
      (numOut + 1) * ((numIn + 1) * (3 * T_mat + 20 * V + 100) + 30 * V + 160) =
      3 * (numOut * (numIn * T_mat)) + 20 * (numOut * (numIn * V)) + 100 * (numOut * numIn) +
      3 * (numOut * T_mat) + 50 * (numOut * V) + 260 * numOut +
      3 * (numIn * T_mat) + 20 * (numIn * V) + 100 * numIn +
      3 * T_mat + 50 * V + 260 := by ring
  have hlhs :
      (2 * V + 10 + numOut * (numIn * (T_mat + 9) + 12)) +
      ((2 * V + 3) + (1 + (1 + ((2 * V + 2) + ((2 * V + 3) +
      (((numIn + numOut) * (2 * V + 8) + 3) +
      ((numOut * (numIn * (T_mat + 18 * V + 80) + 20 * V + 110) + 5) +
      (numOut * (numIn * (T_mat + 9) + 6 * V + 26) + 10)))))))) =
      3 * (numOut * (numIn * T_mat)) + 18 * (numOut * (numIn * V)) + 98 * (numOut * numIn) +
      28 * (numOut * V) + 156 * numOut + 2 * (numIn * V) + 8 * numIn + 8 * V + 38 := by ring
  omega

/-- Generic `linearMapCheckCircuit` emitter (reads `rNumIn`, `rNumOut`, and matrix oracle `B_mat`).
Preserves all registers `< 22` (`rNumIn`, `rNumOut`, and Tiers 0–1!). -/
def blkEmitLinearMap {Q : Type} (B_mat : RMBlock R_emit Q) :=
  blkEmitLinearSetup B_mat ;; blkEmitLinearBody B_mat

theorem blkEmitLinearMap_spec {Q : Type} (B_mat : RMBlock R_emit Q)
    (mat : ℕ → ℕ → Bool) (V T_mat : ℕ) (inp : List Bool) (reg₀ : RegState R_emit)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hgates_V : parityRowStart (reg₀ rNumIn + reg₀ rNumOut) (reg₀ rNumIn) mat (reg₀ rNumOut) +
                  1 + reg₀ rNumOut ≤ V)
    (hmat : ∀ j k reg,
      j < reg₀ rNumOut → k < reg₀ rNumIn →
      reg rRowJ = j → reg rColK = k →
      (∀ i : Fin R_emit, i.val < 22 → reg i = reg₀ i) →
      (∀ i, reg i ≤ V) →
      ∃ reg₁,
        reg₁ rMatHit = (if mat j k then 1 else 0) ∧
        (∀ i : Fin R_emit, i.val < 31 → reg₁ i = reg i) ∧
        RMBlockExec B_mat V inp reg reg₁ [] T_mat) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 22 → reg₁ i = reg₀ i) ∧
      RMBlockExec (blkEmitLinearMap B_mat) V inp reg₀ reg₁
        (QCSD_encodeCircuit (linearMapCheckCircuit (reg₀ rNumIn) (reg₀ rNumOut) mat))
        ((reg₀ rNumOut + 1) * ((reg₀ rNumIn + 1) * (3 * T_mat + 20 * V + 100) + 30 * V + 160)) := by
  set numIn := reg₀ rNumIn
  set numOut := reg₀ rNumOut
  set totalIn := numIn + numOut
  set allBase := parityRowStart totalIn numIn mat numOut
  have htot_V : totalIn ≤ V := by
    have : totalIn ≤ allBase := parityRowStart_mono totalIn numIn mat (Nat.zero_le numOut)
    omega
  rcases blkCopy_clean rTotalIn rNumIn V inp reg₀ hreg₀ with ⟨g1, vt1, fg1, es1⟩
  rcases blkAdd_clean rTotalIn rNumOut s0 (by decide) (by decide) V inp g1 es1.reg₁_le
    (by rw [vt1, fg1 rNumOut (by decide)]; exact htot_V) with ⟨g2, vt2, fg2, es2⟩
  have hg2_tot : g2 rTotalIn = totalIn := by rw [vt2, vt1, fg1 rNumOut (by decide)]
  rcases blkCopy_clean rPairBase rTotalIn V inp g2 es2.reg₁_le with ⟨g3, vp3, fg3, es3⟩
  rcases blkCopy_clean rMatCols rNumIn V inp g3 es3.reg₁_le with ⟨g4, vm4, fg4, es4⟩
  have fg4_22 : ∀ i : Fin R_emit, i.val < 22 → g4 i = reg₀ i := fun i hi => by
    rw [fg4 i (ne_of_lt_val (by change i.val < 24; omega)),
        fg3 i (ne_of_lt_val (by change i.val < 23; omega)),
        fg2 i (ne_of_lt_val (by change i.val < 22; exact hi))
          (ne_of_lt_val (by change i.val < 35; omega)),
        fg1 i (ne_of_lt_val (by change i.val < 22; exact hi))]
  have hg4_tot : g4 rTotalIn = totalIn := by
    rw [fg4 rTotalIn (by decide), fg3 rTotalIn (by decide), hg2_tot]
  have hg4_pb : g4 rPairBase = totalIn := by rw [fg4 rPairBase (by decide), vp3, hg2_tot]
  have hg4_mc : g4 rMatCols = numIn := by rw [vm4, fg3 rNumIn (by decide), fg2 rNumIn (by decide) (by decide), fg1 rNumIn (by decide)]
  have hg4_no : g4 rNumOut = numOut := fg4_22 rNumOut (by decide)
  rcases blkCountAllBase_spec B_mat mat V T_mat inp g4 es4.reg₁_le
      (by rw [hg4_pb, hg4_mc, hg4_no]; omega)
      (fun j k rg hj hk hrj hrk hfr26 hrg =>
        hmat j k rg (by rw [← hg4_no]; exact hj) (by rw [← hg4_mc]; exact hk) hrj hrk
          (fun i hi => (hfr26 i (by omega)).trans (fg4_22 i hi)) hrg)
    with ⟨g5, vall5, fg5, ecount⟩
  rw [hg4_pb, hg4_mc, hg4_no] at vall5
  rw [hg4_mc, hg4_no] at ecount
  have fg5_25 : ∀ i : Fin R_emit, i.val < 25 → g5 i = g4 i := fg5
  have hg5_tot : g5 rTotalIn = totalIn := by rw [fg5_25 rTotalIn (by decide), hg4_tot]
  rcases blkEmitUnary_clean rTotalIn s1 (by decide) V inp g5 ecount.reg₁_le with ⟨g6, fg6, eu_tot⟩
  rw [hg5_tot] at eu_tot
  rcases blkCopy_clean rWArg1 rAllBase V inp g6 eu_tot.reg₁_le with ⟨g7, vw7, fg7, ecpA⟩
  have hg7_w1 : g7 rWArg1 = allBase := by rw [vw7, fg6 rAllBase (by decide), vall5]
  rcases blkInc_clean rWArg1 V inp g7 ecpA.reg₁_le (by rw [hg7_w1]; omega) with ⟨g8, vw8, fg8, eincA⟩
  have hg8_no : g8 rNumOut = numOut := by
    rw [fg8 rNumOut (by decide), fg7 rNumOut (by decide), fg6 rNumOut (by decide),
        fg5_25 rNumOut (by decide), hg4_no]
  rcases blkAdd_clean rWArg1 rNumOut s0 (by decide) (by decide) V inp g8 eincA.reg₁_le
    (by rw [vw8, hg7_w1, hg8_no]; omega) with ⟨g9, vw9, fg9, eaddA⟩
  have hg9_w1 : g9 rWArg1 = allBase + 1 + numOut := by rw [vw9, vw8, hg7_w1, hg8_no]
  rcases blkEmitUnary_clean rWArg1 s1 (by decide) V inp g9 eaddA.reg₁_le with ⟨g10, fg10, eu_gates⟩
  rw [hg9_w1] at eu_gates
  have fg10_26 : ∀ i : Fin R_emit, i.val < 26 → g10 i = g5 i := fun i hi => by
    rw [fg10 i (ne_of_lt_val (by change i.val < 36; omega)),
        fg9 i (ne_of_lt_val (by change i.val < 32; omega))
          (ne_of_lt_val (by change i.val < 35; omega)),
        fg8 i (ne_of_lt_val (by change i.val < 32; omega)),
        fg7 i (ne_of_lt_val (by change i.val < 32; omega)),
        fg6 i (ne_of_lt_val (by change i.val < 36; omega))]
  rcases blkEmitInitInputs_spec V inp g10 eu_gates.reg₁_le with ⟨g11, fg11, einit⟩
  have hg10_tot : g10 rTotalIn = totalIn := by rw [fg10_26 rTotalIn (by decide), hg5_tot]
  rw [hg10_tot] at einit
  have fg11_26 : ∀ i : Fin R_emit, i.val < 26 → g11 i = g5 i := fun i hi =>
    (fg11 i (by omega)).trans (fg10_26 i hi)
  have hg11_pb : g11 rPairBase = totalIn := by rw [fg11_26 rPairBase (by decide), fg5_25 rPairBase (by decide), hg4_pb]
  have hg11_mc : g11 rMatCols = numIn := by rw [fg11_26 rMatCols (by decide), fg5_25 rMatCols (by decide), hg4_mc]
  have hg11_no : g11 rNumOut = numOut := by rw [fg11_26 rNumOut (by decide), fg5_25 rNumOut (by decide), hg4_no]
  have hg11_ni : g11 rNumIn = numIn := by rw [fg11_26 rNumIn (by decide), fg5_25 rNumIn (by decide), fg4_22 rNumIn (by decide)]
  rcases blkEmitParityRows_spec false rNumIn rNumIn (by decide) (by decide) B_mat mat V T_mat inp g11 einit.reg₁_le
      (by rw [hg11_ni, hg11_no]; exact htot_V)
      (by simp [hg11_mc]; omega)
      (by rw [hg11_pb, hg11_mc, hg11_no]; omega)
      (fun j k rg hj hk hrj hrk hfr26 hrg =>
        hmat j k rg (by rw [← hg11_no]; exact hj) (by rw [← hg11_mc]; exact hk) hrj hrk
          (fun i hi => (hfr26 i (by omega)).trans ((fg11_26 i (by omega)).trans
            ((fg5_25 i (by omega)).trans (fg4_22 i hi)))) hrg)
    with ⟨g12, fg12, erows⟩
  rw [hg11_pb, hg11_mc, hg11_no, hg11_ni] at erows
  have fg12_26 : ∀ i : Fin R_emit, i.val < 26 → g12 i = g5 i := fun i hi =>
    (fg12 i hi).trans (fg11_26 i hi)
  have hg12_pb : g12 rPairBase = totalIn := by rw [fg12_26 rPairBase (by decide), fg5_25 rPairBase (by decide), hg4_pb]
  have hg12_mc : g12 rMatCols = numIn := by rw [fg12_26 rMatCols (by decide), fg5_25 rMatCols (by decide), hg4_mc]
  have hg12_no : g12 rNumOut = numOut := by rw [fg12_26 rNumOut (by decide), fg5_25 rNumOut (by decide), hg4_no]
  have hg12_all : g12 rAllBase = allBase := by rw [fg12_26 rAllBase (by decide), vall5]
  rcases blkEmitAllConjs_spec B_mat mat V T_mat inp g12 erows.reg₁_le
      (by rw [hg12_all, hg12_pb, hg12_mc, hg12_no])
      (by rw [hg12_all, hg12_no]; omega)
      (fun j k rg hj hk hrj hrk hfr26 hrg =>
        hmat j k rg (by rw [← hg12_no]; exact hj) (by rw [← hg12_mc]; exact hk) hrj hrk
          (fun i hi => (hfr26 i (by omega)).trans ((fg12_26 i (by omega)).trans
            ((fg5_25 i (by omega)).trans (fg4_22 i hi)))) hrg)
    with ⟨g13, fg13, econjs⟩
  rw [hg12_all, hg12_pb, hg12_mc, hg12_no] at econjs
  have hsetup : RMBlockExec (blkEmitLinearSetup B_mat) V inp reg₀ g5 []
      (2 * V + 10 + numOut * (numIn * (T_mat + 9) + 12)) :=
    (blkSeq_nil_left es1 (blkSeq_nil_left es2 (blkSeq_nil_left es3 (blkSeq_nil_left es4 ecount)))).weaken
      le_rfl (by omega)
  have hbody :=
    blkSeq_spec eu_tot (blkSeq_nil_left ecpA (blkSeq_nil_left eincA
      (blkSeq_nil_left eaddA (blkSeq_spec eu_gates (blkSeq_spec einit
        (blkSeq_spec erows econjs))))))
  have hcomb := blkSeq_nil_left hsetup hbody
  have hout_eq :
      QCSD_natToUnary totalIn ++
        (QCSD_natToUnary (allBase + 1 + numOut) ++
          ((List.range totalIn).flatMap (fun i => [false, false, false] ++ QCSD_natToUnary i) ++
            ((List.range numOut).flatMap (fun j =>
                encodeParityRow totalIn numIn (fun r => numIn + r)
                  (fun k => if false = true then numIn + k else k) mat j) ++
              ([false, false, true] ++
                (List.range numOut).flatMap (fun j =>
                  [true, false, false] ++ QCSD_natToUnary (allBase + j) ++
                    QCSD_natToUnary (parityEqWire totalIn numIn mat j)))))) =
      QCSD_encodeCircuit (linearMapCheckCircuit numIn numOut mat) := by
    have hfn_id : (fun k : ℕ => if false = true then numIn + k else k) = id := by funext k; rfl
    rw [hfn_id, encodeCircuit_linearMapCheckCircuit]
    dsimp only [totalIn, allBase]
    simp only [List.append_assoc]
  refine ⟨g13, fun i hi => ?_,
    hcomb.congr_out_steps hout_eq (linearMap_step_bound numIn numOut T_mat V)⟩
  rw [fg13 i (by omega), fg12_26 i (by omega), fg5_25 i (by omega), fg4_22 i hi]

/-- Division-free pairwise-conjunction emitter for `(2 * J) × (2 * J)` bilinear circuits
(`rBlkAux1` holds `2 * J`). Preserves all registers `< 27`. -/
def blkEmitPairConjs2J :=
  blkForRange rRowJ rRowRem rBlkAux1
    (blkForRange rColK rColRem rBlkAux1
      (blkCopy rWArg1 rBlkAux1 ;;
       blkAdd rWArg1 rColK s0 ;;
       blkEmitBits3 true false false ;;
       blkEmitUnary rRowJ s1 ;;
       blkEmitUnary rWArg1 s1))

theorem blkEmitPairConjs2J_spec (V : ℕ) (inp : List Bool) (reg₀ : RegState R_emit)
    (hreg₀ : ∀ i, reg₀ i ≤ V) (hpos : 0 < reg₀ rBlkAux1) (h2 : 2 * reg₀ rBlkAux1 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 27 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitPairConjs2J V inp reg₀ reg₁
        ((List.range (reg₀ rBlkAux1 * reg₀ rBlkAux1)).flatMap (fun k =>
          [true, false, false] ++
          QCSD_natToUnary (k / reg₀ rBlkAux1) ++
          QCSD_natToUnary (reg₀ rBlkAux1 + k % reg₀ rBlkAux1)))
        (reg₀ rBlkAux1 * (reg₀ rBlkAux1 * (6 * V + 16) + 5) + 3) := by
  set n1 := reg₀ rBlkAux1
  rcases blkForRange_frame_spec rRowJ rRowRem rBlkAux1 (by decide) (by decide)
      (fun r => r.val < 27) (by decide) (by decide)
      _ V (n1 * (6 * V + 16) + 3) inp reg₀
      (fun i1 => (List.range n1).flatMap (fun i2 =>
        [true, false, false] ++ QCSD_natToUnary i1 ++ QCSD_natToUnary (n1 + i2)))
      hreg₀
      (fun i1 reg _ hi1 hreg hk27 => by
        have hreg_aux : reg rBlkAux1 = n1 := hk27 rBlkAux1 (by decide)
        rcases blkForRange_frame_spec rColK rColRem rBlkAux1 (by decide) (by decide)
            (fun r => r.val < 29) (by decide) (by decide)
            _ V (6 * V + 14) inp reg
            (fun i2 => [true, false, false] ++ QCSD_natToUnary i1 ++ QCSD_natToUnary (n1 + i2))
            hreg
            (fun i2 rg hi2lt hk_eq hrg hk29 => by
              rw [hreg_aux] at hi2lt
              rcases blkCopy_clean rWArg1 rBlkAux1 V inp rg hrg with ⟨q1, vq1, fq1, ec1⟩
              have hq1_w1 : q1 rWArg1 = n1 := by rw [vq1, hk29 rBlkAux1 (by decide), hreg_aux]
              have hq1_k : q1 rColK = i2 := by rw [fq1 rColK (by decide), hk_eq]
              rcases blkAdd_clean rWArg1 rColK s0 (by decide) (by decide) V inp q1 ec1.reg₁_le
                (by rw [hq1_w1, hq1_k]; omega) with ⟨q2, vq2, fq2, ea1⟩
              have hq2_w1 : q2 rWArg1 = n1 + i2 := by rw [vq2, hq1_w1, hq1_k]
              have hq2_j : q2 rRowJ = i1 := by
                rw [fq2 rRowJ (by decide) (by decide), fq1 rRowJ (by decide), hk29 rRowJ (by decide), hi1]
              have eb3 := blkEmitBits3_spec true false false V inp q2 ea1.reg₁_le
              rcases blkEmitUnary_clean rRowJ s1 (by decide) V inp q2 ea1.reg₁_le with ⟨q3, fq3, eu1⟩
              rw [hq2_j] at eu1
              have hq3_w1 : q3 rWArg1 = n1 + i2 := by rw [fq3 rWArg1 (by decide), hq2_w1]
              rcases blkEmitUnary_clean rWArg1 s1 (by decide) V inp q3 eu1.reg₁_le with ⟨q4, fq4, eu2⟩
              rw [hq3_w1] at eu2
              have hc := blkSeq_nil_left ec1 (blkSeq_nil_left ea1 (blkSeq_spec eb3 (blkSeq_spec eu1 eu2)))
              simp only [List.append_assoc] at hc ⊢
              have fq4_31 : ∀ r : Fin R_emit, r.val < 31 → q4 r = rg r := fun r hr => by
                rw [fq4 r (ne_of_lt_val (by change r.val < 36; omega)),
                    fq3 r (ne_of_lt_val (by change r.val < 36; omega)),
                    fq2 r (ne_of_lt_val (by change r.val < 32; omega))
                      (ne_of_lt_val (by change r.val < 35; omega)),
                    fq1 r (ne_of_lt_val (by change r.val < 32; omega))]
              exact ⟨q4,
                by rw [fq4_31 rColK (by decide), hk_eq],
                fq4_31 rColRem (by decide),
                fun r hr => by rw [fq4_31 r (by omega), hk29 r hr],
                hc.weaken le_rfl (by omega)⟩)
          with ⟨rg_end, hfr29, hex_in⟩
        rw [hreg_aux] at hex_in
        exact ⟨rg_end,
          by rw [hfr29 rRowJ (by decide), hi1],
          hfr29 rRowRem (by decide),
          fun r hr => by rw [hfr29 r (by omega), hk27 r hr],
          hex_in⟩)
    with ⟨reg_end, hfr27, hex_out⟩
  rw [← encodePairConjs_nested_loop n1 n1 hpos] at hex_out
  exact ⟨reg_end, hfr27, hex_out⟩

def blkEmitBilinearSetup :=
  blkCopy rNumOut rBlkAux1 ;;
  blkCopy rNumIn rBlkAux1 ;; blkAdd rNumIn rBlkAux1 s0 ;;
  blkCopy rTotalIn rNumIn ;; blkAdd rTotalIn rBlkAux1 s0 ;;
  blkMul rMatCols rBlkAux1 rBlkAux1 s5 s6 ;;
  blkCopy rPairBase rTotalIn ;; blkAdd rPairBase rMatCols s0 ;;
  blkCountAllBase blkRingMulActive

def blkEmitBilinearBody :=
  blkEmitUnary rTotalIn s1 ;;
  blkCopy rWArg1 rAllBase ;; blkInc rWArg1 ;; blkAdd rWArg1 rNumOut s0 ;;
  blkEmitUnary rWArg1 s1 ;;
  blkEmitInitInputs ;;
  blkEmitPairConjs2J ;;
  blkEmitParityRows true rNumIn rTotalIn blkRingMulActive ;;
  blkEmitAllConjs blkRingMulActive

/-- Emitter for `bilinearMapCheckCircuit (2 * J) (2 * J) (2 * J) (ringMulTensor J)`
(assumes `rBlkAux1` holds `2 * reg₀ rJ`). Preserves all registers `< 20`. -/
def blkEmitBilinearRingMul :=
  blkEmitBilinearSetup ;; blkEmitBilinearBody

theorem blkEmitBilinearRingMul_spec (V : ℕ) (inp : List Bool) (reg₀ : RegState R_emit)
    (hreg₀ : ∀ i, reg₀ i ≤ V) (hJpos : 0 < reg₀ rJ)
    (hAux : reg₀ rBlkAux1 = 2 * reg₀ rJ)
    (hgates_V :
      let J := reg₀ rJ
      let pairBase := (2 * J + 2 * J + 2 * J) + (2 * J) * (2 * J)
      let active := fun j k => ringMulTensor J j (k / (2 * J)) (k % (2 * J))
      parityRowStart pairBase ((2 * J) * (2 * J)) active (2 * J) + 1 + 2 * J ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 20 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitBilinearRingMul V inp reg₀ reg₁
        (QCSD_encodeCircuit (bilinearMapCheckCircuit
          (2 * reg₀ rJ) (2 * reg₀ rJ) (2 * reg₀ rJ) (ringMulTensor (reg₀ rJ))))
        ((2 * reg₀ rJ + 1) * (((2 * reg₀ rJ) * (2 * reg₀ rJ) + 1) * (270 * V + 500) + 40 * V + 200)) := by
  set J := reg₀ rJ
  set twoJ := 2 * J
  set totalIn := twoJ + twoJ + twoJ
  set M := twoJ * twoJ
  set pairBase := totalIn + M
  set active := fun j k => ringMulTensor J j (k / twoJ) (k % twoJ)
  set allBase := parityRowStart pairBase M active twoJ
  have hgates_V' : allBase + 1 + twoJ ≤ V := hgates_V
  have hpB_le_all : pairBase ≤ allBase := parityRowStart_mono pairBase M active (Nat.zero_le twoJ)
  have h4J_V : 4 * J ≤ V := by dsimp only [pairBase, totalIn, twoJ] at hpB_le_all; omega
  have htot_V : totalIn ≤ V := by omega
  have hpB_V : pairBase ≤ V := by omega
  rcases blkCopy_clean rNumOut rBlkAux1 V inp reg₀ hreg₀ with ⟨g1, vno1, fg1, es1⟩
  rcases blkCopy_clean rNumIn rBlkAux1 V inp g1 es1.reg₁_le with ⟨g2, vni2, fg2, es2⟩
  have hg2_ni : g2 rNumIn = twoJ := by rw [vni2, fg1 rBlkAux1 (by decide), hAux]
  have hg2_aux : g2 rBlkAux1 = twoJ := by rw [fg2 rBlkAux1 (by decide), fg1 rBlkAux1 (by decide), hAux]
  rcases blkAdd_clean rNumIn rBlkAux1 s0 (by decide) (by decide) V inp g2 es2.reg₁_le
    (by rw [hg2_ni, hg2_aux]; omega) with ⟨g3, vni3, fg3, es3⟩
  have hg3_ni : g3 rNumIn = twoJ + twoJ := by rw [vni3, hg2_ni, hg2_aux]
  rcases blkCopy_clean rTotalIn rNumIn V inp g3 es3.reg₁_le with ⟨g4, vt4, fg4, es4⟩
  have hg4_aux : g4 rBlkAux1 = twoJ := by
    rw [fg4 rBlkAux1 (by decide), fg3 rBlkAux1 (by decide) (by decide), hg2_aux]
  rcases blkAdd_clean rTotalIn rBlkAux1 s0 (by decide) (by decide) V inp g4 es4.reg₁_le
    (by rw [vt4, hg3_ni, hg4_aux]; exact htot_V) with ⟨g5, vt5, fg5, es5⟩
  have hg5_tot : g5 rTotalIn = totalIn := by rw [vt5, vt4, hg3_ni, hg4_aux]
  have hg5_aux : g5 rBlkAux1 = twoJ := by rw [fg5 rBlkAux1 (by decide) (by decide), hg4_aux]
  rcases blkMul_clean rMatCols rBlkAux1 rBlkAux1 s5 s6
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      twoJ V inp g5 es5.reg₁_le (by rw [hg5_aux]) (by rw [hg5_aux])
      (by rw [hg5_aux]; dsimp only [pairBase] at hpB_V; omega)
    with ⟨g6, vmc6, fg6, es6⟩
  have hg6_mc : g6 rMatCols = M := by rw [vmc6, hg5_aux]
  have hg6_tot : g6 rTotalIn = totalIn := by rw [fg6 rTotalIn (by decide) (by decide) (by decide), hg5_tot]
  rcases blkCopy_clean rPairBase rTotalIn V inp g6 es6.reg₁_le with ⟨g7, vpb7, fg7, es7⟩
  have hg7_mc : g7 rMatCols = M := by rw [fg7 rMatCols (by decide), hg6_mc]
  rcases blkAdd_clean rPairBase rMatCols s0 (by decide) (by decide) V inp g7 es7.reg₁_le
    (by rw [vpb7, hg6_tot, hg7_mc]; exact hpB_V) with ⟨g8, vpb8, fg8, es8⟩
  have hg8_pb : g8 rPairBase = pairBase := by rw [vpb8, vpb7, hg6_tot, hg7_mc]
  have fg8_20 : ∀ i : Fin R_emit, i.val < 20 → g8 i = reg₀ i := fun i hi => by
    rw [fg8 i (ne_of_lt_val (by change i.val < 23; omega)) (ne_of_lt_val (by change i.val < 35; omega)),
        fg7 i (ne_of_lt_val (by change i.val < 23; omega)),
        fg6 i (ne_of_lt_val (by change i.val < 24; omega)) (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega)),
        fg5 i (ne_of_lt_val (by change i.val < 22; omega)) (ne_of_lt_val (by change i.val < 35; omega)),
        fg4 i (ne_of_lt_val (by change i.val < 22; omega)),
        fg3 i (ne_of_lt_val (by change i.val < 20; exact hi)) (ne_of_lt_val (by change i.val < 35; omega)),
        fg2 i (ne_of_lt_val (by change i.val < 20; exact hi)),
        fg1 i (ne_of_lt_val (by change i.val < 21; omega))]
  have hg8_ni : g8 rNumIn = twoJ + twoJ := by
    rw [fg8 rNumIn (by decide) (by decide), fg7 rNumIn (by decide),
        fg6 rNumIn (by decide) (by decide) (by decide),
        fg5 rNumIn (by decide) (by decide), fg4 rNumIn (by decide), hg3_ni]
  have hg8_no : g8 rNumOut = twoJ := by
    rw [fg8 rNumOut (by decide) (by decide), fg7 rNumOut (by decide),
        fg6 rNumOut (by decide) (by decide) (by decide),
        fg5 rNumOut (by decide) (by decide), fg4 rNumOut (by decide),
        fg3 rNumOut (by decide) (by decide), fg2 rNumOut (by decide), vno1, hAux]
  have hg8_tot : g8 rTotalIn = totalIn := by
    rw [fg8 rTotalIn (by decide) (by decide), fg7 rTotalIn (by decide), hg6_tot]
  have hg8_mc : g8 rMatCols = M := by rw [fg8 rMatCols (by decide) (by decide), hg7_mc]
  have hact_oracle : ∀ (g_base : RegState R_emit),
      (∀ i : Fin R_emit, i.val < 20 → g_base i = reg₀ i) →
      ∀ j k rg, j < twoJ → k < M → rg rRowJ = j → rg rColK = k →
      (∀ i : Fin R_emit, i.val < 26 → rg i = g_base i) → (∀ i, rg i ≤ V) →
      ∃ rg₁, rg₁ rMatHit = (if active j k then 1 else 0) ∧
        (∀ i : Fin R_emit, i.val < 31 → rg₁ i = rg i) ∧
        RMBlockExec blkRingMulActive V inp rg rg₁ [] (80 * V + 120) := by
    intro g_base hgb j k rg _ hk hrj hrk hfr26 hrg
    have hrg_J : rg rJ = J := (hfr26 rJ (by decide)).trans (hgb rJ (by decide))
    have hrg_aux : rg rBlkAux1 = twoJ := by
      rw [(hfr26 rBlkAux1 (by decide)).trans (hgb rBlkAux1 (by decide)), hAux]
    rcases blkRingMulActive_spec V inp rg hrg (by rw [hrg_J]; exact hJpos)
        (by rw [hrg_aux, hrg_J]) (by rw [hrg_J, hrk]; exact hk) (by rw [hrg_J]; exact h4J_V)
      with ⟨rg₁, vhit, frg₁, eact⟩
    rw [hrg_J, hrj, hrk] at vhit
    exact ⟨rg₁, vhit, frg₁, eact⟩
  rcases blkCountAllBase_spec blkRingMulActive active V (80 * V + 120) inp g8 es8.reg₁_le
      (by rw [hg8_pb, hg8_mc, hg8_no]; omega)
      (fun j k rg hj hk => hact_oracle g8 fg8_20 j k rg (by rw [← hg8_no]; exact hj) (by rw [← hg8_mc]; exact hk))
    with ⟨g9, vall9, fg9, ecount⟩
  rw [hg8_pb, hg8_mc, hg8_no] at vall9
  rw [hg8_mc, hg8_no] at ecount
  have hmul_le_V : twoJ * (2 * twoJ + 3) + 3 ≤ 4 * V + 3 := by
    have hM_V : twoJ * twoJ ≤ V := by dsimp only [pairBase] at hpB_V; omega
    have hexp : twoJ * (2 * twoJ + 3) = 2 * (twoJ * twoJ) + 3 * twoJ := by ring
    omega
  have hsetup : RMBlockExec blkEmitBilinearSetup V inp reg₀ g9 []
      (10 * V + 20 + twoJ * (M * ((80 * V + 120) + 9) + 12)) :=
    (blkSeq_nil_left es1 (blkSeq_nil_left es2 (blkSeq_nil_left es3 (blkSeq_nil_left es4
      (blkSeq_nil_left es5 (blkSeq_nil_left (es6.weaken le_rfl hmul_le_V)
        (blkSeq_nil_left es7 (blkSeq_nil_left es8 ecount)))))))).weaken le_rfl (by omega)
  have hg9_tot : g9 rTotalIn = totalIn := by rw [fg9 rTotalIn (by decide), hg8_tot]
  rcases blkEmitUnary_clean rTotalIn s1 (by decide) V inp g9 ecount.reg₁_le with ⟨g10, fg10, eu_tot⟩
  rw [hg9_tot] at eu_tot
  rcases blkCopy_clean rWArg1 rAllBase V inp g10 eu_tot.reg₁_le with ⟨g11, vw11, fg11, ecpA⟩
  have hg11_w1 : g11 rWArg1 = allBase := by rw [vw11, fg10 rAllBase (by decide), vall9]
  rcases blkInc_clean rWArg1 V inp g11 ecpA.reg₁_le (by rw [hg11_w1]; omega) with ⟨g12, vw12, fg12, eincA⟩
  have hg12_no : g12 rNumOut = twoJ := by
    rw [fg12 rNumOut (by decide), fg11 rNumOut (by decide), fg10 rNumOut (by decide),
        fg9 rNumOut (by decide), hg8_no]
  rcases blkAdd_clean rWArg1 rNumOut s0 (by decide) (by decide) V inp g12 eincA.reg₁_le
    (by rw [vw12, hg11_w1, hg12_no]; omega) with ⟨g13, vw13, fg13, eaddA⟩
  have hg13_w1 : g13 rWArg1 = allBase + 1 + twoJ := by rw [vw13, vw12, hg11_w1, hg12_no]
  rcases blkEmitUnary_clean rWArg1 s1 (by decide) V inp g13 eaddA.reg₁_le with ⟨g14, fg14, eu_gates⟩
  rw [hg13_w1] at eu_gates
  have fg14_26 : ∀ i : Fin R_emit, i.val < 26 → g14 i = g9 i := fun i hi => by
    rw [fg14 i (ne_of_lt_val (by change i.val < 36; omega)),
        fg13 i (ne_of_lt_val (by change i.val < 32; omega)) (ne_of_lt_val (by change i.val < 35; omega)),
        fg12 i (ne_of_lt_val (by change i.val < 32; omega)),
        fg11 i (ne_of_lt_val (by change i.val < 32; omega)),
        fg10 i (ne_of_lt_val (by change i.val < 36; omega))]
  rcases blkEmitInitInputs_spec V inp g14 eu_gates.reg₁_le with ⟨g15, fg15, einit⟩
  have hg14_tot : g14 rTotalIn = totalIn := by rw [fg14_26 rTotalIn (by decide), hg9_tot]
  rw [hg14_tot] at einit
  have fg15_26 : ∀ i : Fin R_emit, i.val < 26 → g15 i = g9 i := fun i hi =>
    (fg15 i (by omega)).trans (fg14_26 i hi)
  have hg15_aux : g15 rBlkAux1 = twoJ := by
    rw [fg15_26 rBlkAux1 (by decide), fg9 rBlkAux1 (by decide), fg8_20 rBlkAux1 (by decide), hAux]
  rcases blkEmitPairConjs2J_spec V inp g15 einit.reg₁_le
      (by rw [hg15_aux]; omega) (by rw [hg15_aux]; dsimp only [twoJ]; omega)
    with ⟨g16, fg16, epairs⟩
  rw [hg15_aux] at epairs
  have fg16_26 : ∀ i : Fin R_emit, i.val < 26 → g16 i = g9 i := fun i hi =>
    (fg16 i (by omega)).trans (fg15_26 i hi)
  have fg16_20 : ∀ i : Fin R_emit, i.val < 20 → g16 i = reg₀ i := fun i hi => by
    rw [fg16_26 i (by omega), fg9 i (by omega), fg8_20 i hi]
  have hg16_pb : g16 rPairBase = pairBase := by rw [fg16_26 rPairBase (by decide), fg9 rPairBase (by decide), hg8_pb]
  have hg16_mc : g16 rMatCols = M := by rw [fg16_26 rMatCols (by decide), fg9 rMatCols (by decide), hg8_mc]
  have hg16_no : g16 rNumOut = twoJ := by rw [fg16_26 rNumOut (by decide), fg9 rNumOut (by decide), hg8_no]
  have hg16_ni : g16 rNumIn = twoJ + twoJ := by rw [fg16_26 rNumIn (by decide), fg9 rNumIn (by decide), hg8_ni]
  have hg16_tot : g16 rTotalIn = totalIn := by rw [fg16_26 rTotalIn (by decide), hg9_tot]
  rcases blkEmitParityRows_spec true rNumIn rTotalIn (by decide) (by decide) blkRingMulActive active
      V (80 * V + 120) inp g16 epairs.reg₁_le
      (by rw [hg16_ni, hg16_no]; exact htot_V)
      (by simp [hg16_tot, hg16_mc]; exact hpB_V)
      (by rw [hg16_pb, hg16_mc, hg16_no]; omega)
      (fun j k rg hj hk => hact_oracle g16 fg16_20 j k rg (by rw [← hg16_no]; exact hj) (by rw [← hg16_mc]; exact hk))
    with ⟨g17, fg17, erows⟩
  rw [hg16_pb, hg16_mc, hg16_no, hg16_ni, hg16_tot] at erows
  have fg17_26 : ∀ i : Fin R_emit, i.val < 26 → g17 i = g9 i := fun i hi =>
    (fg17 i hi).trans (fg16_26 i hi)
  have fg17_20 : ∀ i : Fin R_emit, i.val < 20 → g17 i = reg₀ i := fun i hi => by
    rw [fg17_26 i (by omega), fg9 i (by omega), fg8_20 i hi]
  have hg17_pb : g17 rPairBase = pairBase := by rw [fg17_26 rPairBase (by decide), fg9 rPairBase (by decide), hg8_pb]
  have hg17_mc : g17 rMatCols = M := by rw [fg17_26 rMatCols (by decide), fg9 rMatCols (by decide), hg8_mc]
  have hg17_no : g17 rNumOut = twoJ := by rw [fg17_26 rNumOut (by decide), fg9 rNumOut (by decide), hg8_no]
  have hg17_all : g17 rAllBase = allBase := by rw [fg17_26 rAllBase (by decide), vall9]
  rcases blkEmitAllConjs_spec blkRingMulActive active V (80 * V + 120) inp g17 erows.reg₁_le
      (by rw [hg17_all, hg17_pb, hg17_mc, hg17_no])
      (by rw [hg17_all, hg17_no]; omega)
      (fun j k rg hj hk => hact_oracle g17 fg17_20 j k rg (by rw [← hg17_no]; exact hj) (by rw [← hg17_mc]; exact hk))
    with ⟨g18, fg18, econjs⟩
  rw [hg17_all, hg17_pb, hg17_mc, hg17_no] at econjs
  have hbody :=
    blkSeq_spec eu_tot (blkSeq_nil_left ecpA (blkSeq_nil_left eincA
      (blkSeq_nil_left eaddA (blkSeq_spec eu_gates (blkSeq_spec einit
        (blkSeq_spec epairs (blkSeq_spec erows econjs)))))))
  have hcomb' := blkSeq_nil_left hsetup hbody
  have hfn_in : (fun k : ℕ => if true = true then totalIn + k else k) = (fun k => totalIn + k) := by
    funext k; rfl
  rw [hfn_in] at hcomb'
  have hstream := encodeCircuit_bilinearMapCheckCircuit twoJ twoJ twoJ (ringMulTensor J)
  dsimp only at hstream
  simp only [List.append_assoc] at hstream hcomb'
  rw [← hstream] at hcomb'
  have hT_bound :
      (10 * V + 20 + twoJ * (M * ((80 * V + 120) + 9) + 12)) +
      ((2 * V + 3) + (1 + (1 + ((2 * V + 2) + ((2 * V + 3) +
      ((totalIn * (2 * V + 8) + 3) +
      ((twoJ * (twoJ * (6 * V + 16) + 5) + 3) +
      ((twoJ * (M * ((80 * V + 120) + 18 * V + 80) + 20 * V + 110) + 5) +
      (twoJ * (M * ((80 * V + 120) + 9) + 6 * V + 26) + 10))))))))) ≤
      (twoJ + 1) * ((M + 1) * (270 * V + 500) + 40 * V + 200) := by
    have htot_eq : totalIn = 3 * twoJ := by dsimp only [totalIn]; ring
    rw [htot_eq]
    have hlhs :
        (10 * V + 20 + twoJ * (M * ((80 * V + 120) + 9) + 12)) +
        ((2 * V + 3) + (1 + (1 + ((2 * V + 2) + ((2 * V + 3) +
        (((3 * twoJ) * (2 * V + 8) + 3) +
        ((twoJ * (twoJ * (6 * V + 16) + 5) + 3) +
        ((twoJ * (M * ((80 * V + 120) + 18 * V + 80) + 20 * V + 110) + 5) +
        (twoJ * (M * ((80 * V + 120) + 9) + 6 * V + 26) + 10))))))))) =
        258 * (twoJ * (M * V)) + 458 * (twoJ * M) + 32 * (twoJ * V) + 177 * twoJ +
        6 * (M * V) + 16 * M + 16 * V + 51 := by dsimp only [M]; ring
    have hrhs :
        (twoJ + 1) * ((M + 1) * (270 * V + 500) + 40 * V + 200) =
        270 * (twoJ * (M * V)) + 500 * (twoJ * M) + 310 * (twoJ * V) + 700 * twoJ +
        270 * (M * V) + 500 * M + 310 * V + 700 := by ring
    omega
  refine ⟨g18, fun i hi => ?_, hcomb'.weaken le_rfl hT_bound⟩
  rw [fg18 i (by omega), fg17_20 i hi]

/-!
## Section 5: Verified Emitters for All 19 Vertex Blocks, Parameter Computer, and Full `padNet` Encoder
-/

/-! ### 5.1 Algebraic & Bit-Test Helpers, `ValidTier0`, and Gate/Step Bound Lemmas -/

lemma fwdSt1InIndices_length_tight (n j2 : ℕ) :
    (fwdSt1InIndices n (paramJ n) (paramL2 n) j2).length ≤ paramJ n * paramL1 n := by
  by_cases hj2 : j2 < paramL2 n
  · have hmap := fwdSt1InIndices_eq_map n (paramJ n) (paramL2 n) j2 (paramJ_pos n) hj2
    set cnt := (fwdSt1InIndices n (paramJ n) (paramL2 n) j2).length
    rcases Nat.eq_zero_or_pos cnt with h0 | hpos
    · omega
    · have hmem : fwdIdx (paramJ n) (paramL2 n) j2 (cnt - 1) ∈
          fwdSt1InIndices n (paramJ n) (paramL2 n) j2 := by
        rw [hmap, List.mem_map]
        exact ⟨cnt - 1, List.mem_range.mpr (by omega), rfl⟩
      simp only [fwdSt1InIndices, List.mem_filter, List.mem_range] at hmem
      have hlt_n : fwdIdx (paramJ n) (paramL2 n) j2 (cnt - 1) < n := hmem.1
      have hn_le : n ≤ paramM n * paramJ n := by
        unfold paramM
        have hJ : 0 < paramJ n := paramJ_pos n
        have hdiv := Nat.div_add_mod (n + paramJ n - 1) (paramJ n)
        have hmod : (n + paramJ n - 1) % paramJ n < paramJ n := Nat.mod_lt _ hJ
        have hmul : paramJ n * ((n + paramJ n - 1) / paramJ n) =
            ((n + paramJ n - 1) / paramJ n) * paramJ n := Nat.mul_comm _ _
        omega
      have hM_le_L : paramM n ≤ paramL n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn_pos
        · simp [paramM, paramJ, paramK, minPowExp, minPowExpAux]
        · have hM1 : 1 ≤ paramM n :=
            (Nat.le_div_iff_mul_le (one_le_paramJ n)).2 (by omega)
          have h2M : 2 * paramM n - 1 ≤ paramL n := minPowExp_le_pow (by decide) _
          omega
      have hlt_LJ : fwdIdx (paramJ n) (paramL2 n) j2 (cnt - 1) < (paramL1 n * paramL2 n) * paramJ n := by
        calc
          fwdIdx (paramJ n) (paramL2 n) j2 (cnt - 1) < n := hlt_n
          _ ≤ paramM n * paramJ n := hn_le
          _ ≤ paramL n * paramJ n := Nat.mul_le_mul_right _ hM_le_L
          _ = (paramL1 n * paramL2 n) * paramJ n := by rw [paramL_eq_mul]
      have hdiv1 : ((cnt - 1) / paramJ n) * paramL2 n + j2 < paramL1 n * paramL2 n := by
        have h1 := (fwdIdx_div_mod (paramJ_pos n) (paramL2 n) j2 (cnt - 1)).1
        rw [← h1]
        exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hlt_LJ)
      have hdiv2 : (cnt - 1) / paramJ n < paramL1 n := by
        by_contra hge
        have hle : paramL1 n * paramL2 n ≤ ((cnt - 1) / paramJ n) * paramL2 n :=
          Nat.mul_le_mul_right _ (Nat.le_of_not_lt hge)
        omega
      have hcnt_lt : cnt - 1 < paramL1 n * paramJ n := by
        have hdm := Nat.div_add_mod (cnt - 1) (paramJ n)
        have hmod : (cnt - 1) % paramJ n < paramJ n := Nat.mod_lt _ (paramJ_pos n)
        have hle : ((cnt - 1) / paramJ n + 1) * paramJ n ≤ paramL1 n * paramJ n :=
          Nat.mul_le_mul_right _ hdiv2
        have hexp : ((cnt - 1) / paramJ n + 1) * paramJ n =
            paramJ n * ((cnt - 1) / paramJ n) + paramJ n := by ring
        omega
      have hc : paramL1 n * paramJ n = paramJ n * paramL1 n := Nat.mul_comm _ _
      omega
  · have hemp : fwdSt1InIndices n (paramJ n) (paramL2 n) j2 = [] := by
      unfold fwdSt1InIndices
      rw [List.filter_eq_nil_iff]
      intro idx _
      have hmod : (idx / paramJ n) % paramL2 n < paramL2 n := Nat.mod_lt _ (one_le_paramL2 n)
      simp [show (idx / paramJ n) % paramL2 n ≠ j2 by omega]
    rw [hemp]; simp

lemma filter_range_length_eq_prefixHits (P : ℕ → Bool) :
    ∀ m : ℕ, ((List.range m).filter P).length = prefixHits P m
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.filter_append, prefixHits_succ]
    cases hm : P m <;> simp [List.filter, hm, filter_range_length_eq_prefixHits P m]

private lemma n_succ_le_sq (n : ℕ) : n + 1 ≤ (n + 1) ^ 2 :=
  Nat.le_self_pow (by decide) _

lemma ecopyBits_length_le : ecopyBits.length ≤ 800 := by
  simp only [ecopyBits, encodeXorAt, encodeEqAt, List.length_append, List.length_cons,
             List.length_nil, natToUnary_length]
  omega

lemma testBit_eq_div_pow_mod_two (x b : ℕ) :
    (if x.testBit b then 1 else 0) = (x / 2 ^ b) % 2 := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
  have hm : (x / 2 ^ b) % 2 < 2 := Nat.mod_lt _ (by decide)
  match h : (x / 2 ^ b) % 2 with
  | 0 => rfl
  | 1 => rfl
  | k + 2 => omega

lemma paramJ_mul_L1_le (d : ℕ) : paramJ d * paramL1 d ≤ 16 * (d + 1) :=
  (Nat.mul_le_mul_left _ (paramL1_le_paramL2 d)).trans (paramJ_mul_L2_le d)

lemma paramL1_le (d : ℕ) : paramL1 d ≤ 16 * (d + 1) :=
  (paramL1_le_paramL2 d).trans (paramL2_le d)

lemma paramL1_le_three_J (d : ℕ) : paramL1 d ≤ 3 * paramJ d := by
  have h1 : paramL1 d * 1 ≤ paramL1 d * paramL2 d := Nat.mul_le_mul_left _ (one_le_paramL2 d)
  rw [Nat.mul_one, ← paramL_eq_mul] at h1
  exact h1.trans (paramL_le_three_J d)

lemma paramL2_le_three_J (d : ℕ) : paramL2 d ≤ 3 * paramJ d := by
  have h1 : 1 * paramL2 d ≤ paramL1 d * paramL2 d := Nat.mul_le_mul_right _ (one_le_paramL1 d)
  rw [Nat.one_mul, ← paramL_eq_mul] at h1
  exact h1.trans (paramL_le_three_J d)

lemma dft_gates_le_6000 (numIn numOut n : ℕ) (mat : ℕ → ℕ → Bool)
    (hIn : numIn ≤ 32 * (n + 1)) (hOut : numOut ≤ 32 * (n + 1)) :
    parityRowStart (numIn + numOut) numIn mat numOut + 1 + numOut ≤ 6000 * (n + 1) ^ 2 := by
  have hb := parityRowStart_le_bound (numIn + numOut) numIn numOut mat
  have hprod : numOut * (7 + 5 * numIn) ≤ (32 * (n + 1)) * (7 + 5 * (32 * (n + 1))) :=
    Nat.mul_le_mul hOut (by omega)
  have hexp : (32 * (n + 1)) * (7 + 5 * (32 * (n + 1))) = 5120 * (n + 1) ^ 2 + 224 * (n + 1) := by ring
  have h1 := n_succ_le_sq n
  omega

lemma bilinear_gates_le_6000 (n : ℕ) :
    let J := paramJ n
    let pairBase := (2 * J + 2 * J + 2 * J) + (2 * J) * (2 * J)
    let active := fun j k => ringMulTensor J j (k / (2 * J)) (k % (2 * J))
    parityRowStart pairBase ((2 * J) * (2 * J)) active (2 * J) + 1 + 2 * J ≤ 6000 * (n + 1) ^ 2 := by
  dsimp only
  set J := paramJ n
  set M := (2 * J) * (2 * J)
  set pairBase := (2 * J + 2 * J + 2 * J) + M
  set active := fun j k => ringMulTensor J j (k / (2 * J)) (k % (2 * J))
  have hJ : J ≤ 3 * (n + 1) := paramJ_le_three n
  have hJ2 : J ^ 2 ≤ 9 * (n + 1) := paramJ_sq_le_nine n
  have hM : M ≤ 36 * (n + 1) := by
    have : M = 4 * J ^ 2 := by dsimp only [M]; ring
    omega
  have hb := parityRowStart_le_bound pairBase M (2 * J) active
  have hprod : (2 * J) * (7 + 5 * M) ≤ (6 * (n + 1)) * (7 + 5 * (36 * (n + 1))) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hexp : (6 * (n + 1)) * (7 + 5 * (36 * (n + 1))) = 1080 * (n + 1) ^ 2 + 42 * (n + 1) := by ring
  have h1 := n_succ_le_sq n
  have hpB : pairBase ≤ 54 * (n + 1) := by dsimp only [pairBase]; omega
  omega

/-- Bit-extraction block: sets `rMatHit := if (reg rVal).testBit (reg rBit) then 1 else 0`
while preserving all registers `< 31`. -/
def blkTestBit (rVal rBit : Fin R_emit) :=
  blkSetConst rThreeJ 2 ;;
  blkPow rWArg1 rThreeJ rBit s2 s3 s5 s6 ;;
  blkDivMod rWArg2 s0 rVal rWArg1 s4 s5 s6 ;;
  blkDivMod s0 rMatHit rWArg2 rThreeJ s4 s5 s6

theorem blkTestBit_spec (rVal rBit : Fin R_emit)
    (hVal : rVal.val < 31) (hBit : rBit.val < 31)
    (E V : ℕ) (inp : List Bool) (reg : RegState R_emit)
    (hreg : ∀ i, reg i ≤ V) (h2V : 2 ≤ V)
    (hBitE : reg rBit ≤ E) (hpowV : 2 ^ reg rBit ≤ V) :
    ∃ reg₁ : RegState R_emit,
      reg₁ rMatHit = (if (reg rVal).testBit (reg rBit) then 1 else 0) ∧
      (∀ i : Fin R_emit, i.val < 31 → reg₁ i = reg i) ∧
      RMBlockExec (blkTestBit rVal rBit) V inp reg reg₁ [] ((E + 1) * (35 * V + 30)) := by
  rcases blkSetConst_clean rThreeJ 2 V inp reg hreg h2V with ⟨g1, v3J_1, fg1, es1⟩
  have g1_bit : g1 rBit = reg rBit := fg1 rBit (ne_of_lt_val (by change rBit.val < 34; omega))
  rcases blkPow_clean rWArg1 rThreeJ rBit s2 s3 s5 s6
      (by decide) (ne_of_lt_val (by change rBit.val < 32; omega)).symm
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      E 2 V inp g1 es1.reg₁_le (by omega)
      (by rw [g1_bit]; exact hBitE) (by rw [v3J_1]) (by rw [v3J_1, g1_bit]; exact hpowV)
    with ⟨g2, vp2, fg2, epow⟩
  rw [v3J_1, g1_bit] at vp2
  have g2_val : g2 rVal = reg rVal := by
    rw [fg2 rVal (ne_of_lt_val (by change rVal.val < 32; omega))
          (ne_of_lt_val (by change rVal.val < 37; omega))
          (ne_of_lt_val (by change rVal.val < 38; omega))
          (ne_of_lt_val (by change rVal.val < 40; omega))
          (ne_of_lt_val (by change rVal.val < 41; omega)),
        fg1 rVal (ne_of_lt_val (by change rVal.val < 34; omega))]
  have hpow_pos : 0 < g2 rWArg1 := by rw [vp2]; exact Nat.one_le_pow _ 2 (by decide)
  rcases blkDivMod_clean rWArg2 s0 rVal rWArg1 s4 s5 s6
      (by decide) (ne_of_lt_val (by change rVal.val < 33; omega)).symm
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      V inp g2 hpow_pos epow.reg₁_le
    with ⟨g3, vq3, _, fg3, ediv1⟩
  rw [g2_val, vp2] at vq3
  have g3_3J : g3 rThreeJ = 2 := by
    rw [fg3 rThreeJ (by decide) (by decide) (by decide) (by decide) (by decide),
        fg2 rThreeJ (by decide) (by decide) (by decide) (by decide) (by decide), v3J_1]
  rcases blkDivMod_clean s0 rMatHit rWArg2 rThreeJ s4 s5 s6
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      V inp g3 (by rw [g3_3J]; decide) ediv1.reg₁_le
    with ⟨g4, _, vr4, fg4, ediv2⟩
  rw [vq3, g3_3J, ← testBit_eq_div_pow_mod_two] at vr4
  have hcomb := blkSeq_nil_left es1 (blkSeq_nil_left epow (blkSeq_nil_left ediv1 ediv2))
  have hT : (1 + 2) + ((E * (V * (2 * 2 + 3) + 5) + 4) + ((17 * V + 10) + (17 * V + 10))) ≤
      (E + 1) * (35 * V + 30) := by
    have hl : (1 + 2) + ((E * (V * (2 * 2 + 3) + 5) + 4) + ((17 * V + 10) + (17 * V + 10))) =
        7 * (E * V) + 5 * E + 34 * V + 27 := by ring
    have hr : (E + 1) * (35 * V + 30) = 35 * (E * V) + 30 * E + 35 * V + 30 := by ring
    omega
  refine ⟨g4, vr4, fun i hi => ?_, hcomb.weaken le_rfl hT⟩
  rw [fg4 i (ne_of_lt_val (by change i.val < 35; omega)) (ne_of_lt_val hi)
        (ne_of_lt_val (by change i.val < 39; omega)) (ne_of_lt_val (by change i.val < 40; omega))
        (ne_of_lt_val (by change i.val < 41; omega)),
      fg3 i (ne_of_lt_val (by change i.val < 33; omega)) (ne_of_lt_val (by change i.val < 35; omega))
        (ne_of_lt_val (by change i.val < 39; omega)) (ne_of_lt_val (by change i.val < 40; omega))
        (ne_of_lt_val (by change i.val < 41; omega)),
      fg2 i (ne_of_lt_val (by change i.val < 32; omega)) (ne_of_lt_val (by change i.val < 37; omega))
        (ne_of_lt_val (by change i.val < 38; omega)) (ne_of_lt_val (by change i.val < 40; omega))
        (ne_of_lt_val (by change i.val < 41; omega)),
      fg1 i (ne_of_lt_val (by change i.val < 34; omega))]

/-- Tier 0 (`0..14`) invariant holding all read-only QCSD instance parameters and offsets. -/
def ValidTier0 (n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre : List Bool)
    (inp : List Bool) (reg : RegState R_emit) : Prop :=
  reg rN = n ∧
  reg rPreLen = pre.length ∧
  reg rT0 = t0 ∧
  reg rT1 = t1 ∧
  reg rJ = paramJ n ∧
  reg rL = paramL n ∧
  reg rL1 = paramL1 n ∧
  reg rL2 = paramL2 n ∧
  reg rWExp = paramOmegaExp n ∧
  reg rInvWExp = paramInvOmegaExp n ∧
  reg rTreeLog = treeLog n ∧
  reg rTreeM = treeM n ∧
  (∀ idx (hlt : idx < n), inp.getD (reg rHOff + idx) false = zmod2ToBool (h ⟨idx, hlt⟩)) ∧
  (∀ idx (hlt : idx < n), inp.getD (reg rSOff + idx) false = zmod2ToBool (s ⟨idx, hlt⟩)) ∧
  (∀ v, v < pre.length → inp.getD (reg rPreOff + v) false = pre.getD v false)

lemma ValidTier0.of_frame {n : ℕ} {h s : Fin n → ZMod 2} {t0 t1 : ℕ} {pre inp : List Bool}
    {reg₀ reg₁ : RegState R_emit}
    (hv : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hfr : ∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) :
    ValidTier0 n h s t0 t1 pre inp reg₁ := by
  rcases hv with ⟨h0, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hh, hs, hp⟩
  refine ⟨(hfr rN (by decide)).trans h0,
          (hfr rPreLen (by decide)).trans h4,
          (hfr rT0 (by decide)).trans h5,
          (hfr rT1 (by decide)).trans h6,
          (hfr rJ (by decide)).trans h7,
          (hfr rL (by decide)).trans h8,
          (hfr rL1 (by decide)).trans h9,
          (hfr rL2 (by decide)).trans h10,
          (hfr rWExp (by decide)).trans h11,
          (hfr rInvWExp (by decide)).trans h12,
          (hfr rTreeLog (by decide)).trans h13,
          (hfr rTreeM (by decide)).trans h14, ?_, ?_, ?_⟩
  · rw [hfr rHOff (by decide)]; exact hh
  · rw [hfr rSOff (by decide)]; exact hs
  · rw [hfr rPreOff (by decide)]; exact hp

/-! ### 5.2 Individual Verified Emitters for Vertex Blocks 0 through 11 -/

-- Block 0: `2 * n` prefix-pinned `pinBitCircuit` vertices
def blkEmitBlock0Read :=
  blkCopy rWArg1 rPreOff ;;
  blkAdd rWArg1 rBlkIdx s0 ;;
  blkIfReadIn rWArg1 (blkEmitBits pinBitFalseBits) (blkEmitBits pinBitTrueBits)

def blkEmitBlock0Body :=
  blkCmpLt rMatHit rBlkIdx rPreLen s5 s6 ;;
  blkIfZero rMatHit (blkEmitBits pinBitNoneBits) blkEmitBlock0Read

def blkEmitBlock0 :=
  blkCopy rBlkCnt rN ;;
  blkAdd rBlkCnt rN s0 ;;
  blkForRange rBlkIdx rBlkRem rBlkCnt blkEmitBlock0Body

theorem blkEmitBlock0_spec (n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre inp : List Bool)
    (V : ℕ) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hPreV : reg₀ rPreOff + 2 * n ≤ V)
    (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitBlock0 V inp reg₀ reg₁ (blockStream0 n pre)
        ((n + 1) * (10 * V + 100)) := by
  have h1V : 1 ≤ V := by have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (by omega); omega
  have h2nV : 2 * n ≤ V := by omega
  rcases blkCopy_clean rBlkCnt rN V inp reg₀ hreg₀ with ⟨g1, vc1, fg1, es1⟩
  rw [hT0.1] at vc1
  rcases blkAdd_clean rBlkCnt rN s0 (by decide) (by decide) V inp g1 es1.reg₁_le
    (by rw [vc1, fg1 rN (by decide), hT0.1]; omega) with ⟨g2, vc2, fg2, es2⟩
  have hg2_cnt : g2 rBlkCnt = 2 * n := by rw [vc2, vc1, fg1 rN (by decide), hT0.1]; omega
  have fg2_15 : ∀ i : Fin R_emit, i.val < 15 → g2 i = reg₀ i := fun i hi => by
    rw [fg2 i (ne_of_lt_val hi) (ne_of_lt_val (by change i.val < 35; omega)),
        fg1 i (ne_of_lt_val hi)]
  rcases blkForRange_frame_spec rBlkIdx rBlkRem rBlkCnt (by decide) (by decide)
      (fun r => r.val < 15) (by decide) (by decide)
      blkEmitBlock0Body V (4 * V + 30) inp g2
      (fun v => if v < pre.length then
          if pre.getD v false then pinBitTrueBits else pinBitFalseBits
        else pinBitNoneBits)
      es2.reg₁_le
      (fun v reg hvlt hv_idx hreg hk15 => by
        rw [hg2_cnt] at hvlt
        have hreg_plen : reg rPreLen = pre.length :=
          (hk15 rPreLen (by decide)).trans ((fg2_15 rPreLen (by decide)).trans hT0.2.1)
        have hreg_poff : reg rPreOff = reg₀ rPreOff :=
          (hk15 rPreOff (by decide)).trans (fg2_15 rPreOff (by decide))
        rcases blkCmpLt_clean rMatHit rBlkIdx rPreLen s5 s6
            (by decide) (by decide) (by decide) (by decide) V inp reg hreg h1V
          with ⟨q1, vcmp, fq1, ecmp⟩
        rw [hv_idx, hreg_plen] at vcmp
        have fq1_31 : ∀ r : Fin R_emit, r.val < 31 → q1 r = reg r := fun r hr =>
          fq1 r (ne_of_lt_val hr) (ne_of_lt_val (by change r.val < 40; omega))
            (ne_of_lt_val (by change r.val < 41; omega))
        by_cases hvpre : v < pre.length
        · have hnz : q1 rMatHit ≠ 0 := by rw [vcmp]; simp [hvpre]
          rcases blkCopy_clean rWArg1 rPreOff V inp q1 ecmp.reg₁_le with ⟨q2, vw2, fq2, ecp⟩
          rw [fq1_31 rPreOff (by decide), hreg_poff] at vw2
          have hq2_idx : q2 rBlkIdx = v := by rw [fq2 rBlkIdx (by decide), fq1_31 rBlkIdx (by decide), hv_idx]
          rcases blkAdd_clean rWArg1 rBlkIdx s0 (by decide) (by decide) V inp q2 ecp.reg₁_le
            (by rw [vw2, hq2_idx]; omega) with ⟨q3, vw3, fq3, eadd⟩
          rw [vw2, hq2_idx] at vw3
          have hget : inp.getD (q3 rWArg1) false = pre.getD v false := by
            rw [vw3]; exact hT0.2.2.2.2.2.2.2.2.2.2.2.2.2.2 v hvpre
          have fq3_31 : ∀ r : Fin R_emit, r.val < 31 → q3 r = reg r := fun r hr => by
            rw [fq3 r (ne_of_lt_val (by change r.val < 32; omega))
                  (ne_of_lt_val (by change r.val < 35; omega)),
                fq2 r (ne_of_lt_val (by change r.val < 32; omega)),
                fq1_31 r hr]
          cases hb : pre.getD v false with
          | false =>
            rw [hb] at hget
            have erd := blkIfReadIn_false_spec rWArg1 (blkEmitBits pinBitTrueBits) hget
              (blkEmitBits_spec pinBitFalseBits V inp q3 eadd.reg₁_le)
            have erd_blk : RMBlockExec blkEmitBlock0Read V inp q1 q3 pinBitFalseBits
                (1 + ((2 * V + 2) + (1 + 13))) :=
              blkSeq_nil_left ecp (blkSeq_nil_left eadd erd)
            have eif := blkIfZero_pos_spec rMatHit (blkEmitBits pinBitNoneBits) hnz erd_blk
            have hstep : RMBlockExec blkEmitBlock0Body V inp reg q3
                (if v < pre.length then
                  if false = true then pinBitTrueBits else pinBitFalseBits
                else pinBitNoneBits) (4 * V + 30) :=
              (blkSeq_nil_left ecmp eif).congr_out_steps
                (by simp [hvpre]) (by omega : (2 * V + 6) + (2 + (1 + ((2 * V + 2) + (1 + 13)))) ≤ 4 * V + 30)
            exact ⟨q3, by rw [fq3_31 rBlkIdx (by decide), hv_idx], fq3_31 rBlkRem (by decide),
              fun r hr => (fq3_31 r (by omega)).trans (hk15 r hr), hstep⟩
          | true =>
            rw [hb] at hget
            have erd := blkIfReadIn_true_spec rWArg1 (blkEmitBits pinBitFalseBits) hget
              (blkEmitBits_spec pinBitTrueBits V inp q3 eadd.reg₁_le)
            have erd_blk : RMBlockExec blkEmitBlock0Read V inp q1 q3 pinBitTrueBits
                (1 + ((2 * V + 2) + (1 + 8))) :=
              blkSeq_nil_left ecp (blkSeq_nil_left eadd erd)
            have eif := blkIfZero_pos_spec rMatHit (blkEmitBits pinBitNoneBits) hnz erd_blk
            have hstep : RMBlockExec blkEmitBlock0Body V inp reg q3
                (if v < pre.length then
                  if true = true then pinBitTrueBits else pinBitFalseBits
                else pinBitNoneBits) (4 * V + 30) :=
              (blkSeq_nil_left ecmp eif).congr_out_steps
                (by simp [hvpre]) (by omega : (2 * V + 6) + (2 + (1 + ((2 * V + 2) + (1 + 8)))) ≤ 4 * V + 30)
            exact ⟨q3, by rw [fq3_31 rBlkIdx (by decide), hv_idx], fq3_31 rBlkRem (by decide),
              fun r hr => (fq3_31 r (by omega)).trans (hk15 r hr), hstep⟩
        · have hz : q1 rMatHit = 0 := by rw [vcmp]; simp [hvpre]
          have eif := blkIfZero_zero_spec rMatHit blkEmitBlock0Read hz
            (blkEmitBits_spec pinBitNoneBits V inp q1 ecmp.reg₁_le)
          have hstep : RMBlockExec blkEmitBlock0Body V inp reg q1
              (if v < pre.length then
                if pre.getD v false then pinBitTrueBits else pinBitFalseBits
              else pinBitNoneBits) (4 * V + 30) :=
            (blkSeq_nil_left ecmp eif).congr_out_steps
              (by simp [hvpre]) (by omega : (2 * V + 6) + (2 + 7) ≤ 4 * V + 30)
          exact ⟨q1, by rw [fq1_31 rBlkIdx (by decide), hv_idx], fq1_31 rBlkRem (by decide),
            fun r hr => (fq1_31 r (by omega)).trans (hk15 r hr), hstep⟩)
    with ⟨g_end, hfr_end, eloop⟩
  rw [hg2_cnt] at eloop
  have hcomb := blkSeq_nil_left es1 (blkSeq_nil_left es2 eloop)
  have hT : 1 + ((2 * V + 2) + ((2 * n) * ((4 * V + 30) + 2) + 3)) ≤ (n + 1) * (10 * V + 100) := by
    have hl : 1 + ((2 * V + 2) + ((2 * n) * ((4 * V + 30) + 2) + 3)) =
        8 * (n * V) + 64 * n + 2 * V + 6 := by ring
    have hr : (n + 1) * (10 * V + 100) = 10 * (n * V) + 100 * n + 10 * V + 100 := by ring
    omega
  exact ⟨g_end, fun i hi => (hfr_end i hi).trans (fg2_15 i hi),
    hcomb.congr_out_steps rfl hT⟩

-- Block 1: `2 * n` copies of `ecopyBits`
def blkEmitBlock1 :=
  blkCopy rBlkCnt rN ;;
  blkAdd rBlkCnt rN s0 ;;
  blkForRange rBlkIdx rBlkRem rBlkCnt (blkEmitBits ecopyBits)

theorem blkEmitBlock1_spec (n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre inp : List Bool)
    (V : ℕ) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitBlock1 V inp reg₀ reg₁ (blockStream1 n)
        ((n + 1) * (2 * V + 1800)) := by
  have hn1 := n_succ_le_sq n
  rcases blkCopy_clean rBlkCnt rN V inp reg₀ hreg₀ with ⟨g1, vc1, fg1, es1⟩
  rw [hT0.1] at vc1
  rcases blkAdd_clean rBlkCnt rN s0 (by decide) (by decide) V inp g1 es1.reg₁_le
    (by rw [vc1, fg1 rN (by decide), hT0.1]; omega) with ⟨g2, vc2, fg2, es2⟩
  have hg2_cnt : g2 rBlkCnt = 2 * n := by rw [vc2, vc1, fg1 rN (by decide), hT0.1]; omega
  have fg2_15 : ∀ i : Fin R_emit, i.val < 15 → g2 i = reg₀ i := fun i hi => by
    rw [fg2 i (ne_of_lt_val hi) (ne_of_lt_val (by change i.val < 35; omega)),
        fg1 i (ne_of_lt_val hi)]
  have hlen : ecopyBits.length ≤ 800 := ecopyBits_length_le
  rcases blkForRange_frame_spec rBlkIdx rBlkRem rBlkCnt (by decide) (by decide)
      (fun r => r.val < 15) (by decide) (by decide)
      (blkEmitBits ecopyBits) V 800 inp g2 (fun _ => ecopyBits)
      es2.reg₁_le
      (fun i reg _ hidx hreg hk15 =>
        ⟨reg, hidx, rfl, hk15, (blkEmitBits_spec ecopyBits V inp reg hreg).weaken le_rfl hlen⟩)
    with ⟨g_end, hfr_end, eloop⟩
  rw [hg2_cnt] at eloop
  have hcomb := blkSeq_nil_left es1 (blkSeq_nil_left es2 eloop)
  have hT : 1 + ((2 * V + 2) + ((2 * n) * (800 + 2) + 3)) ≤ (n + 1) * (2 * V + 1800) := by
    have hl : 1 + ((2 * V + 2) + ((2 * n) * (800 + 2) + 3)) = 1604 * n + 2 * V + 6 := by ring
    have hr : (n + 1) * (2 * V + 1800) = 2 * (n * V) + 1800 * n + 2 * V + 1800 := by ring
    omega
  exact ⟨g_end, fun i hi => (hfr_end i hi).trans (fg2_15 i hi),
    hcomb.congr_out_steps rfl hT⟩

-- Block 2: `n` hint-pinned `pinBitCircuit` vertices
def blkEmitBlock2Body :=
  blkCopy rWArg1 rHOff ;;
  blkAdd rWArg1 rBlkIdx s0 ;;
  blkIfReadIn rWArg1 (blkEmitBits pinBitFalseBits) (blkEmitBits pinBitTrueBits)

def blkEmitBlock2 :=
  blkForRange rBlkIdx rBlkRem rN blkEmitBlock2Body

theorem blkEmitBlock2_spec (n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre inp : List Bool)
    (V : ℕ) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hHV : reg₀ rHOff + n ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitBlock2 V inp reg₀ reg₁ (blockStream2 n h)
        ((n + 1) * (2 * V + 30)) := by
  rcases blkForRange_frame_spec rBlkIdx rBlkRem rN (by decide) (by decide)
      (fun r => r.val < 15) (by decide) (by decide)
      blkEmitBlock2Body V (2 * V + 20) inp reg₀
      (fun idx => if hlt : idx < n then
          if zmod2ToBool (h ⟨idx, hlt⟩) then pinBitTrueBits else pinBitFalseBits
        else pinBitFalseBits)
      hreg₀
      (fun idx reg hilt hidx hreg hk15 => by
        rw [hT0.1] at hilt
        rcases blkCopy_clean rWArg1 rHOff V inp reg hreg with ⟨q1, vw1, fq1, ecp⟩
        rw [hk15 rHOff (by decide)] at vw1
        have hq1_idx : q1 rBlkIdx = idx := by rw [fq1 rBlkIdx (by decide), hidx]
        rcases blkAdd_clean rWArg1 rBlkIdx s0 (by decide) (by decide) V inp q1 ecp.reg₁_le
          (by rw [vw1, hq1_idx]; omega) with ⟨q2, vw2, fq2, eadd⟩
        rw [vw1, hq1_idx] at vw2
        have hget : inp.getD (q2 rWArg1) false = zmod2ToBool (h ⟨idx, hilt⟩) := by
          rw [vw2]; exact hT0.2.2.2.2.2.2.2.2.2.2.2.2.1 idx hilt
        have fq2_31 : ∀ r : Fin R_emit, r.val < 31 → q2 r = reg r := fun r hr => by
          rw [fq2 r (ne_of_lt_val (by change r.val < 32; omega))
                (ne_of_lt_val (by change r.val < 35; omega)),
              fq1 r (ne_of_lt_val (by change r.val < 32; omega))]
        cases hb : zmod2ToBool (h ⟨idx, hilt⟩) with
        | false =>
          rw [hb] at hget
          have erd := blkIfReadIn_false_spec rWArg1 (blkEmitBits pinBitTrueBits) hget
            (blkEmitBits_spec pinBitFalseBits V inp q2 eadd.reg₁_le)
          have hstep : RMBlockExec blkEmitBlock2Body V inp reg q2
              (if hlt : idx < n then
                if zmod2ToBool (h ⟨idx, hlt⟩) then pinBitTrueBits else pinBitFalseBits
              else pinBitFalseBits) (2 * V + 20) :=
            (blkSeq_nil_left ecp (blkSeq_nil_left eadd erd)).congr_out_steps
              (by simp [hilt, hb]) (by omega : 1 + ((2 * V + 2) + (1 + 13)) ≤ 2 * V + 20)
          exact ⟨q2, by rw [fq2_31 rBlkIdx (by decide), hidx], fq2_31 rBlkRem (by decide),
            fun r hr => (fq2_31 r (by omega)).trans (hk15 r hr), hstep⟩
        | true =>
          rw [hb] at hget
          have erd := blkIfReadIn_true_spec rWArg1 (blkEmitBits pinBitFalseBits) hget
            (blkEmitBits_spec pinBitTrueBits V inp q2 eadd.reg₁_le)
          have hstep : RMBlockExec blkEmitBlock2Body V inp reg q2
              (if hlt : idx < n then
                if zmod2ToBool (h ⟨idx, hlt⟩) then pinBitTrueBits else pinBitFalseBits
              else pinBitFalseBits) (2 * V + 20) :=
            (blkSeq_nil_left ecp (blkSeq_nil_left eadd erd)).congr_out_steps
              (by simp [hilt, hb]) (by omega : 1 + ((2 * V + 2) + (1 + 8)) ≤ 2 * V + 20)
          exact ⟨q2, by rw [fq2_31 rBlkIdx (by decide), hidx], fq2_31 rBlkRem (by decide),
            fun r hr => (fq2_31 r (by omega)).trans (hk15 r hr), hstep⟩)
    with ⟨g_end, hfr_end, eloop⟩
  rw [hT0.1] at eloop
  have hT : n * ((2 * V + 20) + 2) + 3 ≤ (n + 1) * (2 * V + 30) := by
    have hl : n * ((2 * V + 20) + 2) + 3 = 2 * (n * V) + 22 * n + 3 := by ring
    have hr : (n + 1) * (2 * V + 30) = 2 * (n * V) + 30 * n + 2 * V + 30 := by ring
    omega
  exact ⟨g_end, hfr_end, eloop.congr_out_steps rfl hT⟩

-- Blocks 3 & 5: Forward stage-1 DFT (`L2` circuits of `fwdSt1Mat`)
def blkCountFwdInStep :=
  blkDivMod rWArg1 s0 rRowJ rJ s4 s5 s6 ;;
  blkDivMod s0 rWArg2 rWArg1 rL2 s4 s5 s6 ;;
  blkEqTest rMatHit rWArg2 rBlkIdx ;;
  blkIfZero rMatHit blkNop (blkInc rNumIn)

def blkCountFwdIn :=
  blkZero rNumIn ;;
  blkForRange rRowJ rRowRem rN blkCountFwdInStep

theorem blkCountFwdIn_spec (n : ℕ) (V : ℕ) (inp : List Bool) (reg₀ : RegState R_emit)
    (hreg₀ : ∀ i, reg₀ i ≤ V) (hn_eq : reg₀ rN = n)
    (hJ_eq : reg₀ rJ = paramJ n) (hL2_eq : reg₀ rL2 = paramL2 n)
    (hV : n + 1 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      reg₁ rNumIn = (fwdSt1InIndices n (paramJ n) (paramL2 n) (reg₀ rBlkIdx)).length ∧
      (∀ i : Fin R_emit, i.val < 20 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkCountFwdIn V inp reg₀ reg₁ [] ((n + 1) * (42 * V + 70)) := by
  set j2 := reg₀ rBlkIdx
  set predF : ℕ → Bool := fun idx => decide ((idx / paramJ n) % paramL2 n = j2)
  have h1V : 1 ≤ V := by omega
  rcases blkZero_clean rNumIn V inp reg₀ hreg₀ with ⟨g0, vz0, fg0, ez0⟩
  have hg0_n : g0 rN = n := (fg0 rN (by decide)).trans hn_eq
  set Inv : ℕ → RegState R_emit → Prop := fun idx reg =>
    reg rRowJ = idx ∧
    reg rNumIn = prefixHits predF idx ∧
    (∀ i, reg i ≤ V) ∧
    (∀ i : Fin R_emit, i.val < 20 → reg i = reg₀ i)
  rcases blkForRange_spec rRowJ rRowRem rN (by decide) (by decide)
      blkCountFwdInStep V (40 * V + 55) inp g0 Inv (fun _ => [])
      ez0.reg₁_le
      ⟨by rw [regUpd_ne _ (by decide), regUpd_self],
       by rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide), vz0]; rfl,
       regUpd_le (regUpd_le ez0.reg₁_le rRowJ (Nat.zero_le V)) rRowRem (ez0.reg₁_le rN),
       fun i hi => by
         rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 28; omega)),
             regUpd_ne _ (ne_of_lt_val (by change i.val < 27; omega)),
             fg0 i (ne_of_lt_val hi)]⟩
      (fun _ _ hI => hI.2.2.1)
      (fun _ _ hI => hI.1)
      (fun idx reg v hv hI =>
        ⟨by rw [regUpd_ne _ (by decide), hI.1],
         by rw [regUpd_ne _ (by decide), hI.2.1],
         regUpd_le hI.2.2.1 rRowRem hv,
         fun i hi => by rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 28; omega)), hI.2.2.2 i hi]⟩)
      (fun idx reg hidx_lt hI => by
        rw [hg0_n] at hidx_lt
        have hrJ : reg rJ = paramJ n := (hI.2.2.2 rJ (by decide)).trans hJ_eq
        have hrL2 : reg rL2 = paramL2 n := (hI.2.2.2 rL2 (by decide)).trans hL2_eq
        have hrj2 : reg rBlkIdx = j2 := hI.2.2.2 rBlkIdx (by decide)
        rcases blkDivMod_clean rWArg1 s0 rRowJ rJ s4 s5 s6
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            V inp reg (by rw [hrJ]; exact paramJ_pos n) hI.2.2.1
          with ⟨q1, vq1, _, fq1, ed1⟩
        rw [hI.1, hrJ] at vq1
        have hq1_L2 : q1 rL2 = paramL2 n := by
          rw [fq1 rL2 (by decide) (by decide) (by decide) (by decide) (by decide), hrL2]
        rcases blkDivMod_clean s0 rWArg2 rWArg1 rL2 s4 s5 s6
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)
            V inp q1 (by rw [hq1_L2]; exact one_le_paramL2 n) ed1.reg₁_le
          with ⟨q2, _, vr2, fq2, ed2⟩
        rw [vq1, hq1_L2] at vr2
        have fq2_32 : ∀ r : Fin R_emit, r.val < 32 → q2 r = reg r := fun r hr => by
          rw [fq2 r (ne_of_lt_val (by change r.val < 35; omega))
                (ne_of_lt_val (by change r.val < 33; omega))
                (ne_of_lt_val (by change r.val < 39; omega))
                (ne_of_lt_val (by change r.val < 40; omega))
                (ne_of_lt_val (by change r.val < 41; omega)),
              fq1 r (ne_of_lt_val hr)
                (ne_of_lt_val (by change r.val < 35; omega))
                (ne_of_lt_val (by change r.val < 39; omega))
                (ne_of_lt_val (by change r.val < 40; omega))
                (ne_of_lt_val (by change r.val < 41; omega))]
        rcases blkEqTest_spec rMatHit rWArg2 rBlkIdx (by decide) (by decide) (by decide)
            V inp q2 ed2.reg₁_le h1V
          with ⟨q3, veq3, fq3, eeq⟩
        rw [vr2, fq2_32 rBlkIdx (by decide), hrj2] at veq3
        have fq3_31 : ∀ r : Fin R_emit, r.val < 31 → q3 r = reg r := fun r hr =>
          (fq3 r (ne_of_lt_val hr) (by omega)).trans (fq2_32 r (by omega))
        by_cases hm_eq : (idx / paramJ n) % paramL2 n = j2
        · have hnz : q3 rMatHit ≠ 0 := by rw [veq3]; simp [hm_eq]
          have hph_le : prefixHits predF idx + 1 ≤ V := by
            have := prefixHits_le predF idx; omega
          rcases blkInc_clean rNumIn V inp q3 eeq.reg₁_le
            (by rw [fq3_31 rNumIn (by decide), hI.2.1]; exact hph_le)
            with ⟨q4, vinc4, fq4, einc⟩
          have eif := blkIfZero_pos_spec rMatHit blkNop hnz einc
          have hcomb := (blkSeq_nil_left ed1 (blkSeq_nil_left ed2 (blkSeq_nil_left eeq eif))).weaken
            le_rfl (by omega : (17 * V + 10) + ((17 * V + 10) + ((6 * V + 25) + (2 + 1))) ≤ 40 * V + 55)
          refine ⟨q4,
            by rw [fq4 rRowJ (by decide), fq3_31 rRowJ (by decide), hI.1],
            by rw [fq4 rRowRem (by decide), fq3_31 rRowRem (by decide)],
            ⟨regUpd_self _ _ _,
             by rw [regUpd_ne _ (by decide), vinc4, fq3_31 rNumIn (by decide), hI.2.1, prefixHits_succ]
                dsimp only [predF]; simp [hm_eq],
             regUpd_le einc.reg₁_le rRowJ (by omega),
             fun i hi => by
               rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 27; omega)),
                   fq4 i (ne_of_lt_val hi), fq3_31 i (by omega), hI.2.2.2 i hi]⟩,
            hcomb⟩
        · have hz : q3 rMatHit = 0 := by rw [veq3]; simp [hm_eq]
          have eif := blkIfZero_zero_spec rMatHit (blkInc rNumIn) hz (blkNop_spec V inp q3 eeq.reg₁_le)
          have hcomb := (blkSeq_nil_left ed1 (blkSeq_nil_left ed2 (blkSeq_nil_left eeq eif))).weaken
            le_rfl (by omega : (17 * V + 10) + ((17 * V + 10) + ((6 * V + 25) + (2 + 0))) ≤ 40 * V + 55)
          refine ⟨q3,
            by rw [fq3_31 rRowJ (by decide), hI.1],
            fq3_31 rRowRem (by decide),
            ⟨regUpd_self _ _ _,
             by rw [regUpd_ne _ (by decide), fq3_31 rNumIn (by decide), hI.2.1, prefixHits_succ]
                dsimp only [predF]; simp [hm_eq],
             regUpd_le eeq.reg₁_le rRowJ (by omega),
             fun i hi => by
               rw [regUpd_ne _ (ne_of_lt_val (by change i.val < 27; omega)),
                   fq3_31 i (by omega), hI.2.2.2 i hi]⟩,
            hcomb⟩)
    with ⟨g_end, _, _, hInv_end, eloop⟩
  have hnil : (List.range (g0 rN)).flatMap (fun _ => ([] : List Bool)) = [] := by simp
  rw [hnil, hg0_n] at eloop
  rw [hg0_n] at hInv_end
  have hlen_eq : g_end rNumIn = (fwdSt1InIndices n (paramJ n) (paramL2 n) j2).length := by
    rw [hInv_end.2.1]; unfold fwdSt1InIndices; symm; exact filter_range_length_eq_prefixHits predF n
  have hT : 1 + (n * ((40 * V + 55) + 2) + 3) ≤ (n + 1) * (42 * V + 70) := by
    have hl : 1 + (n * ((40 * V + 55) + 2) + 3) = 40 * (n * V) + 57 * n + 4 := by ring
    have hr : (n + 1) * (42 * V + 70) = 42 * (n * V) + 70 * n + 42 * V + 70 := by ring
    omega
  exact ⟨g_end, hlen_eq, hInv_end.2.2.2, (blkSeq_nil_left ez0 eloop).weaken le_rfl hT⟩

def blkEmitBlock3Step :=
  blkCountFwdIn ;;
  blkCopy rNumOut rBlkAux1 ;;
  blkEmitLinearMap (blkDftUnifiedMat rWExp rJ rL2 rBlkIdx)

def blkEmitBlock3 :=
  blkCopy rWArg1 rJ ;;
  blkAdd rWArg1 rJ s0 ;;
  blkMul rBlkAux1 rWArg1 rL1 s5 s6 ;;
  blkForRange rBlkIdx rBlkRem rL2 blkEmitBlock3Step

def blkEmitBlock5 := blkEmitBlock3

private lemma block3_step_bound (n V : ℕ) (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    let J := paramJ n; let L1 := paramL1 n; let L2 := paramL2 n
    let T_iter := (n + 1) * (42 * V + 70) +
      (1 + (2 * J * L1 + 1) * ((n + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160))
    1 + ((2 * V + 2) + (((16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 3) +
      (L2 * (T_iter + 2) + 3))) ≤
    120000 * (n + 1) ^ 2 * V := by
  intro J L1 L2 T_iter
  have h1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (by omega)
  have hn1 := n_succ_le_sq n
  have h1V : 1 ≤ V := by omega
  have hJL : J * (L1 * L2) ≤ 27 * (n + 1) := by rw [← paramL_eq_mul]; exact paramJ_mul_L_le n
  have hL2 : L2 ≤ 16 * (n + 1) := paramL2_le n
  have hprod_key : L2 * (2 * J * L1 + 1) ≤ 70 * (n + 1) := by
    have heq : L2 * (2 * J * L1 + 1) = 2 * (J * (L1 * L2)) + L2 := by ring
    omega
  have h_inner : (n + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160 ≤
      1550 * ((n + 1) * V) := by
    have hl : (n + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160 =
        500 * ((n + 1) * V) + 850 * (n + 1) + 30 * V + 160 := by ring
    have hnV : n + 1 ≤ (n + 1) * V := Nat.le_mul_of_pos_right _ h1V
    have hVV : V ≤ (n + 1) * V := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h_iter : T_iter + 2 ≤ (115 + 1550 * (2 * J * L1 + 1)) * ((n + 1) * V) := by
    dsimp only [T_iter]
    have h42 : (n + 1) * (42 * V + 70) + 3 ≤ 115 * ((n + 1) * V) := by
      have hl : (n + 1) * (42 * V + 70) + 3 = 42 * ((n + 1) * V) + 70 * (n + 1) + 3 := by ring
      have hnV : n + 1 ≤ (n + 1) * V := Nat.le_mul_of_pos_right _ h1V
      omega
    have hm : (2 * J * L1 + 1) * ((n + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160) ≤
        (2 * J * L1 + 1) * (1550 * ((n + 1) * V)) := Nat.mul_le_mul_left _ h_inner
    have hr : (115 + 1550 * (2 * J * L1 + 1)) * ((n + 1) * V) =
        115 * ((n + 1) * V) + (2 * J * L1 + 1) * (1550 * ((n + 1) * V)) := by ring
    omega
  have h_loop : L2 * (T_iter + 2) ≤ 112000 * ((n + 1) ^ 2 * V) := by
    calc
      L2 * (T_iter + 2) ≤ L2 * ((115 + 1550 * (2 * J * L1 + 1)) * ((n + 1) * V)) :=
        Nat.mul_le_mul_left _ h_iter
      _ = (115 * L2 + 1550 * (L2 * (2 * J * L1 + 1))) * ((n + 1) * V) := by ring
      _ ≤ (115 * (16 * (n + 1)) + 1550 * (70 * (n + 1))) * ((n + 1) * V) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 110340 * ((n + 1) ^ 2 * V) := by ring
      _ ≤ 112000 * ((n + 1) ^ 2 * V) := Nat.mul_le_mul_right _ (by decide)
  have hmul_setup : (16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 6 ≤ V := by
    have : (16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 6 =
        512 * (n + 1) ^ 2 + 48 * (n + 1) + 6 := by ring
    omega
  have h1_sqV : V ≤ (n + 1) ^ 2 * V := Nat.le_mul_of_pos_left V h1
  have h_assoc : 120000 * (n + 1) ^ 2 * V = 120000 * ((n + 1) ^ 2 * V) := by ring
  omega

theorem blkEmitBlock3_spec (n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre inp : List Bool)
    (V : ℕ) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitBlock3 V inp reg₀ reg₁ (blockStream3 n)
        (120000 * (n + 1) ^ 2 * V) := by
  set J := paramJ n; set L1 := paramL1 n; set L2 := paramL2 n; set wExp := paramOmegaExp n
  have hn1_sq := n_succ_le_sq n
  have h2J_le : 2 * J ≤ 16 * (n + 1) := by have := paramJ_le_three n; omega
  have hL1_le : L1 ≤ 16 * (n + 1) := paramL1_le n
  have h2JL1_le : 2 * J * L1 ≤ 32 * (n + 1) := by
    have h := paramJ_mul_L1_le n
    change J * L1 ≤ 16 * (n + 1) at h
    have : 2 * J * L1 = 2 * (J * L1) := by ring
    omega
  rcases blkCopy_clean rWArg1 rJ V inp reg₀ hreg₀ with ⟨g1, vw1, fg1, es1⟩
  rw [hT0.2.2.2.2.1] at vw1
  rcases blkAdd_clean rWArg1 rJ s0 (by decide) (by decide) V inp g1 es1.reg₁_le
    (by rw [vw1, fg1 rJ (by decide), hT0.2.2.2.2.1]; omega) with ⟨g2, vw2, fg2, es2⟩
  have hg2_w1 : g2 rWArg1 = 2 * J := by rw [vw2, vw1, fg1 rJ (by decide), hT0.2.2.2.2.1]; omega
  have hg2_L1 : g2 rL1 = L1 := by
    rw [fg2 rL1 (by decide) (by decide), fg1 rL1 (by decide), hT0.2.2.2.2.2.2.1]
  rcases blkMul_clean rBlkAux1 rWArg1 rL1 s5 s6
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (16 * (n + 1)) V inp g2 es2.reg₁_le
      (by rw [hg2_w1]; exact h2J_le) (by rw [hg2_L1]; exact hL1_le)
      (by rw [hg2_w1, hg2_L1]; omega)
    with ⟨g3, vaux3, fg3, es3⟩
  rw [hg2_w1, hg2_L1] at vaux3
  have fg3_15 : ∀ i : Fin R_emit, i.val < 15 → g3 i = reg₀ i := fun i hi => by
    rw [fg3 i (ne_of_lt_val (by change i.val < 18; omega))
          (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega)),
        fg2 i (ne_of_lt_val (by change i.val < 32; omega))
          (ne_of_lt_val (by change i.val < 35; omega)),
        fg1 i (ne_of_lt_val (by change i.val < 32; omega))]
  set T_iter := (n + 1) * (42 * V + 70) +
    (1 + (2 * J * L1 + 1) * ((n + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160))
  rcases blkForRange_frame_spec rBlkIdx rBlkRem rL2 (by decide) (by decide)
      (fun r => r.val < 15 ∨ r = rBlkAux1) (by decide) (by decide)
      blkEmitBlock3Step V T_iter inp g3
      (fun j2 =>
        let numIn := (fwdSt1InIndices n J L2 j2).length
        QCSD_encodeCircuit (linearMapCheckCircuit numIn (2 * J * L1) (dftUnifiedMat J wExp J L2 j2)))
      es3.reg₁_le
      (fun j2 reg hj2lt hj2_idx hreg hk => by
        rw [fg3_15 rL2 (by decide), hT0.2.2.2.2.2.2.2.1] at hj2lt
        have hr_15 : ∀ i : Fin R_emit, i.val < 15 → reg i = reg₀ i := fun i hi =>
          (hk i (Or.inl hi)).trans (fg3_15 i hi)
        rcases blkCountFwdIn_spec n V inp reg hreg
            (hr_15 rN (by decide) |>.trans hT0.1)
            (hr_15 rJ (by decide) |>.trans hT0.2.2.2.2.1)
            (hr_15 rL2 (by decide) |>.trans hT0.2.2.2.2.2.2.2.1)
            (by omega)
          with ⟨q1, vni1, fq1, ecnt⟩
        rw [hj2_idx] at vni1
        rcases blkCopy_clean rNumOut rBlkAux1 V inp q1 ecnt.reg₁_le with ⟨q2, vno2, fq2, ecp⟩
        have hq2_no : q2 rNumOut = 2 * J * L1 := by
          rw [vno2, fq1 rBlkAux1 (by decide), hk rBlkAux1 (Or.inr rfl), vaux3]
        have hq2_ni : q2 rNumIn = (fwdSt1InIndices n J L2 j2).length :=
          (fq2 rNumIn (by decide)).trans vni1
        have fq2_20 : ∀ i : Fin R_emit, i.val < 20 → q2 i = reg i := fun i hi =>
          (fq2 i (ne_of_lt_val (by change i.val < 21; omega))).trans (fq1 i hi)
        have hni_le_n : q2 rNumIn ≤ n := by rw [hq2_ni]; exact fwdSt1InIndices_length_le_n n J L2 j2
        have hni_le_JL1 : q2 rNumIn ≤ J * L1 := by rw [hq2_ni]; exact fwdSt1InIndices_length_tight n j2
        rcases blkEmitLinearMap_spec (blkDftUnifiedMat rWExp rJ rL2 rBlkIdx)
            (dftUnifiedMat J wExp J L2 j2) V (160 * V + 250) inp q2 ecp.reg₁_le
            (by
              have hg := dft_gates_le_6000 (q2 rNumIn) (q2 rNumOut) n (dftUnifiedMat J wExp J L2 j2)
                (by omega) (by rw [hq2_no]; exact h2JL1_le)
              omega)
            (fun r k rg hr hk_lt hrr hrk hfr22 hrg => by
              have hrg_20 : ∀ i : Fin R_emit, i.val < 20 → rg i = reg i := fun i hi =>
                (hfr22 i (by omega)).trans (fq2_20 i hi)
              have hrg_15 : ∀ i : Fin R_emit, i.val < 15 → rg i = reg₀ i := fun i hi =>
                (hrg_20 i (by omega)).trans (hr_15 i hi)
              have hrg_J : rg rJ = J := (hrg_15 rJ (by decide)).trans hT0.2.2.2.2.1
              have hrg_W : rg rWExp = wExp := (hrg_15 rWExp (by decide)).trans hT0.2.2.2.2.2.2.2.2.1
              have hrg_L2 : rg rL2 = L2 := (hrg_15 rL2 (by decide)).trans hT0.2.2.2.2.2.2.2.1
              have hrg_j2 : rg rBlkIdx = j2 := (hrg_20 rBlkIdx (by decide)).trans hj2_idx
              have hqOut : r / (2 * J) < L1 := by
                rw [hq2_no] at hr
                exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hr)
              have hqIn : k / J < L1 := by
                have hkJL : k < J * L1 := lt_of_lt_of_le hk_lt hni_le_JL1
                exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hkJL)
              have hL1_3J : L1 ≤ 3 * J := paramL1_le_three_J n
              have hL2_3J : L2 ≤ 3 * J := paramL2_le_three_J n
              have hr_bound : L2 * (k / J) + j2 ≤ 3 * J := by
                have hm : L2 * (k / J + 1) ≤ L2 * L1 := Nat.mul_le_mul_left L2 hqIn
                have he : L2 * (k / J + 1) = L2 * (k / J) + L2 := by ring
                have hmulL : L2 * L1 = paramL n := by rw [Nat.mul_comm, ← paramL_eq_mul]
                have hL3J : paramL n ≤ 3 * J := paramL_le_three_J n
                omega
              rcases blkDftUnifiedMat_spec rWExp rJ rL2 rBlkIdx
                  (by decide) (by decide) (by decide) (by decide)
                  V inp rg hrg
                  (by rw [hrg_J]; exact paramJ_pos n)
                  (by rw [hrg_J]; exact paramJ_pos n)
                  (by rw [hrg_J]; omega)
                  (by rw [hrg_W, hrg_J]; exact paramOmegaExp_le_three_J n)
                  (by rw [hrg_L2, hrg_J]; exact hL2_3J)
                  (by rw [hrr, hrg_J]; omega)
                  (by rw [hrk, hrg_J]; omega)
                  (by rw [hrg_L2, hrk, hrg_J, hrg_j2]; exact hr_bound)
                  (by rw [hrg_J]; have hJ2 : J ^ 2 ≤ 9 * (n + 1) := paramJ_sq_le_nine n; omega)
                with ⟨rg₁, vhit, frg₁, edft⟩
              rw [hrg_J, hrg_W, hrg_L2, hrg_j2, hrr, hrk] at vhit
              exact ⟨rg₁, vhit, frg₁, edft⟩)
          with ⟨q3, fq3, elin⟩
        rw [hq2_ni, hq2_no] at elin
        have fq3_20 : ∀ i : Fin R_emit, i.val < 20 → q3 i = reg i := fun i hi =>
          (fq3 i (by omega)).trans (fq2_20 i hi)
        have hlin_T :
            (2 * J * L1 + 1) * (((fwdSt1InIndices n J L2 j2).length + 1) *
              (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160) ≤
            (2 * J * L1 + 1) * ((n + 1) *
              (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160) := by
          apply Nat.mul_le_mul_left
          apply Nat.add_le_add_right
          apply Nat.add_le_add_right
          apply Nat.mul_le_mul_right
          have := fwdSt1InIndices_length_le_n n J L2 j2
          omega
        have elin' := elin.weaken le_rfl hlin_T
        exact ⟨q3,
          by rw [fq3_20 rBlkIdx (by decide), hj2_idx],
          fq3_20 rBlkRem (by decide),
          fun r hr => (fq3_20 r (by rcases hr with h | rfl <;> [omega; decide])).trans (hk r hr),
          blkSeq_nil_left ecnt (blkSeq_nil_left ecp elin')⟩)
    with ⟨g_end, hfr_end, eloop⟩
  rw [fg3_15 rL2 (by decide), hT0.2.2.2.2.2.2.2.1] at eloop
  have hcomb := blkSeq_nil_left es1 (blkSeq_nil_left es2 (blkSeq_nil_left es3 eloop))
  exact ⟨g_end, fun i hi => (hfr_end i (Or.inl hi)).trans (fg3_15 i hi),
    hcomb.congr_out_steps rfl (block3_step_bound n V hV)⟩

theorem blkEmitBlock5_spec (n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre inp : List Bool)
    (V : ℕ) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitBlock5 V inp reg₀ reg₁ (blockStream5 n)
        (120000 * (n + 1) ^ 2 * V) :=
  blkEmitBlock3_spec n h s t0 t1 pre inp V reg₀ hT0 hreg₀ hV

-- Blocks 4, 6, and 9: Stage-2 DFT (`L1` circuits of `st2Mat`, parameterized by `rWParam`)
def blkEmitSt2 (rWParam : Fin R_emit) :=
  blkCopy rBlkAux1 rJ ;;
  blkAdd rBlkAux1 rJ s0 ;;
  blkZero rBlkAux2 ;;
  blkMul rNumIn rBlkAux1 rL2 s5 s6 ;;
  blkCopy rNumOut rNumIn ;;
  blkForRange rBlkIdx rBlkRem rL1
    (blkEmitLinearMap (blkDftUnifiedMat rWParam rBlkAux1 rL1 rBlkAux2))

def blkEmitBlock4 := blkEmitSt2 rWExp
def blkEmitBlock6 := blkEmitSt2 rWExp
def blkEmitBlock9 := blkEmitSt2 rInvWExp

private lemma st2_step_bound (n V : ℕ) (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    let J := paramJ n; let L1 := paramL1 n; let L2 := paramL2 n
    let d := 2 * J * L2
    let T_iter := (d + 1) * ((d + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160)
    1 + ((2 * V + 2) + (1 + (((16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 3) +
      (1 + (L1 * (T_iter + 2) + 3))))) ≤
    3000000 * (n + 1) ^ 2 * V := by
  intro J L1 L2 d T_iter
  have h1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (by omega)
  have hn1 := n_succ_le_sq n
  have h1V : 1 ≤ V := by omega
  have hJL : J * (L1 * L2) ≤ 27 * (n + 1) := by rw [← paramL_eq_mul]; exact paramJ_mul_L_le n
  have hJL2 : J * L2 ≤ 16 * (n + 1) := paramJ_mul_L2_le n
  have hL1 : L1 ≤ 16 * (n + 1) := paramL1_le n
  have hL1_d2 : L1 * (d + 1) * (d + 1) ≤ 1900 * (n + 1) ^ 2 := by
    have heq : L1 * (d + 1) * (d + 1) =
        4 * ((J * (L1 * L2)) * (J * L2)) + 4 * (J * (L1 * L2)) + L1 := by
      dsimp only [d]; ring
    have hm : (J * (L1 * L2)) * (J * L2) ≤ (27 * (n + 1)) * (16 * (n + 1)) :=
      Nat.mul_le_mul hJL hJL2
    have hm_exp : (27 * (n + 1)) * (16 * (n + 1)) = 432 * (n + 1) ^ 2 := by ring
    omega
  have h_unit : T_iter + 2 ≤ (d + 1) * (d + 1) * (1550 * V) := by
    dsimp only [T_iter]
    have hd1 : 1 ≤ (d + 1) * (d + 1) := Nat.mul_pos (by omega) (by omega)
    have hu1 : 3 * (160 * V + 250) + 20 * V + 100 ≤ 1350 * V := by omega
    have hu2 : 30 * V + 160 ≤ 190 * ((d + 1) * V) := by
      have : V ≤ (d + 1) * V := Nat.le_mul_of_pos_left V (by omega)
      omega
    have hinner : (d + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160 ≤
        (d + 1) * (1540 * V) := by
      have h_m : (d + 1) * (3 * (160 * V + 250) + 20 * V + 100) ≤ (d + 1) * (1350 * V) :=
        Nat.mul_le_mul_left _ hu1
      have h_r : (d + 1) * (1540 * V) = (d + 1) * (1350 * V) + 190 * ((d + 1) * V) := by ring
      omega
    have hm2 : (d + 1) * ((d + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160) ≤
        (d + 1) * ((d + 1) * (1540 * V)) := Nat.mul_le_mul_left _ hinner
    have h2_le : 2 ≤ 10 * ((d + 1) * (d + 1) * V) := by
      have : 1 ≤ (d + 1) * (d + 1) * V := Nat.mul_pos hd1 h1V
      omega
    have hr : (d + 1) * (d + 1) * (1550 * V) =
        (d + 1) * ((d + 1) * (1540 * V)) + 10 * ((d + 1) * (d + 1) * V) := by ring
    rw [hr]; exact Nat.add_le_add hm2 h2_le
  have h_loop : L1 * (T_iter + 2) ≤ 2945000 * ((n + 1) ^ 2 * V) := by
    calc
      L1 * (T_iter + 2) ≤ L1 * ((d + 1) * (d + 1) * (1550 * V)) := Nat.mul_le_mul_left _ h_unit
      _ = (L1 * (d + 1) * (d + 1)) * (1550 * V) := by ring
      _ ≤ (1900 * (n + 1) ^ 2) * (1550 * V) := Nat.mul_le_mul_right _ hL1_d2
      _ = 2945000 * ((n + 1) ^ 2 * V) := by ring
  have hmul_setup : 1 + ((2 * V + 2) + (1 + (((16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 3) + 4))) ≤
      5 * ((n + 1) ^ 2 * V) := by
    have hs : (16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 11 ≤ V := by
      have : (16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 11 =
          512 * (n + 1) ^ 2 + 48 * (n + 1) + 11 := by ring
      omega
    have h1_sqV : V ≤ (n + 1) ^ 2 * V := Nat.le_mul_of_pos_left V h1
    omega
  calc
    1 + ((2 * V + 2) + (1 + (((16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 3) +
      (1 + (L1 * (T_iter + 2) + 3)))))
        = (1 + ((2 * V + 2) + (1 + (((16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 3) + 4)))) +
            L1 * (T_iter + 2) := by ring
    _ ≤ 5 * ((n + 1) ^ 2 * V) + 2945000 * ((n + 1) ^ 2 * V) := Nat.add_le_add hmul_setup h_loop
    _ = 2945005 * ((n + 1) ^ 2 * V) := by ring
    _ ≤ 3000000 * ((n + 1) ^ 2 * V) := Nat.mul_le_mul_right _ (by decide)
    _ = 3000000 * (n + 1) ^ 2 * V := by ring

theorem blkEmitSt2_spec (rWParam : Fin R_emit) (hWP : rWParam.val < 15)
    (n wVal : ℕ) (inp : List Bool) (V : ℕ) (reg₀ : RegState R_emit)
    (hJ_eq : reg₀ rJ = paramJ n)
    (hL1_eq : reg₀ rL1 = paramL1 n)
    (hL2_eq : reg₀ rL2 = paramL2 n)
    (hW_eq : reg₀ rWParam = wVal)
    (hW_le : wVal ≤ 3 * paramJ n)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMBlockExec (blkEmitSt2 rWParam) V inp reg₀ reg₁
        ((List.range (paramL1 n)).flatMap (fun _ =>
          QCSD_encodeCircuit (linearMapCheckCircuit (2 * paramJ n * paramL2 n)
            (2 * paramJ n * paramL2 n)
            (dftUnifiedMat (paramJ n) wVal (2 * paramJ n) (paramL1 n) 0))))
        (3000000 * (n + 1) ^ 2 * V) := by
  set J := paramJ n; set L1 := paramL1 n; set L2 := paramL2 n; set d := 2 * J * L2
  have hn1_sq := n_succ_le_sq n
  have h2J_le : 2 * J ≤ 16 * (n + 1) := by have := paramJ_le_three n; omega
  have hL2_le : L2 ≤ 16 * (n + 1) := paramL2_le n
  have hd_le : d ≤ 32 * (n + 1) := by
    have h := paramJ_mul_L2_le n
    change J * L2 ≤ 16 * (n + 1) at h
    have : d = 2 * (J * L2) := by dsimp only [d]; ring
    omega
  rcases blkCopy_clean rBlkAux1 rJ V inp reg₀ hreg₀ with ⟨g1, va1, fg1, es1⟩
  rw [hJ_eq] at va1
  rcases blkAdd_clean rBlkAux1 rJ s0 (by decide) (by decide) V inp g1 es1.reg₁_le
    (by rw [va1, fg1 rJ (by decide), hJ_eq]; omega) with ⟨g2, va2, fg2, es2⟩
  have hg2_aux1 : g2 rBlkAux1 = 2 * J := by rw [va2, va1, fg1 rJ (by decide), hJ_eq]; omega
  rcases blkZero_clean rBlkAux2 V inp g2 es2.reg₁_le with ⟨g3, va3, fg3, es3⟩
  have hg3_aux1 : g3 rBlkAux1 = 2 * J := (fg3 rBlkAux1 (by decide)).trans hg2_aux1
  have hg3_L2 : g3 rL2 = L2 := by
    rw [fg3 rL2 (by decide), fg2 rL2 (by decide) (by decide), fg1 rL2 (by decide), hL2_eq]
  rcases blkMul_clean rNumIn rBlkAux1 rL2 s5 s6
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (16 * (n + 1)) V inp g3 es3.reg₁_le
      (by rw [hg3_aux1]; exact h2J_le) (by rw [hg3_L2]; exact hL2_le)
      (by rw [hg3_aux1, hg3_L2]; change d ≤ V; omega)
    with ⟨g4, vni4, fg4, es4⟩
  rw [hg3_aux1, hg3_L2] at vni4
  rcases blkCopy_clean rNumOut rNumIn V inp g4 es4.reg₁_le with ⟨g5, vno5, fg5, es5⟩
  rw [vni4] at vno5
  have hg5_ni : g5 rNumIn = d := (fg5 rNumIn (by decide)).trans vni4
  have hg5_aux1 : g5 rBlkAux1 = 2 * J := by
    rw [fg5 rBlkAux1 (by decide), fg4 rBlkAux1 (by decide) (by decide) (by decide), hg3_aux1]
  have hg5_aux2 : g5 rBlkAux2 = 0 := by
    rw [fg5 rBlkAux2 (by decide), fg4 rBlkAux2 (by decide) (by decide) (by decide), va3]
  have fg5_15 : ∀ i : Fin R_emit, i.val < 15 → g5 i = reg₀ i := fun i hi => by
    rw [fg5 i (ne_of_lt_val (by change i.val < 21; omega)),
        fg4 i (ne_of_lt_val (by change i.val < 20; omega))
          (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega)),
        fg3 i (ne_of_lt_val (by change i.val < 19; omega)),
        fg2 i (ne_of_lt_val (by change i.val < 18; omega))
          (ne_of_lt_val (by change i.val < 35; omega)),
        fg1 i (ne_of_lt_val (by change i.val < 18; omega))]
  set T_iter := (d + 1) * ((d + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160)
  rcases blkForRange_frame_spec rBlkIdx rBlkRem rL1 (by decide) (by decide)
      (fun r => r.val < 15 ∨ (18 ≤ r.val ∧ r.val < 22)) (by decide) (by decide)
      (blkEmitLinearMap (blkDftUnifiedMat rWParam rBlkAux1 rL1 rBlkAux2))
      V T_iter inp g5
      (fun _ => QCSD_encodeCircuit (linearMapCheckCircuit d d (dftUnifiedMat J wVal (2 * J) L1 0)))
      es5.reg₁_le
      (fun idx reg _ hidx hreg hk => by
        have hr_15 : ∀ i : Fin R_emit, i.val < 15 → reg i = reg₀ i := fun i hi =>
          (hk i (Or.inl hi)).trans (fg5_15 i hi)
        have hr_ni : reg rNumIn = d := (hk rNumIn (Or.inr (by decide))).trans hg5_ni
        have hr_no : reg rNumOut = d := (hk rNumOut (Or.inr (by decide))).trans vno5
        have hr_a1 : reg rBlkAux1 = 2 * J := (hk rBlkAux1 (Or.inr (by decide))).trans hg5_aux1
        have hr_a2 : reg rBlkAux2 = 0 := (hk rBlkAux2 (Or.inr (by decide))).trans hg5_aux2
        rcases blkEmitLinearMap_spec (blkDftUnifiedMat rWParam rBlkAux1 rL1 rBlkAux2)
            (dftUnifiedMat J wVal (2 * J) L1 0) V (160 * V + 250) inp reg hreg
            (by rw [hr_ni, hr_no]; exact (dft_gates_le_6000 d d n _ hd_le hd_le).trans (by omega))
            (fun r k rg hr hk_lt hrr hrk hfr22 hrg => by
              have hrg_15 : ∀ i : Fin R_emit, i.val < 15 → rg i = reg₀ i := fun i hi =>
                (hfr22 i (by omega)).trans (hr_15 i hi)
              have hrg_J : rg rJ = J := (hrg_15 rJ (by decide)).trans hJ_eq
              have hrg_W : rg rWParam = wVal := (hrg_15 rWParam hWP).trans hW_eq
              have hrg_L1 : rg rL1 = L1 := (hrg_15 rL1 (by decide)).trans hL1_eq
              have hrg_a1 : rg rBlkAux1 = 2 * J := (hfr22 rBlkAux1 (by decide)).trans hr_a1
              have hrg_a2 : rg rBlkAux2 = 0 := (hfr22 rBlkAux2 (by decide)).trans hr_a2
              have hqOut : r / (2 * J) < L2 := by
                rw [hr_no] at hr
                exact Nat.div_lt_of_lt_mul (by simpa [d, Nat.mul_comm] using hr)
              have hqIn : k / (2 * J) < L2 := by
                rw [hr_ni] at hk_lt
                exact Nat.div_lt_of_lt_mul (by simpa [d, Nat.mul_comm] using hk_lt)
              have hr_bound : L1 * (k / (2 * J)) + 0 ≤ 3 * J := by
                have hm : L1 * (k / (2 * J)) ≤ L1 * L2 := Nat.mul_le_mul_left L1 (le_of_lt hqIn)
                rw [← paramL_eq_mul] at hm
                have := paramL_le_three_J n
                omega
              rcases blkDftUnifiedMat_spec rWParam rBlkAux1 rL1 rBlkAux2
                  (by omega) (by decide) (by decide) (by decide)
                  V inp rg hrg
                  (by rw [hrg_J]; exact paramJ_pos n)
                  (by rw [hrg_a1]; have := paramJ_pos n; omega)
                  (by rw [hrg_a1, hrg_J])
                  (by rw [hrg_W, hrg_J]; exact hW_le)
                  (by rw [hrg_L1, hrg_J]; exact paramL1_le_three_J n)
                  (by rw [hrr, hrg_J]; have := paramL2_le_three_J n; omega)
                  (by rw [hrk, hrg_a1, hrg_J]; have := paramL2_le_three_J n; omega)
                  (by rw [hrg_L1, hrk, hrg_a1, hrg_a2, hrg_J]; exact hr_bound)
                  (by rw [hrg_J]; have hJ2 : J ^ 2 ≤ 9 * (n + 1) := paramJ_sq_le_nine n; omega)
                with ⟨rg₁, vhit, frg₁, edft⟩
              rw [hrg_J, hrg_W, hrg_a1, hrg_L1, hrg_a2, hrr, hrk] at vhit
              exact ⟨rg₁, vhit, frg₁, edft⟩)
          with ⟨q1, fq1, elin⟩
        rw [hr_ni, hr_no] at elin
        exact ⟨q1,
          by rw [fq1 rBlkIdx (by decide), hidx],
          fq1 rBlkRem (by decide),
          fun r hr => (fq1 r (by rcases hr with h | h <;> omega)).trans (hk r hr),
          elin⟩)
    with ⟨g_end, hfr_end, eloop⟩
  rw [fg5_15 rL1 (by decide), hL1_eq] at eloop
  have hcomb := blkSeq_nil_left es1 (blkSeq_nil_left es2
    (blkSeq_nil_left es3 (blkSeq_nil_left es4 (blkSeq_nil_left es5 eloop))))
  exact ⟨g_end, fun i hi => (hfr_end i (Or.inl hi)).trans (fg5_15 i hi),
    hcomb.congr_out_steps rfl (st2_step_bound n V hV)⟩

theorem blkEmitBlock4_spec (n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre inp : List Bool)
    (V : ℕ) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ V) (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitBlock4 V inp reg₀ reg₁ (blockStream4 n)
        (3000000 * (n + 1) ^ 2 * V) :=
  blkEmitSt2_spec rWExp (by decide) n (paramOmegaExp n) inp V reg₀
    hT0.2.2.2.2.1 hT0.2.2.2.2.2.2.1 hT0.2.2.2.2.2.2.2.1
    hT0.2.2.2.2.2.2.2.2.1 (paramOmegaExp_le_three_J n) hreg₀ hV

theorem blkEmitBlock6_spec (n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre inp : List Bool)
    (V : ℕ) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ V) (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitBlock6 V inp reg₀ reg₁ (blockStream6 n)
        (3000000 * (n + 1) ^ 2 * V) :=
  blkEmitBlock4_spec n h s t0 t1 pre inp V reg₀ hT0 hreg₀ hV

theorem blkEmitBlock9_spec (n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre inp : List Bool)
    (V : ℕ) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ V) (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitBlock9 V inp reg₀ reg₁ (blockStream9 n)
        (3000000 * (n + 1) ^ 2 * V) :=
  blkEmitSt2_spec rInvWExp (by decide) n (paramInvOmegaExp n) inp V reg₀
    hT0.2.2.2.2.1 hT0.2.2.2.2.2.2.1 hT0.2.2.2.2.2.2.2.1
    hT0.2.2.2.2.2.2.2.2.2.1 (paramInvOmegaExp_le_three_J n) hreg₀ hV

-- Block 7: `L` copies of `bilinearMapCheckCircuit` (`ringMulTensor`)
def blkEmitBlock7 :=
  blkCopy rBlkAux1 rJ ;;
  blkAdd rBlkAux1 rJ s0 ;;
  blkForRange rBlkIdx rBlkRem rL blkEmitBilinearRingMul

private lemma block7_step_bound (n V : ℕ) (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    let J := paramJ n; let L := paramL n
    let T_iter := (2 * J + 1) * (((2 * J) * (2 * J) + 1) * (270 * V + 500) + 40 * V + 200)
    1 + ((2 * V + 2) + (L * (T_iter + 2) + 3)) ≤
    3500000 * (n + 1) ^ 2 * V := by
  intro J L T_iter
  have h1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (by omega)
  have hn1 := n_succ_le_sq n
  have h1V : 1 ≤ V := by omega
  have hJL : J * L ≤ 27 * (n + 1) := paramJ_mul_L_le n
  have hL : L ≤ 27 * (n + 1) := paramL_le n
  have hJ2 : J ^ 2 ≤ 9 * (n + 1) := paramJ_sq_le_nine n
  set M := (2 * J) * (2 * J)
  have hcount : L * ((2 * J + 1) * (M + 1)) ≤ 3100 * (n + 1) ^ 2 := by
    have heq : L * ((2 * J + 1) * (M + 1)) =
        8 * ((J * L) * J ^ 2) + 4 * (L * J ^ 2) + 2 * (J * L) + L := by
      dsimp only [M]; ring
    have hm1 : (J * L) * J ^ 2 ≤ (27 * (n + 1)) * (9 * (n + 1)) := Nat.mul_le_mul hJL hJ2
    have hm2 : L * J ^ 2 ≤ (27 * (n + 1)) * (9 * (n + 1)) := Nat.mul_le_mul hL hJ2
    have hexp : (27 * (n + 1)) * (9 * (n + 1)) = 243 * (n + 1) ^ 2 := by ring
    omega
  have h_unit : T_iter + 2 ≤ ((2 * J + 1) * (M + 1)) * (1020 * V) := by
    dsimp only [T_iter]
    have hd1 : 1 ≤ (2 * J + 1) * (M + 1) := Nat.mul_pos (by omega) (by omega)
    have hu1 : 270 * V + 500 ≤ 770 * V := by omega
    have hu2 : 40 * V + 200 ≤ 240 * ((M + 1) * V) := by
      have : V ≤ (M + 1) * V := Nat.le_mul_of_pos_left V (by omega)
      omega
    have hinner : (M + 1) * (270 * V + 500) + 40 * V + 200 ≤ (M + 1) * (1010 * V) := by
      have h_m : (M + 1) * (270 * V + 500) ≤ (M + 1) * (770 * V) := Nat.mul_le_mul_left _ hu1
      have h_r : (M + 1) * (1010 * V) = (M + 1) * (770 * V) + 240 * ((M + 1) * V) := by ring
      omega
    have hm2 : (2 * J + 1) * ((M + 1) * (270 * V + 500) + 40 * V + 200) ≤
        (2 * J + 1) * ((M + 1) * (1010 * V)) := Nat.mul_le_mul_left _ hinner
    have h2_le : 2 ≤ 10 * (((2 * J + 1) * (M + 1)) * V) := by
      have : 1 ≤ ((2 * J + 1) * (M + 1)) * V := Nat.mul_pos hd1 h1V
      omega
    have hr : ((2 * J + 1) * (M + 1)) * (1020 * V) =
        (2 * J + 1) * ((M + 1) * (1010 * V)) + 10 * (((2 * J + 1) * (M + 1)) * V) := by ring
    rw [hr]; exact Nat.add_le_add hm2 h2_le
  have h_loop : L * (T_iter + 2) ≤ 3162000 * ((n + 1) ^ 2 * V) := by
    calc
      L * (T_iter + 2) ≤ L * (((2 * J + 1) * (M + 1)) * (1020 * V)) := Nat.mul_le_mul_left _ h_unit
      _ = (L * ((2 * J + 1) * (M + 1))) * (1020 * V) := by ring
      _ ≤ (3100 * (n + 1) ^ 2) * (1020 * V) := Nat.mul_le_mul_right _ hcount
      _ = 3162000 * ((n + 1) ^ 2 * V) := by ring
  have hsetup : 1 + ((2 * V + 2) + 3) ≤ 5 * ((n + 1) ^ 2 * V) := by
    have h1_sqV : V ≤ (n + 1) ^ 2 * V := Nat.le_mul_of_pos_left V h1
    omega
  calc
    1 + ((2 * V + 2) + (L * (T_iter + 2) + 3))
        = (1 + ((2 * V + 2) + 3)) + L * (T_iter + 2) := by ring
    _ ≤ 5 * ((n + 1) ^ 2 * V) + 3162000 * ((n + 1) ^ 2 * V) := Nat.add_le_add hsetup h_loop
    _ = 3162005 * ((n + 1) ^ 2 * V) := by ring
    _ ≤ 3500000 * ((n + 1) ^ 2 * V) := Nat.mul_le_mul_right _ (by decide)
    _ = 3500000 * (n + 1) ^ 2 * V := by ring

theorem blkEmitBlock7_spec (n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre inp : List Bool)
    (V : ℕ) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ V) (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitBlock7 V inp reg₀ reg₁ (blockStream7 n)
        (3500000 * (n + 1) ^ 2 * V) := by
  set J := paramJ n; set L := paramL n
  have hn1_sq := n_succ_le_sq n
  have h2J_V : 2 * J ≤ V := by have := paramJ_le_three n; omega
  rcases blkCopy_clean rBlkAux1 rJ V inp reg₀ hreg₀ with ⟨g1, va1, fg1, es1⟩
  rw [hT0.2.2.2.2.1] at va1
  rcases blkAdd_clean rBlkAux1 rJ s0 (by decide) (by decide) V inp g1 es1.reg₁_le
    (by rw [va1, fg1 rJ (by decide), hT0.2.2.2.2.1]; omega) with ⟨g2, va2, fg2, es2⟩
  have hg2_aux1 : g2 rBlkAux1 = 2 * J := by rw [va2, va1, fg1 rJ (by decide), hT0.2.2.2.2.1]; omega
  have fg2_15 : ∀ i : Fin R_emit, i.val < 15 → g2 i = reg₀ i := fun i hi => by
    rw [fg2 i (ne_of_lt_val (by change i.val < 18; omega))
          (ne_of_lt_val (by change i.val < 35; omega)),
        fg1 i (ne_of_lt_val (by change i.val < 18; omega))]
  set T_iter := (2 * J + 1) * (((2 * J) * (2 * J) + 1) * (270 * V + 500) + 40 * V + 200)
  rcases blkForRange_frame_spec rBlkIdx rBlkRem rL (by decide) (by decide)
      (fun r => r.val < 15 ∨ r = rBlkAux1) (by decide) (by decide)
      blkEmitBilinearRingMul V T_iter inp g2
      (fun _ => QCSD_encodeCircuit (bilinearMapCheckCircuit (2 * J) (2 * J) (2 * J) (ringMulTensor J)))
      es2.reg₁_le
      (fun _ reg _ hidx hreg hk => by
        have hr_J : reg rJ = J := (hk rJ (Or.inl (by decide))).trans ((fg2_15 rJ (by decide)).trans hT0.2.2.2.2.1)
        have hr_aux : reg rBlkAux1 = 2 * J := (hk rBlkAux1 (Or.inr rfl)).trans hg2_aux1
        rcases blkEmitBilinearRingMul_spec V inp reg hreg
            (by rw [hr_J]; exact paramJ_pos n)
            (by rw [hr_aux, hr_J])
            (by rw [hr_J]; exact (bilinear_gates_le_6000 n).trans (by omega))
          with ⟨q1, fq1, ebil⟩
        rw [hr_J] at ebil
        exact ⟨q1,
          by rw [fq1 rBlkIdx (by decide), hidx],
          fq1 rBlkRem (by decide),
          fun r hr => (fq1 r (by rcases hr with h | rfl <;> [omega; decide])).trans (hk r hr),
          ebil⟩)
    with ⟨g_end, hfr_end, eloop⟩
  rw [fg2_15 rL (by decide), hT0.2.2.2.2.2.1] at eloop
  have hcomb := blkSeq_nil_left es1 (blkSeq_nil_left es2 eloop)
  exact ⟨g_end, fun i hi => (hfr_end i (Or.inl hi)).trans (fg2_15 i hi),
    hcomb.congr_out_steps rfl (block7_step_bound n V hV)⟩

-- Block 8: Inverse stage-1 DFT (`L2` circuits of `fullSt1Mat`)
def blkEmitBlock8 :=
  blkCopy rBlkAux1 rJ ;;
  blkAdd rBlkAux1 rJ s0 ;;
  blkMul rNumIn rBlkAux1 rL1 s5 s6 ;;
  blkCopy rNumOut rNumIn ;;
  blkForRange rBlkIdx rBlkRem rL2
    (blkEmitLinearMap (blkDftUnifiedMat rInvWExp rBlkAux1 rL2 rBlkIdx))

private lemma block8_step_bound (n V : ℕ) (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    let J := paramJ n; let L1 := paramL1 n; let L2 := paramL2 n
    let d := 2 * J * L1
    let T_iter := (d + 1) * ((d + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160)
    1 + ((2 * V + 2) + (((16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 3) +
      (1 + (L2 * (T_iter + 2) + 3)))) ≤
    3000000 * (n + 1) ^ 2 * V := by
  intro J L1 L2 d T_iter
  have h1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (by omega)
  have hn1 := n_succ_le_sq n
  have h1V : 1 ≤ V := by omega
  have hJL : J * (L1 * L2) ≤ 27 * (n + 1) := by rw [← paramL_eq_mul]; exact paramJ_mul_L_le n
  have hJL1 : J * L1 ≤ 16 * (n + 1) := paramJ_mul_L1_le n
  have hL2 : L2 ≤ 16 * (n + 1) := paramL2_le n
  have hL2_d2 : L2 * (d + 1) * (d + 1) ≤ 1900 * (n + 1) ^ 2 := by
    have heq : L2 * (d + 1) * (d + 1) =
        4 * ((J * (L1 * L2)) * (J * L1)) + 4 * (J * (L1 * L2)) + L2 := by
      dsimp only [d]; ring
    have hm : (J * (L1 * L2)) * (J * L1) ≤ (27 * (n + 1)) * (16 * (n + 1)) :=
      Nat.mul_le_mul hJL hJL1
    have hm_exp : (27 * (n + 1)) * (16 * (n + 1)) = 432 * (n + 1) ^ 2 := by ring
    omega
  have h_unit : T_iter + 2 ≤ (d + 1) * (d + 1) * (1550 * V) := by
    dsimp only [T_iter]
    have hd1 : 1 ≤ (d + 1) * (d + 1) := Nat.mul_pos (by omega) (by omega)
    have hu1 : 3 * (160 * V + 250) + 20 * V + 100 ≤ 1350 * V := by omega
    have hu2 : 30 * V + 160 ≤ 190 * ((d + 1) * V) := by
      have : V ≤ (d + 1) * V := Nat.le_mul_of_pos_left V (by omega)
      omega
    have hinner : (d + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160 ≤
        (d + 1) * (1540 * V) := by
      have h_m : (d + 1) * (3 * (160 * V + 250) + 20 * V + 100) ≤ (d + 1) * (1350 * V) :=
        Nat.mul_le_mul_left _ hu1
      have h_r : (d + 1) * (1540 * V) = (d + 1) * (1350 * V) + 190 * ((d + 1) * V) := by ring
      omega
    have hm2 : (d + 1) * ((d + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160) ≤
        (d + 1) * ((d + 1) * (1540 * V)) := Nat.mul_le_mul_left _ hinner
    have h2_le : 2 ≤ 10 * ((d + 1) * (d + 1) * V) := by
      have : 1 ≤ (d + 1) * (d + 1) * V := Nat.mul_pos hd1 h1V
      omega
    have hr : (d + 1) * (d + 1) * (1550 * V) =
        (d + 1) * ((d + 1) * (1540 * V)) + 10 * ((d + 1) * (d + 1) * V) := by ring
    rw [hr]; exact Nat.add_le_add hm2 h2_le
  have h_loop : L2 * (T_iter + 2) ≤ 2945000 * ((n + 1) ^ 2 * V) := by
    calc
      L2 * (T_iter + 2) ≤ L2 * ((d + 1) * (d + 1) * (1550 * V)) := Nat.mul_le_mul_left _ h_unit
      _ = (L2 * (d + 1) * (d + 1)) * (1550 * V) := by ring
      _ ≤ (1900 * (n + 1) ^ 2) * (1550 * V) := Nat.mul_le_mul_right _ hL2_d2
      _ = 2945000 * ((n + 1) ^ 2 * V) := by ring
  have hmul_setup : 1 + ((2 * V + 2) + (((16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 3) + 4)) ≤
      5 * ((n + 1) ^ 2 * V) := by
    have hs : (16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 10 ≤ V := by
      have : (16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 10 =
          512 * (n + 1) ^ 2 + 48 * (n + 1) + 10 := by ring
      omega
    have h1_sqV : V ≤ (n + 1) ^ 2 * V := Nat.le_mul_of_pos_left V h1
    omega
  calc
    1 + ((2 * V + 2) + (((16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 3) +
      (1 + (L2 * (T_iter + 2) + 3))))
        = (1 + ((2 * V + 2) + (((16 * (n + 1)) * (2 * (16 * (n + 1)) + 3) + 3) + 4))) +
            L2 * (T_iter + 2) := by ring
    _ ≤ 5 * ((n + 1) ^ 2 * V) + 2945000 * ((n + 1) ^ 2 * V) := Nat.add_le_add hmul_setup h_loop
    _ = 2945005 * ((n + 1) ^ 2 * V) := by ring
    _ ≤ 3000000 * ((n + 1) ^ 2 * V) := Nat.mul_le_mul_right _ (by decide)
    _ = 3000000 * (n + 1) ^ 2 * V := by ring

theorem blkEmitBlock8_spec (n : ℕ) (h s : Fin n → ZMod 2) (t0 t1 : ℕ) (pre inp : List Bool)
    (V : ℕ) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ V) (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitBlock8 V inp reg₀ reg₁ (blockStream8 n)
        (3000000 * (n + 1) ^ 2 * V) := by
  set J := paramJ n; set L1 := paramL1 n; set L2 := paramL2 n
  set invW := paramInvOmegaExp n; set d := 2 * J * L1
  have hn1_sq := n_succ_le_sq n
  have h2J_le : 2 * J ≤ 16 * (n + 1) := by have := paramJ_le_three n; omega
  have hL1_le : L1 ≤ 16 * (n + 1) := paramL1_le n
  have hd_le : d ≤ 32 * (n + 1) := by
    have h := paramJ_mul_L1_le n
    change J * L1 ≤ 16 * (n + 1) at h
    have : d = 2 * (J * L1) := by dsimp only [d]; ring
    omega
  rcases blkCopy_clean rBlkAux1 rJ V inp reg₀ hreg₀ with ⟨g1, va1, fg1, es1⟩
  rw [hT0.2.2.2.2.1] at va1
  rcases blkAdd_clean rBlkAux1 rJ s0 (by decide) (by decide) V inp g1 es1.reg₁_le
    (by rw [va1, fg1 rJ (by decide), hT0.2.2.2.2.1]; omega) with ⟨g2, va2, fg2, es2⟩
  have hg2_aux1 : g2 rBlkAux1 = 2 * J := by rw [va2, va1, fg1 rJ (by decide), hT0.2.2.2.2.1]; omega
  have hg2_L1 : g2 rL1 = L1 := by
    rw [fg2 rL1 (by decide) (by decide), fg1 rL1 (by decide), hT0.2.2.2.2.2.2.1]
  rcases blkMul_clean rNumIn rBlkAux1 rL1 s5 s6
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (16 * (n + 1)) V inp g2 es2.reg₁_le
      (by rw [hg2_aux1]; exact h2J_le) (by rw [hg2_L1]; exact hL1_le)
      (by rw [hg2_aux1, hg2_L1]; change d ≤ V; omega)
    with ⟨g3, vni3, fg3, es3⟩
  rw [hg2_aux1, hg2_L1] at vni3
  rcases blkCopy_clean rNumOut rNumIn V inp g3 es3.reg₁_le with ⟨g4, vno4, fg4, es4⟩
  rw [vni3] at vno4
  have hg4_ni : g4 rNumIn = d := (fg4 rNumIn (by decide)).trans vni3
  have hg4_aux1 : g4 rBlkAux1 = 2 * J := by
    rw [fg4 rBlkAux1 (by decide), fg3 rBlkAux1 (by decide) (by decide) (by decide), hg2_aux1]
  have fg4_15 : ∀ i : Fin R_emit, i.val < 15 → g4 i = reg₀ i := fun i hi => by
    rw [fg4 i (ne_of_lt_val (by change i.val < 21; omega)),
        fg3 i (ne_of_lt_val (by change i.val < 20; omega))
          (ne_of_lt_val (by change i.val < 40; omega))
          (ne_of_lt_val (by change i.val < 41; omega)),
        fg2 i (ne_of_lt_val (by change i.val < 18; omega))
          (ne_of_lt_val (by change i.val < 35; omega)),
        fg1 i (ne_of_lt_val (by change i.val < 18; omega))]
  set T_iter := (d + 1) * ((d + 1) * (3 * (160 * V + 250) + 20 * V + 100) + 30 * V + 160)
  rcases blkForRange_frame_spec rBlkIdx rBlkRem rL2 (by decide) (by decide)
      (fun r => r.val < 15 ∨ r = rBlkAux1 ∨ r = rNumIn ∨ r = rNumOut) (by decide) (by decide)
      (blkEmitLinearMap (blkDftUnifiedMat rInvWExp rBlkAux1 rL2 rBlkIdx))
      V T_iter inp g4
      (fun j2 => QCSD_encodeCircuit (linearMapCheckCircuit d d (dftUnifiedMat J invW (2 * J) L2 j2)))
      es4.reg₁_le
      (fun j2 reg hj2lt hj2_idx hreg hk => by
        rw [fg4_15 rL2 (by decide), hT0.2.2.2.2.2.2.2.1] at hj2lt
        have hr_15 : ∀ i : Fin R_emit, i.val < 15 → reg i = reg₀ i := fun i hi =>
          (hk i (Or.inl hi)).trans (fg4_15 i hi)
        have hr_a1 : reg rBlkAux1 = 2 * J := (hk rBlkAux1 (Or.inr (Or.inl rfl))).trans hg4_aux1
        have hr_ni : reg rNumIn = d := (hk rNumIn (Or.inr (Or.inr (Or.inl rfl)))).trans hg4_ni
        have hr_no : reg rNumOut = d := (hk rNumOut (Or.inr (Or.inr (Or.inr rfl)))).trans vno4
        rcases blkEmitLinearMap_spec (blkDftUnifiedMat rInvWExp rBlkAux1 rL2 rBlkIdx)
            (dftUnifiedMat J invW (2 * J) L2 j2) V (160 * V + 250) inp reg hreg
            (by rw [hr_ni, hr_no]; exact (dft_gates_le_6000 d d n _ hd_le hd_le).trans (by omega))
            (fun r k rg hr hk_lt hrr hrk hfr22 hrg => by
              have hrg_15 : ∀ i : Fin R_emit, i.val < 15 → rg i = reg₀ i := fun i hi =>
                (hfr22 i (by omega)).trans (hr_15 i hi)
              have hrg_J : rg rJ = J := (hrg_15 rJ (by decide)).trans hT0.2.2.2.2.1
              have hrg_W : rg rInvWExp = invW := (hrg_15 rInvWExp (by decide)).trans hT0.2.2.2.2.2.2.2.2.2.1
              have hrg_L2 : rg rL2 = L2 := (hrg_15 rL2 (by decide)).trans hT0.2.2.2.2.2.2.2.1
              have hrg_a1 : rg rBlkAux1 = 2 * J := (hfr22 rBlkAux1 (by decide)).trans hr_a1
              have hrg_j2 : rg rBlkIdx = j2 := (hfr22 rBlkIdx (by decide)).trans hj2_idx
              have hqOut : r / (2 * J) < L1 := by
                rw [hr_no] at hr
                exact Nat.div_lt_of_lt_mul (by simpa [d, Nat.mul_comm] using hr)
              have hqIn : k / (2 * J) < L1 := by
                rw [hr_ni] at hk_lt
                exact Nat.div_lt_of_lt_mul (by simpa [d, Nat.mul_comm] using hk_lt)
              have hr_bound : L2 * (k / (2 * J)) + j2 ≤ 3 * J := by
                have hm : L2 * (k / (2 * J) + 1) ≤ L2 * L1 := Nat.mul_le_mul_left L2 hqIn
                have he : L2 * (k / (2 * J) + 1) = L2 * (k / (2 * J)) + L2 := by ring
                have hmulL : L2 * L1 = paramL n := by rw [Nat.mul_comm, ← paramL_eq_mul]
                have := paramL_le_three_J n
                omega
              rcases blkDftUnifiedMat_spec rInvWExp rBlkAux1 rL2 rBlkIdx
                  (by decide) (by decide) (by decide) (by decide)
                  V inp rg hrg
                  (by rw [hrg_J]; exact paramJ_pos n)
                  (by rw [hrg_a1]; have := paramJ_pos n; omega)
                  (by rw [hrg_a1, hrg_J])
                  (by rw [hrg_W, hrg_J]; exact paramInvOmegaExp_le_three_J n)
                  (by rw [hrg_L2, hrg_J]; exact paramL2_le_three_J n)
                  (by rw [hrr, hrg_J]; have := paramL1_le_three_J n; omega)
                  (by rw [hrk, hrg_a1, hrg_J]; have := paramL1_le_three_J n; omega)
                  (by rw [hrg_L2, hrk, hrg_a1, hrg_j2, hrg_J]; exact hr_bound)
                  (by rw [hrg_J]; have hJ2 : J ^ 2 ≤ 9 * (n + 1) := paramJ_sq_le_nine n; omega)
                with ⟨rg₁, vhit, frg₁, edft⟩
              rw [hrg_J, hrg_W, hrg_a1, hrg_L2, hrg_j2, hrr, hrk] at vhit
              exact ⟨rg₁, vhit, frg₁, edft⟩)
          with ⟨q1, fq1, elin⟩
        rw [hr_ni, hr_no] at elin
        exact ⟨q1,
          by rw [fq1 rBlkIdx (by decide), hj2_idx],
          fq1 rBlkRem (by decide),
          fun r hr => (fq1 r (by rcases hr with h | rfl | rfl | rfl <;> [omega; decide; decide; decide])).trans (hk r hr),
          elin⟩)
    with ⟨g_end, hfr_end, eloop⟩
  rw [fg4_15 rL2 (by decide), hT0.2.2.2.2.2.2.2.1] at eloop
  have hcomb := blkSeq_nil_left es1 (blkSeq_nil_left es2 (blkSeq_nil_left es3 (blkSeq_nil_left es4 eloop)))
  exact ⟨g_end, fun i hi => (hfr_end i (Or.inl hi)).trans (fg4_15 i hi),
    hcomb.congr_out_steps rfl (block8_step_bound n V hV)⟩

/-! ### 5.3 Combined Verified Emitter for Vertex Blocks 0–9 (`v < netV10 n`) -/

/-- Exact stream decomposition for the first 10 vertex blocks (`v < netV10 n`). -/
theorem encodeVertices0to9_eq_blocks (mode n : ℕ) (h s : Fin n → ZMod 2)
    (t0 t1 : ℕ) (pre : List Bool) :
    (List.range (netV10 n)).flatMap
      (fun v => QCSD_encodeCircuit (rawPred mode n h s t0 t1 pre v)) =
    blockStream0 n pre ++
    blockStream1 n ++
    blockStream2 n h ++
    blockStream3 n ++
    blockStream4 n ++
    blockStream5 n ++
    blockStream6 n ++
    blockStream7 n ++
    blockStream8 n ++
    blockStream9 n := by
  set F := fun v => QCSD_encodeCircuit (rawPred mode n h s t0 t1 pre v)
  rcases netV_chain n with
    ⟨_, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, _⟩
  rw [range_sub_split_flatMap hv9 F,
      range_sub_split_flatMap hv8 F,
      range_sub_split_flatMap hv7 F,
      range_sub_split_flatMap hv6 F,
      range_sub_split_flatMap hv5 F,
      range_sub_split_flatMap hv4 F,
      range_sub_split_flatMap hv3 F,
      range_sub_split_flatMap hv2 F,
      range_sub_split_flatMap hv1 F]
  have hb0 : (List.range (netV1 n)).flatMap F = blockStream0 n pre := by
    change (List.range (2 * n)).flatMap F = blockStream0 n pre
    unfold blockStream0
    refine List.flatMap_congr (fun v hv => ?_)
    have hvlt : v < netV1 n := List.mem_range.mp hv
    dsimp only [F]; rw [rawPred_V0 _ _ _ _ _ _ _ hvlt]
    by_cases hpre : v < pre.length
    · simp only [hpre, ↓reduceIte]; cases pre.getD v false <;> rfl
    · simp only [hpre, ↓reduceIte]; rfl
  have hb1 : (List.range (netV2 n - netV1 n)).flatMap (fun i => F (netV1 n + i)) = blockStream1 n := by
    have hd : netV2 n - netV1 n = 2 * n := by simp [netV2, netV1]; omega
    rw [hd]; unfold blockStream1
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < 2 * n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V1 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV1, netV2]; omega), encodeCircuit_ecopy]
  have hb2 : (List.range (netV3 n - netV2 n)).flatMap (fun i => F (netV2 n + i)) = blockStream2 n h := by
    have hd : netV3 n - netV2 n = n := by simp [netV3, netV2]; omega
    rw [hd]; unfold blockStream2
    refine List.flatMap_congr (fun idx hi => ?_)
    have hilt : idx < n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V2 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV2, netV3]; omega)]
    simp only [Nat.add_sub_cancel_left, hilt, ↓reduceDIte]
    cases zmod2ToBool (h ⟨idx, hilt⟩) <;> rfl
  have hb3 : (List.range (netV4 n - netV3 n)).flatMap (fun i => F (netV3 n + i)) = blockStream3 n := by
    have hd : netV4 n - netV3 n = paramL2 n := by simp [netV4, netV3]
    rw [hd]; unfold blockStream3; dsimp only
    refine List.flatMap_congr (fun j2 hj2 => ?_)
    have hj2lt : j2 < paramL2 n := List.mem_range.mp hj2
    dsimp only [F]
    rw [rawPred_V3 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV3, netV4]; omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [fwdSt1Mat_circuit_eq_unified n (paramJ n) (paramL1 n) (paramL2 n) (paramOmegaExp n) j2
          (paramJ_pos n) hj2lt]
  have hb4 : (List.range (netV5 n - netV4 n)).flatMap (fun i => F (netV4 n + i)) = blockStream4 n := by
    have hd : netV5 n - netV4 n = paramL1 n := by simp [netV5, netV4]
    rw [hd]; unfold blockStream4; dsimp only
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < paramL1 n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V4 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV4, netV5]; omega),
        st2Mat_circuit_eq_unified]
  have hb5 : (List.range (netV6 n - netV5 n)).flatMap (fun i => F (netV5 n + i)) = blockStream5 n := by
    have hd : netV6 n - netV5 n = paramL2 n := by simp [netV6, netV5]; omega
    rw [hd]; unfold blockStream5 blockStream3; dsimp only
    refine List.flatMap_congr (fun j2 hj2 => ?_)
    have hj2lt : j2 < paramL2 n := List.mem_range.mp hj2
    dsimp only [F]
    rw [rawPred_V5 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV5, netV6]; omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [fwdSt1Mat_circuit_eq_unified n (paramJ n) (paramL1 n) (paramL2 n) (paramOmegaExp n) j2
          (paramJ_pos n) hj2lt]
  have hb6 : (List.range (netV7 n - netV6 n)).flatMap (fun i => F (netV6 n + i)) = blockStream6 n := by
    have hd : netV7 n - netV6 n = paramL1 n := by simp [netV7, netV6]; omega
    rw [hd]; unfold blockStream6 blockStream4; dsimp only
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < paramL1 n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V6 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV6, netV7]; omega),
        st2Mat_circuit_eq_unified]
  have hb7 : (List.range (netV8 n - netV7 n)).flatMap (fun i => F (netV7 n + i)) = blockStream7 n := by
    have hd : netV8 n - netV7 n = paramL n := by simp [netV8]
    rw [hd]; unfold blockStream7; dsimp only
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < paramL n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V7 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV8]; omega)]
  have hb8 : (List.range (netV9 n - netV8 n)).flatMap (fun i => F (netV8 n + i)) = blockStream8 n := by
    have hd : netV9 n - netV8 n = paramL2 n := by simp [netV9]
    rw [hd]; unfold blockStream8; dsimp only
    refine List.flatMap_congr (fun j2 hj2 => ?_)
    have hj2lt : j2 < paramL2 n := List.mem_range.mp hj2
    dsimp only [F]
    rw [rawPred_V8 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV9]; omega)]
    simp only [Nat.add_sub_cancel_left, fullSt1Mat_circuit_eq_unified]
  have hb9 : (List.range (netV10 n - netV9 n)).flatMap (fun i => F (netV9 n + i)) = blockStream9 n := by
    have hd : netV10 n - netV9 n = paramL1 n := by simp [netV10]
    rw [hd]; unfold blockStream9; dsimp only
    refine List.flatMap_congr (fun i hi => ?_)
    have hilt : i < paramL1 n := List.mem_range.mp hi
    dsimp only [F]
    rw [rawPred_V9 _ _ _ _ _ _ _ (Nat.le_add_right _ _) (by simp [netV10]; omega),
        st2Mat_circuit_eq_unified]
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9]

def blkEmitBlocks0to4 :=
  blkEmitBlock0 ;;
  blkEmitBlock1 ;;
  blkEmitBlock2 ;;
  blkEmitBlock3 ;;
  blkEmitBlock4

def blkEmitBlocks5to9 :=
  blkEmitBlock5 ;;
  blkEmitBlock6 ;;
  blkEmitBlock7 ;;
  blkEmitBlock8 ;;
  blkEmitBlock9

def blkEmitBlocks0to9 :=
  blkEmitBlocks0to4 ;; blkEmitBlocks5to9

def rmEmitBlocks0to9 := blkEmitBlocks0to9.1
def rmEmitBlocks0to9Entry := blkEmitBlocks0to9.2

private lemma blocks0to4_step_bound (n V : ℕ) (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    (n + 1) * (10 * V + 100) +
    ((n + 1) * (2 * V + 1800) +
     ((n + 1) * (2 * V + 30) +
      (120000 * (n + 1) ^ 2 * V + 3000000 * (n + 1) ^ 2 * V))) ≤
    3200000 * (n + 1) ^ 2 * V := by
  have h1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (by omega)
  have hn1 := n_succ_le_sq n
  have h1V : 1 ≤ V := by omega
  have hsmall :
      (n + 1) * (10 * V + 100) + (n + 1) * (2 * V + 1800) + (n + 1) * (2 * V + 30) ≤
      2000 * ((n + 1) ^ 2 * V) := by
    have hl :
        (n + 1) * (10 * V + 100) + (n + 1) * (2 * V + 1800) + (n + 1) * (2 * V + 30) =
        14 * ((n + 1) * V) + 1930 * (n + 1) := by ring
    have hn_sqV : n + 1 ≤ (n + 1) ^ 2 * V :=
      hn1.trans (Nat.le_mul_of_pos_right _ h1V)
    have hnV_sqV : (n + 1) * V ≤ (n + 1) ^ 2 * V := Nat.mul_le_mul_right V hn1
    omega
  calc
    (n + 1) * (10 * V + 100) +
    ((n + 1) * (2 * V + 1800) +
     ((n + 1) * (2 * V + 30) +
      (120000 * (n + 1) ^ 2 * V + 3000000 * (n + 1) ^ 2 * V)))
        = ((n + 1) * (10 * V + 100) + (n + 1) * (2 * V + 1800) + (n + 1) * (2 * V + 30)) +
            3120000 * ((n + 1) ^ 2 * V) := by ring
    _ ≤ 2000 * ((n + 1) ^ 2 * V) + 3120000 * ((n + 1) ^ 2 * V) := Nat.add_le_add_right hsmall _
    _ = 3122000 * ((n + 1) ^ 2 * V) := by ring
    _ ≤ 3200000 * ((n + 1) ^ 2 * V) := Nat.mul_le_mul_right _ (by decide)
    _ = 3200000 * (n + 1) ^ 2 * V := by ring

private lemma blocks5to9_step_bound (n V : ℕ) :
    120000 * (n + 1) ^ 2 * V +
    (3000000 * (n + 1) ^ 2 * V +
     (3500000 * (n + 1) ^ 2 * V +
      (3000000 * (n + 1) ^ 2 * V + 3000000 * (n + 1) ^ 2 * V))) ≤
    12700000 * (n + 1) ^ 2 * V := by
  calc
    120000 * (n + 1) ^ 2 * V +
    (3000000 * (n + 1) ^ 2 * V +
     (3500000 * (n + 1) ^ 2 * V +
      (3000000 * (n + 1) ^ 2 * V + 3000000 * (n + 1) ^ 2 * V)))
        = 12620000 * ((n + 1) ^ 2 * V) := by ring
    _ ≤ 12700000 * ((n + 1) ^ 2 * V) := Nat.mul_le_mul_right _ (by decide)
    _ = 12700000 * (n + 1) ^ 2 * V := by ring

/-- Compositional `RMBlock` specification for Vertex Blocks 0–9 (`v < netV10 n`). -/
theorem blkEmitBlocks0to9_spec (mode n : ℕ) (h s : Fin n → ZMod 2)
    (t0 t1 : ℕ) (pre inp : List Bool) (V : ℕ) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hHV : reg₀ rHOff + n ≤ V)
    (hPreV : reg₀ rPreOff + 2 * n ≤ V)
    (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    ∃ reg₁ : RegState R_emit,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMBlockExec blkEmitBlocks0to9 V inp reg₀ reg₁
        ((List.range (netV10 n)).flatMap
          (fun v => QCSD_encodeCircuit (rawPred mode n h s t0 t1 pre v)))
        (16000000 * (n + 1) ^ 2 * V) := by
  rcases blkEmitBlock0_spec n h s t0 t1 pre inp V reg₀ hT0 hreg₀ hPreV hV with ⟨g1, f1, e0⟩
  have hT1 := hT0.of_frame f1
  rcases blkEmitBlock1_spec n h s t0 t1 pre inp V g1 hT1 e0.reg₁_le hV with ⟨g2, f2, e1⟩
  have f02 : ∀ i : Fin R_emit, i.val < 15 → g2 i = reg₀ i := fun i hi => (f2 i hi).trans (f1 i hi)
  have hT2 := hT0.of_frame f02
  rcases blkEmitBlock2_spec n h s t0 t1 pre inp V g2 hT2 e1.reg₁_le
    (by rw [f02 rHOff (by decide)]; exact hHV) with ⟨g3, f3, e2⟩
  have f03 : ∀ i : Fin R_emit, i.val < 15 → g3 i = reg₀ i := fun i hi => (f3 i hi).trans (f02 i hi)
  have hT3 := hT0.of_frame f03
  rcases blkEmitBlock3_spec n h s t0 t1 pre inp V g3 hT3 e2.reg₁_le hV with ⟨g4, f4, e3⟩
  have f04 : ∀ i : Fin R_emit, i.val < 15 → g4 i = reg₀ i := fun i hi => (f4 i hi).trans (f03 i hi)
  have hT4 := hT0.of_frame f04
  rcases blkEmitBlock4_spec n h s t0 t1 pre inp V g4 hT4 e3.reg₁_le hV with ⟨g5, f5, e4⟩
  have f05 : ∀ i : Fin R_emit, i.val < 15 → g5 i = reg₀ i := fun i hi => (f5 i hi).trans (f04 i hi)
  have e04 : RMBlockExec blkEmitBlocks0to4 V inp reg₀ g5
      (blockStream0 n pre ++ (blockStream1 n ++ (blockStream2 n h ++ (blockStream3 n ++ blockStream4 n))))
      (3200000 * (n + 1) ^ 2 * V) :=
    (blkSeq_spec e0 (blkSeq_spec e1 (blkSeq_spec e2 (blkSeq_spec e3 e4)))).weaken
      le_rfl (blocks0to4_step_bound n V hV)
  have hT5 := hT0.of_frame f05
  rcases blkEmitBlock5_spec n h s t0 t1 pre inp V g5 hT5 e4.reg₁_le hV with ⟨g6, f6, e5⟩
  have f06 : ∀ i : Fin R_emit, i.val < 15 → g6 i = reg₀ i := fun i hi => (f6 i hi).trans (f05 i hi)
  have hT6 := hT0.of_frame f06
  rcases blkEmitBlock6_spec n h s t0 t1 pre inp V g6 hT6 e5.reg₁_le hV with ⟨g7, f7, e6⟩
  have f07 : ∀ i : Fin R_emit, i.val < 15 → g7 i = reg₀ i := fun i hi => (f7 i hi).trans (f06 i hi)
  have hT7 := hT0.of_frame f07
  rcases blkEmitBlock7_spec n h s t0 t1 pre inp V g7 hT7 e6.reg₁_le hV with ⟨g8, f8, e7⟩
  have f08 : ∀ i : Fin R_emit, i.val < 15 → g8 i = reg₀ i := fun i hi => (f8 i hi).trans (f07 i hi)
  have hT8 := hT0.of_frame f08
  rcases blkEmitBlock8_spec n h s t0 t1 pre inp V g8 hT8 e7.reg₁_le hV with ⟨g9, f9, e8⟩
  have f09 : ∀ i : Fin R_emit, i.val < 15 → g9 i = reg₀ i := fun i hi => (f9 i hi).trans (f08 i hi)
  have hT9 := hT0.of_frame f09
  rcases blkEmitBlock9_spec n h s t0 t1 pre inp V g9 hT9 e8.reg₁_le hV with ⟨g10, f10, e9⟩
  have f010 : ∀ i : Fin R_emit, i.val < 15 → g10 i = reg₀ i := fun i hi => (f10 i hi).trans (f09 i hi)
  have e59 : RMBlockExec blkEmitBlocks5to9 V inp g5 g10
      (blockStream5 n ++ (blockStream6 n ++ (blockStream7 n ++ (blockStream8 n ++ blockStream9 n))))
      (12700000 * (n + 1) ^ 2 * V) :=
    (blkSeq_spec e5 (blkSeq_spec e6 (blkSeq_spec e7 (blkSeq_spec e8 e9)))).weaken
      le_rfl (blocks5to9_step_bound n V)
  have hcomb := blkSeq_spec e04 e59
  have hout_eq :
      (blockStream0 n pre ++ (blockStream1 n ++ (blockStream2 n h ++ (blockStream3 n ++ blockStream4 n)))) ++
      (blockStream5 n ++ (blockStream6 n ++ (blockStream7 n ++ (blockStream8 n ++ blockStream9 n)))) =
      (List.range (netV10 n)).flatMap
        (fun v => QCSD_encodeCircuit (rawPred mode n h s t0 t1 pre v)) := by
    rw [encodeVertices0to9_eq_blocks]
    simp only [List.append_assoc]
  have hT_tot : 3200000 * (n + 1) ^ 2 * V + 12700000 * (n + 1) ^ 2 * V ≤
      16000000 * (n + 1) ^ 2 * V := by
    calc
      3200000 * (n + 1) ^ 2 * V + 12700000 * (n + 1) ^ 2 * V
          = 15900000 * ((n + 1) ^ 2 * V) := by ring
      _ ≤ 16000000 * ((n + 1) ^ 2 * V) := Nat.mul_le_mul_right _ (by decide)
      _ = 16000000 * (n + 1) ^ 2 * V := by ring
  exact ⟨g10, f010, hcomb.congr_out_steps hout_eq hT_tot⟩

/-- Direct `RMExec` specification for `rmEmitBlocks0to9` (`v < netV10 n`). -/
theorem rmEmitBlocks0to9_spec (mode n : ℕ) (h s : Fin n → ZMod 2)
    (t0 t1 : ℕ) (pre inp : List Bool) (V : ℕ) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hHV : reg₀ rHOff + n ≤ V)
    (hPreV : reg₀ rPreOff + 2 * n ≤ V)
    (hV : 8000 * (n + 1) ^ 2 ≤ V) :
    ∃ q₁ reg₁,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMExec rmEmitBlocks0to9 V inp rmEmitBlocks0to9Entry reg₀ q₁ reg₁
        ((List.range (netV10 n)).flatMap
          (fun v => QCSD_encodeCircuit (rawPred mode n h s t0 t1 pre v)))
        (16000000 * (n + 1) ^ 2 * V) := by
  rcases blkEmitBlocks0to9_spec mode n h s t0 t1 pre inp V reg₀ hT0 hreg₀ hHV hPreV hV
    with ⟨reg₁, hfr, q₁, hex⟩
  exact ⟨q₁, reg₁, hfr, hex⟩

/-- Quartic `O((n + 1)^4)` step-bound specialization of `rmEmitBlocks0to9_spec` valid at ANY
outer register bound `Vmax ≥ (C₀ + 8005) * (n + 1) ^ 2` (in particular `Vmax = O(n^3)`). -/
theorem rmEmitBlocks0to9_quartic_spec (mode n C₀ Vmax : ℕ) (h s : Fin n → ZMod 2)
    (t0 t1 : ℕ) (pre inp : List Bool) (reg₀ : RegState R_emit)
    (hT0 : ValidTier0 n h s t0 t1 pre inp reg₀)
    (hreg₀ : ∀ i, reg₀ i ≤ C₀ * (n + 1) ^ 2)
    (hVmax : (C₀ + 8005) * (n + 1) ^ 2 ≤ Vmax) :
    ∃ q₁ reg₁,
      (∀ i : Fin R_emit, i.val < 15 → reg₁ i = reg₀ i) ∧
      RMExec rmEmitBlocks0to9 Vmax inp rmEmitBlocks0to9Entry reg₀ q₁ reg₁
        ((List.range (netV10 n)).flatMap
          (fun v => QCSD_encodeCircuit (rawPred mode n h s t0 t1 pre v)))
        (16000000 * (C₀ + 8005) * (n + 1) ^ 4) := by
  set V := (C₀ + 8005) * (n + 1) ^ 2
  have hn1 := n_succ_le_sq n
  have hregV : ∀ i, reg₀ i ≤ V := fun i =>
    (hreg₀ i).trans (Nat.mul_le_mul_right _ (by omega))
  have hHV : reg₀ rHOff + n ≤ V := by
    have h0 := hreg₀ rHOff
    have hd : V = C₀ * (n + 1) ^ 2 + 8005 * (n + 1) ^ 2 := by dsimp only [V]; ring
    omega
  have hPreV : reg₀ rPreOff + 2 * n ≤ V := by
    have h0 := hreg₀ rPreOff
    have hd : V = C₀ * (n + 1) ^ 2 + 8005 * (n + 1) ^ 2 := by dsimp only [V]; ring
    omega
  have hV_ge : 8000 * (n + 1) ^ 2 ≤ V :=
    Nat.mul_le_mul_right _ (by omega)
  rcases rmEmitBlocks0to9_spec mode n h s t0 t1 pre inp V reg₀ hT0 hregV hHV hPreV hV_ge
    with ⟨q₁, reg₁, hfr, hex⟩
  have hT_eq : 16000000 * (n + 1) ^ 2 * V = 16000000 * (C₀ + 8005) * (n + 1) ^ 4 := by
    dsimp only [V]; ring
  exact ⟨q₁, reg₁, hfr, hex.weaken hVmax (le_of_eq hT_eq)⟩

end Branch8CircuitEmit
