import Branch6_EncoderMacros
import Branch6b_ParseAndEdges
import Branch7_EncodeNetSpec

namespace Branch8bTail

open QCSD.Defs
open Branch5PadAndSep
open Branch6Encoder
open Branch7EncodeSpec

/-!
## Section 1: Exact `Branch3` Tail-Predicate Definitions, Tree-Vertex Decoding, and Bit-Literal Lemmas

Zero custom `structure`, `inductive`, or `class` declarations.
All definitions (`ovlInLocal`, `decodeTreeVertAux`, `decodeTreeVert`, `zmod2ToBool`, `rawPredTail`)
are definitionally identical to `Branch3_Network.lean` on `netV10 n ≤ v < netVertCount n`.
-/

def ovlInLocal (J L tk : ℕ) : List ℕ :=
  (if 0 < tk / J ∧ tk / J - 1 < L then [(tk / J - 1) * (2 * J) + (J + tk % J)] else []) ++
  (if tk / J < L then [(tk / J) * (2 * J) + tk % J] else [])

def decodeTreeVertAux (r rem : ℕ) : ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, j => (j, 0, 0)
  | fuel + 1, j =>
    let blk := (j + 1) * 2 ^ (r - j)
    if rem < blk then (j, rem / (j + 1), rem % (j + 1))
    else decodeTreeVertAux r (rem - blk) fuel (j + 1)

def decodeTreeVert (r locV : ℕ) : ℕ × ℕ × ℕ :=
  decodeTreeVertAux r locV r 1

def zmod2ToBool (z : ZMod 2) : Bool := decide (z = (1 : ZMod 2))

/-- Exact `Branch3_Network.rawPred` restricted to Blocks 10–18 (`netV10 n ≤ v < netVertCount n`). -/
def rawPredTail (mode n : ℕ) (s : Fin n → ZMod 2) (t0 t1 : ℕ) (v : ℕ) : QCSD_BoolCircuit :=
  let J := paramJ n
  let L := paramL n
  let r := treeLog n + 1
  let W := treeLog n + 2
  if v < netV11 n then
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

/-! ### `decodeTreeVert_encode` (exact inverse property for nested Block 15 loops) -/

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
    · have hstep : treeVertOff r (j + 1) = treeVertOff r j + blk := treeVertOff_step hj1
      have hrec := decodeTreeVertAux_spec r fuel (j + 1) (rem - blk)
        (by omega) (by omega) (by omega)
      exact ⟨hrec.1, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1, by have := hrec.2.2.2.2; omega⟩

lemma decodeTreeVert_spec {r locV : ℕ} (hloc : locV < treeVertOff r (r + 1)) :
    let t := decodeTreeVert r locV
    1 ≤ t.1 ∧ t.1 ≤ r ∧ t.2.1 < 2 ^ (r - t.1) ∧ t.2.2 < t.1 + 1 ∧
    locV = treeVertOff r t.1 + t.2.1 * (t.1 + 1) + t.2.2 := by
  have h := decodeTreeVertAux_spec r r 1 locV (by omega) (by omega)
    (by simpa [treeVertOff] using hloc)
  simpa [decodeTreeVert, treeVertOff] using h

lemma encodeTreeVert_lt {r j node u : ℕ}
    (hj1 : 1 ≤ j) (hjr : j ≤ r) (hnode : node < 2 ^ (r - j)) (hu : u < j + 1) :
    treeVertOff r j + node * (j + 1) + u < treeVertOff r (r + 1) := by
  have h1 : node * (j + 1) + u < (node + 1) * (j + 1) := by
    have : (node + 1) * (j + 1) = node * (j + 1) + (j + 1) := by ring
    omega
  have h2 : (node + 1) * (j + 1) ≤ 2 ^ (r - j) * (j + 1) := Nat.mul_le_mul_right _ hnode
  have h3 : treeVertOff r (j + 1) = treeVertOff r j + (j + 1) * 2 ^ (r - j) := treeVertOff_step hj1
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
        have hstep := treeVertOff_step (r := r) hj1_lo
        have hmul : (n1 + 1) * (j1 + 1) ≤ 2 ^ (r - j1) * (j1 + 1) := Nat.mul_le_mul_right _ hn1
        have hcomm : 2 ^ (r - j1) * (j1 + 1) = (j1 + 1) * 2 ^ (r - j1) := Nat.mul_comm _ _
        have hlin : (n1 + 1) * (j1 + 1) = n1 * (j1 + 1) + (j1 + 1) := by ring
        omega
      have hb2 : treeVertOff r (j1 + 1) ≤ treeVertOff r j2 := treeVertOff_mono r hlt
      omega
    · rfl
    · have hb2 : treeVertOff r j2 + n2 * (j2 + 1) + u2 < treeVertOff r (j2 + 1) := by
        have hstep := treeVertOff_step (r := r) hj2_lo
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
  have hsp := decodeTreeVert_spec hlt
  set t := decodeTreeVert r (treeVertOff r j + node * (j + 1) + u)
  obtain ⟨e1, e2, e3⟩ := encodeTreeVert_inj hsp.1 hsp.2.2.1 hsp.2.2.2.1 hj1 hnode hu hsp.2.2.2.2.symm
  rcases t with ⟨tj, tn, tu⟩
  dsimp only at e1 e2 e3
  rw [e1, e2, e3]

/-! ### Constant Bit-Literals, Lengths, and `Nat.testBit` Helpers -/

def const0TrueBits : List Bool := [false, true, false, false, false, true]
def const1TrueBits : List Bool := [true, false, true, false, false, false, true]
def pinFalseBits : List Bool :=
  [true, false, true, true, false, false, false, false, false, false, true, true, false]
def sepFAFalseBits : List Bool :=
  [true, true, true, true, true, false, true, false, false, true, false]
def exactCmpFalseBits : List Bool :=
  [true, true, true, false, true, false, false, true, false]
def sepCmpStepBits : List Bool :=
  [true, true, true, false, true, true, false, false, false, false, true, true, false,
   false, true, true, false]

lemma const0TrueBits_len : const0TrueBits.length = 6 := rfl
lemma const1TrueBits_len : const1TrueBits.length = 7 := rfl
lemma pinFalseBits_len : pinFalseBits.length = 13 := rfl
lemma sepFAFalseBits_len : sepFAFalseBits.length = 11 := rfl
lemma exactCmpFalseBits_len : exactCmpFalseBits.length = 9 := rfl
lemma sepCmpStepBits_len : sepCmpStepBits.length = 17 := rfl

lemma ovl0Bits_len : ovl0Bits.length = 92 := by
  simp [ovl0Bits, Branch5PadAndSep.natToUnary_length, encodeEqAt_length]

lemma ovl1Bits_len : ovl1Bits.length = 205 := by
  simp [ovl1Bits, Branch5PadAndSep.natToUnary_length, encodeXorAt_length, encodeEqAt_length]

lemma ovl2Bits_len : ovl2Bits.length = 363 := by
  simp [ovl2Bits, Branch5PadAndSep.natToUnary_length, encodeXorAt_length, encodeEqAt_length]

lemma synCheckBits_len (b : Bool) : (synCheckBits b).length = 322 := by
  rw [← encodeCircuit_synCheckCircuit]; exact encodeCircuit_synCheckCircuit_length b

lemma fullAdderBits_len : fullAdderBits.length = 760 := by
  rw [← encodeCircuit_fullAdderCircuit]; exact encodeCircuit_fullAdderCircuit_length

lemma sepFullAdderBits_len (g b0 b1 : Bool) :
    (sepFullAdderBits g b0 b1).length = if g then 1553 else 11 := by
  rw [← encodeCircuit_sepFullAdderCircuit]; exact encodeCircuit_sepFullAdderCircuit_length g b0 b1

lemma borrowStepBits_len (b : Bool) : (borrowStepBits b).length = 103 := by
  rw [← encodeCircuit_borrowStepCircuit]; exact encodeCircuit_borrowStepCircuit_length b

lemma exactCmpStepBits_len (g b : Bool) :
    (exactCmpStepBits g b).length = if g then 128 else 9 := by
  rw [← encodeCircuit_exactCmpStepCircuit]; exact encodeCircuit_exactCmpStepCircuit_length g b

lemma rmEmitBits_active {R : ℕ} (bs : List Bool) (h : 0 < bs.length) :
    rmEmitBits (R := R) bs ⟨0, by omega⟩ ≠ none := by
  simp [rmEmitBits, h]

lemma testBit_zero_eq_mod (x : ℕ) : x.testBit 0 = decide (x % 2 ≠ 0) := by
  rw [Nat.testBit_zero]
  by_cases h : x % 2 = 0
  · simp [h]
  · have h1 : x % 2 = 1 := by omega
    simp [h1]

lemma testBit_div_two (x k : ℕ) : (x / 2).testBit k = x.testBit (k + 1) :=
  (Nat.testBit_succ x k).symm

lemma two_pow_treeLog_succ (n : ℕ) : 2 ^ (treeLog n + 1) = 2 * treeM n := by
  unfold treeM; rw [pow_succ']

lemma two_pow_treeLog_succ2 (n : ℕ) : 2 ^ (treeLog n + 2) = 4 * treeM n := by
  unfold treeM; rw [pow_succ', pow_succ']; ring

/-! ### 8-Group FlatMap Decomposition of `rawPredTail` across Blocks 10–18 -/

lemma flatMap_range_rawPredTail_eq (mode n : ℕ) (s : Fin n → ZMod 2) (t0 t1 : ℕ) :
    (List.range (netVertCount n - netV10 n)).flatMap
      (fun d => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV10 n + d))) =
    ((((List.range (2 * paramJ n * paramL n)).flatMap (fun k =>
          if ovlTargetBit (paramJ n) (k / (2 * paramJ n)) (k % (2 * paramJ n)) < 2 * n
          then const0TrueBits else const1TrueBits) ++
        (List.range (2 * n)).flatMap (fun tk =>
          QCSD_encodeCircuit (linearMapCheckCircuit (ovlInLocal (paramJ n) (paramL n) tk).length 1
            (fun _ _ => true)))) ++
       ((List.range n).flatMap (fun i =>
          synCheckBits (if hlt : i < n then zmod2ToBool (s ⟨i, hlt⟩) else false)) ++
        (List.range (2 * (treeM n - n))).flatMap (fun _ => pinFalseBits))) ++
      ((List.range (treeVertOff (treeLog n + 1) (treeLog n + 2))).flatMap (fun locV =>
          QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + locV))) ++
       ((pinFalseBits ++
         (List.range (treeLog n + 2)).flatMap (fun b =>
           QCSD_encodeCircuit
             (if mode = 0 then exactCmpStepCircuit (decide (t0 < 2 ^ (treeLog n + 2))) (t0.testBit b)
              else if mode = 1 then borrowStepCircuit (t0.testBit b)
              else sepCmpStepCircuit))) ++
        (if mode = 1 ∧ ¬(t0 < 2 ^ (treeLog n + 2)) then const1TrueBits else pinFalseBits)))) := by
  have h11 : netV11 n = netV10 n + 2 * paramJ n * paramL n := rfl
  have h12 : netV12 n = netV11 n + 2 * n := rfl
  have h13 : netV13 n = netV12 n + n := rfl
  have h14 : netV14 n = netV13 n + (treeM n - n) := rfl
  have h15 : netV15 n = netV14 n + (treeM n - n) := rfl
  have h16 : netV16 n = netV15 n + treeVertOff (treeLog n + 1) (treeLog n + 2) := rfl
  have h17 : netV17 n = netV16 n + 1 := rfl
  have h18 : netV18 n = netV17 n + (treeLog n + 2) := rfl
  have hVC : netVertCount n = netV18 n + 1 := rfl
  have htot : netVertCount n - netV10 n =
      ((((((2 * paramJ n * paramL n + 2 * n) + n) + 2 * (treeM n - n)) +
          treeVertOff (treeLog n + 1) (treeLog n + 2)) + 1) + (treeLog n + 2)) + 1 := by
    omega
  rw [htot, flatMap_range_add, flatMap_range_add, flatMap_range_add, flatMap_range_add,
      flatMap_range_add, flatMap_range_add, flatMap_range_add]
  have hb10 : (List.range (2 * paramJ n * paramL n)).flatMap
      (fun d => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV10 n + d))) =
      (List.range (2 * paramJ n * paramL n)).flatMap (fun k =>
        if ovlTargetBit (paramJ n) (k / (2 * paramJ n)) (k % (2 * paramJ n)) < 2 * n
        then const0TrueBits else const1TrueBits) :=
    list_flatMap_range_congr _ (fun k hk => by
      have hlt : netV10 n + k < netV11 n := by omega
      simp only [rawPredTail, hlt, ↓reduceIte, Nat.add_sub_cancel_left]
      split_ifs <;> rfl)
  have hb11 : (List.range (2 * n)).flatMap
      (fun k => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV10 n + (2 * paramJ n * paramL n + k)))) =
      (List.range (2 * n)).flatMap (fun tk =>
        QCSD_encodeCircuit (linearMapCheckCircuit (ovlInLocal (paramJ n) (paramL n) tk).length 1
          (fun _ _ => true))) :=
    list_flatMap_range_congr _ (fun tk htk => by
      have heq : netV10 n + (2 * paramJ n * paramL n + tk) = netV11 n + tk := by omega
      rw [heq]
      simp only [rawPredTail, show ¬(netV11 n + tk < netV11 n) by omega,
        show netV11 n + tk < netV12 n by omega, ↓reduceIte, Nat.add_sub_cancel_left])
  have hb12 : (List.range n).flatMap
      (fun k => QCSD_encodeCircuit (rawPredTail mode n s t0 t1
        (netV10 n + (2 * paramJ n * paramL n + 2 * n + k)))) =
      (List.range n).flatMap (fun i =>
        synCheckBits (if hlt : i < n then zmod2ToBool (s ⟨i, hlt⟩) else false)) :=
    list_flatMap_range_congr _ (fun i hi => by
      have heq : netV10 n + (2 * paramJ n * paramL n + 2 * n + i) = netV12 n + i := by omega
      rw [heq]
      simp only [rawPredTail, show ¬(netV12 n + i < netV11 n) by omega,
        show ¬(netV12 n + i < netV12 n) by omega, show netV12 n + i < netV13 n by omega,
        ↓reduceIte, Nat.add_sub_cancel_left]
      exact encodeCircuit_synCheckCircuit _)
  have hb1314 : (List.range (2 * (treeM n - n))).flatMap
      (fun k => QCSD_encodeCircuit (rawPredTail mode n s t0 t1
        (netV10 n + (2 * paramJ n * paramL n + 2 * n + n + k)))) =
      (List.range (2 * (treeM n - n))).flatMap (fun _ => pinFalseBits) :=
    list_flatMap_range_congr _ (fun k hk => by
      have heq : netV10 n + (2 * paramJ n * paramL n + 2 * n + n + k) = netV13 n + k := by omega
      rw [heq]
      by_cases h14lt : netV13 n + k < netV14 n
      · simp only [rawPredTail, show ¬(netV13 n + k < netV11 n) by omega,
          show ¬(netV13 n + k < netV12 n) by omega, show ¬(netV13 n + k < netV13 n) by omega,
          h14lt, ↓reduceIte]; rfl
      · simp only [rawPredTail, show ¬(netV13 n + k < netV11 n) by omega,
          show ¬(netV13 n + k < netV12 n) by omega, show ¬(netV13 n + k < netV13 n) by omega,
          h14lt, show netV13 n + k < netV15 n by omega, ↓reduceIte]; rfl)
  have hb15 : (List.range (treeVertOff (treeLog n + 1) (treeLog n + 2))).flatMap
      (fun k => QCSD_encodeCircuit (rawPredTail mode n s t0 t1
        (netV10 n + (2 * paramJ n * paramL n + 2 * n + n + 2 * (treeM n - n) + k)))) =
      (List.range (treeVertOff (treeLog n + 1) (treeLog n + 2))).flatMap
        (fun locV => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + locV))) :=
    list_flatMap_range_congr _ (fun k _ => by
      have heq : netV10 n + (2 * paramJ n * paramL n + 2 * n + n + 2 * (treeM n - n) + k) =
          netV15 n + k := by omega
      rw [heq])
  have hb16 : (List.range 1).flatMap
      (fun k => QCSD_encodeCircuit (rawPredTail mode n s t0 t1
        (netV10 n + (2 * paramJ n * paramL n + 2 * n + n + 2 * (treeM n - n) +
          treeVertOff (treeLog n + 1) (treeLog n + 2) + k)))) = pinFalseBits := by
    have heq : netV10 n + (2 * paramJ n * paramL n + 2 * n + n + 2 * (treeM n - n) +
        treeVertOff (treeLog n + 1) (treeLog n + 2) + 0) = netV16 n := by omega
    simp only [List.range_one, List.flatMap_singleton, heq]
    simp only [rawPredTail, show ¬(netV16 n < netV11 n) by omega,
      show ¬(netV16 n < netV12 n) by omega, show ¬(netV16 n < netV13 n) by omega,
      show ¬(netV16 n < netV14 n) by omega, show ¬(netV16 n < netV15 n) by omega,
      show ¬(netV16 n < netV16 n) by omega, show netV16 n < netV17 n by omega, ↓reduceIte]
    rfl
  have hb17 : (List.range (treeLog n + 2)).flatMap
      (fun k => QCSD_encodeCircuit (rawPredTail mode n s t0 t1
        (netV10 n + (2 * paramJ n * paramL n + 2 * n + n + 2 * (treeM n - n) +
          treeVertOff (treeLog n + 1) (treeLog n + 2) + 1 + k)))) =
      (List.range (treeLog n + 2)).flatMap (fun b =>
        QCSD_encodeCircuit
          (if mode = 0 then exactCmpStepCircuit (decide (t0 < 2 ^ (treeLog n + 2))) (t0.testBit b)
           else if mode = 1 then borrowStepCircuit (t0.testBit b)
           else sepCmpStepCircuit)) :=
    list_flatMap_range_congr _ (fun b hb => by
      have heq : netV10 n + (2 * paramJ n * paramL n + 2 * n + n + 2 * (treeM n - n) +
          treeVertOff (treeLog n + 1) (treeLog n + 2) + 1 + b) = netV17 n + b := by omega
      rw [heq]
      simp only [rawPredTail, show ¬(netV17 n + b < netV11 n) by omega,
        show ¬(netV17 n + b < netV12 n) by omega, show ¬(netV17 n + b < netV13 n) by omega,
        show ¬(netV17 n + b < netV14 n) by omega, show ¬(netV17 n + b < netV15 n) by omega,
        show ¬(netV17 n + b < netV16 n) by omega, show ¬(netV17 n + b < netV17 n) by omega,
        show netV17 n + b < netV18 n by omega, ↓reduceIte, Nat.add_sub_cancel_left])
  have hb18 : (List.range 1).flatMap
      (fun k => QCSD_encodeCircuit (rawPredTail mode n s t0 t1
        (netV10 n + (2 * paramJ n * paramL n + 2 * n + n + 2 * (treeM n - n) +
          treeVertOff (treeLog n + 1) (treeLog n + 2) + 1 + (treeLog n + 2) + k)))) =
      (if mode = 1 ∧ ¬(t0 < 2 ^ (treeLog n + 2)) then const1TrueBits else pinFalseBits) := by
    have heq : netV10 n + (2 * paramJ n * paramL n + 2 * n + n + 2 * (treeM n - n) +
        treeVertOff (treeLog n + 1) (treeLog n + 2) + 1 + (treeLog n + 2) + 0) = netV18 n := by omega
    simp only [List.range_one, List.flatMap_singleton, heq]
    simp only [rawPredTail, show ¬(netV18 n < netV11 n) by omega,
      show ¬(netV18 n < netV12 n) by omega, show ¬(netV18 n < netV13 n) by omega,
      show ¬(netV18 n < netV14 n) by omega, show ¬(netV18 n < netV15 n) by omega,
      show ¬(netV18 n < netV16 n) by omega, show ¬(netV18 n < netV17 n) by omega,
      show ¬(netV18 n < netV18 n) by omega, ↓reduceIte]
    split_ifs <;> rfl
  rw [hb10, hb11, hb12, hb1314, hb15, hb16, hb17, hb18]
  simp only [List.append_assoc]

/-!
## Section 2: Vertex Circuit Emitters for Blocks 10, 11, 12, and 13–14
-/

/-! ### Block 10 (`v_c2`, `2 * J * L` vertices) -/

abbrev RMV10IfQ : Type := Option Bool ⊕ (Fin (const1TrueBits.length + 1) ⊕ (Bool ⊕ Fin (const0TrueBits.length + 1)))
abbrev RMV10BodyQ : Type := RMDivModQ ⊕ (RMMulQ ⊕ (RMAddQ ⊕ (Fin 8 ⊕ RMV10IfQ)))
abbrev RMEmitV10Q : Type := RMForRangeQ RMV10BodyQ

def rmV10Body : RMProg EncR RMV10BodyQ :=
  rmChain (rmDivMod regS1 regS2 regLoopI regTwoJ regS3 regS4 regS5)
    (rmChain (rmMul regS3 regS1 regJ regS4 regS5)
      (rmChain (rmAdd regS3 regS2 regS4)
        (rmChain (rmCmpLt regS0 regS3 regV1 regS4 regS5)
          (rmIfZero regS0 (rmEmitBits const1TrueBits) (rmEmitBits const0TrueBits)
            ⟨0, by decide⟩ ⟨0, by decide⟩)
          rmIfZeroEntry)
        (Sum.inl 0))
      (Sum.inl rmAddEntry))
    (Sum.inl rmMulEntry)

def rmV10BodyEntry : RMV10BodyQ := Sum.inl rmDivModEntry

def rmEmitV10 : RMProg EncR RMEmitV10Q :=
  rmForRange regLoopI regLoopRem regTwoJL rmV10Body rmV10BodyEntry

lemma rmEmitV10_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitV10 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * paramJ n * paramL n)).flatMap (fun k =>
          if ovlTargetBit (paramJ n) (k / (2 * paramJ n)) (k % (2 * paramJ n)) < 2 * n
          then const0TrueBits else const1TrueBits))
        (65000 * n ^ 2 + 4000 * n + 10) := by
  have h1V : 1 ≤ V := by omega
  have hJ_pos : 0 < paramJ n := one_le_paramJ n
  have hJ_le : paramJ n ≤ 9 * n := paramJ_le_nine_mul hn
  have hL_le : paramL n ≤ 27 * n := paramL_le_27_mul hn
  have h2JL_lt : 2 * paramJ n * paramL n < 54 * n := two_J_L_lt hn
  have hcnt : reg₀ regTwoJL = 2 * paramJ n * paramL n :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rcases rmEdgeLoop_spec regTwoJL (by decide) rmV10Body rmV10BodyEntry
      V (1100 * n + 60) inp reg₀
      (fun k =>
        if ovlTargetBit (paramJ n) (k / (2 * paramJ n)) (k % (2 * paramJ n)) < 2 * n
        then const0TrueBits else const1TrueBits)
      hreg₀ (by
        intro k reg hk hpr hreg hI
        have hp' := hp.of_preserved hpr
        have hJ : reg regJ = paramJ n := hp'.2.2.1
        have hV1 : reg regV1 = netV1 n := hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have h2J : reg regTwoJ = 2 * paramJ n :=
          hp'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hk' : k < 2 * paramJ n * paramL n := by omega
        set blk := k / (2 * paramJ n)
        set p := k % (2 * paramJ n)
        have hblk_lt : blk < paramL n := Nat.div_lt_of_lt_mul hk'
        have hp_lt : p < 2 * paramJ n := Nat.mod_lt _ (by omega)
        have hblkJ_lt : blk * paramJ n < 27 * n := by
          have h1 : blk * paramJ n ≤ paramL n * paramJ n := Nat.mul_le_mul_right _ (le_of_lt hblk_lt)
          have h2 : paramL n * paramJ n = paramJ n * paramL n := Nat.mul_comm _ _
          have h3 : 2 * paramJ n * paramL n = 2 * (paramJ n * paramL n) := by ring
          omega
        rcases rmDivMod_spec regS1 regS2 regLoopI regTwoJ regS3 regS4 regS5
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp reg (by rw [h2J]; omega) hreg h1V
          with ⟨s1, hs1_q, hs1_r, hs1_fr, hd1⟩
        have hs1_blk : s1 regS1 = blk := by rw [hs1_q, hI, h2J]
        have hs1_p : s1 regS2 = p := by rw [hs1_r, hI, h2J]
        have hs1_J : s1 regJ = paramJ n := by
          rw [hs1_fr regJ (by decide) (by decide) (by decide) (by decide) (by decide), hJ]
        rcases rmMul_spec regS3 regS1 regJ regS4 regS5
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            V inp s1 hd1.reg₁_le (by rw [hs1_blk, hs1_J]; omega)
          with ⟨s2, hs2_mul, hs2_fr, hm2⟩
        have hs2_S3 : s2 regS3 = blk * paramJ n := by rw [hs2_mul, hs1_blk, hs1_J]
        have hs2_p : s2 regS2 = p := by rw [hs2_fr regS2 (by decide) (by decide) (by decide), hs1_p]
        have ha3 := rmAdd_spec regS3 regS2 regS4 (by decide) (by decide) V inp s2 hm2.reg₁_le
          (by rw [hs2_S3, hs2_p]; omega)
        set s3 := regUpd (regUpd s2 regS3 (s2 regS3 + s2 regS2)) regS4 0
        have hs3_tk : s3 regS3 = blk * paramJ n + p := by simp [s3, hs2_S3, hs2_p]
        have hs3_V1 : s3 regV1 = 2 * n := by
          dsimp only [s3]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide),
            hs2_fr regV1 (by decide) (by decide) (by decide),
            hs1_fr regV1 (by decide) (by decide) (by decide) (by decide) (by decide), hV1, netV1]
        rcases rmCmpLt_spec regS0 regS3 regV1 regS4 regS5 (by decide) (by decide) (by decide) (by decide)
            V inp s3 ha3.reg₁_le h1V with ⟨s4, hs4_fl, hs4_fr, hcmp4⟩
        have hbr : ∃ qB, RMExec
            (rmIfZero regS0 (rmEmitBits const1TrueBits) (rmEmitBits const0TrueBits)
              ⟨0, by decide⟩ ⟨0, by decide⟩)
            V inp rmIfZeroEntry s4 qB s4
            (if blk * paramJ n + p < 2 * n then const0TrueBits else const1TrueBits) 10 := by
          by_cases hlt : blk * paramJ n + p < 2 * n
          · have hfl : s4 regS0 ≠ 0 := by rw [hs4_fl, hs3_tk, hs3_V1]; simp [hlt]
            have he := rmEmitBits_spec const0TrueBits V inp s4 hcmp4.reg₁_le
            have hif := (rmIfZero_pos_spec regS0 (rmEmitBits const1TrueBits) ⟨0, by decide⟩ hfl he).weaken
              (V₂ := V) (T₂ := 10) (le_refl _) (by rw [const0TrueBits_len]; omega)
            simp only [hlt, ↓reduceIte]; exact ⟨_, hif⟩
          · have hfl : s4 regS0 = 0 := by rw [hs4_fl, hs3_tk, hs3_V1]; simp [hlt]
            have he := rmEmitBits_spec const1TrueBits V inp s4 hcmp4.reg₁_le
            have hif := (rmIfZero_zero_spec regS0 (rmEmitBits const0TrueBits) ⟨0, by decide⟩ hfl he).weaken
              (V₂ := V) (T₂ := 10) (le_refl _) (by rw [const1TrueBits_len]; omega)
            simp only [hlt, ↓reduceIte]; exact ⟨_, hif⟩
        rcases hbr with ⟨qB, hif⟩
        have hcomb := rmChain_spec_inl (by simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]) hd1
          (rmChain_spec_inl (by simp [rmMul, rmMulEntry, rmChain, rmSeq, rmZero]) hm2
            (rmChain_spec_inl (by simp [rmAdd, rmAddEntry, rmChain, rmSeq, rmCopy]) ha3
              (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp4 hif)))
        have hmul_le : blk * (2 * paramJ n + 3) ≤ 140 * n := by
          have : blk * (2 * paramJ n + 3) = 2 * (blk * paramJ n) + 3 * blk := by ring
          omega
        have hT : 15 * reg regLoopI + 2 * reg regTwoJ + 10 +
            (s1 regS1 * (2 * s1 regJ + 3) + 3 +
              (2 * s2 regS2 + 2 + (2 * min (s3 regS3) (s3 regV1) + 6 + 10))) ≤ 1100 * n + 60 := by
          rw [hI, h2J, hs1_blk, hs1_J, hs2_p, hs3_tk, hs3_V1]
          have : min (blk * paramJ n + p) (2 * n) ≤ 2 * n := min_le_right _ _
          omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 1100 * n + 60) (by simp) hT
        simp only [List.nil_append] at hfin
        have hkeep : ∀ j : Fin EncR, j.val < 41 ∨ j = regLoopI ∨ j = regLoopRem → s4 j = reg j := by
          intro j hj
          have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 46) → j ≠ r := by
            intro r hr heq; have hv := congrArg Fin.val heq
            rcases hj with hj | rfl | rfl <;> (try simp at hv) <;> omega
          rw [hs4_fr j (hne regS0 (by decide)) (hne regS4 (by decide)) (hne regS5 (by decide))]
          dsimp only [s3]
          rw [regUpd_ne _ (hne regS4 (by decide)), regUpd_ne _ (hne regS3 (by decide)),
              hs2_fr j (hne regS3 (by decide)) (hne regS4 (by decide)) (hne regS5 (by decide)),
              hs1_fr j (hne regS1 (by decide)) (hne regS2 (by decide)) (hne regS3 (by decide))
                (hne regS4 (by decide)) (hne regS5 (by decide))]
        refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr qB))), s4,
          fun j hj => hkeep j (Or.inl hj),
          by rw [hkeep regLoopI (Or.inr (Or.inl rfl)), hI],
          hkeep regLoopRem (Or.inr (Or.inr rfl)), ?_⟩
        rw [ovlTargetBit_eq]
        exact hfin)
    with ⟨reg₁, hpr₁, hex⟩
  rw [hcnt] at hex
  have hT : 2 * paramJ n * paramL n * (1100 * n + 60 + 2) + 3 ≤ 65000 * n ^ 2 + 4000 * n + 10 := by
    have hmul : 2 * paramJ n * paramL n * (1100 * n + 60 + 2) ≤ 54 * n * (1100 * n + 60 + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have hring : 54 * n * (1100 * n + 60 + 2) = 59400 * n ^ 2 + 3348 * n := by ring
    omega
  exact ⟨reg₁, hpr₁, hex.weaken (V₂ := V) (T₂ := 65000 * n ^ 2 + 4000 * n + 10) (le_refl _) hT⟩

/-! ### Block 11 (`v_ovl`, `2 * n` vertices) -/

abbrev RMV11Inc1Q : Type := Option Bool ⊕ (Unit ⊕ (Bool ⊕ Bool))
abbrev RMV11Check2Q : Type := Bool ⊕ (Bool ⊕ (Fin 8 ⊕ RMV11Inc1Q))
abbrev RMV11Inc2Q : Type := Option Bool ⊕ (Unit ⊕ (Bool ⊕ RMV11Check2Q))
abbrev RMV11Emit12Q : Type :=
  Bool ⊕ (Option Bool ⊕ (Fin (ovl1Bits.length + 1) ⊕ (Bool ⊕ Fin (ovl2Bits.length + 1))))
abbrev RMV11EmitQ : Type := Option Bool ⊕ (Fin (ovl0Bits.length + 1) ⊕ (Bool ⊕ RMV11Emit12Q))
abbrev RMV11BodyQ : Type := RMDivModQ ⊕ (Bool ⊕ (Fin 8 ⊕ (RMV11Inc1Q ⊕ (RMV11Inc2Q ⊕ RMV11EmitQ))))
abbrev RMEmitV11Q : Type := RMForRangeQ RMV11BodyQ

def rmV11Inc1 : RMProg EncR RMV11Inc1Q :=
  rmIfZero regS0 rmNop (rmInc regS7) () false

def rmV11Check2 : RMProg EncR RMV11Check2Q :=
  rmChain (rmCopy regS4 regS1)
    (rmChain (rmDec1 regS4)
      (rmChain (rmCmpLt regS0 regS4 regL regS2 regS3) rmV11Inc1 rmIfZeroEntry)
      (Sum.inl 0))
    (Sum.inl false)

def rmV11Inc2 : RMProg EncR RMV11Inc2Q :=
  rmIfZero regS1 rmNop rmV11Check2 () (Sum.inl false)

def rmV11Emit12 : RMProg EncR RMV11Emit12Q :=
  rmChain (rmDec1 regS7)
    (rmIfZero regS7 (rmEmitBits ovl1Bits) (rmEmitBits ovl2Bits) ⟨0, by omega⟩ ⟨0, by omega⟩)
    rmIfZeroEntry

def rmV11Emit : RMProg EncR RMV11EmitQ :=
  rmIfZero regS7 (rmEmitBits ovl0Bits) rmV11Emit12 ⟨0, by omega⟩ (Sum.inl false)

def rmV11Body : RMProg EncR RMV11BodyQ :=
  rmChain (rmDivMod regS1 regS2 regLoopI regJ regS3 regS4 regS5)
    (rmChain (rmZero regS7)
      (rmChain (rmCmpLt regS0 regS1 regL regS2 regS3)
        (rmChain rmV11Inc1 (rmChain rmV11Inc2 rmV11Emit rmIfZeroEntry) (Sum.inl rmIfZeroEntry))
        (Sum.inl rmIfZeroEntry))
      (Sum.inl 0))
    (Sum.inl false)

def rmV11BodyEntry : RMV11BodyQ := Sum.inl rmDivModEntry

def rmEmitV11 : RMProg EncR RMEmitV11Q :=
  rmForRange regLoopI regLoopRem regV1 rmV11Body rmV11BodyEntry

lemma ovlInLocal_length_eq (J L tk : ℕ) :
    (ovlInLocal J L tk).length =
      (if tk / J < L then 1 else 0) + (if 0 < tk / J ∧ tk / J - 1 < L then 1 else 0) := by
  unfold ovlInLocal
  rw [List.length_append]
  split_ifs <;> simp

lemma rmEmitV11_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitV11 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range (2 * n)).flatMap (fun tk =>
          QCSD_encodeCircuit (linearMapCheckCircuit (ovlInLocal (paramJ n) (paramL n) tk).length 1
            (fun _ _ => true))))
        (300 * n ^ 2 + 1200 * n + 10) := by
  have h1V : 1 ≤ V := by omega
  have hJ_pos : 0 < paramJ n := one_le_paramJ n
  have hJ_le : paramJ n ≤ 9 * n := paramJ_le_nine_mul hn
  have hL_le : paramL n ≤ 27 * n := paramL_le_27_mul hn
  have hovl0 := ovl0Bits_len
  have hovl1 := ovl1Bits_len
  have hovl2 := ovl2Bits_len
  have hcnt : reg₀ regV1 = 2 * n := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases rmEdgeLoop_spec regV1 (by decide) rmV11Body rmV11BodyEntry
      V (100 * n + 470) inp reg₀
      (fun tk =>
        QCSD_encodeCircuit (linearMapCheckCircuit (ovlInLocal (paramJ n) (paramL n) tk).length 1
          (fun _ _ => true)))
      hreg₀ (by
        intro tk reg htk hpr hreg hI
        have hp' := hp.of_preserved hpr
        have hJ : reg regJ = paramJ n := hp'.2.2.1
        have hL : reg regL = paramL n := hp'.2.2.2.2.2.1
        have htk' : tk < 2 * n := by omega
        set q := tk / paramJ n
        have hq_le : q ≤ 2 * n := le_trans (Nat.div_le_self _ _) (by omega)
        rcases rmDivMod_spec regS1 regS2 regLoopI regJ regS3 regS4 regS5
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide)
            V inp reg (by rw [hJ]; exact hJ_pos) hreg h1V
          with ⟨s1, hs1_q, _, hs1_fr, hd1⟩
        have hs1_S1 : s1 regS1 = q := by rw [hs1_q, hI, hJ]
        have hs1_L : s1 regL = paramL n := by
          rw [hs1_fr regL (by decide) (by decide) (by decide) (by decide) (by decide), hL]
        have hz2 := rmZero_spec regS7 V inp s1 hd1.reg₁_le
        set s2 := regUpd s1 regS7 0
        have hs2_S1 : s2 regS1 = q := by simp [s2, hs1_S1]
        have hs2_L : s2 regL = paramL n := by simp [s2, hs1_L]
        rcases rmCmpLt_spec regS0 regS1 regL regS2 regS3 (by decide) (by decide) (by decide) (by decide)
            V inp s2 hz2.reg₁_le h1V with ⟨s3, hs3_fl, hs3_fr, hcmp3⟩
        have hs3_S7 : s3 regS7 = 0 := by rw [hs3_fr regS7 (by decide) (by decide) (by decide)]; simp [s2]
        have hs3_S1 : s3 regS1 = q := by rw [hs3_fr regS1 (by decide) (by decide) (by decide), hs2_S1]
        have hs3_L : s3 regL = paramL n := by rw [hs3_fr regL (by decide) (by decide) (by decide), hs2_L]
        -- Step 4: rmV11Inc1
        have hinc1 : ∃ q4 s4,
            s4 regS7 = (if q < paramL n then 1 else 0) ∧
            (∀ k : Fin EncR, k ≠ regS7 → s4 k = s3 k) ∧
            RMExec rmV11Inc1 V inp rmIfZeroEntry s3 q4 s4 [] 3 := by
          by_cases hlt : q < paramL n
          · have hfl : s3 regS0 ≠ 0 := by rw [hs3_fl, hs2_S1, hs2_L]; simp [hlt]
            have hi := rmInc_spec regS7 V inp s3 hcmp3.reg₁_le (by rw [hs3_S7]; omega)
            have hif := rmIfZero_pos_spec regS0 rmNop () hfl hi
            exact ⟨_, regUpd s3 regS7 (s3 regS7 + 1), by simp [hlt, hs3_S7],
              fun k hk => regUpd_ne s3 hk _, hif⟩
          · have hfl : s3 regS0 = 0 := by rw [hs3_fl, hs2_S1, hs2_L]; simp [hlt]
            have hif := (rmIfZero_zero_spec regS0 (rmInc regS7) false hfl
              (rmNop_spec V inp s3 hcmp3.reg₁_le)).weaken (V₂ := V) (T₂ := 3) (le_refl _) (by omega)
            exact ⟨_, s3, by simp [hlt, hs3_S7], fun _ _ => rfl, hif⟩
        rcases hinc1 with ⟨q4, s4, hs4_S7, hs4_fr, hi4⟩
        have hs4_S1 : s4 regS1 = q := by rw [hs4_fr regS1 (by decide), hs3_S1]
        have hs4_L : s4 regL = paramL n := by rw [hs4_fr regL (by decide), hs3_L]
        -- Step 5: rmV11Inc2
        have hinc2 : ∃ q5 s5,
            s5 regS7 = (if q < paramL n then 1 else 0) + (if 0 < q ∧ q - 1 < paramL n then 1 else 0) ∧
            (∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem → s5 k = s4 k) ∧
            RMExec rmV11Inc2 V inp rmIfZeroEntry s4 q5 s5 [] (4 * n + 20) := by
          by_cases hq0 : q = 0
          · have hif := (rmIfZero_zero_spec regS1 rmV11Check2 (Sum.inl false) (by rw [hs4_S1, hq0])
              (rmNop_spec V inp s4 hi4.reg₁_le)).weaken (V₂ := V) (T₂ := 4 * n + 20) (le_refl _) (by omega)
            exact ⟨_, s4, by simp [hq0, hs4_S7], fun _ _ => rfl, hif⟩
          · have hc1 := rmCopy_spec regS4 regS1 V inp s4 hi4.reg₁_le
            set t1 := regUpd s4 regS4 (s4 regS1)
            have hd2 := rmDec1_spec regS4 V inp t1 hc1.reg₁_le
            set t2 := regUpd t1 regS4 (t1 regS4 - 1)
            have ht2_S4 : t2 regS4 = q - 1 := by simp [t2, t1, hs4_S1]
            have ht2_L : t2 regL = paramL n := by simp [t2, t1, hs4_L]
            rcases rmCmpLt_spec regS0 regS4 regL regS2 regS3 (by decide) (by decide) (by decide) (by decide)
                V inp t2 hd2.reg₁_le h1V with ⟨t3, ht3_fl, ht3_fr, hcmp⟩
            have ht3_S7 : t3 regS7 = (if q < paramL n then 1 else 0) := by
              rw [ht3_fr regS7 (by decide) (by decide) (by decide)]; simp [t2, t1, hs4_S7]
            have hsub : ∃ qS t4,
                t4 regS7 = (if q < paramL n then 1 else 0) + (if q - 1 < paramL n then 1 else 0) ∧
                (∀ k : Fin EncR, k ≠ regS7 → t4 k = t3 k) ∧
                RMExec rmV11Inc1 V inp rmIfZeroEntry t3 qS t4 [] 3 := by
              by_cases hlt2 : q - 1 < paramL n
              · have hfl2 : t3 regS0 ≠ 0 := by rw [ht3_fl, ht2_S4, ht2_L]; simp [hlt2]
                have hi := rmInc_spec regS7 V inp t3 hcmp.reg₁_le (by rw [ht3_S7]; split_ifs <;> omega)
                exact ⟨_, regUpd t3 regS7 (t3 regS7 + 1), by simp [hlt2, ht3_S7],
                  fun k hk => regUpd_ne t3 hk _, rmIfZero_pos_spec regS0 rmNop () hfl2 hi⟩
              · have hfl2 : t3 regS0 = 0 := by rw [ht3_fl, ht2_S4, ht2_L]; simp [hlt2]
                have hif := (rmIfZero_zero_spec regS0 (rmInc regS7) false hfl2
                  (rmNop_spec V inp t3 hcmp.reg₁_le)).weaken (V₂ := V) (T₂ := 3) (le_refl _) (by omega)
                exact ⟨_, t3, by simp [hlt2, ht3_S7], fun _ _ => rfl, hif⟩
            rcases hsub with ⟨qS, t4, ht4_S7, ht4_fr, hif_s⟩
            have hchk := rmChain_spec_inl (by simp [rmCopy]) hc1
              (rmChain_spec_inl (by simp [rmDec1]) hd2
                (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp hif_s))
            have hT2 : 2 + (1 + (1 + (2 * min (t2 regS4) (t2 regL) + 6 + 3))) ≤ 4 * n + 20 := by
              rw [ht2_S4, ht2_L]; have : min (q - 1) (paramL n) ≤ q - 1 := min_le_left _ _; omega
            have hif := (rmIfZero_pos_spec regS1 rmNop () (by rw [hs4_S1]; exact hq0) hchk).weaken
              (V₂ := V) (T₂ := 4 * n + 20) (by simp) hT2
            simp only [List.nil_append] at hif
            refine ⟨_, t4, by rw [ht4_S7]; simp [show 0 < q by omega], ?_, hif⟩
            intro k hk
            have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) → k ≠ r := by
              intro r hr heq; have hv := congrArg Fin.val heq
              rcases hk with hk | rfl | rfl <;> (try simp at hv) <;> omega
            rw [ht4_fr k (hne regS7 (by decide)),
                ht3_fr k (hne regS0 (by decide)) (hne regS2 (by decide)) (hne regS3 (by decide))]
            dsimp only [t2, t1]
            rw [regUpd_ne _ (hne regS4 (by decide)), regUpd_ne _ (hne regS4 (by decide))]
        rcases hinc2 with ⟨q5, s5, hs5_S7, hs5_keep, hi5⟩
        have hs5_dIn : s5 regS7 = (ovlInLocal (paramJ n) (paramL n) tk).length := by
          rw [hs5_S7, ovlInLocal_length_eq]
        -- Step 6: rmV11Emit
        have hemit : ∃ q6 s6,
            (∀ k : Fin EncR, k ≠ regS7 → s6 k = s5 k) ∧
            RMExec rmV11Emit V inp rmIfZeroEntry s5 q6 s6
              (QCSD_encodeCircuit (linearMapCheckCircuit (ovlInLocal (paramJ n) (paramL n) tk).length 1
                (fun _ _ => true))) 400 := by
          have hdle : (ovlInLocal (paramJ n) (paramL n) tk).length ≤ 2 := by
            rw [ovlInLocal_length_eq]; split_ifs <;> omega
          rcases (show (ovlInLocal (paramJ n) (paramL n) tk).length = 0 ∨
              (ovlInLocal (paramJ n) (paramL n) tk).length = 1 ∨
              (ovlInLocal (paramJ n) (paramL n) tk).length = 2 by omega) with hd0 | hd1' | hd2'
          · have h0 := rmEmitBits_spec ovl0Bits V inp s5 hi5.reg₁_le
            have hif := (rmIfZero_zero_spec regS7 rmV11Emit12 (Sum.inl false) (by rw [hs5_dIn, hd0]) h0).weaken
              (V₂ := V) (T₂ := 400) (le_refl _) (by omega)
            rw [hd0, encodeCircuit_ovl0]
            exact ⟨_, s5, fun _ _ => rfl, hif⟩
          · have hd := rmDec1_spec regS7 V inp s5 hi5.reg₁_le
            set s6 := regUpd s5 regS7 (s5 regS7 - 1)
            have h1 := rmEmitBits_spec ovl1Bits V inp s6 hd.reg₁_le
            have hif1 := rmIfZero_zero_spec regS7 (rmEmitBits ovl2Bits) ⟨0, by omega⟩
              (by simp [s6, hs5_dIn, hd1']) h1
            have hc12 := rmChain_spec_inl (by simp [rmDec1]) hd hif1
            have hif := (rmIfZero_pos_spec regS7 (rmEmitBits ovl0Bits) ⟨0, by omega⟩
              (by rw [hs5_dIn, hd1']; omega) hc12).weaken (V₂ := V) (T₂ := 400) (by simp) (by omega)
            simp only [List.nil_append] at hif
            rw [hd1', encodeCircuit_ovl1]
            exact ⟨_, s6, fun k hk => regUpd_ne s5 hk _, hif⟩
          · have hd := rmDec1_spec regS7 V inp s5 hi5.reg₁_le
            set s6 := regUpd s5 regS7 (s5 regS7 - 1)
            have h2 := rmEmitBits_spec ovl2Bits V inp s6 hd.reg₁_le
            have hif2 := rmIfZero_pos_spec regS7 (rmEmitBits ovl1Bits) ⟨0, by omega⟩
              (by simp [s6, hs5_dIn, hd2']) h2
            have hc12 := rmChain_spec_inl (by simp [rmDec1]) hd hif2
            have hif := (rmIfZero_pos_spec regS7 (rmEmitBits ovl0Bits) ⟨0, by omega⟩
              (by rw [hs5_dIn, hd2']; omega) hc12).weaken (V₂ := V) (T₂ := 400) (by simp) (by omega)
            simp only [List.nil_append] at hif
            rw [hd2', encodeCircuit_ovl2]
            exact ⟨_, s6, fun k hk => regUpd_ne s5 hk _, hif⟩
        rcases hemit with ⟨q6, s6, hs6_fr, he6⟩
        have hact_if : ∀ (r : Fin EncR) {Qa Qb : Type} (Ma : RMProg EncR Qa) (Mb : RMProg EncR Qb)
            (qa : Qa) (qb : Qb), rmIfZero r Ma Mb qa qb rmIfZeroEntry ≠ none := by
          intros; simp [rmIfZero, rmIfZeroEntry, rmDecBranch, rmDecBranchEntry, rmSeq, rmDecJzProg]
        have hcomb := rmChain_spec_inl (by simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]) hd1
          (rmChain_spec_inl (by simp [rmZero]) hz2
            (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp3
              (rmChain_spec_inl (hact_if _ _ _ _ _) hi4
                (rmChain_spec_inl (hact_if _ _ _ _ _) hi5 he6))))
        have hT : 15 * reg regLoopI + 2 * reg regJ + 10 +
            (1 + (2 * min (s2 regS1) (s2 regL) + 6 + (3 + (4 * n + 20 + 400)))) ≤ 100 * n + 470 := by
          rw [hI, hJ, hs2_S1, hs2_L]; have : min q (paramL n) ≤ q := min_le_left _ _; omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 100 * n + 470) (by simp) hT
        simp only [List.nil_append] at hfin
        have hkeep : ∀ k : Fin EncR, k.val < 41 ∨ k = regLoopI ∨ k = regLoopRem → s6 k = reg k := by
          intro k hk
          have hne : ∀ r : Fin EncR, (41 ≤ r.val ∧ r.val ≤ 48) → k ≠ r := by
            intro r hr heq; have hv := congrArg Fin.val heq
            rcases hk with hk | rfl | rfl <;> (try simp at hv) <;> omega
          rw [hs6_fr k (hne regS7 (by decide)), hs5_keep k hk, hs4_fr k (hne regS7 (by decide)),
              hs3_fr k (hne regS0 (by decide)) (hne regS2 (by decide)) (hne regS3 (by decide))]
          dsimp only [s2]
          rw [regUpd_ne _ (hne regS7 (by decide)),
              hs1_fr k (hne regS1 (by decide)) (hne regS2 (by decide)) (hne regS3 (by decide))
                (hne regS4 (by decide)) (hne regS5 (by decide))]
        exact ⟨_, s6, fun k hk => hkeep k (Or.inl hk),
          by rw [hkeep regLoopI (Or.inr (Or.inl rfl)), hI],
          hkeep regLoopRem (Or.inr (Or.inr rfl)), hfin⟩)
    with ⟨reg₁, hpr₁, hex⟩
  rw [hcnt] at hex
  have hT : 2 * n * (100 * n + 470 + 2) + 3 ≤ 300 * n ^ 2 + 1200 * n + 10 := by
    have : 2 * n * (100 * n + 470 + 2) + 3 = 200 * n ^ 2 + 944 * n + 3 := by ring
    omega
  exact ⟨reg₁, hpr₁, hex.weaken (V₂ := V) (T₂ := 300 * n ^ 2 + 1200 * n + 10) (le_refl _) hT⟩

/-! ### Block 12 (`v_syn`, `n` vertices) -/

abbrev RMV12IfQ : Type :=
  Option Bool ⊕ (Fin ((synCheckBits false).length + 1) ⊕ Fin ((synCheckBits true).length + 1))
abbrev RMV12BodyQ : Type := RMSetAddQ ⊕ RMV12IfQ
abbrev RMEmitV12Q : Type := RMForRangeQ RMV12BodyQ

def rmV12Body : RMProg EncR RMV12BodyQ :=
  rmChain (rmSetAdd regS1 regOffS regLoopI)
    (rmIfReadIn regS1 (rmEmitBits (synCheckBits false)) (rmEmitBits (synCheckBits true))
      ⟨0, by omega⟩ ⟨0, by omega⟩)
    rmIfReadInEntry

def rmV12BodyEntry : RMV12BodyQ := Sum.inl rmSetAddEntry

def rmEmitV12 : RMProg EncR RMEmitV12Q :=
  rmForRange regLoopI regLoopRem regN rmV12Body rmV12BodyEntry

lemma rmEmitV12_spec (n V : ℕ) (s : Fin n → ZMod 2) (inp : List Bool) (reg₀ : RegState EncR)
    (_hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V)
    (hOffS : reg₀ regOffS + n ≤ V)
    (hs_bits : ∀ (i : ℕ) (hi : i < n), inp.getD (reg₀ regOffS + i) false = decide (s ⟨i, hi⟩ = (1 : ZMod 2))) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitV12 V inp rmForRangeEntry reg₀ rmForRangeExit reg₁
        ((List.range n).flatMap (fun i =>
          synCheckBits (if hlt : i < n then zmod2ToBool (s ⟨i, hlt⟩) else false)))
        (5 * n ^ 2 + 400 * n + 10) := by
  have hcnt : reg₀ regN = n := hp.1
  have hsF := synCheckBits_len false
  have hsT := synCheckBits_len true
  rcases rmEdgeLoop_spec regN (by decide) rmV12Body rmV12BodyEntry
      V (2 * n + 330) inp reg₀
      (fun i => synCheckBits (if hlt : i < n then zmod2ToBool (s ⟨i, hlt⟩) else false))
      hreg₀ (by
        intro i reg hi hpr hreg hI
        have hi' : i < n := by omega
        have hoS : reg regOffS = reg₀ regOffS := hpr regOffS (by decide)
        have ha := rmSetAdd_spec regS1 regOffS regLoopI (by decide) (by decide) (by decide)
          V inp reg hreg (by rw [hoS, hI]; omega)
        set r1 := regUpd (regUpd reg regS1 (reg regOffS + reg regLoopI)) regS0 0
        have hr1_S1 : r1 regS1 = reg₀ regOffS + i := by simp [r1, hoS, hI]
        have hbit : inp.getD (r1 regS1) false = zmod2ToBool (s ⟨i, hi'⟩) := by
          rw [hr1_S1]; exact hs_bits i hi'
        have hbr : ∃ qB, RMExec
            (rmIfReadIn regS1 (rmEmitBits (synCheckBits false)) (rmEmitBits (synCheckBits true))
              ⟨0, by omega⟩ ⟨0, by omega⟩)
            V inp rmIfReadInEntry r1 qB r1 (synCheckBits (zmod2ToBool (s ⟨i, hi'⟩))) 323 := by
          cases hb : zmod2ToBool (s ⟨i, hi'⟩)
          · rw [hb] at hbit
            have he := rmEmitBits_spec (synCheckBits false) V inp r1 ha.reg₁_le
            have hif := (rmIfReadIn_false_spec regS1 (rmEmitBits (synCheckBits true)) ⟨0, by omega⟩ hbit he).weaken
              (V₂ := V) (T₂ := 323) (le_refl _) (by omega)
            exact ⟨_, hif⟩
          · rw [hb] at hbit
            have he := rmEmitBits_spec (synCheckBits true) V inp r1 ha.reg₁_le
            have hif := (rmIfReadIn_true_spec regS1 (rmEmitBits (synCheckBits false)) ⟨0, by omega⟩ hbit he).weaken
              (V₂ := V) (T₂ := 323) (le_refl _) (by omega)
            exact ⟨_, hif⟩
        rcases hbr with ⟨qB, hif⟩
        have hcomb := rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha hif
        have hT : 2 * reg regLoopI + 3 + 323 ≤ 2 * n + 330 := by rw [hI]; omega
        have hfin := hcomb.weaken (V₂ := V) (T₂ := 2 * n + 330) (by simp) hT
        simp only [List.nil_append] at hfin
        refine ⟨Sum.inr qB, r1,
          (PreservedRegs.upd_ge _ regS0 _ (by decide)).trans (PreservedRegs.upd_ge _ regS1 _ (by decide)),
          by simp [r1, hI], by simp [r1], ?_⟩
        simp only [hi', ↓reduceDIte]
        exact hfin)
    with ⟨reg₁, hpr₁, hex⟩
  rw [hcnt] at hex
  have hT : n * (2 * n + 330 + 2) + 3 ≤ 5 * n ^ 2 + 400 * n + 10 := by
    have : n * (2 * n + 330 + 2) + 3 = 2 * n ^ 2 + 332 * n + 3 := by ring
    omega
  exact ⟨reg₁, hpr₁, hex.weaken (V₂ := V) (T₂ := 5 * n ^ 2 + 400 * n + 10) (le_refl _) hT⟩

/-! ### Blocks 13 & 14 (`v_pad0, v_pad1`, `2 * (treeM n - n)` vertices) -/

abbrev RMEmitV13to14Q : Type :=
  Bool ⊕ (RMSubQ ⊕ (RMSetAddQ ⊕ RMForRangeQ (Fin (pinFalseBits.length + 1))))

def rmEmitV13to14 : RMProg EncR RMEmitV13to14Q :=
  rmChain (rmCopy regS1 regTreeM)
    (rmChain (rmSub regS1 regN regS2)
      (rmChain (rmSetAdd regLoopJ regS1 regS1)
        (rmForRange regLoopI regLoopRem regLoopJ (rmEmitBits pinFalseBits) ⟨0, by decide⟩)
        rmForRangeEntry)
      (Sum.inl rmSetAddEntry))
    (Sum.inl rmSubEntry)

def rmEmitV13to14Entry : RMEmitV13to14Q := Sum.inl false
def rmEmitV13to14Exit : RMEmitV13to14Q := Sum.inr (Sum.inr (Sum.inr rmForRangeExit))

lemma rmEmitV13to14_spec (n V : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitV13to14 V inp rmEmitV13to14Entry reg₀ rmEmitV13to14Exit reg₁
        ((List.range (2 * (treeM n - n))).flatMap (fun _ => pinFalseBits))
        (100 * n + 50) := by
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hN : reg₀ regN = n := hp.1
  have hTM : reg₀ regTreeM = treeM n := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hc1 := rmCopy_spec regS1 regTreeM V inp reg₀ hreg₀
  set r1 := regUpd reg₀ regS1 (reg₀ regTreeM)
  have hs2 := rmSub_spec regS1 regN regS2 (by decide) V inp r1 hc1.reg₁_le
  set r2 := regUpd (regUpd r1 regS1 (r1 regS1 - r1 regN)) regS2 0
  have hr2_S1 : r2 regS1 = treeM n - n := by simp [r2, r1, hTM, hN]
  have ha3 := rmSetAdd_spec regLoopJ regS1 regS1 (by decide) (by decide) (by decide)
    V inp r2 hs2.reg₁_le (by rw [hr2_S1]; omega)
  set r3 := regUpd (regUpd r2 regLoopJ (r2 regS1 + r2 regS1)) regS0 0
  have hr3_J : r3 regLoopJ = 2 * (treeM n - n) := by simp [r3, hr2_S1]; omega
  have hr3_pr : PreservedRegs r3 reg₀ :=
    (PreservedRegs.upd_ge _ regS0 _ (by decide)).trans
      ((PreservedRegs.upd_ge _ regLoopJ _ (by decide)).trans
        ((PreservedRegs.upd_ge _ regS2 _ (by decide)).trans
          ((PreservedRegs.upd_ge _ regS1 _ (by decide)).trans
            (PreservedRegs.upd_ge _ regS1 _ (by decide)))))
  rcases rmEdgeLoop_spec regLoopJ (by decide) (rmEmitBits pinFalseBits) ⟨0, by decide⟩
      V 13 inp r3 (fun _ => pinFalseBits) ha3.reg₁_le (by
        intro i reg _ _ hreg hI
        exact ⟨_, reg, PreservedRegs.refl reg, hI, rfl, rmEmitBits_spec pinFalseBits V inp reg hreg⟩)
    with ⟨reg₁, hpr₁, hloop⟩
  rw [hr3_J] at hloop
  have hcomb := rmChain_spec_inl (by simp [rmCopy]) hc1
    (rmChain_spec_inl (by simp [rmSub, rmSubEntry, rmChain, rmSeq, rmCopy]) hs2
      (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha3 hloop))
  have hT : 1 + (2 * r1 regN + 2 + (2 * r2 regS1 + 3 + (2 * (treeM n - n) * (13 + 2) + 3))) ≤
      100 * n + 50 := by
    have hr1N : r1 regN = n := by simp [r1, hN]
    rw [hr1N, hr2_S1]; omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 100 * n + 50) (by simp) hT
  simp only [List.nil_append] at hfin
  exact ⟨reg₁, hpr₁.trans hr3_pr, hfin⟩

/-!
## Section 3: Vertex Circuit Emitter for Block 15 (`v_tree`, `treeVertOff (treeLog n + 1) (treeLog n + 2)` vertices)
-/

/-- Reusable constant-stream repeat loop: emits `bs` `reg rCnt` times, zeroing `rCnt`. -/
lemma rmEmitRepeat_spec {R : ℕ} (rCnt : Fin R) (bs : List Bool) (V : ℕ) (inp : List Bool) :
    ∀ (m : ℕ) (reg : RegState R),
      reg rCnt = m → (∀ i, reg i ≤ V) →
      RMExec (rmWhileDec rCnt (rmEmitBits bs) ⟨0, by omega⟩) V inp rmWhileDecEntry reg rmWhileDecExit
        (regUpd reg rCnt 0) ((List.range m).flatMap (fun _ => bs)) (m * (bs.length + 1) + 1)
  | 0, reg, hm, hreg => by
    have hupd : regUpd reg rCnt 0 = reg := by funext i; by_cases hi : i = rCnt <;> simp [regUpd, hi, hm]
    rw [hupd]
    simpa using rmWhileDec_zero rCnt (rmEmitBits bs) ⟨0, by omega⟩ V inp reg hm hreg
  | m + 1, reg, hm, hreg => by
    have hne : reg rCnt ≠ 0 := by omega
    set r1 := regUpd reg rCnt (reg rCnt - 1)
    have hr1 : ∀ i, r1 i ≤ V := regUpd_le hreg rCnt (le_trans (Nat.sub_le _ _) (hreg rCnt))
    have h1_cnt : r1 rCnt = m := by simp [r1, hm]
    have he := rmEmitBits_spec bs V inp r1 hr1
    have hrest := rmEmitRepeat_spec rCnt bs V inp m r1 h1_cnt hr1
    have hupd : regUpd r1 rCnt 0 = regUpd reg rCnt 0 := by simp [r1]
    rw [hupd] at hrest
    have hstep := rmWhileDec_step rCnt (rmEmitBits bs) hne hreg he hrest
    have hT : 1 + bs.length + (m * (bs.length + 1) + 1) = (m + 1) * (bs.length + 1) + 1 := by ring
    have hfm : bs ++ (List.range m).flatMap (fun _ => bs) = (List.range (m + 1)).flatMap (fun _ => bs) := by
      have := list_range_succ_flatMap_shift (fun _ => bs) m 0
      simpa using this.symm
    rw [max_self, hT, hfm] at hstep
    exact hstep

lemma rawPredTail_of_V15 (mode n : ℕ) (s : Fin n → ZMod 2) (t0 t1 locV : ℕ)
    (hloc : locV < treeVertOff (treeLog n + 1) (treeLog n + 2)) :
    let r := treeLog n + 1
    let tv := decodeTreeVert r locV
    rawPredTail mode n s t0 t1 (netV15 n + locV) =
      if tv.2.2 = 0 then pinBitCircuit (some false)
      else if mode = 2 ∧ tv.1 = r then
        sepFullAdderCircuit (decide (t0 < 2 ^ r ∧ t1 < 2 ^ r)) (t0.testBit (tv.2.2 - 1)) (t1.testBit (tv.2.2 - 1))
      else fullAdderCircuit := by
  have h11 : netV11 n = netV10 n + 2 * paramJ n * paramL n := rfl
  have h12 : netV12 n = netV11 n + 2 * n := rfl
  have h13 : netV13 n = netV12 n + n := rfl
  have h14 : netV14 n = netV13 n + (treeM n - n) := rfl
  have h15 : netV15 n = netV14 n + (treeM n - n) := rfl
  have h16 : netV16 n = netV15 n + treeVertOff (treeLog n + 1) (treeLog n + 2) := rfl
  simp only [rawPredTail,
    show ¬(netV15 n + locV < netV11 n) by omega, show ¬(netV15 n + locV < netV12 n) by omega,
    show ¬(netV15 n + locV < netV13 n) by omega, show ¬(netV15 n + locV < netV14 n) by omega,
    show ¬(netV15 n + locV < netV15 n) by omega, show netV15 n + locV < netV16 n by omega,
    ↓reduceIte, Nat.add_sub_cancel_left]

lemma v15_level_flatMap_lt (mode n : ℕ) (s : Fin n → ZMod 2) (t0 t1 j : ℕ)
    (hj1 : 1 ≤ j) (hjr : j < treeLog n + 1) :
    let r := treeLog n + 1
    (List.range ((j + 1) * 2 ^ (r - j))).flatMap
      (fun d => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + (treeVertOff r j + d)))) =
    (List.range (2 ^ (r - j))).flatMap
      (fun _ => pinFalseBits ++ (List.range j).flatMap (fun _ => fullAdderBits)) := by
  intro r
  have hcomm : (j + 1) * 2 ^ (r - j) = 2 ^ (r - j) * (j + 1) := Nat.mul_comm _ _
  rw [hcomm, range_mul_eq_flatMap, flatMap_flatMap_eq]
  refine List.flatMap_congr (fun node hnode => ?_)
  have hnode_lt : node < 2 ^ (r - j) := List.mem_range.mp hnode
  rw [List.flatMap_map]
  have hsh := list_range_succ_flatMap_shift
    (fun u => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + (treeVertOff r j + (node * (j + 1) + u)))))
    j 0
  simp only [Nat.zero_add] at hsh
  rw [hsh]
  congr 1
  · have hlt : treeVertOff r j + (node * (j + 1) + 0) < treeVertOff r (r + 1) := by
      simpa [Nat.add_assoc] using encodeTreeVert_lt (r := r) (u := 0) hj1 (le_of_lt hjr) hnode_lt (by omega)
    have hdec : decodeTreeVert r (treeVertOff r j + (node * (j + 1) + 0)) = (j, node, 0) := by
      simpa [Nat.add_assoc] using decodeTreeVert_encode (r := r) (u := 0) hj1 (le_of_lt hjr) hnode_lt (by omega)
    have hlt' : treeVertOff r j + (node * (j + 1) + 0) < treeVertOff (treeLog n + 1) (treeLog n + 2) := hlt
    rw [rawPredTail_of_V15 mode n s t0 t1 _ hlt']
    rw [hdec]; rfl
  · refine list_flatMap_range_congr j (fun d hd => ?_)
    have hu : 1 + d < j + 1 := by omega
    have hlt : treeVertOff r j + (node * (j + 1) + (1 + d)) < treeVertOff r (r + 1) := by
      simpa [Nat.add_assoc] using encodeTreeVert_lt (r := r) hj1 (le_of_lt hjr) hnode_lt hu
    have hdec : decodeTreeVert r (treeVertOff r j + (node * (j + 1) + (1 + d))) = (j, node, 1 + d) := by
      simpa [Nat.add_assoc] using decodeTreeVert_encode (r := r) hj1 (le_of_lt hjr) hnode_lt hu
    have hlt' : treeVertOff r j + (node * (j + 1) + (1 + d)) < treeVertOff (treeLog n + 1) (treeLog n + 2) := hlt
    rw [rawPredTail_of_V15 mode n s t0 t1 _ hlt']
    rw [hdec]
    have hne0 : ¬(1 + d = 0) := by omega
    have hnej : ¬(mode = 2 ∧ j = treeLog n + 1) := by omega
    simp only [hne0, hnej, ↓reduceIte]
    exact encodeCircuit_fullAdderCircuit

lemma v15_root_flatMap (mode n : ℕ) (s : Fin n → ZMod 2) (t0 t1 : ℕ) :
    let r := treeLog n + 1
    (List.range (r + 1)).flatMap
      (fun u => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + (treeVertOff r r + u)))) =
    pinFalseBits ++ (List.range r).flatMap (fun b =>
      if mode = 2 then sepFullAdderBits (decide (t0 < 2 ^ r ∧ t1 < 2 ^ r)) (t0.testBit b) (t1.testBit b)
      else fullAdderBits) := by
  intro r
  have hr1 : 1 ≤ r := by omega
  have hsh := list_range_succ_flatMap_shift
    (fun u => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + (treeVertOff r r + u))))
    r 0
  simp only [Nat.zero_add] at hsh
  rw [hsh]
  congr 1
  · have hlt : treeVertOff r r + 0 < treeVertOff r (r + 1) := by
      simpa using encodeTreeVert_lt (r := r) (j := r) (node := 0) (u := 0) hr1 (le_refl r) (by simp) (by omega)
    have hdec : decodeTreeVert r (treeVertOff r r + 0) = (r, 0, 0) := by
      simpa using decodeTreeVert_encode (r := r) (j := r) (node := 0) (u := 0) hr1 (le_refl r) (by simp) (by omega)
    have hlt' : treeVertOff r r + 0 < treeVertOff (treeLog n + 1) (treeLog n + 2) := hlt
    rw [rawPredTail_of_V15 mode n s t0 t1 _ hlt']
    rw [hdec]; rfl
  · refine list_flatMap_range_congr r (fun b hb => ?_)
    have hu : 1 + b < r + 1 := by omega
    have hlt : treeVertOff r r + (1 + b) < treeVertOff r (r + 1) := by
      simpa using encodeTreeVert_lt (r := r) (j := r) (node := 0) (u := 1 + b) hr1 (le_refl r) (by simp) hu
    have hdec : decodeTreeVert r (treeVertOff r r + (1 + b)) = (r, 0, 1 + b) := by
      simpa using decodeTreeVert_encode (r := r) (j := r) (node := 0) (u := 1 + b) hr1 (le_refl r) (by simp) hu
    have hlt' : treeVertOff r r + (1 + b) < treeVertOff (treeLog n + 1) (treeLog n + 2) := hlt
    rw [rawPredTail_of_V15 mode n s t0 t1 _ hlt']
    rw [hdec]
    have hne0 : ¬(1 + b = 0) := by omega
    have hsub : 1 + b - 1 = b := by omega
    have hreq : r = treeLog n + 1 := rfl
    simp only [hne0, hsub, hreq, and_true, ↓reduceIte]
    split_ifs
    · exact encodeCircuit_sepFullAdderCircuit _ _ _
    · exact encodeCircuit_fullAdderCircuit

/-! ### Part 15a: Levels `j = 1 .. treeLog n` (`treeVertOff r r` vertices) -/

abbrev RMV15aNodeBodyQ : Type :=
  Fin (pinFalseBits.length + 1) ⊕ (Bool ⊕ (Option Bool ⊕ (Unit ⊕ Fin (fullAdderBits.length + 1))))
abbrev RMV15aLevelQ : Type := Bool ⊕ (Option Bool ⊕ (Unit ⊕ RMV15aNodeBodyQ))
abbrev RMV15aStepQ : Type :=
  RMV15aLevelQ ⊕ (RMSetConstQ 2 ⊕ (RMDivModQ ⊕ (Bool ⊕ Bool)))
abbrev RMEmitV15aQ : Type :=
  RMSetConstQ 1 ⊕ (Bool ⊕ (Bool ⊕ (Option Bool ⊕ (Unit ⊕ RMV15aStepQ))))

def rmV15aNodeBody : RMProg EncR RMV15aNodeBodyQ :=
  rmChain (rmEmitBits pinFalseBits)
    (rmChain (rmCopy regEndU regLoopJ)
      (rmWhileDec regEndU (rmEmitBits fullAdderBits) ⟨0, by omega⟩)
      rmWhileDecEntry)
    (Sum.inl false)

def rmV15aNodeBodyEntry : RMV15aNodeBodyQ := Sum.inl ⟨0, by decide⟩

def rmV15aLevel : RMProg EncR RMV15aLevelQ :=
  rmChain (rmCopy regLoopNode regLoopW)
    (rmWhileDec regLoopNode rmV15aNodeBody rmV15aNodeBodyEntry)
    rmWhileDecEntry

def rmV15aStep : RMProg EncR RMV15aStepQ :=
  rmChain rmV15aLevel
    (rmChain (rmSetConst regS1 2)
      (rmChain (rmDivMod regS2 regS3 regLoopW regS1 regS4 regS5 regS6)
        (rmChain (rmCopy regLoopW regS2) (rmInc regLoopJ) false)
        (Sum.inl false))
      (Sum.inl rmDivModEntry))
    (Sum.inl rmSetConstEntry)

def rmV15aStepEntry : RMV15aStepQ := Sum.inl (Sum.inl false)

def rmEmitV15a : RMProg EncR RMEmitV15aQ :=
  rmChain (rmSetConst regLoopJ 1)
    (rmChain (rmCopy regLoopW regTreeM)
      (rmChain (rmCopy regLoopRem regTreeLog)
        (rmWhileDec regLoopRem rmV15aStep rmV15aStepEntry)
        rmWhileDecEntry)
      (Sum.inl false))
    (Sum.inl false)

def rmEmitV15aEntry : RMEmitV15aQ := Sum.inl rmSetConstEntry
def rmEmitV15aExit : RMEmitV15aQ := Sum.inr (Sum.inr (Sum.inr rmWhileDecExit))

lemma rmV15aNodeLoop_spec (j V : ℕ) (inp : List Bool) :
    ∀ (m : ℕ) (reg : RegState EncR),
      reg regLoopJ = j → reg regLoopNode = m → (∀ i, reg i ≤ V) →
      ∃ r1 : RegState EncR,
        (∀ k : Fin EncR, k ≠ regLoopNode → k ≠ regEndU → r1 k = reg k) ∧
        RMExec (rmWhileDec regLoopNode rmV15aNodeBody rmV15aNodeBodyEntry) V inp
          rmWhileDecEntry reg rmWhileDecExit r1
          ((List.range m).flatMap (fun _ => pinFalseBits ++ (List.range j).flatMap (fun _ => fullAdderBits)))
          (m * (765 * (j + 1)) + 1)
  | 0, reg, _, hm, hreg =>
    ⟨reg, fun _ _ _ => rfl, by
      simpa using rmWhileDec_zero regLoopNode rmV15aNodeBody rmV15aNodeBodyEntry V inp reg hm hreg⟩
  | m + 1, reg, hJ, hm, hreg => by
    have hne : reg regLoopNode ≠ 0 := by omega
    set r1 := regUpd reg regLoopNode (reg regLoopNode - 1)
    have hr1 : ∀ i, r1 i ≤ V := regUpd_le hreg regLoopNode (le_trans (Nat.sub_le _ _) (hreg regLoopNode))
    have h1_J : r1 regLoopJ = j := by simp [r1, hJ]
    have h1_N : r1 regLoopNode = m := by simp [r1, hm]
    have hp := rmEmitBits_spec pinFalseBits V inp r1 hr1
    have hc := rmCopy_spec regEndU regLoopJ V inp r1 hr1
    set r2 := regUpd r1 regEndU (r1 regLoopJ)
    have hrep := rmEmitRepeat_spec regEndU fullAdderBits V inp j r2 (by simp [r2, h1_J]) hc.reg₁_le
    set r3 := regUpd r2 regEndU 0
    have hbody := rmChain_spec_inl (rmEmitBits_active pinFalseBits (by rw [pinFalseBits_len]; omega)) hp
      (rmChain_spec_inl (by simp [rmCopy]) hc hrep)
    have hfa := fullAdderBits_len
    have hpf := pinFalseBits_len
    have hTbody : pinFalseBits.length + (1 + (j * (fullAdderBits.length + 1) + 1)) ≤ 765 * (j + 1) - 1 := by
      rw [hfa, hpf]; omega
    have hbody' := hbody.weaken (V₂ := V) (T₂ := 765 * (j + 1) - 1) (by simp) hTbody
    simp only [List.nil_append] at hbody'
    rcases rmV15aNodeLoop_spec j V inp m r3 (by simp [r3, r2, h1_J]) (by simp [r3, r2, h1_N]) hbody'.reg₁_le
      with ⟨r_end, hfr_end, hrest⟩
    have hstep := rmWhileDec_step regLoopNode rmV15aNodeBody hne hreg hbody' hrest
    have hT : 1 + (765 * (j + 1) - 1) + (m * (765 * (j + 1)) + 1) = (m + 1) * (765 * (j + 1)) + 1 := by
      have hpos : 1 ≤ 765 * (j + 1) := by omega
      have : 1 + (765 * (j + 1) - 1) = 765 * (j + 1) := by omega
      rw [this]; ring
    have hfm : (pinFalseBits ++ (List.range j).flatMap (fun _ => fullAdderBits)) ++
        (List.range m).flatMap (fun _ => pinFalseBits ++ (List.range j).flatMap (fun _ => fullAdderBits)) =
        (List.range (m + 1)).flatMap (fun _ => pinFalseBits ++ (List.range j).flatMap (fun _ => fullAdderBits)) := by
      have := list_range_succ_flatMap_shift
        (fun _ => pinFalseBits ++ (List.range j).flatMap (fun _ => fullAdderBits)) m 0
      simpa using this.symm
    rw [max_self, hT, hfm] at hstep
    refine ⟨r_end, fun k hkN hkU => ?_, hstep⟩
    rw [hfr_end k hkN hkU]; dsimp only [r3, r2, r1]
    rw [regUpd_ne _ hkU, regUpd_ne _ hkU, regUpd_ne _ hkN]

lemma rmV15aOuterLoop_spec (mode n V : ℕ) (s : Fin n → ZMod 2) (t0 t1 : ℕ) (inp : List Bool)
    (hn : 1 ≤ n) (hV : 500 * n + 20 ≤ V) :
    ∀ (rem j : ℕ) (reg : RegState EncR),
      1 ≤ j →
      j + rem = treeLog n + 1 →
      reg regLoopJ = j →
      reg regLoopW = 2 ^ (treeLog n + 1 - j) →
      reg regLoopRem = rem →
      (∀ i, reg i ≤ V) →
      ∃ r1 : RegState EncR,
        PreservedRegs r1 reg ∧
        RMExec (rmWhileDec regLoopRem rmV15aStep rmV15aStepEntry) V inp rmWhileDecEntry reg rmWhileDecExit r1
          ((List.range (treeVertOff (treeLog n + 1) (treeLog n + 1) - treeVertOff (treeLog n + 1) j)).flatMap
            (fun d => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + (treeVertOff (treeLog n + 1) j + d)))))
          (765 * (treeVertOff (treeLog n + 1) (treeLog n + 1) - treeVertOff (treeLog n + 1) j) +
            rem * (35 * n + 30) + 1)
  | 0, j, reg, _, hjr, _, _, hrem, hreg => by
    have hjeq : j = treeLog n + 1 := by omega
    subst hjeq
    refine ⟨reg, PreservedRegs.refl reg, ?_⟩
    simpa [Nat.sub_self] using rmWhileDec_zero regLoopRem rmV15aStep rmV15aStepEntry V inp reg hrem hreg
  | rem + 1, j, reg, hj1, hjr, hJ, hW, hrem, hreg => by
    set r := treeLog n + 1
    have h1V : 1 ≤ V := by omega
    have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
    have hlog_le : treeLog n ≤ n := treeLog_le_self hn
    have hjlt : j < r := by omega
    have hne : reg regLoopRem ≠ 0 := by omega
    set r1 := regUpd reg regLoopRem (reg regLoopRem - 1)
    have hr1 : ∀ i, r1 i ≤ V := regUpd_le hreg regLoopRem (le_trans (Nat.sub_le _ _) (hreg regLoopRem))
    have h1_rem : r1 regLoopRem = rem := by simp [r1, hrem]
    have h1_J : r1 regLoopJ = j := by simp [r1, hJ]
    have h1_W : r1 regLoopW = 2 ^ (r - j) := by simp [r1, hW]
    have hc1 := rmCopy_spec regLoopNode regLoopW V inp r1 hr1
    set r2 := regUpd r1 regLoopNode (r1 regLoopW)
    rcases rmV15aNodeLoop_spec j V inp (2 ^ (r - j)) r2 (by simp [r2, h1_J]) (by simp [r2, h1_W]) hc1.reg₁_le
      with ⟨r3, h3_fr, hl3⟩
    have hlev := rmChain_spec_inl (by simp [rmCopy]) hc1 hl3
    have h3_W : r3 regLoopW = 2 ^ (r - j) := by rw [h3_fr regLoopW (by decide) (by decide)]; simp [r2, h1_W]
    have h3_J : r3 regLoopJ = j := by rw [h3_fr regLoopJ (by decide) (by decide)]; simp [r2, h1_J]
    have h3_rem : r3 regLoopRem = rem := by rw [h3_fr regLoopRem (by decide) (by decide)]; simp [r2, h1_rem]
    have hsc4 := rmSetConst_spec regS1 2 V inp r3 (by simpa using hlev.reg₁_le) (by omega)
    set r4 := regUpd r3 regS1 2
    have h4_W : r4 regLoopW = 2 ^ (r - j) := by simp [r4, h3_W]
    rcases rmDivMod_spec regS2 regS3 regLoopW regS1 regS4 regS5 regS6
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        V inp r4 (by simp [r4]) hsc4.reg₁_le h1V
      with ⟨r5, h5_q, _, h5_fr, hd5⟩
    have hpow_div : 2 ^ (r - j) / 2 = 2 ^ (r - (j + 1)) := by
      have : r - j = (r - (j + 1)) + 1 := by omega
      rw [this, pow_succ']; omega
    have h5_S2 : r5 regS2 = 2 ^ (r - (j + 1)) := by rw [h5_q, h4_W]; simp [r4, hpow_div]
    have h5_J : r5 regLoopJ = j := by
      rw [h5_fr regLoopJ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r4, h3_J]
    have h5_rem : r5 regLoopRem = rem := by
      rw [h5_fr regLoopRem (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r4, h3_rem]
    have hc6 := rmCopy_spec regLoopW regS2 V inp r5 hd5.reg₁_le
    set r6 := regUpd r5 regLoopW (r5 regS2)
    have hi7 := rmInc_spec regLoopJ V inp r6 hc6.reg₁_le (by simp [r6, h5_J]; omega)
    set r7 := regUpd r6 regLoopJ (r6 regLoopJ + 1)
    have h7_J : r7 regLoopJ = j + 1 := by simp [r7, r6, h5_J]
    have h7_W : r7 regLoopW = 2 ^ (r - (j + 1)) := by simp [r7, r6, h5_S2]
    have h7_rem : r7 regLoopRem = rem := by simp [r7, r6, h5_rem]
    have hstep_body := rmChain_spec_inl (by simp [rmChain, rmSeq, rmCopy]) hlev
      (rmChain_spec_inl (by simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]) hsc4
        (rmChain_spec_inl (by simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]) hd5
          (rmChain_spec_inl (by simp [rmCopy]) hc6 hi7)))
    have hpow_le : 2 ^ (r - j) ≤ 2 * n := by
      calc 2 ^ (r - j) ≤ 2 ^ treeLog n := Nat.pow_le_pow_right (by decide) (by omega)
        _ = treeM n := rfl
        _ ≤ 2 * n := hM_le
    have hT_body : 1 + (2 ^ (r - j) * (765 * (j + 1)) + 1) +
        (1 + 2 + (15 * r4 regLoopW + 2 * r4 regS1 + 10 + (1 + 1))) ≤
        765 * ((j + 1) * 2 ^ (r - j)) + (35 * n + 29) := by
      have hr4S1 : r4 regS1 = 2 := by simp [r4]
      rw [h4_W, hr4S1]
      have hcomm : 2 ^ (r - j) * (765 * (j + 1)) = 765 * ((j + 1) * 2 ^ (r - j)) := by ring
      omega
    have hbody' := hstep_body.weaken (V₂ := V)
      (T₂ := 765 * ((j + 1) * 2 ^ (r - j)) + (35 * n + 29)) (by simp) hT_body
    simp only [List.nil_append, List.append_nil] at hbody'
    rcases rmV15aOuterLoop_spec mode n V s t0 t1 inp hn hV rem (j + 1) r7
        (by omega) (by omega) h7_J h7_W h7_rem hbody'.reg₁_le
      with ⟨r_end, hpr_end, hrest⟩
    have hstep := rmWhileDec_step regLoopRem rmV15aStep hne hreg hbody' hrest
    have hvostep : treeVertOff r (j + 1) = treeVertOff r j + (j + 1) * 2 ^ (r - j) := treeVertOff_step hj1
    have hmono1 : treeVertOff r (j + 1) ≤ treeVertOff r r := treeVertOff_mono r (by omega)
    have hsub_eq : treeVertOff r r - treeVertOff r j =
        (j + 1) * 2 ^ (r - j) + (treeVertOff r r - treeVertOff r (j + 1)) := by omega
    have hT_tot : 1 + (765 * ((j + 1) * 2 ^ (r - j)) + (35 * n + 29)) +
        (765 * (treeVertOff r r - treeVertOff r (j + 1)) + rem * (35 * n + 30) + 1) =
        765 * (treeVertOff r r - treeVertOff r j) + (rem + 1) * (35 * n + 30) + 1 := by
      rw [hsub_eq]; ring
    have hout_eq :
        (List.range (2 ^ (r - j))).flatMap
          (fun _ => pinFalseBits ++ (List.range j).flatMap (fun _ => fullAdderBits)) ++
        (List.range (treeVertOff r r - treeVertOff r (j + 1))).flatMap
          (fun d => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + (treeVertOff r (j + 1) + d)))) =
        (List.range (treeVertOff r r - treeVertOff r j)).flatMap
          (fun d => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + (treeVertOff r j + d)))) := by
      rw [hsub_eq, flatMap_range_add, v15_level_flatMap_lt mode n s t0 t1 j hj1 hjlt]
      congr 1
      refine list_flatMap_range_congr _ (fun d _ => ?_)
      have : treeVertOff r j + ((j + 1) * 2 ^ (r - j) + d) = treeVertOff r (j + 1) + d := by omega
      rw [this]
    rw [max_self, hT_tot, hout_eq] at hstep
    have h7pr : PreservedRegs r7 reg := fun k hk => by
      have hne : ∀ q : Fin EncR, 41 ≤ q.val → k ≠ q := fun q hq heq => by
        have := congrArg Fin.val heq; omega
      dsimp only [r7, r6]
      rw [regUpd_ne _ (hne regLoopJ (by decide)), regUpd_ne _ (hne regLoopW (by decide)),
          h5_fr k (hne regS2 (by decide)) (hne regS3 (by decide)) (hne regS4 (by decide))
            (hne regS5 (by decide)) (hne regS6 (by decide))]
      dsimp only [r4]
      rw [regUpd_ne _ (hne regS1 (by decide)),
          h3_fr k (hne regLoopNode (by decide)) (hne regEndU (by decide))]
      dsimp only [r2, r1]
      rw [regUpd_ne _ (hne regLoopNode (by decide)), regUpd_ne _ (hne regLoopRem (by decide))]
    exact ⟨r_end, hpr_end.trans h7pr, hstep⟩

lemma rmEmitV15a_spec (mode n V : ℕ) (s : Fin n → ZMod 2) (t0 t1 : ℕ) (inp : List Bool)
    (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V) :
    ∃ reg₁ : RegState EncR,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitV15a V inp rmEmitV15aEntry reg₀ rmEmitV15aExit reg₁
        ((List.range (treeVertOff (treeLog n + 1) (treeLog n + 1))).flatMap
          (fun locV => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + locV))))
        (40 * n ^ 2 + 10000 * n + 50) := by
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have hTL : reg₀ regTreeLog = treeLog n := hp.2.2.2.2.2.2.2.2.2.2.1
  have hTM : reg₀ regTreeM = treeM n := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hs1 := rmSetConst_spec regLoopJ 1 V inp reg₀ hreg₀ (by omega)
  set r1 := regUpd reg₀ regLoopJ 1
  have hc2 := rmCopy_spec regLoopW regTreeM V inp r1 hs1.reg₁_le
  set r2 := regUpd r1 regLoopW (r1 regTreeM)
  have hc3 := rmCopy_spec regLoopRem regTreeLog V inp r2 hc2.reg₁_le
  set r3 := regUpd r2 regLoopRem (r2 regTreeLog)
  have h3_J : r3 regLoopJ = 1 := by simp [r3, r2, r1]
  have h3_W : r3 regLoopW = 2 ^ (treeLog n + 1 - 1) := by
    have : treeLog n + 1 - 1 = treeLog n := by omega
    rw [this]; simp [r3, r2, r1, hTM, treeM]
  have h3_rem : r3 regLoopRem = treeLog n := by simp [r3, r2, r1, hTL]
  have h3_pr : PreservedRegs r3 reg₀ :=
    (PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
      ((PreservedRegs.upd_ge _ regLoopW _ (by decide)).trans
        (PreservedRegs.upd_ge _ regLoopJ _ (by decide)))
  rcases rmV15aOuterLoop_spec mode n V s t0 t1 inp hn hV (treeLog n) 1 r3
      (le_refl 1) (by omega) h3_J h3_W h3_rem hc3.reg₁_le
    with ⟨reg₁, hpr₁, hloop⟩
  have hcomb := rmChain_spec_inl (by simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]) hs1
    (rmChain_spec_inl (by simp [rmCopy]) hc2 (rmChain_spec_inl (by simp [rmCopy]) hc3 hloop))
  have hvo_le : treeVertOff (treeLog n + 1) (treeLog n + 1) ≤ 12 * n := by
    have h1 := treeVertOff_mono (treeLog n + 1) (show treeLog n + 1 ≤ treeLog n + 2 by omega)
    have h2 : treeVertOff (treeLog n + 1) (treeLog n + 2) ≤ 12 * n := by rw [treeVertOff_net]; omega
    omega
  have hT : 1 + 1 + (1 + (1 + (765 * (treeVertOff (treeLog n + 1) (treeLog n + 1) -
      treeVertOff (treeLog n + 1) 1) + treeLog n * (35 * n + 30) + 1))) ≤
      40 * n ^ 2 + 10000 * n + 50 := by
    have hmul : treeLog n * (35 * n + 30) ≤ n * (35 * n + 30) := Nat.mul_le_mul_right _ hlog_le
    have hring : n * (35 * n + 30) = 35 * n ^ 2 + 30 * n := by ring
    simp only [treeVertOff, Nat.sub_zero]; omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 40 * n ^ 2 + 10000 * n + 50) (by simp) hT
  simp only [List.nil_append, treeVertOff, Nat.sub_zero, Nat.zero_add] at hfin
  exact ⟨reg₁, hpr₁.trans h3_pr, hfin⟩

/-! ### Part 15b: Root Level `j = treeLog n + 1` (`r + 1` vertices, all 3 modes) -/

abbrev RMV15bPlainQ : Type :=
  Bool ⊕ (Bool ⊕ (Option Bool ⊕ (Unit ⊕ Fin (fullAdderBits.length + 1))))

def rmV15bPlain : RMProg EncR RMV15bPlainQ :=
  rmChain (rmCopy regLoopRem regTreeLog)
    (rmChain (rmInc regLoopRem)
      (rmWhileDec regLoopRem (rmEmitBits fullAdderBits) ⟨0, by omega⟩)
      rmWhileDecEntry)
    (Sum.inl false)

def rmV15bPlainEntry : RMV15bPlainQ := Sum.inl false

abbrev RMV15bSepEmit4Q : Type :=
  Option Bool ⊕
    ((Option Bool ⊕ (Fin ((sepFullAdderBits true false false).length + 1) ⊕
                     (Bool ⊕ Fin ((sepFullAdderBits true false true).length + 1)))) ⊕
     (Bool ⊕ (Option Bool ⊕ (Fin ((sepFullAdderBits true true false).length + 1) ⊕
                             (Bool ⊕ Fin ((sepFullAdderBits true true true).length + 1))))))

abbrev RMV15bSepBitStepQ : Type :=
  RMSetConstQ 2 ⊕ (RMDivModQ ⊕ (Bool ⊕ (RMDivModQ ⊕ (Bool ⊕ RMV15bSepEmit4Q))))

abbrev RMV15bSepFalseQ : Type :=
  Bool ⊕ (Bool ⊕ (Option Bool ⊕ (Unit ⊕ Fin (sepFAFalseBits.length + 1))))

abbrev RMV15bSepTrueQ : Type :=
  Bool ⊕ (Bool ⊕ (Bool ⊕ (Bool ⊕ (Option Bool ⊕ (Unit ⊕ RMV15bSepBitStepQ)))))

abbrev RMV15bSepQ : Type :=
  RMSetAddQ ⊕ (Fin 8 ⊕ (Fin 8 ⊕ ((Option Bool ⊕ (Bool ⊕ (Bool ⊕ Unit))) ⊕
    (Option Bool ⊕ (RMV15bSepFalseQ ⊕ (Bool ⊕ RMV15bSepTrueQ))))))

def rmV15bSepEmit4F : RMProg EncR
    (Option Bool ⊕ (Fin ((sepFullAdderBits true false false).length + 1) ⊕
                    (Bool ⊕ Fin ((sepFullAdderBits true false true).length + 1)))) :=
  rmIfZero regS7 (rmEmitBits (sepFullAdderBits true false false))
    (rmEmitBits (sepFullAdderBits true false true)) ⟨0, by omega⟩ ⟨0, by omega⟩

def rmV15bSepEmit4T : RMProg EncR
    (Option Bool ⊕ (Fin ((sepFullAdderBits true true false).length + 1) ⊕
                    (Bool ⊕ Fin ((sepFullAdderBits true true true).length + 1)))) :=
  rmIfZero regS7 (rmEmitBits (sepFullAdderBits true true false))
    (rmEmitBits (sepFullAdderBits true true true)) ⟨0, by omega⟩ ⟨0, by omega⟩

def rmV15bSepEmit4 : RMProg EncR RMV15bSepEmit4Q :=
  rmIfZero regS3 rmV15bSepEmit4F rmV15bSepEmit4T rmIfZeroEntry rmIfZeroEntry

def rmV15bSepBitStep : RMProg EncR RMV15bSepBitStepQ :=
  rmChain (rmSetConst regS1 2)
    (rmChain (rmDivMod regS2 regS3 regLoopJ regS1 regS4 regS5 regS6)
      (rmChain (rmCopy regLoopJ regS2)
        (rmChain (rmDivMod regS2 regS7 regLoopNode regS1 regS4 regS5 regS6)
          (rmChain (rmCopy regLoopNode regS2) rmV15bSepEmit4 rmIfZeroEntry)
          (Sum.inl false))
        (Sum.inl rmDivModEntry))
      (Sum.inl false))
    (Sum.inl rmDivModEntry)

def rmV15bSepBitStepEntry : RMV15bSepBitStepQ := Sum.inl rmSetConstEntry

def rmV15bSepFalse : RMProg EncR RMV15bSepFalseQ :=
  rmChain (rmCopy regLoopRem regTreeLog)
    (rmChain (rmInc regLoopRem)
      (rmWhileDec regLoopRem (rmEmitBits sepFAFalseBits) ⟨0, by decide⟩)
      rmWhileDecEntry)
    (Sum.inl false)

def rmV15bSepTrue : RMProg EncR RMV15bSepTrueQ :=
  rmChain (rmCopy regLoopJ regT0)
    (rmChain (rmCopy regLoopNode regT1)
      (rmChain (rmCopy regLoopRem regTreeLog)
        (rmChain (rmInc regLoopRem)
          (rmWhileDec regLoopRem rmV15bSepBitStep rmV15bSepBitStepEntry)
          rmWhileDecEntry)
        (Sum.inl false))
      (Sum.inl false))
    (Sum.inl false)

def rmV15bSep : RMProg EncR RMV15bSepQ :=
  rmChain (rmSetAdd regS7 regTreeM regTreeM)
    (rmChain (rmCmpLt regS0 regT0 regS7 regS1 regS2)
      (rmChain (rmCmpLt regS3 regT1 regS7 regS1 regS2)
        (rmChain (rmIfZero regS3 (rmZero regS0) rmNop false ())
          (rmIfZero regS0 rmV15bSepFalse rmV15bSepTrue (Sum.inl false) (Sum.inl false))
          rmIfZeroEntry)
        (Sum.inl rmIfZeroEntry))
      (Sum.inl 0))
    (Sum.inl 0)

def rmV15bSepEntry : RMV15bSepQ := Sum.inl rmSetAddEntry

abbrev RMV15bQ : Type := Fin (pinFalseBits.length + 1) ⊕ (RMV15bPlainQ ⊕ RMV15bSepQ)

def rmEmitV15b (mode : ℕ) : RMProg EncR RMV15bQ :=
  rmChain (rmEmitBits pinFalseBits) (rmBranch rmV15bPlain rmV15bSep)
    (if mode = 2 then Sum.inr rmV15bSepEntry else Sum.inl rmV15bPlainEntry)

def rmEmitV15bEntry : RMV15bQ := Sum.inl ⟨0, by decide⟩

lemma rmV15bSepBitLoop_spec (n V : ℕ) (inp : List Bool)
    (hn : 1 ≤ n) (hV : 500 * n + 20 ≤ V) :
    ∀ (rem _b cur0 cur1 : ℕ) (reg : RegState EncR),
      cur0 < 4 * n → cur1 < 4 * n →
      reg regLoopRem = rem → reg regLoopJ = cur0 → reg regLoopNode = cur1 →
      (∀ i, reg i ≤ V) →
      ∃ r1 : RegState EncR,
        PreservedRegs r1 reg ∧
        RMExec (rmWhileDec regLoopRem rmV15bSepBitStep rmV15bSepBitStepEntry) V inp
          rmWhileDecEntry reg rmWhileDecExit r1
          ((List.range rem).flatMap (fun d => sepFullAdderBits true (cur0.testBit d) (cur1.testBit d)))
          (rem * (150 * n + 1600) + 1)
  | 0, _, _, _, reg, _, _, hrem, _, _, hreg =>
    ⟨reg, PreservedRegs.refl reg, by
      simpa using rmWhileDec_zero regLoopRem rmV15bSepBitStep rmV15bSepBitStepEntry V inp reg hrem hreg⟩
  | rem + 1, _b, cur0, cur1, reg, hc0, hc1, hrem, hJ, hN, hreg => by
    have h1V : 1 ≤ V := by omega
    have hne : reg regLoopRem ≠ 0 := by omega
    set r1 := regUpd reg regLoopRem (reg regLoopRem - 1)
    have hr1 : ∀ i, r1 i ≤ V := regUpd_le hreg regLoopRem (le_trans (Nat.sub_le _ _) (hreg regLoopRem))
    have h1_rem : r1 regLoopRem = rem := by simp [r1, hrem]
    have h1_J : r1 regLoopJ = cur0 := by simp [r1, hJ]
    have h1_N : r1 regLoopNode = cur1 := by simp [r1, hN]
    have hsc := rmSetConst_spec regS1 2 V inp r1 hr1 (by omega)
    set r2 := regUpd r1 regS1 2
    have h2_J : r2 regLoopJ = cur0 := by simp [r2, h1_J]
    rcases rmDivMod_spec regS2 regS3 regLoopJ regS1 regS4 regS5 regS6
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        V inp r2 (by simp [r2]) hsc.reg₁_le h1V
      with ⟨r3, h3_q, h3_r, h3_fr, hd3⟩
    have h3_q' : r3 regS2 = cur0 / 2 := by rw [h3_q, h2_J]; simp [r2]
    have h3_r' : r3 regS3 = cur0 % 2 := by rw [h3_r, h2_J]; simp [r2]
    have hc4 := rmCopy_spec regLoopJ regS2 V inp r3 hd3.reg₁_le
    set r4 := regUpd r3 regLoopJ (r3 regS2)
    have h4_N : r4 regLoopNode = cur1 := by
      dsimp only [r4]; rw [regUpd_ne _ (by decide),
        h3_fr regLoopNode (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r2, h1_N]
    have h4_S1 : r4 regS1 = 2 := by
      dsimp only [r4]; rw [regUpd_ne _ (by decide),
        h3_fr regS1 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r2]
    rcases rmDivMod_spec regS2 regS7 regLoopNode regS1 regS4 regS5 regS6
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        V inp r4 (by rw [h4_S1]; decide) hc4.reg₁_le h1V
      with ⟨r5, h5_q, h5_r, h5_fr, hd5⟩
    have h5_q' : r5 regS2 = cur1 / 2 := by rw [h5_q, h4_N, h4_S1]
    have h5_r' : r5 regS7 = cur1 % 2 := by rw [h5_r, h4_N, h4_S1]
    have hc6 := rmCopy_spec regLoopNode regS2 V inp r5 hd5.reg₁_le
    set r6 := regUpd r5 regLoopNode (r5 regS2)
    have h6_S3 : r6 regS3 = cur0 % 2 := by
      dsimp only [r6]; rw [regUpd_ne _ (by decide),
        h5_fr regS3 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r4, h3_r']
    have h6_S7 : r6 regS7 = cur1 % 2 := by simp [r6, h5_r']
    have h6_J : r6 regLoopJ = cur0 / 2 := by
      dsimp only [r6]; rw [regUpd_ne _ (by decide),
        h5_fr regLoopJ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r4, h3_q']
    have h6_N : r6 regLoopNode = cur1 / 2 := by simp [r6, h5_q']
    have h6_rem : r6 regLoopRem = rem := by
      dsimp only [r6]; rw [regUpd_ne _ (by decide),
        h5_fr regLoopRem (by decide) (by decide) (by decide) (by decide) (by decide)]
      dsimp only [r4]; rw [regUpd_ne _ (by decide),
        h3_fr regLoopRem (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r2, h1_rem]
    have hem4 : ∃ qE, RMExec rmV15bSepEmit4 V inp rmIfZeroEntry r6 qE r6
        (sepFullAdderBits true (cur0.testBit 0) (cur1.testBit 0)) 1560 := by
      have hlen := fun a c => sepFullAdderBits_len true a c
      by_cases h0 : cur0 % 2 = 0
      · have ht0 : cur0.testBit 0 = false := by rw [testBit_zero_eq_mod]; simp [h0]
        rw [ht0]
        by_cases h1 : cur1 % 2 = 0
        · have ht1 : cur1.testBit 0 = false := by rw [testBit_zero_eq_mod]; simp [h1]
          rw [ht1]
          have he := rmEmitBits_spec (sepFullAdderBits true false false) V inp r6 hc6.reg₁_le
          have hsub := rmIfZero_zero_spec regS7 (rmEmitBits (sepFullAdderBits true false true))
            ⟨0, by omega⟩ (by rw [h6_S7, h1]) he
          have htop := (rmIfZero_zero_spec regS3 rmV15bSepEmit4T rmIfZeroEntry (by rw [h6_S3, h0]) hsub).weaken
            (V₂ := V) (T₂ := 1560) (le_refl _) (by have := hlen false false; simp at this; omega)
          exact ⟨_, htop⟩
        · have ht1 : cur1.testBit 0 = true := by rw [testBit_zero_eq_mod]; simp [h1]
          rw [ht1]
          have he := rmEmitBits_spec (sepFullAdderBits true false true) V inp r6 hc6.reg₁_le
          have hsub := rmIfZero_pos_spec regS7 (rmEmitBits (sepFullAdderBits true false false))
            ⟨0, by omega⟩ (by rw [h6_S7]; exact h1) he
          have htop := (rmIfZero_zero_spec regS3 rmV15bSepEmit4T rmIfZeroEntry (by rw [h6_S3, h0]) hsub).weaken
            (V₂ := V) (T₂ := 1560) (le_refl _) (by have := hlen false true; simp at this; omega)
          exact ⟨_, htop⟩
      · have ht0 : cur0.testBit 0 = true := by rw [testBit_zero_eq_mod]; simp [h0]
        rw [ht0]
        by_cases h1 : cur1 % 2 = 0
        · have ht1 : cur1.testBit 0 = false := by rw [testBit_zero_eq_mod]; simp [h1]
          rw [ht1]
          have he := rmEmitBits_spec (sepFullAdderBits true true false) V inp r6 hc6.reg₁_le
          have hsub := rmIfZero_zero_spec regS7 (rmEmitBits (sepFullAdderBits true true true))
            ⟨0, by omega⟩ (by rw [h6_S7, h1]) he
          have htop := (rmIfZero_pos_spec regS3 rmV15bSepEmit4F rmIfZeroEntry (by rw [h6_S3]; exact h0) hsub).weaken
            (V₂ := V) (T₂ := 1560) (le_refl _) (by have := hlen true false; simp at this; omega)
          exact ⟨_, htop⟩
        · have ht1 : cur1.testBit 0 = true := by rw [testBit_zero_eq_mod]; simp [h1]
          rw [ht1]
          have he := rmEmitBits_spec (sepFullAdderBits true true true) V inp r6 hc6.reg₁_le
          have hsub := rmIfZero_pos_spec regS7 (rmEmitBits (sepFullAdderBits true true false))
            ⟨0, by omega⟩ (by rw [h6_S7]; exact h1) he
          have htop := (rmIfZero_pos_spec regS3 rmV15bSepEmit4F rmIfZeroEntry (by rw [h6_S3]; exact h0) hsub).weaken
            (V₂ := V) (T₂ := 1560) (le_refl _) (by have := hlen true true; simp at this; omega)
          exact ⟨_, htop⟩
    rcases hem4 with ⟨qE, he4⟩
    have hact_div : ∀ a b c d e f g : Fin EncR, rmDivMod a b c d e f g rmDivModEntry ≠ none := by
      intros; simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]
    have hbody := rmChain_spec_inl (by simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]) hsc
      (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd3
        (rmChain_spec_inl (by simp [rmCopy]) hc4
          (rmChain_spec_inl (hact_div _ _ _ _ _ _ _) hd5
            (rmChain_spec_inl (by simp [rmCopy]) hc6 he4))))
    have hTbody : 1 + 2 + (15 * r2 regLoopJ + 2 * r2 regS1 + 10 + (1 +
        (15 * r4 regLoopNode + 2 * r4 regS1 + 10 + (1 + 1560)))) ≤ 150 * n + 1599 := by
      have hr2S1 : r2 regS1 = 2 := by simp [r2]
      rw [h2_J, hr2S1, h4_N, h4_S1]; omega
    have hbody' := hbody.weaken (V₂ := V) (T₂ := 150 * n + 1599) (by simp) hTbody
    simp only [List.nil_append] at hbody'
    rcases rmV15bSepBitLoop_spec n V inp hn hV rem 0 (cur0 / 2) (cur1 / 2) r6
        (by omega) (by omega) h6_rem h6_J h6_N hbody'.reg₁_le
      with ⟨r_end, hpr_end, hrest⟩
    have hstep := rmWhileDec_step regLoopRem rmV15bSepBitStep hne hreg hbody' hrest
    have hT : 1 + (150 * n + 1599) + (rem * (150 * n + 1600) + 1) =
        (rem + 1) * (150 * n + 1600) + 1 := by ring
    have hfm : sepFullAdderBits true (cur0.testBit 0) (cur1.testBit 0) ++
        (List.range rem).flatMap (fun d => sepFullAdderBits true ((cur0 / 2).testBit d) ((cur1 / 2).testBit d)) =
        (List.range (rem + 1)).flatMap (fun d => sepFullAdderBits true (cur0.testBit d) (cur1.testBit d)) := by
      have hsh := list_range_succ_flatMap_shift
        (fun d => sepFullAdderBits true (cur0.testBit d) (cur1.testBit d)) rem 0
      simp only [Nat.zero_add] at hsh
      rw [hsh]
      exact congrArg (sepFullAdderBits true (cur0.testBit 0) (cur1.testBit 0) ++ ·)
        (list_flatMap_range_congr rem (fun d _ => by
          rw [testBit_div_two, testBit_div_two, show 1 + d = d + 1 by omega]))
    rw [max_self, hT, hfm] at hstep
    have h6pr : PreservedRegs r6 reg := fun k hk => by
      have hne : ∀ q : Fin EncR, 41 ≤ q.val → k ≠ q := fun q hq heq => by
        have := congrArg Fin.val heq; omega
      dsimp only [r6]; rw [regUpd_ne _ (hne regLoopNode (by decide)),
        h5_fr k (hne regS2 (by decide)) (hne regS7 (by decide)) (hne regS4 (by decide))
          (hne regS5 (by decide)) (hne regS6 (by decide))]
      dsimp only [r4]; rw [regUpd_ne _ (hne regLoopJ (by decide)),
        h3_fr k (hne regS2 (by decide)) (hne regS3 (by decide)) (hne regS4 (by decide))
          (hne regS5 (by decide)) (hne regS6 (by decide))]
      dsimp only [r2, r1]
      rw [regUpd_ne _ (hne regS1 (by decide)), regUpd_ne _ (hne regLoopRem (by decide))]
    exact ⟨r_end, hpr_end.trans h6pr, hstep⟩

lemma rmEmitV15b_spec (mode n V t0 t1 : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V)
    (hT0 : reg₀ regT0 = t0) (hT1 : reg₀ regT1 = t1) :
    let r := treeLog n + 1
    ∃ q₁ reg₁,
      PreservedRegs reg₁ reg₀ ∧
      RMExec (rmEmitV15b mode) V inp rmEmitV15bEntry reg₀ q₁ reg₁
        (pinFalseBits ++ (List.range r).flatMap (fun b =>
          if mode = 2 then sepFullAdderBits (decide (t0 < 2 ^ r ∧ t1 < 2 ^ r)) (t0.testBit b) (t1.testBit b)
          else fullAdderBits))
        (200 * n ^ 2 + 2000 * n + 2000) := by
  intro r
  have h1V : 1 ≤ V := by omega
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have hpowr : 2 ^ r = 2 * treeM n := two_pow_treeLog_succ n
  have hTL : reg₀ regTreeLog = treeLog n := hp.2.2.2.2.2.2.2.2.2.2.1
  have hTM : reg₀ regTreeM = treeM n := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hpin := rmEmitBits_spec pinFalseBits V inp reg₀ hreg₀
  by_cases hm2 : mode = 2
  · -- mode = 2: run rmV15bSep
    have ha1 := rmSetAdd_spec regS7 regTreeM regTreeM (by decide) (by decide) (by decide)
      V inp reg₀ hreg₀ (by rw [hTM]; omega)
    set s1 := regUpd (regUpd reg₀ regS7 (reg₀ regTreeM + reg₀ regTreeM)) regS0 0
    have hs1_S7 : s1 regS7 = 2 ^ r := by simp [s1, hTM, hpowr]; omega
    have hs1_T0 : s1 regT0 = t0 := by simp [s1, hT0]
    have hs1_T1 : s1 regT1 = t1 := by simp [s1, hT1]
    rcases rmCmpLt_spec regS0 regT0 regS7 regS1 regS2 (by decide) (by decide) (by decide) (by decide)
        V inp s1 ha1.reg₁_le h1V with ⟨s2, hs2_fl, hs2_fr, hcmp2⟩
    have hs2_S7 : s2 regS7 = 2 ^ r := by rw [hs2_fr regS7 (by decide) (by decide) (by decide), hs1_S7]
    have hs2_T1 : s2 regT1 = t1 := by rw [hs2_fr regT1 (by decide) (by decide) (by decide), hs1_T1]
    rcases rmCmpLt_spec regS3 regT1 regS7 regS1 regS2 (by decide) (by decide) (by decide) (by decide)
        V inp s2 hcmp2.reg₁_le h1V with ⟨s3, hs3_fl, hs3_fr, hcmp3⟩
    have hs3_S0 : s3 regS0 = (if t0 < 2 ^ r then 1 else 0) := by
      rw [hs3_fr regS0 (by decide) (by decide) (by decide), hs2_fl, hs1_T0, hs1_S7]
    have hs3_S3 : s3 regS3 = (if t1 < 2 ^ r then 1 else 0) := by rw [hs3_fl, hs2_T1, hs2_S7]
    have hmask : ∃ qM s4,
        s4 regS0 = (if t0 < 2 ^ r ∧ t1 < 2 ^ r then 1 else 0) ∧
        (∀ k : Fin EncR, k ≠ regS0 → s4 k = s3 k) ∧
        RMExec (rmIfZero regS3 (rmZero regS0) rmNop false ()) V inp rmIfZeroEntry s3 qM s4 [] 3 := by
      by_cases h1 : t1 < 2 ^ r
      · have hfl : s3 regS3 ≠ 0 := by rw [hs3_S3]; simp [h1]
        have hif := (rmIfZero_pos_spec regS3 (rmZero regS0) false hfl (rmNop_spec V inp s3 hcmp3.reg₁_le)).weaken
          (V₂ := V) (T₂ := 3) (le_refl _) (by omega)
        exact ⟨_, s3, by rw [hs3_S0]; simp [h1], fun _ _ => rfl, hif⟩
      · have hfl : s3 regS3 = 0 := by rw [hs3_S3]; simp [h1]
        have hz := rmZero_spec regS0 V inp s3 hcmp3.reg₁_le
        have hif := rmIfZero_zero_spec regS3 rmNop () hfl hz
        exact ⟨_, regUpd s3 regS0 0, by simp [h1], fun k hk => regUpd_ne s3 hk 0, hif⟩
    rcases hmask with ⟨qM, s4, hs4_S0, hs4_fr, hif4⟩
    have hs4_pr : PreservedRegs s4 reg₀ := fun k hk => by
      have hne : ∀ q : Fin EncR, 41 ≤ q.val → k ≠ q := fun q hq heq => by
        have := congrArg Fin.val heq; omega
      rw [hs4_fr k (hne regS0 (by decide)),
          hs3_fr k (hne regS3 (by decide)) (hne regS1 (by decide)) (hne regS2 (by decide)),
          hs2_fr k (hne regS0 (by decide)) (hne regS1 (by decide)) (hne regS2 (by decide))]
      dsimp only [s1]
      rw [regUpd_ne _ (hne regS0 (by decide)), regUpd_ne _ (hne regS7 (by decide))]
    have hs4_TL : s4 regTreeLog = treeLog n := by rw [hs4_pr regTreeLog (by decide), hTL]
    have hs4_T0 : s4 regT0 = t0 := by rw [hs4_pr regT0 (by decide), hT0]
    have hs4_T1 : s4 regT1 = t1 := by rw [hs4_pr regT1 (by decide), hT1]
    have hbr : ∃ qB s5,
        PreservedRegs s5 s4 ∧
        RMExec (rmIfZero regS0 rmV15bSepFalse rmV15bSepTrue (Sum.inl false) (Sum.inl false))
          V inp rmIfZeroEntry s4 qB s5
          ((List.range r).flatMap (fun b =>
            sepFullAdderBits (decide (t0 < 2 ^ r ∧ t1 < 2 ^ r)) (t0.testBit b) (t1.testBit b)))
          (180 * n ^ 2 + 1900 * n + 1800) := by
      by_cases hg : t0 < 2 ^ r ∧ t1 < 2 ^ r
      · have hfl : s4 regS0 ≠ 0 := by rw [hs4_S0]; simp [hg]
        have hc1 := rmCopy_spec regLoopJ regT0 V inp s4 hif4.reg₁_le
        set t1s := regUpd s4 regLoopJ (s4 regT0)
        have hc2 := rmCopy_spec regLoopNode regT1 V inp t1s hc1.reg₁_le
        set t2s := regUpd t1s regLoopNode (t1s regT1)
        have hc3 := rmCopy_spec regLoopRem regTreeLog V inp t2s hc2.reg₁_le
        set t3s := regUpd t2s regLoopRem (t2s regTreeLog)
        have hi4 := rmInc_spec regLoopRem V inp t3s hc3.reg₁_le (by simp [t3s, t2s, t1s, hs4_TL]; omega)
        set t4s := regUpd t3s regLoopRem (t3s regLoopRem + 1)
        rcases rmV15bSepBitLoop_spec n V inp hn hV r 0 t0 t1 t4s
            (by omega) (by omega) (by simp [t4s, t3s, t2s, t1s, hs4_TL, r])
            (by simp [t4s, t3s, t2s, t1s, hs4_T0]) (by simp [t4s, t3s, t2s, t1s, hs4_T1]) hi4.reg₁_le
          with ⟨t5s, ht5_pr, hloop⟩
        have htrue := rmChain_spec_inl (by simp [rmCopy]) hc1
          (rmChain_spec_inl (by simp [rmCopy]) hc2
            (rmChain_spec_inl (by simp [rmCopy]) hc3
              (rmChain_spec_inl (by simp [rmInc]) hi4 hloop)))
        have hT : 2 + (1 + (1 + (1 + (1 + (r * (150 * n + 1600) + 1))))) ≤
            180 * n ^ 2 + 1900 * n + 1800 := by
          have hmul : r * (150 * n + 1600) ≤ (n + 1) * (150 * n + 1600) := Nat.mul_le_mul_right _ (by omega)
          have hring : (n + 1) * (150 * n + 1600) = 150 * n ^ 2 + 1750 * n + 1600 := by ring
          omega
        have hif := (rmIfZero_pos_spec regS0 rmV15bSepFalse (Sum.inl false) hfl htrue).weaken
          (V₂ := V) (T₂ := 180 * n ^ 2 + 1900 * n + 1800) (by simp) hT
        simp only [List.nil_append] at hif
        have ht4_pr : PreservedRegs t4s s4 :=
          (PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
            ((PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
              ((PreservedRegs.upd_ge _ regLoopNode _ (by decide)).trans
                (PreservedRegs.upd_ge _ regLoopJ _ (by decide))))
        have hdec : decide (t0 < 2 ^ r ∧ t1 < 2 ^ r) = true := decide_eq_true hg
        rw [hdec]; exact ⟨_, t5s, ht5_pr.trans ht4_pr, hif⟩
      · have hfl : s4 regS0 = 0 := by rw [hs4_S0]; simp [hg]
        have hc1 := rmCopy_spec regLoopRem regTreeLog V inp s4 hif4.reg₁_le
        set t1s := regUpd s4 regLoopRem (s4 regTreeLog)
        have hi2 := rmInc_spec regLoopRem V inp t1s hc1.reg₁_le (by simp [t1s, hs4_TL]; omega)
        set t2s := regUpd t1s regLoopRem (t1s regLoopRem + 1)
        have hrep := rmEmitRepeat_spec regLoopRem sepFAFalseBits V inp r t2s
          (by simp [t2s, t1s, hs4_TL, r]) hi2.reg₁_le
        have hfalse := rmChain_spec_inl (by simp [rmCopy]) hc1 (rmChain_spec_inl (by simp [rmInc]) hi2 hrep)
        have hT : 2 + (1 + (1 + (r * (sepFAFalseBits.length + 1) + 1))) ≤
            180 * n ^ 2 + 1900 * n + 1800 := by
          rw [sepFAFalseBits_len]; omega
        have hif := (rmIfZero_zero_spec regS0 rmV15bSepTrue (Sum.inl false) hfl hfalse).weaken
          (V₂ := V) (T₂ := 180 * n ^ 2 + 1900 * n + 1800) (by simp) hT
        simp only [List.nil_append] at hif
        have hdec : decide (t0 < 2 ^ r ∧ t1 < 2 ^ r) = false := decide_eq_false hg
        rw [hdec]
        have hout : (List.range r).flatMap (fun _ => sepFAFalseBits) =
            (List.range r).flatMap (fun b => sepFullAdderBits false (t0.testBit b) (t1.testBit b)) :=
          list_flatMap_range_congr r (fun _ _ => rfl)
        rw [hout] at hif
        refine ⟨_, _, (PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
            ((PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
              (PreservedRegs.upd_ge _ regLoopRem _ (by decide))), hif⟩
    rcases hbr with ⟨qB, s5, hs5_pr, hif5⟩
    have hsep := rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha1
      (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp2
        (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp3
          (rmChain_spec_inl (by simp [rmIfZero, rmIfZeroEntry, rmDecBranch, rmDecBranchEntry, rmSeq, rmDecJzProg]) hif4 hif5)))
    have hbr_s := rmBranch_inr_spec rmV15bPlain hsep
    have hcomb := rmChain_spec_inl (rmEmitBits_active pinFalseBits (by rw [pinFalseBits_len]; omega)) hpin hbr_s
    have hT : pinFalseBits.length + (2 * reg₀ regTreeM + 3 + (2 * min (s1 regT0) (s1 regS7) + 6 +
        (2 * min (s2 regT1) (s2 regS7) + 6 + (3 + (180 * n ^ 2 + 1900 * n + 1800))))) ≤
        200 * n ^ 2 + 2000 * n + 2000 := by
      rw [pinFalseBits_len, hTM, hs1_T0, hs1_S7, hs2_T1, hs2_S7]
      have : min t0 (2 ^ r) ≤ 2 ^ r := min_le_right _ _
      have : min t1 (2 ^ r) ≤ 2 ^ r := min_le_right _ _
      omega
    have hfin := hcomb.weaken (V₂ := V) (T₂ := 200 * n ^ 2 + 2000 * n + 2000) (by simp) hT
    simp only [List.nil_append] at hfin
    simp only [rmEmitV15b, rmEmitV15bEntry, hm2, ↓reduceIte]
    exact ⟨_, s5, hs5_pr.trans hs4_pr, hfin⟩
  · -- mode ≠ 2: run rmV15bPlain
    have hc1 := rmCopy_spec regLoopRem regTreeLog V inp reg₀ hreg₀
    set s1 := regUpd reg₀ regLoopRem (reg₀ regTreeLog)
    have hi2 := rmInc_spec regLoopRem V inp s1 hc1.reg₁_le (by simp [s1, hTL]; omega)
    set s2 := regUpd s1 regLoopRem (s1 regLoopRem + 1)
    have hrep := rmEmitRepeat_spec regLoopRem fullAdderBits V inp r s2 (by simp [s2, s1, hTL, r]) hi2.reg₁_le
    have hpl := rmChain_spec_inl (by simp [rmCopy]) hc1 (rmChain_spec_inl (by simp [rmInc]) hi2 hrep)
    have hbr_p := rmBranch_inl_spec rmV15bSep hpl
    have hcomb := rmChain_spec_inl (rmEmitBits_active pinFalseBits (by rw [pinFalseBits_len]; omega)) hpin hbr_p
    have hT : pinFalseBits.length + (1 + (1 + (r * (fullAdderBits.length + 1) + 1))) ≤
        200 * n ^ 2 + 2000 * n + 2000 := by
      rw [pinFalseBits_len, fullAdderBits_len]; omega
    have hfin := hcomb.weaken (V₂ := V) (T₂ := 200 * n ^ 2 + 2000 * n + 2000) (by simp) hT
    simp only [List.nil_append] at hfin
    simp only [rmEmitV15b, rmEmitV15bEntry, hm2, ↓reduceIte]
    exact ⟨_, _, (PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
        ((PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
          (PreservedRegs.upd_ge _ regLoopRem _ (by decide))), hfin⟩

/-- Full Block 15 emitter (`v_tree`), uniform state type `RMEmitV15Q` across all 3 modes. -/
abbrev RMEmitV15Q : Type := RMEmitV15aQ ⊕ RMV15bQ

def rmEmitV15 (mode : ℕ) : RMProg EncR RMEmitV15Q :=
  rmChain rmEmitV15a (rmEmitV15b mode) rmEmitV15bEntry

def rmEmitV15Entry : RMEmitV15Q := Sum.inl rmEmitV15aEntry

lemma rmEmitV15_spec (mode n V : ℕ) (s : Fin n → ZMod 2) (t0 t1 : ℕ) (inp : List Bool)
    (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V)
    (hT0 : reg₀ regT0 = t0) (hT1 : reg₀ regT1 = t1) :
    ∃ q₁ reg₁,
      PreservedRegs reg₁ reg₀ ∧
      RMExec (rmEmitV15 mode) V inp rmEmitV15Entry reg₀ q₁ reg₁
        ((List.range (treeVertOff (treeLog n + 1) (treeLog n + 2))).flatMap
          (fun locV => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + locV))))
        (300 * n ^ 2 + 13000 * n + 2500) := by
  rcases rmEmitV15a_spec mode n V s t0 t1 inp reg₀ hn hp hreg₀ hV with ⟨r1, hpr1, ha⟩
  have hp1 := hp.of_preserved hpr1
  rcases rmEmitV15b_spec mode n V t0 t1 inp r1 hn hp1 ha.reg₁_le hV
      (by rw [hpr1 regT0 (by decide), hT0]) (by rw [hpr1 regT1 (by decide), hT1])
    with ⟨q2, r2, hpr2, hb⟩
  have hact : rmEmitV15a rmEmitV15aEntry ≠ none := by
    simp [rmEmitV15a, rmEmitV15aEntry, rmChain, rmSeq, rmSetConst, rmSetConstEntry, rmZero]
  have hcomb := rmChain_spec_inl hact ha hb
  have hT : 40 * n ^ 2 + 10000 * n + 50 + (200 * n ^ 2 + 2000 * n + 2000) ≤
      300 * n ^ 2 + 13000 * n + 2500 := by omega
  have hfin := hcomb.weaken (V₂ := V) (T₂ := 300 * n ^ 2 + 13000 * n + 2500) (by simp) hT
  have hstep : treeVertOff (treeLog n + 1) (treeLog n + 2) =
      treeVertOff (treeLog n + 1) (treeLog n + 1) + (treeLog n + 1 + 1) := by
    have := treeVertOff_step (r := treeLog n + 1) (j := treeLog n + 1) (by omega)
    simpa [Nat.sub_self] using this
  have hout :
      (List.range (treeVertOff (treeLog n + 1) (treeLog n + 1))).flatMap
        (fun locV => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + locV))) ++
      (pinFalseBits ++ (List.range (treeLog n + 1)).flatMap (fun b =>
        if mode = 2 then sepFullAdderBits (decide (t0 < 2 ^ (treeLog n + 1) ∧ t1 < 2 ^ (treeLog n + 1)))
          (t0.testBit b) (t1.testBit b)
        else fullAdderBits)) =
      (List.range (treeVertOff (treeLog n + 1) (treeLog n + 2))).flatMap
        (fun locV => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV15 n + locV))) := by
    conv_rhs => rw [hstep, flatMap_range_add, v15_root_flatMap]
  rw [hout] at hfin
  exact ⟨Sum.inr q2, r2, hpr2.trans hpr1, hfin⟩

/-!
## Section 4: Vertex Circuit Emitters for Blocks 16, 17, and 18 (`v_cmp_init`, `v_cmp`, `v_cmp_end`)
-/

/-- Shared single-bit-shift emitter loop: emits `(List.range rem).flatMap (fun d => if cur.testBit d then bsT else bsF)`
in linear time `30 * cur + rem * (max bsF.length bsT.length + 25) + 1`. -/
abbrev RMBitShiftStepQ (bsF bsT : List Bool) : Type :=
  RMSetConstQ 2 ⊕ (RMDivModQ ⊕ (Bool ⊕
    (Option Bool ⊕ (Fin (bsF.length + 1) ⊕ (Bool ⊕ Fin (bsT.length + 1))))))

def rmBitShiftStep (bsF bsT : List Bool) : RMProg EncR (RMBitShiftStepQ bsF bsT) :=
  rmChain (rmSetConst regS1 2)
    (rmChain (rmDivMod regS2 regS3 regLoopJ regS1 regS4 regS5 regS6)
      (rmChain (rmCopy regLoopJ regS2)
        (rmIfZero regS3 (rmEmitBits bsF) (rmEmitBits bsT) ⟨0, by omega⟩ ⟨0, by omega⟩)
        rmIfZeroEntry)
      (Sum.inl false))
    (Sum.inl rmDivModEntry)

def rmBitShiftStepEntry {bsF bsT : List Bool} : RMBitShiftStepQ bsF bsT := Sum.inl rmSetConstEntry

lemma rmBitShiftLoop_spec (bsF bsT : List Bool) (V : ℕ) (inp : List Bool) (h2V : 2 ≤ V) :
    ∀ (rem cur : ℕ) (reg : RegState EncR),
      reg regLoopRem = rem → reg regLoopJ = cur → (∀ i, reg i ≤ V) →
      ∃ r1 : RegState EncR,
        PreservedRegs r1 reg ∧
        RMExec (rmWhileDec regLoopRem (rmBitShiftStep bsF bsT) rmBitShiftStepEntry) V inp
          rmWhileDecEntry reg rmWhileDecExit r1
          ((List.range rem).flatMap (fun d => if cur.testBit d then bsT else bsF))
          (30 * cur + rem * (max bsF.length bsT.length + 25) + 1)
  | 0, cur, reg, hrem, _, hreg =>
    ⟨reg, PreservedRegs.refl reg,
      (rmWhileDec_zero regLoopRem (rmBitShiftStep bsF bsT) rmBitShiftStepEntry V inp reg hrem hreg).weaken
        (V₂ := V) (T₂ := 30 * cur + 0 * (max bsF.length bsT.length + 25) + 1) (le_refl _) (by omega)⟩
  | rem + 1, cur, reg, hrem, hJ, hreg => by
    have h1V : 1 ≤ V := by omega
    have hne : reg regLoopRem ≠ 0 := by omega
    set r1 := regUpd reg regLoopRem (reg regLoopRem - 1)
    have hr1 : ∀ i, r1 i ≤ V := regUpd_le hreg regLoopRem (le_trans (Nat.sub_le _ _) (hreg regLoopRem))
    have h1_rem : r1 regLoopRem = rem := by simp [r1, hrem]
    have h1_J : r1 regLoopJ = cur := by simp [r1, hJ]
    have hsc := rmSetConst_spec regS1 2 V inp r1 hr1 h2V
    set r2 := regUpd r1 regS1 2
    have h2_J : r2 regLoopJ = cur := by simp [r2, h1_J]
    rcases rmDivMod_spec regS2 regS3 regLoopJ regS1 regS4 regS5 regS6
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        V inp r2 (by simp [r2]) hsc.reg₁_le h1V
      with ⟨r3, h3_q, h3_r, h3_fr, hd3⟩
    have h3_q' : r3 regS2 = cur / 2 := by rw [h3_q, h2_J]; simp [r2]
    have h3_r' : r3 regS3 = cur % 2 := by rw [h3_r, h2_J]; simp [r2]
    have hc4 := rmCopy_spec regLoopJ regS2 V inp r3 hd3.reg₁_le
    set r4 := regUpd r3 regLoopJ (r3 regS2)
    have h4_S3 : r4 regS3 = cur % 2 := by simp [r4, h3_r']
    have h4_J : r4 regLoopJ = cur / 2 := by simp [r4, h3_q']
    have h4_rem : r4 regLoopRem = rem := by
      dsimp only [r4]; rw [regUpd_ne _ (by decide),
        h3_fr regLoopRem (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [r2, h1_rem]
    have hem : ∃ qE, RMExec
        (rmIfZero regS3 (rmEmitBits bsF) (rmEmitBits bsT) ⟨0, by omega⟩ ⟨0, by omega⟩)
        V inp rmIfZeroEntry r4 qE r4 (if cur.testBit 0 then bsT else bsF) (max bsF.length bsT.length + 2) := by
      by_cases h0 : cur % 2 = 0
      · have ht0 : cur.testBit 0 = false := by rw [testBit_zero_eq_mod]; simp [h0]
        rw [ht0]; simp only [Bool.false_eq_true, ↓reduceIte]
        have he := rmEmitBits_spec bsF V inp r4 hc4.reg₁_le
        have hif := (rmIfZero_zero_spec regS3 (rmEmitBits bsT) ⟨0, by omega⟩ (by rw [h4_S3, h0]) he).weaken
          (V₂ := V) (T₂ := max bsF.length bsT.length + 2) (le_refl _) (by have := le_max_left bsF.length bsT.length; omega)
        exact ⟨_, hif⟩
      · have ht0 : cur.testBit 0 = true := by rw [testBit_zero_eq_mod]; simp [h0]
        rw [ht0]; simp only [↓reduceIte]
        have he := rmEmitBits_spec bsT V inp r4 hc4.reg₁_le
        have hif := (rmIfZero_pos_spec regS3 (rmEmitBits bsF) ⟨0, by omega⟩ (by rw [h4_S3]; exact h0) he).weaken
          (V₂ := V) (T₂ := max bsF.length bsT.length + 2) (le_refl _) (by have := le_max_right bsF.length bsT.length; omega)
        exact ⟨_, hif⟩
    rcases hem with ⟨qE, he4⟩
    have hbody := rmChain_spec_inl (by simp [rmSetConst, rmSetConstEntry, rmChain, rmSeq, rmZero]) hsc
      (rmChain_spec_inl (by simp [rmDivMod, rmDivModEntry, rmChain, rmSeq, rmZero]) hd3
        (rmChain_spec_inl (by simp [rmCopy]) hc4 he4))
    have hTbody : 1 + 2 + (15 * r2 regLoopJ + 2 * r2 regS1 + 10 + (1 + (max bsF.length bsT.length + 2))) ≤
        15 * cur + (max bsF.length bsT.length + 24) := by
      have hr2S1 : r2 regS1 = 2 := by simp [r2]
      rw [h2_J, hr2S1]; omega
    have hbody' := hbody.weaken (V₂ := V) (T₂ := 15 * cur + (max bsF.length bsT.length + 24)) (by simp) hTbody
    simp only [List.nil_append] at hbody'
    rcases rmBitShiftLoop_spec bsF bsT V inp h2V rem (cur / 2) r4 h4_rem h4_J hbody'.reg₁_le
      with ⟨r_end, hpr_end, hrest⟩
    have hstep := rmWhileDec_step regLoopRem (rmBitShiftStep bsF bsT) hne hreg hbody' hrest
    have hT : 1 + (15 * cur + (max bsF.length bsT.length + 24)) +
        (30 * (cur / 2) + rem * (max bsF.length bsT.length + 25) + 1) ≤
        30 * cur + (rem + 1) * (max bsF.length bsT.length + 25) + 1 := by
      have hring : (rem + 1) * (max bsF.length bsT.length + 25) =
          rem * (max bsF.length bsT.length + 25) + (max bsF.length bsT.length + 25) := by ring
      omega
    have hfm : (if cur.testBit 0 then bsT else bsF) ++
        (List.range rem).flatMap (fun d => if (cur / 2).testBit d then bsT else bsF) =
        (List.range (rem + 1)).flatMap (fun d => if cur.testBit d then bsT else bsF) := by
      have hsh := list_range_succ_flatMap_shift
        (fun d => if cur.testBit d then bsT else bsF) rem 0
      simp only [Nat.zero_add] at hsh
      rw [hsh]
      exact congrArg ((if cur.testBit 0 then bsT else bsF) ++ ·)
        (list_flatMap_range_congr rem (fun d _ => by
          rw [testBit_div_two, show 1 + d = d + 1 by omega]))
    have hfin := hstep.weaken (V₂ := V) (T₂ := 30 * cur + (rem + 1) * (max bsF.length bsT.length + 25) + 1)
      (by simp) hT
    rw [hfm] at hfin
    have h4pr : PreservedRegs r4 reg := fun k hk => by
      have hne : ∀ q : Fin EncR, 41 ≤ q.val → k ≠ q := fun q hq heq => by
        have := congrArg Fin.val heq; omega
      dsimp only [r4]; rw [regUpd_ne _ (hne regLoopJ (by decide)),
        h3_fr k (hne regS2 (by decide)) (hne regS3 (by decide)) (hne regS4 (by decide))
          (hne regS5 (by decide)) (hne regS6 (by decide))]
      dsimp only [r2, r1]
      rw [regUpd_ne _ (hne regS1 (by decide)), regUpd_ne _ (hne regLoopRem (by decide))]
    exact ⟨r_end, hpr_end.trans h4pr, hfin⟩

/-! ### Block 17 (`v_cmp`, `W = treeLog n + 2` vertices, uniform across all 3 modes) -/

abbrev RMV17ExactFalseQ : Type :=
  Bool ⊕ (Fin 3 ⊕ (Option Bool ⊕ (Unit ⊕ Fin (exactCmpFalseBits.length + 1))))
abbrev RMV17ExactTrueQ : Type :=
  Bool ⊕ (Bool ⊕ (Fin 3 ⊕ (Option Bool ⊕ (Unit ⊕ RMBitShiftStepQ (exactCmpStepBits true false) (exactCmpStepBits true true)))))
abbrev RMV17ExactQ : Type :=
  RMSetAddQ ⊕ (RMSetAddQ ⊕ (Fin 8 ⊕ (Option Bool ⊕ (RMV17ExactFalseQ ⊕ (Bool ⊕ RMV17ExactTrueQ)))))
abbrev RMV17LeQ : Type :=
  Bool ⊕ (Bool ⊕ (Fin 3 ⊕ (Option Bool ⊕ (Unit ⊕ RMBitShiftStepQ (borrowStepBits false) (borrowStepBits true)))))
abbrev RMV17SepQ : Type :=
  Bool ⊕ (Fin 3 ⊕ (Option Bool ⊕ (Unit ⊕ Fin (sepCmpStepBits.length + 1))))
abbrev RMEmitV17Q : Type := RMV17ExactQ ⊕ (RMV17LeQ ⊕ RMV17SepQ)

def rmV17ExactFalse : RMProg EncR RMV17ExactFalseQ :=
  rmChain (rmCopy regLoopRem regTreeLog)
    (rmChain (rmAddConst regLoopRem 2)
      (rmWhileDec regLoopRem (rmEmitBits exactCmpFalseBits) ⟨0, by decide⟩)
      rmWhileDecEntry)
    (Sum.inl ⟨0, by omega⟩)

def rmV17ExactTrue : RMProg EncR RMV17ExactTrueQ :=
  rmChain (rmCopy regLoopJ regT0)
    (rmChain (rmCopy regLoopRem regTreeLog)
      (rmChain (rmAddConst regLoopRem 2)
        (rmWhileDec regLoopRem
          (rmBitShiftStep (exactCmpStepBits true false) (exactCmpStepBits true true))
          rmBitShiftStepEntry)
        rmWhileDecEntry)
      (Sum.inl ⟨0, by omega⟩))
    (Sum.inl false)

def rmV17Exact : RMProg EncR RMV17ExactQ :=
  rmChain (rmSetAdd regS1 regTreeM regTreeM)
    (rmChain (rmSetAdd regS7 regS1 regS1)
      (rmChain (rmCmpLt regS0 regT0 regS7 regS1 regS2)
        (rmIfZero regS0 rmV17ExactFalse rmV17ExactTrue (Sum.inl false) (Sum.inl false))
        rmIfZeroEntry)
      (Sum.inl 0))
    (Sum.inl rmSetAddEntry)

def rmV17Le : RMProg EncR RMV17LeQ :=
  rmChain (rmCopy regLoopJ regT0)
    (rmChain (rmCopy regLoopRem regTreeLog)
      (rmChain (rmAddConst regLoopRem 2)
        (rmWhileDec regLoopRem
          (rmBitShiftStep (borrowStepBits false) (borrowStepBits true))
          rmBitShiftStepEntry)
        rmWhileDecEntry)
      (Sum.inl ⟨0, by omega⟩))
    (Sum.inl false)

def rmV17Sep : RMProg EncR RMV17SepQ :=
  rmChain (rmCopy regLoopRem regTreeLog)
    (rmChain (rmAddConst regLoopRem 2)
      (rmWhileDec regLoopRem (rmEmitBits sepCmpStepBits) ⟨0, by decide⟩)
      rmWhileDecEntry)
    (Sum.inl ⟨0, by omega⟩)

def rmEmitV17 : RMProg EncR RMEmitV17Q :=
  rmBranch rmV17Exact (rmBranch rmV17Le rmV17Sep)

def rmEmitV17Entry (mode : ℕ) : RMEmitV17Q :=
  if mode = 0 then Sum.inl (Sum.inl rmSetAddEntry)
  else if mode = 1 then Sum.inr (Sum.inl (Sum.inl false))
  else Sum.inr (Sum.inr (Sum.inl false))

lemma rmEmitV17_spec (mode n V t0 : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V)
    (hT0 : reg₀ regT0 = t0) :
    let W := treeLog n + 2
    ∃ q₁ reg₁,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitV17 V inp (rmEmitV17Entry mode) reg₀ q₁ reg₁
        ((List.range W).flatMap (fun b =>
          QCSD_encodeCircuit
            (if mode = 0 then exactCmpStepCircuit (decide (t0 < 2 ^ W)) (t0.testBit b)
             else if mode = 1 then borrowStepCircuit (t0.testBit b)
             else sepCmpStepCircuit)))
        (500 * n + 30 * t0 + 500) := by
  intro W
  have h1V : 1 ≤ V := by omega
  have h2V : 2 ≤ V := by omega
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hlog_le : treeLog n ≤ n := treeLog_le_self hn
  have hpowW : 2 ^ W = 4 * treeM n := two_pow_treeLog_succ2 n
  have hTL : reg₀ regTreeLog = treeLog n := hp.2.2.2.2.2.2.2.2.2.2.1
  have hTM : reg₀ regTreeM = treeM n := hp.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hm0 : mode = 0
  · -- mode = 0: rmV17Exact
    have ha1 := rmSetAdd_spec regS1 regTreeM regTreeM (by decide) (by decide) (by decide)
      V inp reg₀ hreg₀ (by rw [hTM]; omega)
    set s1 := regUpd (regUpd reg₀ regS1 (reg₀ regTreeM + reg₀ regTreeM)) regS0 0
    have hs1_S1 : s1 regS1 = 2 * treeM n := by simp [s1, hTM]; omega
    have ha2 := rmSetAdd_spec regS7 regS1 regS1 (by decide) (by decide) (by decide)
      V inp s1 ha1.reg₁_le (by rw [hs1_S1]; omega)
    set s2 := regUpd (regUpd s1 regS7 (s1 regS1 + s1 regS1)) regS0 0
    have hs2_S7 : s2 regS7 = 2 ^ W := by simp [s2, hs1_S1, hpowW]; omega
    have hs2_T0 : s2 regT0 = t0 := by simp [s2, s1, hT0]
    rcases rmCmpLt_spec regS0 regT0 regS7 regS1 regS2 (by decide) (by decide) (by decide) (by decide)
        V inp s2 ha2.reg₁_le h1V with ⟨s3, hs3_fl, hs3_fr, hcmp3⟩
    have hs3_pr : PreservedRegs s3 reg₀ := fun k hk => by
      have hne : ∀ q : Fin EncR, 41 ≤ q.val → k ≠ q := fun q hq heq => by
        have := congrArg Fin.val heq; omega
      rw [hs3_fr k (hne regS0 (by decide)) (hne regS1 (by decide)) (hne regS2 (by decide))]
      dsimp only [s2, s1]
      rw [regUpd_ne _ (hne regS0 (by decide)), regUpd_ne _ (hne regS7 (by decide)),
          regUpd_ne _ (hne regS0 (by decide)), regUpd_ne _ (hne regS1 (by decide))]
    have hs3_TL : s3 regTreeLog = treeLog n := by rw [hs3_pr regTreeLog (by decide), hTL]
    have hs3_T0 : s3 regT0 = t0 := by rw [hs3_pr regT0 (by decide), hT0]
    have hbr : ∃ qB s4,
        PreservedRegs s4 s3 ∧
        RMExec (rmIfZero regS0 rmV17ExactFalse rmV17ExactTrue (Sum.inl false) (Sum.inl false))
          V inp rmIfZeroEntry s3 qB s4
          ((List.range W).flatMap (fun b =>
            QCSD_encodeCircuit (exactCmpStepCircuit (decide (t0 < 2 ^ W)) (t0.testBit b))))
          (450 * n + 400) := by
      by_cases hg : t0 < 2 ^ W
      · have hfl : s3 regS0 ≠ 0 := by rw [hs3_fl, hs2_T0, hs2_S7]; simp [hg]
        have hc1 := rmCopy_spec regLoopJ regT0 V inp s3 hcmp3.reg₁_le
        set t1 := regUpd s3 regLoopJ (s3 regT0)
        have hc2 := rmCopy_spec regLoopRem regTreeLog V inp t1 hc1.reg₁_le
        set t2 := regUpd t1 regLoopRem (t1 regTreeLog)
        have ha3 := rmAddConst_spec regLoopRem 2 V inp t2 hc2.reg₁_le (by simp [t2, t1, hs3_TL]; omega)
        set t3 := regUpd t2 regLoopRem (t2 regLoopRem + 2)
        rcases rmBitShiftLoop_spec (exactCmpStepBits true false) (exactCmpStepBits true true)
            V inp h2V W t0 t3 (by simp [t3, t2, t1, hs3_TL, W]) (by simp [t3, t2, t1, hs3_T0]) ha3.reg₁_le
          with ⟨t4, ht4_pr, hloop⟩
        have htrue := rmChain_spec_inl (by simp [rmCopy]) hc1
          (rmChain_spec_inl (by simp [rmCopy]) hc2
            (rmChain_spec_inl (by simp [rmAddConst]) ha3 hloop))
        have hlenF := exactCmpStepBits_len true false
        have hlenT := exactCmpStepBits_len true true
        have hT : 2 + (1 + (1 + (2 + (30 * t0 + W * (max (exactCmpStepBits true false).length
            (exactCmpStepBits true true).length + 25) + 1)))) ≤ 450 * n + 400 := by
          simp only [↓reduceIte] at hlenF hlenT
          rw [hlenF, hlenT, max_self]; omega
        have hif := (rmIfZero_pos_spec regS0 rmV17ExactFalse (Sum.inl false) hfl htrue).weaken
          (V₂ := V) (T₂ := 450 * n + 400) (by simp) hT
        simp only [List.nil_append] at hif
        have hout : (List.range W).flatMap (fun d =>
              if t0.testBit d then exactCmpStepBits true true else exactCmpStepBits true false) =
            (List.range W).flatMap (fun b =>
              QCSD_encodeCircuit (exactCmpStepCircuit (decide (t0 < 2 ^ W)) (t0.testBit b))) :=
          list_flatMap_range_congr W (fun b _ => by
            rw [encodeCircuit_exactCmpStepCircuit, decide_eq_true hg]
            cases t0.testBit b <;> rfl)
        rw [hout] at hif
        have ht3_pr : PreservedRegs t3 s3 :=
          (PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
            ((PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
              (PreservedRegs.upd_ge _ regLoopJ _ (by decide)))
        exact ⟨_, t4, ht4_pr.trans ht3_pr, hif⟩
      · have hfl : s3 regS0 = 0 := by rw [hs3_fl, hs2_T0, hs2_S7]; simp [hg]
        have hc1 := rmCopy_spec regLoopRem regTreeLog V inp s3 hcmp3.reg₁_le
        set t1 := regUpd s3 regLoopRem (s3 regTreeLog)
        have ha2 := rmAddConst_spec regLoopRem 2 V inp t1 hc1.reg₁_le (by simp [t1, hs3_TL]; omega)
        set t2 := regUpd t1 regLoopRem (t1 regLoopRem + 2)
        have hrep := rmEmitRepeat_spec regLoopRem exactCmpFalseBits V inp W t2
          (by simp [t2, t1, hs3_TL, W]) ha2.reg₁_le
        have hfalse := rmChain_spec_inl (by simp [rmCopy]) hc1 (rmChain_spec_inl (by simp [rmAddConst]) ha2 hrep)
        have hT : 2 + (1 + (2 + (W * (exactCmpFalseBits.length + 1) + 1))) ≤ 450 * n + 400 := by
          rw [exactCmpFalseBits_len]; omega
        have hif := (rmIfZero_zero_spec regS0 rmV17ExactTrue (Sum.inl false) hfl hfalse).weaken
          (V₂ := V) (T₂ := 450 * n + 400) (by simp) hT
        simp only [List.nil_append] at hif
        have hout : (List.range W).flatMap (fun _ => exactCmpFalseBits) =
            (List.range W).flatMap (fun b =>
              QCSD_encodeCircuit (exactCmpStepCircuit (decide (t0 < 2 ^ W)) (t0.testBit b))) :=
          list_flatMap_range_congr W (fun b _ => by
            rw [encodeCircuit_exactCmpStepCircuit, decide_eq_false hg]; rfl)
        rw [hout] at hif
        exact ⟨_, _, (PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
            ((PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
              (PreservedRegs.upd_ge _ regLoopRem _ (by decide))), hif⟩
    rcases hbr with ⟨qB, s4, hs4_pr, hif4⟩
    have hex := rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha1
      (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha2
        (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp3 hif4))
    have hT : 2 * reg₀ regTreeM + 3 + (2 * s1 regS1 + 3 + (2 * min (s2 regT0) (s2 regS7) + 6 +
        (450 * n + 400))) ≤ 500 * n + 30 * t0 + 500 := by
      rw [hTM, hs1_S1, hs2_T0, hs2_S7]; have : min t0 (2 ^ W) ≤ 2 ^ W := min_le_right _ _; omega
    have hfin := (rmBranch_inl_spec (rmBranch rmV17Le rmV17Sep) hex).weaken
      (V₂ := V) (T₂ := 500 * n + 30 * t0 + 500) (by simp) hT
    simp only [List.nil_append] at hfin
    simp only [rmEmitV17, rmEmitV17Entry, hm0, ↓reduceIte]
    exact ⟨_, s4, hs4_pr.trans hs3_pr, hfin⟩
  · by_cases hm1 : mode = 1
    · -- mode = 1: rmV17Le
      have hc1 := rmCopy_spec regLoopJ regT0 V inp reg₀ hreg₀
      set s1 := regUpd reg₀ regLoopJ (reg₀ regT0)
      have hc2 := rmCopy_spec regLoopRem regTreeLog V inp s1 hc1.reg₁_le
      set s2 := regUpd s1 regLoopRem (s1 regTreeLog)
      have ha3 := rmAddConst_spec regLoopRem 2 V inp s2 hc2.reg₁_le (by simp [s2, s1, hTL]; omega)
      set s3 := regUpd s2 regLoopRem (s2 regLoopRem + 2)
      rcases rmBitShiftLoop_spec (borrowStepBits false) (borrowStepBits true)
          V inp h2V W t0 s3 (by simp [s3, s2, s1, hTL, W]) (by simp [s3, s2, s1, hT0]) ha3.reg₁_le
        with ⟨s4, hs4_pr, hloop⟩
      have hle := rmChain_spec_inl (by simp [rmCopy]) hc1
        (rmChain_spec_inl (by simp [rmCopy]) hc2
          (rmChain_spec_inl (by simp [rmAddConst]) ha3 hloop))
      have hlenF := borrowStepBits_len false
      have hlenT := borrowStepBits_len true
      have hT : 1 + (1 + (2 + (30 * t0 + W * (max (borrowStepBits false).length
          (borrowStepBits true).length + 25) + 1))) ≤ 500 * n + 30 * t0 + 500 := by
        rw [hlenF, hlenT, max_self]; omega
      have hfin := (rmBranch_inr_spec rmV17Exact (rmBranch_inl_spec rmV17Sep hle)).weaken
        (V₂ := V) (T₂ := 500 * n + 30 * t0 + 500) (by simp) hT
      simp only [List.nil_append] at hfin
      have hout : (List.range W).flatMap (fun d =>
            if t0.testBit d then borrowStepBits true else borrowStepBits false) =
          (List.range W).flatMap (fun b => QCSD_encodeCircuit (borrowStepCircuit (t0.testBit b))) :=
        list_flatMap_range_congr W (fun b _ => by
          rw [encodeCircuit_borrowStepCircuit]; cases t0.testBit b <;> rfl)
      rw [hout] at hfin
      have hs3_pr : PreservedRegs s3 reg₀ :=
        (PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
          ((PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
            (PreservedRegs.upd_ge _ regLoopJ _ (by decide)))
      simp only [rmEmitV17, rmEmitV17Entry, hm1, ↓reduceIte]
      exact ⟨_, s4, hs4_pr.trans hs3_pr, hfin⟩
    · -- mode ≥ 2: rmV17Sep
      have hc1 := rmCopy_spec regLoopRem regTreeLog V inp reg₀ hreg₀
      set s1 := regUpd reg₀ regLoopRem (reg₀ regTreeLog)
      have ha2 := rmAddConst_spec regLoopRem 2 V inp s1 hc1.reg₁_le (by simp [s1, hTL]; omega)
      set s2 := regUpd s1 regLoopRem (s1 regLoopRem + 2)
      have hrep := rmEmitRepeat_spec regLoopRem sepCmpStepBits V inp W s2
        (by simp [s2, s1, hTL, W]) ha2.reg₁_le
      have hsep := rmChain_spec_inl (by simp [rmCopy]) hc1 (rmChain_spec_inl (by simp [rmAddConst]) ha2 hrep)
      have hT : 1 + (2 + (W * (sepCmpStepBits.length + 1) + 1)) ≤ 500 * n + 30 * t0 + 500 := by
        rw [sepCmpStepBits_len]; omega
      have hfin := (rmBranch_inr_spec rmV17Exact (rmBranch_inr_spec rmV17Le hsep)).weaken
        (V₂ := V) (T₂ := 500 * n + 30 * t0 + 500) (by simp) hT
      simp only [List.nil_append] at hfin
      have hout : (List.range W).flatMap (fun _ => sepCmpStepBits) =
          (List.range W).flatMap (fun _ => QCSD_encodeCircuit sepCmpStepCircuit) :=
        list_flatMap_range_congr W (fun _ _ => rfl)
      rw [hout] at hfin
      simp only [rmEmitV17, rmEmitV17Entry, hm0, hm1, ↓reduceIte]
      exact ⟨_, _, (PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
          ((PreservedRegs.upd_ge _ regLoopRem _ (by decide)).trans
            (PreservedRegs.upd_ge _ regLoopRem _ (by decide))), hfin⟩

/-! ### Block 18 (`v_cmp_end`, 1 vertex, uniform across all 3 modes) -/

abbrev RMV18LeQ : Type :=
  RMSetAddQ ⊕ (RMSetAddQ ⊕ (Fin 8 ⊕
    (Option Bool ⊕ (Fin (const1TrueBits.length + 1) ⊕ (Bool ⊕ Fin (pinFalseBits.length + 1))))))
abbrev RMEmitV18Q : Type := RMV18LeQ ⊕ Fin (pinFalseBits.length + 1)

def rmV18Le : RMProg EncR RMV18LeQ :=
  rmChain (rmSetAdd regS1 regTreeM regTreeM)
    (rmChain (rmSetAdd regS7 regS1 regS1)
      (rmChain (rmCmpLt regS0 regT0 regS7 regS1 regS2)
        (rmIfZero regS0 (rmEmitBits const1TrueBits) (rmEmitBits pinFalseBits)
          ⟨0, by decide⟩ ⟨0, by decide⟩)
        rmIfZeroEntry)
      (Sum.inl 0))
    (Sum.inl rmSetAddEntry)

def rmEmitV18 : RMProg EncR RMEmitV18Q :=
  rmBranch rmV18Le (rmEmitBits pinFalseBits)

def rmEmitV18Entry (mode : ℕ) : RMEmitV18Q :=
  if mode = 1 then Sum.inl (Sum.inl rmSetAddEntry) else Sum.inr ⟨0, by decide⟩

lemma rmEmitV18_spec (mode n V t0 : ℕ) (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V) (hV : 500 * n + 20 ≤ V)
    (hT0 : reg₀ regT0 = t0) :
    ∃ q₁ reg₁,
      PreservedRegs reg₁ reg₀ ∧
      RMExec rmEmitV18 V inp (rmEmitV18Entry mode) reg₀ q₁ reg₁
        (if mode = 1 ∧ ¬(t0 < 2 ^ (treeLog n + 2)) then const1TrueBits else pinFalseBits)
        (40 * n + 40) := by
  have h1V : 1 ≤ V := by omega
  have hM_le : treeM n ≤ 2 * n := treeM_le_two_mul hn
  have hpowW : 2 ^ (treeLog n + 2) = 4 * treeM n := two_pow_treeLog_succ2 n
  have hTM : reg₀ regTreeM = treeM n := hp.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hm1 : mode = 1
  · have ha1 := rmSetAdd_spec regS1 regTreeM regTreeM (by decide) (by decide) (by decide)
      V inp reg₀ hreg₀ (by rw [hTM]; omega)
    set s1 := regUpd (regUpd reg₀ regS1 (reg₀ regTreeM + reg₀ regTreeM)) regS0 0
    have hs1_S1 : s1 regS1 = 2 * treeM n := by simp [s1, hTM]; omega
    have ha2 := rmSetAdd_spec regS7 regS1 regS1 (by decide) (by decide) (by decide)
      V inp s1 ha1.reg₁_le (by rw [hs1_S1]; omega)
    set s2 := regUpd (regUpd s1 regS7 (s1 regS1 + s1 regS1)) regS0 0
    have hs2_S7 : s2 regS7 = 2 ^ (treeLog n + 2) := by simp [s2, hs1_S1, hpowW]; omega
    have hs2_T0 : s2 regT0 = t0 := by simp [s2, s1, hT0]
    rcases rmCmpLt_spec regS0 regT0 regS7 regS1 regS2 (by decide) (by decide) (by decide) (by decide)
        V inp s2 ha2.reg₁_le h1V with ⟨s3, hs3_fl, hs3_fr, hcmp3⟩
    have hs3_pr : PreservedRegs s3 reg₀ := fun k hk => by
      have hne : ∀ q : Fin EncR, 41 ≤ q.val → k ≠ q := fun q hq heq => by
        have := congrArg Fin.val heq; omega
      rw [hs3_fr k (hne regS0 (by decide)) (hne regS1 (by decide)) (hne regS2 (by decide))]
      dsimp only [s2, s1]
      rw [regUpd_ne _ (hne regS0 (by decide)), regUpd_ne _ (hne regS7 (by decide)),
          regUpd_ne _ (hne regS0 (by decide)), regUpd_ne _ (hne regS1 (by decide))]
    have hbr : ∃ qB, RMExec
        (rmIfZero regS0 (rmEmitBits const1TrueBits) (rmEmitBits pinFalseBits) ⟨0, by decide⟩ ⟨0, by decide⟩)
        V inp rmIfZeroEntry s3 qB s3
        (if ¬(t0 < 2 ^ (treeLog n + 2)) then const1TrueBits else pinFalseBits) 16 := by
      by_cases hlt : t0 < 2 ^ (treeLog n + 2)
      · have hfl : s3 regS0 ≠ 0 := by rw [hs3_fl, hs2_T0, hs2_S7]; simp [hlt]
        have he := rmEmitBits_spec pinFalseBits V inp s3 hcmp3.reg₁_le
        have hif := (rmIfZero_pos_spec regS0 (rmEmitBits const1TrueBits) ⟨0, by decide⟩ hfl he).weaken
          (V₂ := V) (T₂ := 16) (le_refl _) (by rw [pinFalseBits_len]; omega)
        simp only [hlt, not_true_eq_false, ↓reduceIte]; exact ⟨_, hif⟩
      · have hfl : s3 regS0 = 0 := by rw [hs3_fl, hs2_T0, hs2_S7]; simp [hlt]
        have he := rmEmitBits_spec const1TrueBits V inp s3 hcmp3.reg₁_le
        have hif := (rmIfZero_zero_spec regS0 (rmEmitBits pinFalseBits) ⟨0, by decide⟩ hfl he).weaken
          (V₂ := V) (T₂ := 16) (le_refl _) (by rw [const1TrueBits_len]; omega)
        simp only [hlt, not_false_eq_true, ↓reduceIte]; exact ⟨_, hif⟩
    rcases hbr with ⟨qB, hif⟩
    have hle := rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha1
      (rmChain_spec_inl (by simp [rmSetAdd, rmSetAddEntry, rmChain, rmSeq, rmCopy]) ha2
        (rmChain_spec_inl (by simp [rmCmpLt, rmCmp]) hcmp3 hif))
    have hT : 2 * reg₀ regTreeM + 3 + (2 * s1 regS1 + 3 + (2 * min (s2 regT0) (s2 regS7) + 6 + 16)) ≤
        40 * n + 40 := by
      rw [hTM, hs1_S1, hs2_T0, hs2_S7]; have : min t0 (2 ^ (treeLog n + 2)) ≤ 2 ^ (treeLog n + 2) := min_le_right _ _
      omega
    have hfin := (rmBranch_inl_spec (rmEmitBits pinFalseBits) hle).weaken
      (V₂ := V) (T₂ := 40 * n + 40) (by simp) hT
    simp only [List.nil_append] at hfin
    simp only [rmEmitV18, rmEmitV18Entry, hm1, true_and, ↓reduceIte]
    exact ⟨_, s3, hs3_pr, hfin⟩
  · have he := rmEmitBits_spec pinFalseBits V inp reg₀ hreg₀
    have hfin := (rmBranch_inr_spec rmV18Le he).weaken (V₂ := V) (T₂ := 40 * n + 40) (le_refl _)
      (by rw [pinFalseBits_len]; omega)
    simp only [rmEmitV18, rmEmitV18Entry, hm1, false_and, ↓reduceIte]
    exact ⟨_, reg₀, PreservedRegs.refl reg₀, hfin⟩

/-!
## Section 5: Master Tail Circuit Emitter (`rmEmitBlocks10to18`, Blocks 10–18)
-/

abbrev RMEmitTailAQ : Type := (RMEmitV10Q ⊕ RMEmitV11Q) ⊕ (RMEmitV12Q ⊕ RMEmitV13to14Q)
abbrev RMEmitTailBQ : Type :=
  RMEmitV15Q ⊕ ((Fin (pinFalseBits.length + 1) ⊕ RMEmitV17Q) ⊕ RMEmitV18Q)
abbrev RMEmitBlocks10to18Q : Type := (RMEmitTailAQ ⊕ RMEmitTailBQ) ⊕ Unit

def rmEmitTailA : RMProg EncR RMEmitTailAQ :=
  rmChain (rmChain rmEmitV10 rmEmitV11 rmForRangeEntry)
    (rmChain rmEmitV12 rmEmitV13to14 rmEmitV13to14Entry)
    (Sum.inl rmForRangeEntry)

def rmEmitTailB (mode : ℕ) : RMProg EncR RMEmitTailBQ :=
  rmChain (rmEmitV15 mode)
    (rmChain (rmChain (rmEmitBits pinFalseBits) rmEmitV17 (rmEmitV17Entry mode))
      rmEmitV18 (rmEmitV18Entry mode))
    (Sum.inl (Sum.inl ⟨0, by decide⟩))

/-- Unified register-machine emitter for vertex circuit Blocks 10–18 across all 3 modes
(`mode = 0` Exact, `mode = 1` Le, `mode = 2` Sep), with mode-independent state type
`RMEmitBlocks10to18Q` and single deterministic exit state `rmEmitBlocks10to18Exit`. -/
def rmEmitBlocks10to18 (mode : ℕ) : RMProg EncR RMEmitBlocks10to18Q :=
  rmChain (rmChain rmEmitTailA (rmEmitTailB mode) (Sum.inl rmEmitV15Entry)) rmNop ()

def rmEmitBlocks10to18Entry : RMEmitBlocks10to18Q := Sum.inl (Sum.inl (Sum.inl (Sum.inl rmForRangeEntry)))
def rmEmitBlocks10to18Exit : RMEmitBlocks10to18Q := Sum.inr ()

/-- **Main Theorem (`rmEmitBlocks10to18_spec`)**:
Given `ParamsLoaded n reg₀`, `500 * n + 20 ≤ V`, `reg₀ regOffS + n ≤ V`, `reg₀ regT0 = t0`,
`reg₀ regT1 = t1`, and input tape bits matching `s` at `reg₀ regOffS`,
`rmEmitBlocks10to18 mode` emits EXACT
`(List.range (netVertCount n - netV10 n)).flatMap (fun d => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV10 n + d)))`
in `100000 * n ^ 2 + 30 * t0 + 5000` RM steps with register bound `Vmax = V`,
preserving `ParamsLoaded n` and all input-parser registers (`regCur..regOffPre`). -/
theorem rmEmitBlocks10to18_spec (mode n V : ℕ) (s : Fin n → ZMod 2) (t0 t1 : ℕ)
    (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V)
    (hV : 500 * n + 20 ≤ V)
    (hOffS : reg₀ regOffS + n ≤ V)
    (hT0 : reg₀ regT0 = t0) (hT1 : reg₀ regT1 = t1)
    (hs_bits : ∀ (i : ℕ) (hi : i < n), inp.getD (reg₀ regOffS + i) false = decide (s ⟨i, hi⟩ = (1 : ZMod 2))) :
    ∃ reg₁ : RegState EncR,
      ParamsLoaded n reg₁ ∧
      (∀ i : Fin EncR, 34 ≤ i.val → i.val ≤ 40 → reg₁ i = reg₀ i) ∧
      RMExec (rmEmitBlocks10to18 mode) V inp rmEmitBlocks10to18Entry reg₀ rmEmitBlocks10to18Exit reg₁
        ((List.range (netVertCount n - netV10 n)).flatMap
          (fun d => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV10 n + d))))
        (100000 * n ^ 2 + 30 * t0 + 5000) := by
  rcases rmEmitV10_spec n V inp reg₀ hn hp hreg₀ hV with ⟨r1, hpr1, e10⟩
  have hp1 := hp.of_preserved hpr1
  rcases rmEmitV11_spec n V inp r1 hn hp1 e10.reg₁_le hV with ⟨r2, hpr2, e11⟩
  have hpr20 : PreservedRegs r2 reg₀ := hpr2.trans hpr1
  have hp2 := hp.of_preserved hpr20
  have hr2_offS : r2 regOffS = reg₀ regOffS := hpr20 regOffS (by decide)
  rcases rmEmitV12_spec n V s inp r2 hn hp2 e11.reg₁_le (by rw [hr2_offS]; exact hOffS)
      (by rw [hr2_offS]; exact hs_bits)
    with ⟨r3, hpr3, e12⟩
  have hpr30 : PreservedRegs r3 reg₀ := hpr3.trans hpr20
  have hp3 := hp.of_preserved hpr30
  rcases rmEmitV13to14_spec n V inp r3 hn hp3 e12.reg₁_le hV with ⟨r4, hpr4, e1314⟩
  have hpr40 : PreservedRegs r4 reg₀ := hpr4.trans hpr30
  have hp4 := hp.of_preserved hpr40
  rcases rmEmitV15_spec mode n V s t0 t1 inp r4 hn hp4 e1314.reg₁_le hV
      (by rw [hpr40 regT0 (by decide), hT0]) (by rw [hpr40 regT1 (by decide), hT1])
    with ⟨q15, r5, hpr5, e15⟩
  have hpr50 : PreservedRegs r5 reg₀ := hpr5.trans hpr40
  have hp5 := hp.of_preserved hpr50
  have e16 := rmEmitBits_spec pinFalseBits V inp r5 e15.reg₁_le
  rcases rmEmitV17_spec mode n V t0 inp r5 hn hp5 e16.reg₁_le hV
      (by rw [hpr50 regT0 (by decide), hT0])
    with ⟨q17, r6, hpr6, e17⟩
  have hpr60 : PreservedRegs r6 reg₀ := hpr6.trans hpr50
  have hp6 := hp.of_preserved hpr60
  rcases rmEmitV18_spec mode n V t0 inp r6 hn hp6 e17.reg₁_le hV
      (by rw [hpr60 regT0 (by decide), hT0])
    with ⟨q18, r7, hpr7, e18⟩
  have hpr70 : PreservedRegs r7 reg₀ := hpr7.trans hpr60
  have eA1 := rmChain_spec_inl (rmForRange_active _ _ _ _ _) e10 e11
  have eA2 := rmChain_spec_inl (rmForRange_active _ _ _ _ _) e12 e1314
  have eA := rmChain_spec_inl (by simp [rmChain, rmSeq, rmForRange, rmForRangeEntry, rmZero]) eA1 eA2
  have eB1 := rmChain_spec_inl (rmEmitBits_active pinFalseBits (by rw [pinFalseBits_len]; omega)) e16 e17
  have eB2 := rmChain_spec_inl (by simp [rmChain, rmSeq, rmEmitBits, pinFalseBits_len]) eB1 e18
  have hact15 : rmEmitV15 mode rmEmitV15Entry ≠ none := by
    simp [rmEmitV15, rmEmitV15Entry, rmEmitV15a, rmEmitV15aEntry, rmChain, rmSeq,
      rmSetConst, rmSetConstEntry, rmZero]
  have eB := rmChain_spec_inl hact15 e15 eB2
  have eAB := rmChain_spec_inl (by simp [rmChain, rmSeq, rmForRange, rmForRangeEntry, rmZero]) eA eB
  have hactAB : rmChain rmEmitTailA (rmEmitTailB mode) (Sum.inl rmEmitV15Entry)
      (Sum.inl (Sum.inl (Sum.inl rmForRangeEntry))) ≠ none := by
    simp [rmEmitTailA, rmEmitV10, rmChain, rmSeq, rmForRange, rmForRangeEntry, rmZero]
  have eFull := rmChain_spec_inl hactAB eAB (rmNop_spec V inp r7 (by simpa using eAB.reg₁_le))
  have hT :
      (((65000 * n ^ 2 + 4000 * n + 10 + (300 * n ^ 2 + 1200 * n + 10)) +
        (5 * n ^ 2 + 400 * n + 10 + (100 * n + 50))) +
       ((300 * n ^ 2 + 13000 * n + 2500) +
        ((pinFalseBits.length + (500 * n + 30 * t0 + 500)) + (40 * n + 40)))) + 0 ≤
      100000 * n ^ 2 + 30 * t0 + 5000 := by
    rw [pinFalseBits_len]
    have hn12 : n ≤ n ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right n hn
    omega
  have hfin := eFull.weaken (V₂ := V) (T₂ := 100000 * n ^ 2 + 30 * t0 + 5000) (by simp) hT
  simp only [List.append_nil] at hfin
  rw [← flatMap_range_rawPredTail_eq mode n s t0 t1] at hfin
  exact ⟨r7, hp.of_preserved hpr70, fun i _ hi2 => hpr70 i (by omega), hfin⟩

/-- Corollary replacing `t0` with `V` in the step bound (since `t0 = reg₀ regT0 ≤ V`). -/
theorem rmEmitBlocks10to18_spec_V (mode n V : ℕ) (s : Fin n → ZMod 2) (t0 t1 : ℕ)
    (inp : List Bool) (reg₀ : RegState EncR)
    (hn : 1 ≤ n) (hp : ParamsLoaded n reg₀) (hreg₀ : ∀ j, reg₀ j ≤ V)
    (hV : 500 * n + 20 ≤ V)
    (hOffS : reg₀ regOffS + n ≤ V)
    (hT0 : reg₀ regT0 = t0) (hT1 : reg₀ regT1 = t1)
    (hs_bits : ∀ (i : ℕ) (hi : i < n), inp.getD (reg₀ regOffS + i) false = decide (s ⟨i, hi⟩ = (1 : ZMod 2))) :
    ∃ reg₁ : RegState EncR,
      ParamsLoaded n reg₁ ∧
      (∀ i : Fin EncR, 34 ≤ i.val → i.val ≤ 40 → reg₁ i = reg₀ i) ∧
      RMExec (rmEmitBlocks10to18 mode) V inp rmEmitBlocks10to18Entry reg₀ rmEmitBlocks10to18Exit reg₁
        ((List.range (netVertCount n - netV10 n)).flatMap
          (fun d => QCSD_encodeCircuit (rawPredTail mode n s t0 t1 (netV10 n + d))))
        (100000 * n ^ 2 + 30 * V + 5000) := by
  rcases rmEmitBlocks10to18_spec mode n V s t0 t1 inp reg₀ hn hp hreg₀ hV hOffS hT0 hT1 hs_bits
    with ⟨reg₁, hp₁, hpr₁, hex⟩
  have ht0V : t0 ≤ V := by rw [← hT0]; exact hreg₀ regT0
  exact ⟨reg₁, hp₁, hpr₁, hex.weaken (V₂ := V) (T₂ := 100000 * n ^ 2 + 30 * V + 5000) (le_refl _) (by omega)⟩

/-!
## Section 6: Explicit `Fintype` and `DecidableEq` Witnesses for `RMEmitBlocks10to18Q`

Built bottom-up using plain `abbrev`/`def` (zero `instance` declarations) so downstream TM
compilation (`Branch4_TMCompiler`) can supply `Fintype RMEmitBlocks10to18Q` and
`DecidableEq RMEmitBlocks10to18Q` without triggering deep nested-`Sum` typeclass synthesis.
-/

private abbrev ftSum {α β : Type} (hα : Fintype α) (hβ : Fintype β) : Fintype (α ⊕ β) := by
  letI := hα; letI := hβ; exact inferInstance

private def deSum {α β : Type} (hα : DecidableEq α) (hβ : DecidableEq β) : DecidableEq (α ⊕ β) := by
  letI := hα; letI := hβ; exact inferInstance

private abbrev ftForRange {Q : Type} (hQ : Fintype Q) : Fintype (RMForRangeQ Q) := by
  letI := hQ; exact inferInstance

private def deForRange {Q : Type} (hQ : DecidableEq Q) : DecidableEq (RMForRangeQ Q) := by
  letI := hQ; exact inferInstance

private def deRMMul : DecidableEq RMMulQ :=
  deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))

private def deRMDivMod : DecidableEq RMDivModQ :=
  have hBody : DecidableEq RMDivBodyQ :=
    deSum inferInstance (deSum inferInstance inferInstance)
  deSum inferInstance (deSum inferInstance (deSum inferInstance
    (deSum inferInstance (deSum inferInstance (deSum inferInstance hBody)))))

private abbrev ftBitShiftStep (bsF bsT : List Bool) : Fintype (RMBitShiftStepQ bsF bsT) :=
  ftSum inferInstance (ftSum inferInstance (ftSum inferInstance
    (ftSum inferInstance (ftSum (Fin.fintype _) (ftSum inferInstance (Fin.fintype _))))))

private def deBitShiftStep (bsF bsT : List Bool) : DecidableEq (RMBitShiftStepQ bsF bsT) :=
  deSum inferInstance (deSum deRMDivMod (deSum inferInstance
    (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))))

private abbrev ftV10 : Fintype RMEmitV10Q :=
  ftForRange (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance
    (ftSum inferInstance (ftSum (Fin.fintype _) (ftSum inferInstance (Fin.fintype _))))))))

private def deV10 : DecidableEq RMEmitV10Q :=
  deForRange (deSum deRMDivMod (deSum deRMMul (deSum inferInstance (deSum inferInstance
    (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))))))

private abbrev ftV11 : Fintype RMEmitV11Q :=
  have hEmit12 : Fintype RMV11Emit12Q :=
    ftSum inferInstance (ftSum inferInstance (ftSum (Fin.fintype _) (ftSum inferInstance (Fin.fintype _))))
  have hEmit : Fintype RMV11EmitQ :=
    ftSum inferInstance (ftSum (Fin.fintype _) (ftSum inferInstance hEmit12))
  ftForRange (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance
    (ftSum inferInstance (ftSum inferInstance hEmit)))))

private def deV11 : DecidableEq RMEmitV11Q :=
  have hCheck2 : DecidableEq RMV11Check2Q :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance))
  have hInc2 : DecidableEq RMV11Inc2Q :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance hCheck2))
  have hEmit12 : DecidableEq RMV11Emit12Q :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))
  have hEmit : DecidableEq RMV11EmitQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance hEmit12))
  deForRange (deSum deRMDivMod (deSum inferInstance (deSum inferInstance
    (deSum inferInstance (deSum hInc2 hEmit)))))

private abbrev ftV12 : Fintype RMEmitV12Q :=
  ftForRange (ftSum inferInstance
    (ftSum inferInstance (ftSum (Fin.fintype _) (Fin.fintype _))))

private def deV12 : DecidableEq RMEmitV12Q :=
  deForRange (deSum inferInstance
    (deSum inferInstance (deSum inferInstance inferInstance)))

private abbrev ftV13to14 : Fintype RMEmitV13to14Q :=
  ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftForRange (Fin.fintype _))))

private def deV13to14 : DecidableEq RMEmitV13to14Q :=
  deSum inferInstance (deSum inferInstance (deSum inferInstance (deForRange inferInstance)))

private abbrev ftV15a : Fintype RMEmitV15aQ :=
  have hNode : Fintype RMV15aNodeBodyQ :=
    ftSum (Fin.fintype _) (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (Fin.fintype _))))
  have hLvl : Fintype RMV15aLevelQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance hNode))
  have hStep : Fintype RMV15aStepQ :=
    ftSum hLvl (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance inferInstance)))
  ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance hStep))))

private def deV15a : DecidableEq RMEmitV15aQ :=
  have hNode : DecidableEq RMV15aNodeBodyQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))
  have hLvl : DecidableEq RMV15aLevelQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance hNode))
  have hStep : DecidableEq RMV15aStepQ :=
    deSum hLvl (deSum inferInstance (deSum deRMDivMod (deSum inferInstance inferInstance)))
  deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance hStep))))

private abbrev ftV15b : Fintype RMV15bQ :=
  have hPlain : Fintype RMV15bPlainQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (Fin.fintype _))))
  have hEmit4 : Fintype RMV15bSepEmit4Q :=
    ftSum inferInstance (ftSum
      (ftSum inferInstance (ftSum (Fin.fintype _) (ftSum inferInstance (Fin.fintype _))))
      (ftSum inferInstance (ftSum inferInstance (ftSum (Fin.fintype _) (ftSum inferInstance (Fin.fintype _))))))
  have hBit : Fintype RMV15bSepBitStepQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance hEmit4))))
  have hSepF : Fintype RMV15bSepFalseQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (Fin.fintype _))))
  have hSepT : Fintype RMV15bSepTrueQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance
      (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance hBit)))))
  have hSep : Fintype RMV15bSepQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance
      (ftSum inferInstance (ftSum hSepF (ftSum inferInstance hSepT))))))
  ftSum (Fin.fintype _) (ftSum hPlain hSep)

private def deV15b : DecidableEq RMV15bQ :=
  have hPlain : DecidableEq RMV15bPlainQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))
  have hEmit4 : DecidableEq RMV15bSepEmit4Q :=
    deSum inferInstance (deSum
      (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))
      (deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))))
  have hBit : DecidableEq RMV15bSepBitStepQ :=
    deSum inferInstance (deSum deRMDivMod (deSum inferInstance (deSum deRMDivMod (deSum inferInstance hEmit4))))
  have hSepF : DecidableEq RMV15bSepFalseQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))
  have hSepT : DecidableEq RMV15bSepTrueQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance
      (deSum inferInstance (deSum inferInstance (deSum inferInstance hBit)))))
  have hSep : DecidableEq RMV15bSepQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance
      (deSum inferInstance (deSum hSepF (deSum inferInstance hSepT))))))
  deSum inferInstance (deSum hPlain hSep)

private abbrev ftV17 : Fintype RMEmitV17Q :=
  have hExF : Fintype RMV17ExactFalseQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (Fin.fintype _))))
  have hExT : Fintype RMV17ExactTrueQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance
      (ftBitShiftStep _ _)))))
  have hEx : Fintype RMV17ExactQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance
      (ftSum hExF (ftSum inferInstance hExT)))))
  have hLe : Fintype RMV17LeQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance
      (ftBitShiftStep _ _)))))
  have hSep : Fintype RMV17SepQ :=
    ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (Fin.fintype _))))
  ftSum hEx (ftSum hLe hSep)

private def deV17 : DecidableEq RMEmitV17Q :=
  have hExF : DecidableEq RMV17ExactFalseQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))
  have hExT : DecidableEq RMV17ExactTrueQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance
      (deBitShiftStep _ _)))))
  have hEx : DecidableEq RMV17ExactQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance
      (deSum hExF (deSum inferInstance hExT)))))
  have hLe : DecidableEq RMV17LeQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance
      (deBitShiftStep _ _)))))
  have hSep : DecidableEq RMV17SepQ :=
    deSum inferInstance (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))
  deSum hEx (deSum hLe hSep)

private abbrev ftV18 : Fintype RMEmitV18Q :=
  ftSum
    (ftSum inferInstance (ftSum inferInstance (ftSum inferInstance
      (ftSum inferInstance (ftSum (Fin.fintype _) (ftSum inferInstance (Fin.fintype _)))))))
    (Fin.fintype _)

private def deV18 : DecidableEq RMEmitV18Q :=
  deSum
    (deSum inferInstance (deSum inferInstance (deSum inferInstance
      (deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance))))))
    inferInstance

/-- Explicit `Fintype` witness for `RMEmitBlocks10to18Q`. -/
abbrev fintypeRMEmitBlocks10to18Q : Fintype RMEmitBlocks10to18Q :=
  ftSum
    (ftSum (ftSum (ftSum ftV10 ftV11) (ftSum ftV12 ftV13to14))
      (ftSum (ftSum ftV15a ftV15b) (ftSum (ftSum (Fin.fintype _) ftV17) ftV18)))
    inferInstance

/-- Explicit `DecidableEq` witness for `RMEmitBlocks10to18Q`. -/
def decEqRMEmitBlocks10to18Q : DecidableEq RMEmitBlocks10to18Q :=
  deSum
    (deSum (deSum (deSum deV10 deV11) (deSum deV12 deV13to14))
      (deSum (deSum deV15a deV15b) (deSum (deSum inferInstance deV17) deV18)))
    inferInstance

end Branch8bTail
