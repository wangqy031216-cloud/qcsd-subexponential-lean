import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Computability.Encoding
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Core Definitions for Subexponential QCSD under Tensor Contraction

Self-contained Lean 4 definitions of:
1. Deterministic single-tape Turing machines (`QCSD_DetTM`, `QCSD_ComputesOnEncoded3`),
2. Binary Quasi-Cyclic Syndrome Decoding (`QCSD_Instance`, `QCSD_InstanceSep`, `QCSD_IsSol`,
   `QCSD_IsSolSep`, `QCSD_IsSolLe`, `QCSD_Correct`, `QCSD_CorrectSep`, `QCSD_CorrectLe`),
3. Input/output bit encodings (`QCSD_encodeInstance`, `QCSD_encodeInstanceSep`,
   `QCSD_decodeOutputN2`),
4. Boolean circuits and Boolean tensor networks (`QCSD_BoolCircuit`, `QCSD_BoolTensorNetwork2`,
   `QCSD_contraction2`, `QCSD_encodeNet2`),
5. The explicit tensor-contraction hypothesis (`QCSD_TCClass2`, `QCSD_TCAdmissible`, `QCSD_TC10`)
   and subexponential time / polynomial space bounds (`QCSD_timeBound`, `QCSD_spaceBound`).
-/

namespace QCSD.Defs

/-! ## 1. Deterministic Single-Tape Turing Machines -/

noncomputable def QCSD_log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

inductive QCSD_HeadDir where
  | left
  | right
  deriving DecidableEq, Repr

structure QCSD_DetTM where
  Q : Type
  [fintypeQ : Fintype Q]
  [decEqQ : DecidableEq Q]
  q0 : Q
  qhalt : Q
  step : Q → Bool → Q × Bool × QCSD_HeadDir

structure QCSD_Config (M : QCSD_DetTM) where
  state : M.Q
  tape : List Bool
  head : ℕ

def QCSD_tapeRead (t : List Bool) (i : ℕ) : Bool := t.getD i false

def QCSD_tapeWrite2 (t : List Bool) (i : ℕ) (b : Bool) : List Bool :=
  if i < t.length then t.set i b
  else (t ++ List.replicate (i + 1 - t.length) false).set i b

noncomputable def QCSD_stepConfig2 (M : QCSD_DetTM) (c : QCSD_Config M) :
    Option (QCSD_Config M) :=
  if @decide (c.state = M.qhalt) (M.decEqQ c.state M.qhalt) then none
  else
    let r := M.step c.state (QCSD_tapeRead c.tape c.head)
    some ⟨r.1, QCSD_tapeWrite2 c.tape c.head r.2.1,
      match r.2.2 with
      | QCSD_HeadDir.left => c.head - 1
      | QCSD_HeadDir.right => c.head + 1⟩

noncomputable def QCSD_configAt2 (M : QCSD_DetTM) (x : List Bool) : ℕ → QCSD_Config M
  | 0 => ⟨M.q0, x, 0⟩
  | n + 1 =>
    match QCSD_stepConfig2 M (QCSD_configAt2 M x n) with
    | none => QCSD_configAt2 M x n
    | some c => c

def QCSD_spaceUse2 {M : QCSD_DetTM} (c : QCSD_Config M) : ℕ :=
  Nat.max c.tape.length (c.head + 1)

def QCSD_ComputesOnEncoded3 {Input Output : Type*}
    (M : QCSD_DetTM)
    (inEnc : Input → List Bool) (outDec : Input → List Bool → Option Output)
    (domain : Input → Prop) (correct : Input → Output → Prop)
    (T Sp : Input → ℕ) : Prop :=
  ∀ x, domain x → ∃ k : ℕ, k ≤ T x ∧
    (QCSD_configAt2 M (inEnc x) k).state = M.qhalt ∧
    (∃ y, outDec x ((QCSD_configAt2 M (inEnc x) k).tape) = some y ∧ correct x y) ∧
    (∀ j ≤ k, QCSD_spaceUse2 (QCSD_configAt2 M (inEnc x) j) ≤ Sp x)

/-! ## 2. Binary Quasi-Cyclic Syndrome Decoding (Exact, Separated, Upper-Bound) -/

def QCSD_subIdx (n : ℕ) (a b : Fin n) : Fin n :=
  if hn : 0 < n then ⟨(a.val + n - b.val) % n, Nat.mod_lt _ hn⟩
  else ⟨a.val, a.isLt⟩

def QCSD_cycMul (n : ℕ) (a b : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun k => Finset.sum Finset.univ (fun i : Fin n => a i * b (QCSD_subIdx n k i))

def QCSD_wt {n : ℕ} (v : Fin n → ZMod 2) : ℕ := hammingNorm v

structure QCSD_Instance where
  n : ℕ
  h : Fin n → ZMod 2
  s : Fin n → ZMod 2
  t : ℕ

structure QCSD_InstanceSep where
  n : ℕ
  h : Fin n → ZMod 2
  s : Fin n → ZMod 2
  t₀ : ℕ
  t₁ : ℕ

def QCSD_IsSol (inp : QCSD_Instance) (e₀ e₁ : Fin inp.n → ZMod 2) : Prop :=
  (∀ k : Fin inp.n, e₀ k + QCSD_cycMul inp.n inp.h e₁ k = inp.s k) ∧
  QCSD_wt e₀ + QCSD_wt e₁ = inp.t

def QCSD_IsSolSep (inp : QCSD_InstanceSep) (e₀ e₁ : Fin inp.n → ZMod 2) : Prop :=
  (∀ k : Fin inp.n, e₀ k + QCSD_cycMul inp.n inp.h e₁ k = inp.s k) ∧
  QCSD_wt e₀ = inp.t₀ ∧ QCSD_wt e₁ = inp.t₁

def QCSD_IsSolLe (inp : QCSD_Instance) (e₀ e₁ : Fin inp.n → ZMod 2) : Prop :=
  (∀ k : Fin inp.n, e₀ k + QCSD_cycMul inp.n inp.h e₁ k = inp.s k) ∧
  QCSD_wt e₀ + QCSD_wt e₁ ≤ inp.t

noncomputable def QCSD_solutions (inp : QCSD_Instance) :
    Finset ((Fin inp.n → ZMod 2) × (Fin inp.n → ZMod 2)) := by
  classical
  exact Finset.univ.filter (fun p => QCSD_IsSol inp p.1 p.2)

noncomputable def QCSD_count (inp : QCSD_Instance) : ℕ := (QCSD_solutions inp).card

noncomputable def QCSD_solutionsSep (inp : QCSD_InstanceSep) :
    Finset ((Fin inp.n → ZMod 2) × (Fin inp.n → ZMod 2)) := by
  classical
  exact Finset.univ.filter (fun p => QCSD_IsSolSep inp p.1 p.2)

noncomputable def QCSD_countSep (inp : QCSD_InstanceSep) : ℕ := (QCSD_solutionsSep inp).card

noncomputable def QCSD_solutionsLe (inp : QCSD_Instance) :
    Finset ((Fin inp.n → ZMod 2) × (Fin inp.n → ZMod 2)) := by
  classical
  exact Finset.univ.filter (fun p => QCSD_IsSolLe inp p.1 p.2)

noncomputable def QCSD_countLe (inp : QCSD_Instance) : ℕ := (QCSD_solutionsLe inp).card

/-! ## 3. Instance/Witness Encodings, Output Decoding, and Complexity Bounds -/

def QCSD_natToUnary (m : ℕ) : List Bool := List.replicate m true ++ [false]

def QCSD_vecToBits {n : ℕ} (v : Fin n → ZMod 2) : List Bool :=
  (List.finRange n).map (fun i => decide (v i = (1 : ZMod 2)))

def QCSD_encodeInstance (inp : QCSD_Instance) : List Bool :=
  QCSD_natToUnary inp.n ++ QCSD_vecToBits inp.h ++ QCSD_vecToBits inp.s ++ QCSD_natToUnary inp.t

def QCSD_encodeInstanceSep (inp : QCSD_InstanceSep) : List Bool :=
  QCSD_natToUnary inp.n ++ QCSD_vecToBits inp.h ++ QCSD_vecToBits inp.s ++
    QCSD_natToUnary inp.t₀ ++ QCSD_natToUnary inp.t₁

def QCSD_decodeSolPair (n : ℕ) (w : List Bool) :
    Option ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
  if w.length = 2 * n then
    some (fun i : Fin n => if w.getD i.val false then (1 : ZMod 2) else 0,
          fun i : Fin n => if w.getD (n + i.val) false then (1 : ZMod 2) else 0)
  else none

def QCSD_bitsToNat (l : List Bool) : ℕ :=
  l.foldr (fun b acc => 2 * acc + (if b then 1 else 0)) 0

def QCSD_decodeOutputN2 (n : ℕ) (l : List Bool) : Option (ℕ × Option (List Bool)) :=
  if l.length < 2 * n + 1 then none
  else
    let c := QCSD_bitsToNat (l.take (2 * n))
    if l.getD (2 * n) false then
      let w := (l.drop (2 * n + 1)).take (2 * n)
      if w.length = 2 * n then some (c, some w) else none
    else some (c, none)

def QCSD_Correct (inp : QCSD_Instance) (o : ℕ × Option (List Bool)) : Prop :=
  o.1 = QCSD_count inp ∧
  (o.2 = none ↔ o.1 = 0) ∧
  (∀ w : List Bool, o.2 = some w →
    ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSol inp e₀ e₁)

def QCSD_CorrectSep (inp : QCSD_InstanceSep) (o : ℕ × Option (List Bool)) : Prop :=
  o.1 = QCSD_countSep inp ∧
  (o.2 = none ↔ o.1 = 0) ∧
  (∀ w : List Bool, o.2 = some w →
    ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSolSep inp e₀ e₁)

def QCSD_CorrectLe (inp : QCSD_Instance) (o : ℕ × Option (List Bool)) : Prop :=
  o.1 = QCSD_countLe inp ∧
  (o.2 = none ↔ o.1 = 0) ∧
  (∀ w : List Bool, o.2 = some w →
    ∃ e₀ e₁, QCSD_decodeSolPair inp.n w = some (e₀, e₁) ∧ QCSD_IsSolLe inp e₀ e₁)

noncomputable def QCSD_timeBound (C : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil ((2 : ℝ) ^ (C * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ))))

def QCSD_spaceBound (k : ℕ) (n : ℕ) : ℕ := n ^ k

/-! ## 4. Boolean Circuits and Boolean Tensor Networks -/

def QCSD_incidentList (m k : ℕ) (ends : Fin k → Fin m × Fin m) (v : Fin m) : List (Fin k) :=
  (Finset.univ.filter (fun e : Fin k => (ends e).1 = v ∨ (ends e).2 = v)).sort (· ≤ ·)

inductive QCSD_GateOp where
  | input
  | tt
  | ff
  | neg
  | conj
  | disj
  deriving DecidableEq

structure QCSD_Gate where
  op : QCSD_GateOp
  arg1 : ℕ
  arg2 : ℕ

structure QCSD_BoolCircuit where
  numInputs : ℕ
  gates : List QCSD_Gate

def QCSD_circuitSize (c : QCSD_BoolCircuit) : ℕ := c.numInputs + c.gates.length

def QCSD_gateAtOpt (l : List QCSD_Gate) (i : ℕ) : Option QCSD_Gate :=
  if h : i < l.length then some (l.get ⟨i, h⟩) else none

def QCSD_evalGates (inp : ℕ → Bool) : List QCSD_Gate → List Bool → List Bool
  | [], vals => vals
  | g :: gs, vals =>
    let v : Bool := match g.op with
      | QCSD_GateOp.input => inp g.arg1
      | QCSD_GateOp.tt => true
      | QCSD_GateOp.ff => false
      | QCSD_GateOp.neg => !(vals.getD g.arg1 false)
      | QCSD_GateOp.conj => vals.getD g.arg1 false && vals.getD g.arg2 false
      | QCSD_GateOp.disj => vals.getD g.arg1 false || vals.getD g.arg2 false
    QCSD_evalGates inp gs (vals ++ [v])

def QCSD_evalCircuit (c : QCSD_BoolCircuit) (inp : ℕ → Bool) : Bool :=
  let vals := QCSD_evalGates inp c.gates []
  vals.getD (c.gates.length - 1) false

def QCSD_circuitWF (c : QCSD_BoolCircuit) : Prop :=
  ∀ (i : ℕ) (g : QCSD_Gate), QCSD_gateAtOpt c.gates i = some g →
    match g.op with
    | QCSD_GateOp.input => g.arg1 < c.numInputs
    | QCSD_GateOp.tt => True
    | QCSD_GateOp.ff => True
    | QCSD_GateOp.neg => g.arg1 < i
    | QCSD_GateOp.conj => g.arg1 < i ∧ g.arg2 < i
    | QCSD_GateOp.disj => g.arg1 < i ∧ g.arg2 < i

structure QCSD_BoolTensorNetwork2 where
  m : ℕ
  k : ℕ
  ends : Fin k → Fin m × Fin m
  noLoop : ∀ e : Fin k, (ends e).1 ≠ (ends e).2
  pred : (v : Fin m) → QCSD_BoolCircuit
  arity : ∀ v : Fin m, (pred v).numInputs = (QCSD_incidentList m k ends v).length
  wf : ∀ v : Fin m, QCSD_circuitWF (pred v)

def QCSD_edgeCount2 (N : QCSD_BoolTensorNetwork2) : ℕ := N.k

def QCSD_deg2 (N : QCSD_BoolTensorNetwork2) (v : Fin N.m) : ℕ :=
  (QCSD_incidentList N.m N.k N.ends v).length

def QCSD_maxDeg2 (N : QCSD_BoolTensorNetwork2) : ℕ :=
  (Finset.univ : Finset (Fin N.m)).sup (fun v => QCSD_deg2 N v)

def QCSD_contraction2 (N : QCSD_BoolTensorNetwork2) : ℕ :=
  Finset.sum Finset.univ (fun x : Fin N.k → Bool =>
    Finset.prod Finset.univ (fun v : Fin N.m =>
      if QCSD_evalCircuit (N.pred v)
          (fun i => if h : i < (QCSD_incidentList N.m N.k N.ends v).length
            then x ((QCSD_incidentList N.m N.k N.ends v).get ⟨i, h⟩)
            else false) then 1 else 0))

def QCSD_gateTag : QCSD_GateOp → List Bool
  | QCSD_GateOp.input => [false, false, false]
  | QCSD_GateOp.tt => [false, false, true]
  | QCSD_GateOp.ff => [false, true, false]
  | QCSD_GateOp.neg => [false, true, true]
  | QCSD_GateOp.conj => [true, false, false]
  | QCSD_GateOp.disj => [true, false, true]

def QCSD_encodeGate (g : QCSD_Gate) : List Bool :=
  QCSD_gateTag g.op ++
    (match g.op with
     | QCSD_GateOp.input => QCSD_natToUnary g.arg1
     | QCSD_GateOp.tt => []
     | QCSD_GateOp.ff => []
     | QCSD_GateOp.neg => QCSD_natToUnary g.arg1
     | QCSD_GateOp.conj => QCSD_natToUnary g.arg1 ++ QCSD_natToUnary g.arg2
     | QCSD_GateOp.disj => QCSD_natToUnary g.arg1 ++ QCSD_natToUnary g.arg2)

def QCSD_encodeCircuit (c : QCSD_BoolCircuit) : List Bool :=
  QCSD_natToUnary c.numInputs ++
  QCSD_natToUnary c.gates.length ++
  c.gates.flatMap QCSD_encodeGate

def QCSD_encodeNet2 (N : QCSD_BoolTensorNetwork2) : List Bool :=
  QCSD_natToUnary N.m ++
  QCSD_natToUnary N.k ++
  (List.finRange N.k).flatMap (fun e =>
    QCSD_natToUnary (N.ends e).1.val ++ QCSD_natToUnary (N.ends e).2.val) ++
  (List.finRange N.m).flatMap (fun v => QCSD_encodeCircuit (N.pred v))

def QCSD_netCost2 (N : QCSD_BoolTensorNetwork2) : ℕ :=
  (QCSD_encodeNet2 N).length

/-! ## 5. Exact Tensor Contraction Hypothesis (TC) -/

def QCSD_TCClass2 (CΔ : ℝ) (km Km kcost Kcost kpred Kpred : ℕ)
    (N : QCSD_BoolTensorNetwork2) : Prop :=
  2 ≤ QCSD_edgeCount2 N ∧
  (QCSD_maxDeg2 N : ℝ) ≤ CΔ * (QCSD_edgeCount2 N : ℝ) ^ ((9 : ℝ) / 10) ∧
  N.m ≤ Km * (QCSD_edgeCount2 N) ^ km ∧
  QCSD_netCost2 N ≤ Kcost * (QCSD_edgeCount2 N) ^ kcost ∧
  (∀ v : Fin N.m, QCSD_circuitSize (N.pred v) ≤ Kpred * (QCSD_edgeCount2 N) ^ kpred)

def QCSD_TCAdmissible (CΔ : ℝ) (km Km kcost Kcost kpred Kpred : ℕ) : Prop :=
  1 ≤ CΔ ∧ 1 ≤ Km ∧ 1 ≤ Kcost ∧ 1 ≤ Kpred

def QCSD_TC10 : Prop :=
  ∀ (CΔ : ℝ) (km Km kcost Kcost kpred Kpred : ℕ),
    QCSD_TCAdmissible CΔ km Km kcost Kcost kpred Kpred →
      ∃ (A : QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
        1 ≤ Ct ∧ 1 ≤ ksp ∧
          QCSD_ComputesOnEncoded3 A
            QCSD_encodeNet2
            (fun (_ : QCSD_BoolTensorNetwork2) (l : List Bool) => some (QCSD_bitsToNat l))
            (QCSD_TCClass2 CΔ km Km kcost Kcost kpred Kpred)
            (fun (N : QCSD_BoolTensorNetwork2) (y : ℕ) => y = QCSD_contraction2 N)
            (fun (N : QCSD_BoolTensorNetwork2) => QCSD_timeBound Ct (QCSD_edgeCount2 N))
            (fun (N : QCSD_BoolTensorNetwork2) => QCSD_edgeCount2 N ^ ksp)

end QCSD.Defs
