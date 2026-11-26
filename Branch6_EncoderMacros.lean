import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.TakeDrop
import QCSD.Defs
import Branch5_PadAndSep

namespace Branch6Encoder

open QCSD.Defs
open Branch5PadAndSep

/-!
## Section 1: Zero-`inductive` Concrete Register-Machine Execution Model (`RMProg`)

All definitions use exclusively `def`, `abbrev`, `lemma`, and `theorem` over
`Fin`, `Bool`, `ℕ`, `×`, `⊕`, `Option`, `List`, `ZMod 2` (zero custom
`structure`, `inductive`, or `class` declarations).
-/

/-- Register file with `R` natural-number registers. -/
abbrev RegState (R : ℕ) : Type := Fin R → ℕ

/-- Functional register update. -/
def regUpd {R : ℕ} (reg : RegState R) (r : Fin R) (v : ℕ) : RegState R :=
  fun i => if i = r then v else reg i

@[simp] lemma regUpd_self {R : ℕ} (reg : RegState R) (r : Fin R) (v : ℕ) :
    regUpd reg r v r = v := by
  simp [regUpd]

lemma regUpd_ne {R : ℕ} (reg : RegState R) {r i : Fin R} (h : i ≠ r) (v : ℕ) :
    regUpd reg r v i = reg i := by
  simp [regUpd, h]

@[simp] lemma regUpd_idem {R : ℕ} (reg : RegState R) (r : Fin R) (v₁ v₂ : ℕ) :
    regUpd (regUpd reg r v₁) r v₂ = regUpd reg r v₂ := by
  funext i
  by_cases h : i = r <;> simp [regUpd, h]

@[simp] lemma regUpd_eq_self {R : ℕ} (reg : RegState R) (r : Fin R) :
    regUpd reg r (reg r) = reg := by
  funext i
  by_cases h : i = r <;> simp [regUpd, h]

lemma regUpd_le {R : ℕ} {reg : RegState R} {V : ℕ}
    (hreg : ∀ i, reg i ≤ V) (r : Fin R) {v : ℕ} (hv : v ≤ V) :
    ∀ i, regUpd reg r v i ≤ V := by
  intro i
  by_cases h : i = r
  · subst h; simpa using hv
  · rw [regUpd_ne reg h]; exact hreg i

/-- Concrete 6-primitive register-machine instruction encoded over `⊕` and `×`. -/
abbrev RMOp (R : ℕ) (Q : Type) : Type :=
  (Fin R × Q) ⊕
  ((Fin R × Q) ⊕
  ((Fin R × Q × Q) ⊕
  ((Fin R × Fin R × Q) ⊕
  ((Fin R × Q × Q) ⊕
  (Bool × Q)))))

def opZero {R : ℕ} {Q : Type} (r : Fin R) (next : Q) : RMOp R Q :=
  Sum.inl (r, next)

def opInc {R : ℕ} {Q : Type} (r : Fin R) (next : Q) : RMOp R Q :=
  Sum.inr (Sum.inl (r, next))

def opDecJz {R : ℕ} {Q : Type} (r : Fin R) (nextZero nextNonzero : Q) : RMOp R Q :=
  Sum.inr (Sum.inr (Sum.inl (r, nextZero, nextNonzero)))

def opCopy {R : ℕ} {Q : Type} (dst src : Fin R) (next : Q) : RMOp R Q :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl (dst, src, next))))

def opReadIn {R : ℕ} {Q : Type} (rIdx : Fin R) (nextFalse nextTrue : Q) : RMOp R Q :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (rIdx, nextFalse, nextTrue)))))

def opEmit {R : ℕ} {Q : Type} (b : Bool) (next : Q) : RMOp R Q :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (b, next)))))

/-- A register-machine program is a partial instruction table `Q → Option (RMOp R Q)`. -/
abbrev RMProg (R : ℕ) (Q : Type) : Type := Q → Option (RMOp R Q)

/-- Map target states in an `RMOp`. -/
def rmOpMapQ {R : ℕ} {Q₁ Q₂ : Type} (f : Q₁ → Q₂) : RMOp R Q₁ → RMOp R Q₂
  | Sum.inl (r, q) => opZero r (f q)
  | Sum.inr (Sum.inl (r, q)) => opInc r (f q)
  | Sum.inr (Sum.inr (Sum.inl (r, qz, qnz))) => opDecJz r (f qz) (f qnz)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (d, s, q)))) => opCopy d s (f q)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (r, qf, qt))))) => opReadIn r (f qf) (f qt)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (b, q))))) => opEmit b (f q)

/-- Map register indices in an `RMOp`. -/
def rmOpMapR {R₁ R₂ : ℕ} {Q : Type} (g : Fin R₁ → Fin R₂) : RMOp R₁ Q → RMOp R₂ Q
  | Sum.inl (r, q) => opZero (g r) q
  | Sum.inr (Sum.inl (r, q)) => opInc (g r) q
  | Sum.inr (Sum.inr (Sum.inl (r, qz, qnz))) => opDecJz (g r) qz qnz
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (d, s, q)))) => opCopy (g d) (g s) q
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (r, qf, qt))))) => opReadIn (g r) qf qt
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (b, q))))) => opEmit b q

/-- Single-step register-machine transition, returning `(nextState, nextRegs, newlyEmittedBits)`. -/
def rmStep {R : ℕ} {Q : Type} (M : RMProg R Q) (inp : List Bool)
    (q : Q) (reg : RegState R) : Option (Q × RegState R × List Bool) :=
  match M q with
  | none => none
  | some (Sum.inl (r, next)) => some (next, regUpd reg r 0, [])
  | some (Sum.inr (Sum.inl (r, next))) => some (next, regUpd reg r (reg r + 1), [])
  | some (Sum.inr (Sum.inr (Sum.inl (r, qz, qnz)))) =>
      if reg r = 0 then some (qz, reg, [])
      else some (qnz, regUpd reg r (reg r - 1), [])
  | some (Sum.inr (Sum.inr (Sum.inr (Sum.inl (dst, src, next))))) =>
      some (next, regUpd reg dst (reg src), [])
  | some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (rIdx, qf, qt)))))) =>
      if inp.getD (reg rIdx) false then some (qt, reg, [])
      else some (qf, reg, [])
  | some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (b, next)))))) =>
      some (next, reg, [b])

lemma rmStep_mapQ {R : ℕ} {Q₁ Q₂ : Type} (M₁ : RMProg R Q₁) (M₂ : RMProg R Q₂)
    (f : Q₁ → Q₂) (inp : List Bool) {q₁ : Q₁} {q₂ : Q₂} {reg : RegState R}
    {q₁' : Q₁} {reg' : RegState R} {b : List Bool}
    (hmatch : M₂ q₂ = (M₁ q₁).map (rmOpMapQ f))
    (hstep : rmStep M₁ inp q₁ reg = some (q₁', reg', b)) :
    rmStep M₂ inp q₂ reg = some (f q₁', reg', b) := by
  unfold rmStep at hstep ⊢
  rw [hmatch]
  cases hM : M₁ q₁ with
  | none => rw [hM] at hstep; cases hstep
  | some op =>
    rw [hM] at hstep
    rcases op with ⟨r, next⟩ | ⟨r, next⟩ | ⟨r, qz, qnz⟩ | ⟨d, s, next⟩ | ⟨r, qf, qt⟩ | ⟨bit, next⟩
    · simp only [Option.map_some, rmOpMapQ, opZero] at hstep ⊢; cases hstep; rfl
    · simp only [Option.map_some, rmOpMapQ, opInc] at hstep ⊢; cases hstep; rfl
    · simp only [Option.map_some, rmOpMapQ, opDecJz] at hstep ⊢
      split_ifs at hstep ⊢ <;> cases hstep <;> rfl
    · simp only [Option.map_some, rmOpMapQ, opCopy] at hstep ⊢; cases hstep; rfl
    · simp only [Option.map_some, rmOpMapQ, opReadIn] at hstep ⊢
      split_ifs at hstep ⊢ <;> cases hstep <;> rfl
    · simp only [Option.map_some, rmOpMapQ, opEmit] at hstep ⊢; cases hstep; rfl

/-- Multi-step register-machine iteration collecting emitted output bits. -/
def rmIter {R : ℕ} {Q : Type} (M : RMProg R Q) (inp : List Bool) :
    ℕ → Q → RegState R → Option (Q × RegState R × List Bool)
  | 0, q, reg => some (q, reg, [])
  | k + 1, q, reg =>
      match rmStep M inp q reg with
      | none => none
      | some (q', reg', b) =>
          match rmIter M inp k q' reg' with
          | none => none
          | some (q'', reg'', out') => some (q'', reg'', b ++ out')

lemma rmIter_add {R : ℕ} {Q : Type} (M : RMProg R Q) (inp : List Bool) :
    ∀ (a b : ℕ) (q₀ : Q) (reg₀ : RegState R)
      (q₁ : Q) (reg₁ : RegState R) (out₁ : List Bool)
      (q₂ : Q) (reg₂ : RegState R) (out₂ : List Bool),
      rmIter M inp a q₀ reg₀ = some (q₁, reg₁, out₁) →
      rmIter M inp b q₁ reg₁ = some (q₂, reg₂, out₂) →
      rmIter M inp (a + b) q₀ reg₀ = some (q₂, reg₂, out₁ ++ out₂)
  | 0, b, q₀, reg₀, q₁, reg₁, out₁, q₂, reg₂, out₂, ha, hb => by
    simp only [rmIter] at ha
    cases ha
    simpa [Nat.zero_add] using hb
  | a + 1, b, q₀, reg₀, q₁, reg₁, out₁, q₂, reg₂, out₂, ha, hb => by
    rw [Nat.succ_add]
    simp only [rmIter] at ha ⊢
    cases hs : rmStep M inp q₀ reg₀ with
    | none => rw [hs] at ha; cases ha
    | some val =>
      rcases val with ⟨q', reg', bit⟩
      simp only [hs] at ha
      cases hr : rmIter M inp a q' reg' with
      | none => simp only [hr] at ha; cases ha
      | some val2 =>
        rcases val2 with ⟨q'', reg'', out'⟩
        simp only [hr] at ha
        cases ha
        have ih := rmIter_add M inp a b q' reg' q₁ reg₁ out' q₂ reg₂ out₂ hr hb
        simp only [ih, List.append_assoc]

lemma rmIter_add_split {R : ℕ} {Q : Type} (M : RMProg R Q) (inp : List Bool) :
    ∀ (a b : ℕ) (q₀ : Q) (reg₀ : RegState R) (q₂ : Q) (reg₂ : RegState R) (out : List Bool),
      rmIter M inp (a + b) q₀ reg₀ = some (q₂, reg₂, out) →
      ∃ q₁ reg₁ out₁ out₂,
        rmIter M inp a q₀ reg₀ = some (q₁, reg₁, out₁) ∧
        rmIter M inp b q₁ reg₁ = some (q₂, reg₂, out₂) ∧
        out = out₁ ++ out₂
  | 0, b, q₀, reg₀, q₂, reg₂, out, h => by
    exact ⟨q₀, reg₀, [], out, rfl, by simpa using h, rfl⟩
  | a + 1, b, q₀, reg₀, q₂, reg₂, out, h => by
    rw [Nat.succ_add] at h
    simp only [rmIter] at h
    cases hs : rmStep M inp q₀ reg₀ with
    | none => rw [hs] at h; cases h
    | some val =>
      rcases val with ⟨q', reg', bit⟩
      simp only [hs] at h
      cases hr : rmIter M inp (a + b) q' reg' with
      | none => simp only [hr] at h; cases h
      | some val2 =>
        rcases val2 with ⟨q'', reg'', out'⟩
        simp only [hr] at h
        cases h
        obtain ⟨q₁, reg₁, out₁, out₂, h1, h2, hout⟩ :=
          rmIter_add_split M inp a b q' reg' q₂ reg₂ out' hr
        refine ⟨q₁, reg₁, bit ++ out₁, out₂, ?_, h2, ?_⟩
        · simp [rmIter, hs, h1]
        · rw [hout, List.append_assoc]

lemma rmIter_le_some {R : ℕ} {Q : Type} {M : RMProg R Q} {inp : List Bool}
    {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {out : List Bool} {j k : ℕ}
    (hjk : j ≤ k) (hk : rmIter M inp k q₀ reg₀ = some (q₁, reg₁, out)) :
    ∃ q' reg' out', rmIter M inp j q₀ reg₀ = some (q', reg', out') := by
  have heq : k = j + (k - j) := by omega
  rw [heq] at hk
  obtain ⟨q', reg', out₁, _, hj, _, _⟩ := rmIter_add_split M inp j (k - j) q₀ reg₀ q₁ reg₁ out hk
  exact ⟨q', reg', out₁, hj⟩

/-- Halting execution predicate tracking BOTH step bound `steps` AND universal register
value bound `∀ r, reg' r ≤ Vmax` at every intermediate configuration. -/
def RMExec {R : ℕ} {Q : Type} (M : RMProg R Q) (Vmax : ℕ) (inp : List Bool)
    (q₀ : Q) (reg₀ : RegState R) (q₁ : Q) (reg₁ : RegState R)
    (emitted : List Bool) (steps : ℕ) : Prop :=
  ∃ k ≤ steps,
    rmIter M inp k q₀ reg₀ = some (q₁, reg₁, emitted) ∧
    M q₁ = none ∧
    (∀ j ≤ k, ∀ q' reg' out',
      rmIter M inp j q₀ reg₀ = some (q', reg', out') →
      ∀ r, reg' r ≤ Vmax)

lemma RMExec.weaken {R : ℕ} {Q : Type} {M : RMProg R Q} {V₁ V₂ : ℕ} {inp : List Bool}
    {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {out : List Bool} {T₁ T₂ : ℕ}
    (h : RMExec M V₁ inp q₀ reg₀ q₁ reg₁ out T₁)
    (hV : V₁ ≤ V₂) (hT : T₁ ≤ T₂) :
    RMExec M V₂ inp q₀ reg₀ q₁ reg₁ out T₂ := by
  rcases h with ⟨k, hk, hiter, hhalt, hbnd⟩
  exact ⟨k, le_trans hk hT, hiter, hhalt,
    fun j hj q' reg' out' hji r => le_trans (hbnd j hj q' reg' out' hji r) hV⟩

lemma RMExec.reg₀_le {R : ℕ} {Q : Type} {M : RMProg R Q} {V : ℕ} {inp : List Bool}
    {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (h : RMExec M V inp q₀ reg₀ q₁ reg₁ out T) : ∀ r, reg₀ r ≤ V := by
  rcases h with ⟨k, _, _, _, hbnd⟩
  exact hbnd 0 (Nat.zero_le k) q₀ reg₀ [] rfl

lemma RMExec.reg₁_le {R : ℕ} {Q : Type} {M : RMProg R Q} {V : ℕ} {inp : List Bool}
    {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (h : RMExec M V inp q₀ reg₀ q₁ reg₁ out T) : ∀ r, reg₁ r ≤ V := by
  rcases h with ⟨k, _, hiter, _, hbnd⟩
  exact hbnd k (Nat.le_refl k) q₁ reg₁ out hiter

lemma RMExec.halt {R : ℕ} {Q : Type} {M : RMProg R Q} {V : ℕ} {inp : List Bool}
    {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (h : RMExec M V inp q₀ reg₀ q₁ reg₁ out T) : M q₁ = none := by
  rcases h with ⟨_, _, _, hhalt, _⟩
  exact hhalt

/-! ### Atomic Primitive Programs -/

def rmNop {R : ℕ} : RMProg R Unit := fun _ => none

theorem rmNop_spec {R : ℕ} (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ r, reg r ≤ V) :
    RMExec (rmNop (R := R)) V inp () reg () reg [] 0 := by
  refine ⟨0, Nat.le_refl 0, rfl, rfl, ?_⟩
  intro j hj q' reg' out' hji
  obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
  cases hji
  exact hreg

/-- Helper for 1-step atomic programs over `Bool` (`false` = active, `true` = halt). -/
lemma rmExec_one_step {R : ℕ} {Q : Type} {M : RMProg R Q} {V : ℕ} {inp : List Bool}
    {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {b : List Bool}
    (hstep : rmStep M inp q₀ reg₀ = some (q₁, reg₁, b))
    (hhalt : M q₁ = none)
    (h0 : ∀ r, reg₀ r ≤ V) (h1 : ∀ r, reg₁ r ≤ V) :
    RMExec M V inp q₀ reg₀ q₁ reg₁ b 1 := by
  refine ⟨1, Nat.le_refl 1, ?_, hhalt, ?_⟩
  · simp [rmIter, hstep]
  · intro j hj q' reg' out' hji
    match j with
    | 0 => cases hji; exact h0
    | 1 => simp only [rmIter, hstep] at hji; cases hji; exact h1
    | n + 2 => omega

def rmZero {R : ℕ} (r : Fin R) : RMProg R Bool
  | false => some (opZero r true)
  | true => none

theorem rmZero_spec {R : ℕ} (r : Fin R) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmZero r) V inp false reg true (regUpd reg r 0) [] 1 :=
  rmExec_one_step (by rfl) rfl hreg (regUpd_le hreg r (Nat.zero_le V))

def rmInc {R : ℕ} (r : Fin R) : RMProg R Bool
  | false => some (opInc r true)
  | true => none

theorem rmInc_spec {R : ℕ} (r : Fin R) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) (hinc : reg r + 1 ≤ V) :
    RMExec (rmInc r) V inp false reg true (regUpd reg r (reg r + 1)) [] 1 :=
  rmExec_one_step (by rfl) rfl hreg (regUpd_le hreg r hinc)

def rmCopy {R : ℕ} (dst src : Fin R) : RMProg R Bool
  | false => some (opCopy dst src true)
  | true => none

theorem rmCopy_spec {R : ℕ} (dst src : Fin R) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmCopy dst src) V inp false reg true (regUpd reg dst (reg src)) [] 1 :=
  rmExec_one_step (by rfl) rfl hreg (regUpd_le hreg dst (hreg src))

def rmEmit {R : ℕ} (b : Bool) : RMProg R Bool
  | false => some (opEmit b true)
  | true => none

theorem rmEmit_spec {R : ℕ} (b : Bool) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmEmit b) V inp false reg true reg [b] 1 :=
  rmExec_one_step (by rfl) rfl hreg hreg

def rmDecJzProg {R : ℕ} (r : Fin R) : RMProg R (Option Bool)
  | none => some (opDecJz r (some true) (some false))
  | some _ => none

theorem rmDecJzProg_spec {R : ℕ} (r : Fin R) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmDecJzProg r) V inp none reg
      (some (decide (reg r = 0)))
      (if reg r = 0 then reg else regUpd reg r (reg r - 1)) [] 1 := by
  by_cases h0 : reg r = 0
  · simp only [h0, decide_true, ↓reduceIte]
    exact rmExec_one_step (by simp [rmStep, rmDecJzProg, opDecJz, h0]) rfl hreg hreg
  · simp only [h0, decide_false, ↓reduceIte]
    exact rmExec_one_step (by simp [rmStep, rmDecJzProg, opDecJz, h0]) rfl hreg
      (regUpd_le hreg r (le_trans (Nat.sub_le _ _) (hreg r)))

def rmReadInProg {R : ℕ} (rIdx : Fin R) : RMProg R (Option Bool)
  | none => some (opReadIn rIdx (some false) (some true))
  | some _ => none

theorem rmReadInProg_spec {R : ℕ} (rIdx : Fin R) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmReadInProg rIdx) V inp none reg
      (some (inp.getD (reg rIdx) false)) reg [] 1 := by
  cases hb : inp.getD (reg rIdx) false
  · exact rmExec_one_step (by simp only [rmStep, rmReadInProg, opReadIn]; rw [hb]; rfl) rfl hreg hreg
  · exact rmExec_one_step (by simp only [rmStep, rmReadInProg, opReadIn]; rw [hb]; rfl) rfl hreg hreg

/-! ### Compositional Combinators (`rmSeq`, `rmBranch`, `rmIfZero`, `rmIfReadIn`, `rmLoop`, `rmWhile`, `rmLift`) -/

/-- Zero-overhead target redirector: active states stay in `Sum.inl`, halting states jump to `Sum.inr (f q)`. -/
def rmRedirect {R : ℕ} {Q₁ Q₂ : Type} (M₁ : RMProg R Q₁) (f : Q₁ → Q₂) (q₁ : Q₁) : Q₁ ⊕ Q₂ :=
  match M₁ q₁ with
  | some _ => Sum.inl q₁
  | none => Sum.inr (f q₁)

/-- Zero-overhead sequential composition `M₁ ; M₂` with exit-state routing `f : Q₁ → Q₂`. -/
def rmSeq {R : ℕ} {Q₁ Q₂ : Type} (M₁ : RMProg R Q₁) (M₂ : RMProg R Q₂) (f : Q₁ → Q₂) :
    RMProg R (Q₁ ⊕ Q₂)
  | Sum.inl q₁ => (M₁ q₁).map (rmOpMapQ (rmRedirect M₁ f))
  | Sum.inr q₂ => (M₂ q₂).map (rmOpMapQ Sum.inr)

def rmSeqEntry {R : ℕ} {Q₁ Q₂ : Type} (M₁ : RMProg R Q₁) (f : Q₁ → Q₂) (q₀ : Q₁) : Q₁ ⊕ Q₂ :=
  rmRedirect M₁ f q₀

lemma rmIter_seq_left {R : ℕ} {Q₁ Q₂ : Type} (M₁ : RMProg R Q₁) (M₂ : RMProg R Q₂)
    (f : Q₁ → Q₂) (inp : List Bool) :
    ∀ k q₀ reg₀ q₁ reg₁ out,
      rmIter M₁ inp k q₀ reg₀ = some (q₁, reg₁, out) →
      rmIter (rmSeq M₁ M₂ f) inp k (rmRedirect M₁ f q₀) reg₀ =
        some (rmRedirect M₁ f q₁, reg₁, out)
  | 0, q₀, reg₀, q₁, reg₁, out, h => by
    cases h; rfl
  | k + 1, q₀, reg₀, q₁, reg₁, out, h => by
    simp only [rmIter] at h ⊢
    cases hs : rmStep M₁ inp q₀ reg₀ with
    | none => rw [hs] at h; cases h
    | some val =>
      rcases val with ⟨q', reg', bit⟩
      simp only [hs] at h
      cases hr : rmIter M₁ inp k q' reg' with
      | none => simp only [hr] at h; cases h
      | some val2 =>
        rcases val2 with ⟨q'', reg'', out'⟩
        simp only [hr] at h
        cases h
        have hM₁_ne : ∃ op, M₁ q₀ = some op := by
          unfold rmStep at hs
          cases hM : M₁ q₀ with
          | none => rw [hM] at hs; cases hs
          | some op => exact ⟨op, rfl⟩
        rcases hM₁_ne with ⟨op, hop⟩
        have hred : rmRedirect M₁ f q₀ = Sum.inl q₀ := by simp [rmRedirect, hop]
        have hstep' : rmStep (rmSeq M₁ M₂ f) inp (rmRedirect M₁ f q₀) reg₀ =
            some (rmRedirect M₁ f q', reg', bit) := by
          rw [hred]
          exact rmStep_mapQ M₁ (rmSeq M₁ M₂ f) (rmRedirect M₁ f) inp rfl hs
        simp only [hstep', rmIter_seq_left M₁ M₂ f inp k q' reg' q₁ reg₁ out' hr]

lemma rmIter_seq_right {R : ℕ} {Q₁ Q₂ : Type} (M₁ : RMProg R Q₁) (M₂ : RMProg R Q₂)
    (f : Q₁ → Q₂) (inp : List Bool) :
    ∀ k q₀ reg₀ q₁ reg₁ out,
      rmIter M₂ inp k q₀ reg₀ = some (q₁, reg₁, out) →
      rmIter (rmSeq M₁ M₂ f) inp k (Sum.inr q₀) reg₀ = some (Sum.inr q₁, reg₁, out)
  | 0, q₀, reg₀, q₁, reg₁, out, h => by
    cases h; rfl
  | k + 1, q₀, reg₀, q₁, reg₁, out, h => by
    simp only [rmIter] at h ⊢
    cases hs : rmStep M₂ inp q₀ reg₀ with
    | none => rw [hs] at h; cases h
    | some val =>
      rcases val with ⟨q', reg', bit⟩
      simp only [hs] at h
      cases hr : rmIter M₂ inp k q' reg' with
      | none => simp only [hr] at h; cases h
      | some val2 =>
        rcases val2 with ⟨q'', reg'', out'⟩
        simp only [hr] at h
        cases h
        have hstep' : rmStep (rmSeq M₁ M₂ f) inp (Sum.inr q₀) reg₀ =
            some (Sum.inr q', reg', bit) :=
          rmStep_mapQ M₂ (rmSeq M₁ M₂ f) Sum.inr inp rfl hs
        simp only [hstep', rmIter_seq_right M₁ M₂ f inp k q' reg' q₁ reg₁ out' hr]

theorem rmSeq_spec {R : ℕ} {Q₁ Q₂ : Type}
    {M₁ : RMProg R Q₁} {M₂ : RMProg R Q₂} {f : Q₁ → Q₂}
    {V₁ V₂ : ℕ} {inp : List Bool}
    {q₀ q₁ : Q₁} {q₂ : Q₂} {reg₀ reg₁ reg₂ : RegState R}
    {out₁ out₂ : List Bool} {T₁ T₂ : ℕ}
    (h₁ : RMExec M₁ V₁ inp q₀ reg₀ q₁ reg₁ out₁ T₁)
    (h₂ : RMExec M₂ V₂ inp (f q₁) reg₁ q₂ reg₂ out₂ T₂) :
    RMExec (rmSeq M₁ M₂ f) (max V₁ V₂) inp (rmSeqEntry M₁ f q₀) reg₀
      (Sum.inr q₂) reg₂ (out₁ ++ out₂) (T₁ + T₂) := by
  rcases h₁ with ⟨k₁, hk₁, hiter₁, hhalt₁, hbnd₁⟩
  rcases h₂ with ⟨k₂, hk₂, hiter₂, hhalt₂, hbnd₂⟩
  have hred₁ : rmRedirect M₁ f q₁ = Sum.inr (f q₁) := by simp [rmRedirect, hhalt₁]
  have hl₁ : rmIter (rmSeq M₁ M₂ f) inp k₁ (rmRedirect M₁ f q₀) reg₀ =
      some (Sum.inr (f q₁), reg₁, out₁) := by
    rw [← hred₁]
    exact rmIter_seq_left M₁ M₂ f inp k₁ q₀ reg₀ q₁ reg₁ out₁ hiter₁
  have hl₂ : rmIter (rmSeq M₁ M₂ f) inp k₂ (Sum.inr (f q₁)) reg₁ =
      some (Sum.inr q₂, reg₂, out₂) :=
    rmIter_seq_right M₁ M₂ f inp k₂ (f q₁) reg₁ q₂ reg₂ out₂ hiter₂
  refine ⟨k₁ + k₂, Nat.add_le_add hk₁ hk₂, ?_, ?_, ?_⟩
  · exact rmIter_add (rmSeq M₁ M₂ f) inp k₁ k₂ (rmRedirect M₁ f q₀) reg₀
      (Sum.inr (f q₁)) reg₁ out₁ (Sum.inr q₂) reg₂ out₂ hl₁ hl₂
  · simp [rmSeq, hhalt₂]
  · intro j hj q' reg' out' hji r
    by_cases hj1 : j ≤ k₁
    · obtain ⟨qj, regj, outj, hsub⟩ := rmIter_le_some hj1 hiter₁
      have hseqj := rmIter_seq_left M₁ M₂ f inp j q₀ reg₀ qj regj outj hsub
      rw [rmSeqEntry, hseqj] at hji
      cases hji
      exact le_trans (hbnd₁ j hj1 qj reg' out' hsub r) (le_max_left V₁ V₂)
    · have hj2 : j - k₁ ≤ k₂ := by omega
      obtain ⟨qj, regj, outj, hsub⟩ := rmIter_le_some hj2 hiter₂
      have hseqj := rmIter_seq_right M₁ M₂ f inp (j - k₁) (f q₁) reg₁ qj regj outj hsub
      have hcomb := rmIter_add (rmSeq M₁ M₂ f) inp k₁ (j - k₁) (rmRedirect M₁ f q₀) reg₀
        (Sum.inr (f q₁)) reg₁ out₁ (Sum.inr qj) regj outj hl₁ hseqj
      have hjeq : k₁ + (j - k₁) = j := by omega
      rw [hjeq] at hcomb
      rw [rmSeqEntry, hcomb] at hji
      cases hji
      exact le_trans (hbnd₂ (j - k₁) hj2 qj reg' outj hsub r) (le_max_right V₁ V₂)

/-- Convenience sequential composition ignoring exit state of `M₁`. -/
def rmChain {R : ℕ} {Q₁ Q₂ : Type} (M₁ : RMProg R Q₁) (M₂ : RMProg R Q₂) (q₂₀ : Q₂) :
    RMProg R (Q₁ ⊕ Q₂) :=
  rmSeq M₁ M₂ (fun _ => q₂₀)

def rmChainEntry {R : ℕ} {Q₁ Q₂ : Type} (M₁ : RMProg R Q₁) (q₁₀ : Q₁) (q₂₀ : Q₂) : Q₁ ⊕ Q₂ :=
  rmSeqEntry M₁ (fun _ => q₂₀) q₁₀

theorem rmChain_spec {R : ℕ} {Q₁ Q₂ : Type}
    {M₁ : RMProg R Q₁} {M₂ : RMProg R Q₂} {V₁ V₂ : ℕ} {inp : List Bool}
    {q₁₀ q₁₁ : Q₁} {q₂₀ q₂₁ : Q₂} {reg₀ reg₁ reg₂ : RegState R}
    {out₁ out₂ : List Bool} {T₁ T₂ : ℕ}
    (h₁ : RMExec M₁ V₁ inp q₁₀ reg₀ q₁₁ reg₁ out₁ T₁)
    (h₂ : RMExec M₂ V₂ inp q₂₀ reg₁ q₂₁ reg₂ out₂ T₂) :
    RMExec (rmChain M₁ M₂ q₂₀) (max V₁ V₂) inp (rmChainEntry M₁ q₁₀ q₂₀) reg₀
      (Sum.inr q₂₁) reg₂ (out₁ ++ out₂) (T₁ + T₂) :=
  rmSeq_spec h₁ h₂

/-- Disjoint sum of two register-machine programs. -/
def rmBranch {R : ℕ} {Q₁ Q₂ : Type} (M₁ : RMProg R Q₁) (M₂ : RMProg R Q₂) :
    RMProg R (Q₁ ⊕ Q₂)
  | Sum.inl q₁ => (M₁ q₁).map (rmOpMapQ Sum.inl)
  | Sum.inr q₂ => (M₂ q₂).map (rmOpMapQ Sum.inr)

lemma rmIter_branch_inl {R : ℕ} {Q₁ Q₂ : Type} (M₁ : RMProg R Q₁) (M₂ : RMProg R Q₂)
    (inp : List Bool) :
    ∀ k q₀ reg₀ q₁ reg₁ out,
      rmIter M₁ inp k q₀ reg₀ = some (q₁, reg₁, out) →
      rmIter (rmBranch M₁ M₂) inp k (Sum.inl q₀) reg₀ = some (Sum.inl q₁, reg₁, out)
  | 0, q₀, reg₀, q₁, reg₁, out, h => by cases h; rfl
  | k + 1, q₀, reg₀, q₁, reg₁, out, h => by
    simp only [rmIter] at h ⊢
    cases hs : rmStep M₁ inp q₀ reg₀ with
    | none => rw [hs] at h; cases h
    | some val =>
      rcases val with ⟨q', reg', bit⟩
      simp only [hs] at h
      cases hr : rmIter M₁ inp k q' reg' with
      | none => simp only [hr] at h; cases h
      | some val2 =>
        rcases val2 with ⟨q'', reg'', out'⟩
        simp only [hr] at h; cases h
        have hstep' : rmStep (rmBranch M₁ M₂) inp (Sum.inl q₀) reg₀ =
            some (Sum.inl q', reg', bit) :=
          rmStep_mapQ M₁ (rmBranch M₁ M₂) Sum.inl inp rfl hs
        simp only [hstep', rmIter_branch_inl M₁ M₂ inp k q' reg' q₁ reg₁ out' hr]

lemma rmIter_branch_inr {R : ℕ} {Q₁ Q₂ : Type} (M₁ : RMProg R Q₁) (M₂ : RMProg R Q₂)
    (inp : List Bool) :
    ∀ k q₀ reg₀ q₁ reg₁ out,
      rmIter M₂ inp k q₀ reg₀ = some (q₁, reg₁, out) →
      rmIter (rmBranch M₁ M₂) inp k (Sum.inr q₀) reg₀ = some (Sum.inr q₁, reg₁, out)
  | 0, q₀, reg₀, q₁, reg₁, out, h => by cases h; rfl
  | k + 1, q₀, reg₀, q₁, reg₁, out, h => by
    simp only [rmIter] at h ⊢
    cases hs : rmStep M₂ inp q₀ reg₀ with
    | none => rw [hs] at h; cases h
    | some val =>
      rcases val with ⟨q', reg', bit⟩
      simp only [hs] at h
      cases hr : rmIter M₂ inp k q' reg' with
      | none => simp only [hr] at h; cases h
      | some val2 =>
        rcases val2 with ⟨q'', reg'', out'⟩
        simp only [hr] at h; cases h
        have hstep' : rmStep (rmBranch M₁ M₂) inp (Sum.inr q₀) reg₀ =
            some (Sum.inr q', reg', bit) :=
          rmStep_mapQ M₂ (rmBranch M₁ M₂) Sum.inr inp rfl hs
        simp only [hstep', rmIter_branch_inr M₁ M₂ inp k q' reg' q₁ reg₁ out' hr]

theorem rmBranch_inl_spec {R : ℕ} {Q₁ Q₂ : Type}
    {M₁ : RMProg R Q₁} (M₂ : RMProg R Q₂) {V : ℕ} {inp : List Bool}
    {q₀ q₁ : Q₁} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (h : RMExec M₁ V inp q₀ reg₀ q₁ reg₁ out T) :
    RMExec (rmBranch M₁ M₂) V inp (Sum.inl q₀) reg₀ (Sum.inl q₁) reg₁ out T := by
  rcases h with ⟨k, hk, hiter, hhalt, hbnd⟩
  refine ⟨k, hk, rmIter_branch_inl M₁ M₂ inp k q₀ reg₀ q₁ reg₁ out hiter,
    by simp [rmBranch, hhalt], ?_⟩
  intro j hj q' reg' out' hji r
  obtain ⟨qj, regj, outj, hsub⟩ := rmIter_le_some hj hiter
  rw [rmIter_branch_inl M₁ M₂ inp j q₀ reg₀ qj regj outj hsub] at hji
  cases hji
  exact hbnd j hj qj reg' out' hsub r

theorem rmBranch_inr_spec {R : ℕ} {Q₁ Q₂ : Type}
    (M₁ : RMProg R Q₁) {M₂ : RMProg R Q₂} {V : ℕ} {inp : List Bool}
    {q₀ q₁ : Q₂} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (h : RMExec M₂ V inp q₀ reg₀ q₁ reg₁ out T) :
    RMExec (rmBranch M₁ M₂) V inp (Sum.inr q₀) reg₀ (Sum.inr q₁) reg₁ out T := by
  rcases h with ⟨k, hk, hiter, hhalt, hbnd⟩
  refine ⟨k, hk, rmIter_branch_inr M₁ M₂ inp k q₀ reg₀ q₁ reg₁ out hiter,
    by simp [rmBranch, hhalt], ?_⟩
  intro j hj q' reg' out' hji r
  obtain ⟨qj, regj, outj, hsub⟩ := rmIter_le_some hj hiter
  rw [rmIter_branch_inr M₁ M₂ inp j q₀ reg₀ qj regj outj hsub] at hji
  cases hji
  exact hbnd j hj qj reg' out' hsub r

/-- Destructive branch on `reg r = 0` (`opDecJz`): jumps to `Mz` if `0`, else decrements `r` and jumps to `Mnz`. -/
def rmDecBranch {R : ℕ} {Qz Qnz : Type} (r : Fin R)
    (Mz : RMProg R Qz) (Mnz : RMProg R Qnz) (qz₀ : Qz) (qnz₀ : Qnz) :
    RMProg R (Option Bool ⊕ (Qz ⊕ Qnz)) :=
  rmSeq (rmDecJzProg r) (rmBranch Mz Mnz)
    (fun s => match s with
      | some true => Sum.inl qz₀
      | _ => Sum.inr qnz₀)

def rmDecBranchEntry {Qz Qnz : Type} : Option Bool ⊕ (Qz ⊕ Qnz) :=
  Sum.inl none

lemma rmDecBranch_entry_eq {R : ℕ} {Qz Qnz : Type} (r : Fin R)
    (qz₀ : Qz) (qnz₀ : Qnz) :
    rmSeqEntry (rmDecJzProg r)
      (fun s : Option Bool => match s with | some true => Sum.inl qz₀ | _ => Sum.inr qnz₀) none =
    rmDecBranchEntry := rfl

theorem rmDecBranch_zero_spec {R : ℕ} {Qz Qnz : Type} (r : Fin R)
    {Mz : RMProg R Qz} (Mnz : RMProg R Qnz) {qz₀ qz₁ : Qz} (qnz₀ : Qnz)
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (hr : reg₀ r = 0)
    (hz : RMExec Mz V inp qz₀ reg₀ qz₁ reg₁ out T) :
    RMExec (rmDecBranch r Mz Mnz qz₀ qnz₀) V inp
      rmDecBranchEntry reg₀ (Sum.inr (Sum.inl qz₁)) reg₁ out (1 + T) := by
  have h0 := rmDecJzProg_spec r V inp reg₀ hz.reg₀_le
  simp only [hr, decide_true, ↓reduceIte] at h0
  have hcomb := rmSeq_spec (f := fun s : Option Bool =>
    match s with | some true => Sum.inl qz₀ | _ => Sum.inr qnz₀) h0 (rmBranch_inl_spec Mnz hz)
  simpa [rmDecBranch, rmDecBranch_entry_eq, max_self] using hcomb

theorem rmDecBranch_pos_spec {R : ℕ} {Qz Qnz : Type} (r : Fin R)
    (Mz : RMProg R Qz) {Mnz : RMProg R Qnz} (qz₀ : Qz) {qnz₀ qnz₁ : Qnz}
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (hr : reg₀ r ≠ 0) (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hnz : RMExec Mnz V inp qnz₀ (regUpd reg₀ r (reg₀ r - 1)) qnz₁ reg₁ out T) :
    RMExec (rmDecBranch r Mz Mnz qz₀ qnz₀) V inp
      rmDecBranchEntry reg₀ (Sum.inr (Sum.inr qnz₁)) reg₁ out (1 + T) := by
  have h0 := rmDecJzProg_spec r V inp reg₀ hreg₀
  simp only [hr, decide_false, ↓reduceIte] at h0
  have hcomb := rmSeq_spec (f := fun s : Option Bool =>
    match s with | some true => Sum.inl qz₀ | _ => Sum.inr qnz₀) h0 (rmBranch_inr_spec Mz hnz)
  simpa [rmDecBranch, rmDecBranch_entry_eq, max_self] using hcomb

/-- Non-destructive conditional `if reg r = 0 then Mz else Mnz` (no scratch register needed). -/
def rmIfZero {R : ℕ} {Qz Qnz : Type} (r : Fin R)
    (Mz : RMProg R Qz) (Mnz : RMProg R Qnz) (qz₀ : Qz) (qnz₀ : Qnz) :
    RMProg R (Option Bool ⊕ (Qz ⊕ (Bool ⊕ Qnz))) :=
  rmDecBranch r Mz (rmChain (rmInc r) Mnz qnz₀) qz₀ (rmChainEntry (rmInc r) false qnz₀)

def rmIfZeroEntry {Qz Qnz : Type} : Option Bool ⊕ (Qz ⊕ (Bool ⊕ Qnz)) :=
  rmDecBranchEntry

theorem rmIfZero_zero_spec {R : ℕ} {Qz Qnz : Type} (r : Fin R)
    {Mz : RMProg R Qz} (Mnz : RMProg R Qnz) {qz₀ qz₁ : Qz} (qnz₀ : Qnz)
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (hr : reg₀ r = 0)
    (hz : RMExec Mz V inp qz₀ reg₀ qz₁ reg₁ out T) :
    RMExec (rmIfZero r Mz Mnz qz₀ qnz₀) V inp
      rmIfZeroEntry reg₀ (Sum.inr (Sum.inl qz₁)) reg₁ out (2 + T) :=
  (rmDecBranch_zero_spec r _ _ hr hz).weaken (Nat.le_refl V) (by omega)

theorem rmIfZero_pos_spec {R : ℕ} {Qz Qnz : Type} (r : Fin R)
    (Mz : RMProg R Qz) {Mnz : RMProg R Qnz} (qz₀ : Qz) {qnz₀ qnz₁ : Qnz}
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (hr : reg₀ r ≠ 0)
    (hnz : RMExec Mnz V inp qnz₀ reg₀ qnz₁ reg₁ out T) :
    RMExec (rmIfZero r Mz Mnz qz₀ qnz₀) V inp
      rmIfZeroEntry reg₀ (Sum.inr (Sum.inr (Sum.inr qnz₁))) reg₁ out (2 + T) := by
  have hreg₀ := hnz.reg₀_le
  have hdec_le : ∀ i, regUpd reg₀ r (reg₀ r - 1) i ≤ V :=
    regUpd_le hreg₀ r (le_trans (Nat.sub_le _ _) (hreg₀ r))
  have hinc_val : regUpd reg₀ r (reg₀ r - 1) r + 1 = reg₀ r := by
    rw [regUpd_self]; omega
  have hinc := rmInc_spec r V inp (regUpd reg₀ r (reg₀ r - 1)) hdec_le (by rw [hinc_val]; exact hreg₀ r)
  have hrestore : regUpd (regUpd reg₀ r (reg₀ r - 1)) r (regUpd reg₀ r (reg₀ r - 1) r + 1) = reg₀ := by
    rw [hinc_val, regUpd_idem, regUpd_eq_self]
  rw [hrestore] at hinc
  have hchain := rmChain_spec hinc hnz
  simp only [max_self, List.nil_append] at hchain
  have hbr := rmDecBranch_pos_spec r Mz qz₀ hr hreg₀ hchain
  exact hbr.weaken (Nat.le_refl V) (by omega)

/-- Input-bit branch `if inp.getD (reg rIdx) false = false then Mf else Mt`. -/
def rmIfReadIn {R : ℕ} {Qf Qt : Type} (rIdx : Fin R)
    (Mf : RMProg R Qf) (Mt : RMProg R Qt) (qf₀ : Qf) (qt₀ : Qt) :
    RMProg R (Option Bool ⊕ (Qf ⊕ Qt)) :=
  rmSeq (rmReadInProg rIdx) (rmBranch Mf Mt)
    (fun s => match s with
      | some true => Sum.inr qt₀
      | _ => Sum.inl qf₀)

def rmIfReadInEntry {Qf Qt : Type} : Option Bool ⊕ (Qf ⊕ Qt) :=
  Sum.inl none

theorem rmIfReadIn_false_spec {R : ℕ} {Qf Qt : Type} (rIdx : Fin R)
    {Mf : RMProg R Qf} (Mt : RMProg R Qt) {qf₀ qf₁ : Qf} (qt₀ : Qt)
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (hb : inp.getD (reg₀ rIdx) false = false)
    (hf : RMExec Mf V inp qf₀ reg₀ qf₁ reg₁ out T) :
    RMExec (rmIfReadIn rIdx Mf Mt qf₀ qt₀) V inp
      rmIfReadInEntry reg₀ (Sum.inr (Sum.inl qf₁)) reg₁ out (1 + T) := by
  have h0 := rmReadInProg_spec rIdx V inp reg₀ hf.reg₀_le
  rw [hb] at h0
  have hcomb := rmSeq_spec (f := fun s : Option Bool =>
    match s with | some true => Sum.inr qt₀ | _ => Sum.inl qf₀) h0 (rmBranch_inl_spec Mt hf)
  simpa [rmIfReadIn, rmIfReadInEntry, rmSeqEntry, rmRedirect, rmReadInProg, max_self] using hcomb

theorem rmIfReadIn_true_spec {R : ℕ} {Qf Qt : Type} (rIdx : Fin R)
    (Mf : RMProg R Qf) {Mt : RMProg R Qt} (qf₀ : Qf) {qt₀ qt₁ : Qt}
    {V : ℕ} {inp : List Bool} {reg₀ reg₁ : RegState R} {out : List Bool} {T : ℕ}
    (hb : inp.getD (reg₀ rIdx) false = true)
    (ht : RMExec Mt V inp qt₀ reg₀ qt₁ reg₁ out T) :
    RMExec (rmIfReadIn rIdx Mf Mt qf₀ qt₀) V inp
      rmIfReadInEntry reg₀ (Sum.inr (Sum.inr qt₁)) reg₁ out (1 + T) := by
  have h0 := rmReadInProg_spec rIdx V inp reg₀ ht.reg₀_le
  rw [hb] at h0
  have hcomb := rmSeq_spec (f := fun s : Option Bool =>
    match s with | some true => Sum.inr qt₀ | _ => Sum.inl qf₀) h0 (rmBranch_inr_spec Mf ht)
  simpa [rmIfReadIn, rmIfReadInEntry, rmSeqEntry, rmRedirect, rmReadInProg, max_self] using hcomb

/-- Zero-overhead general tail-loop combinator (preserves state space `Q`!). -/
def rmLoopTarget {R : ℕ} {Q : Type} (M : RMProg R Q) (next : Q → Option Q) (q : Q) : Q :=
  match M q with
  | some _ => q
  | none =>
      match next q with
      | some q' => q'
      | none => q

def rmLoop {R : ℕ} {Q : Type} (M : RMProg R Q) (next : Q → Option Q) : RMProg R Q :=
  fun q => (M q).map (rmOpMapQ (rmLoopTarget M next))

lemma rmIter_loop_pos {R : ℕ} {Q : Type} (M : RMProg R Q) (next : Q → Option Q) (inp : List Bool) :
    ∀ k q₀ reg₀ q₁ reg₁ out,
      rmIter M inp (k + 1) q₀ reg₀ = some (q₁, reg₁, out) →
      rmIter (rmLoop M next) inp (k + 1) q₀ reg₀ = some (rmLoopTarget M next q₁, reg₁, out)
  | 0, q₀, reg₀, q₁, reg₁, out, h => by
    simp only [rmIter] at h ⊢
    cases hs : rmStep M inp q₀ reg₀ with
    | none => rw [hs] at h; cases h
    | some val =>
      rcases val with ⟨q', reg', bit⟩
      simp only [hs] at h; cases h
      rw [rmStep_mapQ M (rmLoop M next) (rmLoopTarget M next) inp rfl hs]
  | k + 1, q₀, reg₀, q₁, reg₁, out, h => by
    conv at h => lhs; unfold rmIter
    conv => lhs; unfold rmIter
    cases hs : rmStep M inp q₀ reg₀ with
    | none => simp only [hs] at h; cases h
    | some val =>
      rcases val with ⟨q', reg', bit⟩
      simp only [hs] at h
      cases hr : rmIter M inp (k + 1) q' reg' with
      | none => simp only [hr] at h; cases h
      | some val2 =>
        rcases val2 with ⟨q'', reg'', out'⟩
        simp only [hr] at h; cases h
        have hMq'_ne : ∃ op, M q' = some op := by
          conv at hr => lhs; unfold rmIter
          cases hs' : rmStep M inp q' reg' with
          | none => simp only [hs'] at hr; cases hr
          | some _ =>
            unfold rmStep at hs'
            cases hM : M q' with
            | none => rw [hM] at hs'; cases hs'
            | some op => exact ⟨op, rfl⟩
        rcases hMq'_ne with ⟨op, hop⟩
        have htgt : rmLoopTarget M next q' = q' := by simp [rmLoopTarget, hop]
        have hstep' : rmStep (rmLoop M next) inp q₀ reg₀ = some (q', reg', bit) := by
          rw [← htgt]
          exact rmStep_mapQ M (rmLoop M next) (rmLoopTarget M next) inp rfl hs
        simp only [hstep', rmIter_loop_pos M next inp k q' reg' q₁ reg₁ out' hr]

lemma rmIter_loop_lt {R : ℕ} {Q : Type} (M : RMProg R Q) (next : Q → Option Q) (inp : List Bool)
    {j k : ℕ} {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {out : List Bool}
    (hjk : j < k) (hk : rmIter M inp k q₀ reg₀ = some (q₁, reg₁, out)) :
    ∃ qj regj outj,
      rmIter M inp j q₀ reg₀ = some (qj, regj, outj) ∧
      rmIter (rmLoop M next) inp j q₀ reg₀ = some (qj, regj, outj) := by
  cases j with
  | zero => exact ⟨q₀, reg₀, [], rfl, rfl⟩
  | succ j' =>
    have heq : k = (j' + 1) + (k - (j' + 1)) := by omega
    rw [heq] at hk
    obtain ⟨qj, regj, outj, out_rem, hj, hrem, _⟩ :=
      rmIter_add_split M inp (j' + 1) (k - (j' + 1)) q₀ reg₀ q₁ reg₁ out hk
    have hpos : ∃ m, k - (j' + 1) = m + 1 := ⟨k - (j' + 1) - 1, by omega⟩
    rcases hpos with ⟨m, hm⟩
    rw [hm] at hrem
    have hMqj : ∃ op, M qj = some op := by
      simp only [rmIter] at hrem
      cases hs' : rmStep M inp qj regj with
      | none => rw [hs'] at hrem; cases hrem
      | some _ =>
        unfold rmStep at hs'
        cases hM : M qj with
        | none => rw [hM] at hs'; cases hs'
        | some op => exact ⟨op, rfl⟩
    rcases hMqj with ⟨op, hop⟩
    have htgt : rmLoopTarget M next qj = qj := by simp [rmLoopTarget, hop]
    have hlj := rmIter_loop_pos M next inp j' q₀ reg₀ qj regj outj hj
    rw [htgt] at hlj
    exact ⟨qj, regj, outj, hj, hlj⟩

theorem rmLoop_done {R : ℕ} {Q : Type} {M : RMProg R Q} {next : Q → Option Q}
    {V : ℕ} {inp : List Bool} {q₀ q₁ : Q} {reg₀ reg₁ : RegState R}
    {out : List Bool} {T : ℕ}
    (h : RMExec M V inp q₀ reg₀ q₁ reg₁ out T) (hstop : next q₁ = none) :
    RMExec (rmLoop M next) V inp q₀ reg₀ q₁ reg₁ out T := by
  rcases h with ⟨k, hk, hiter, hhalt, hbnd⟩
  have htgt : rmLoopTarget M next q₁ = q₁ := by simp [rmLoopTarget, hhalt, hstop]
  have hl : rmIter (rmLoop M next) inp k q₀ reg₀ = some (q₁, reg₁, out) := by
    cases k with
    | zero => cases hiter; rfl
    | succ k' =>
      have := rmIter_loop_pos M next inp k' q₀ reg₀ q₁ reg₁ out hiter
      rwa [htgt] at this
  refine ⟨k, hk, hl, by simp [rmLoop, hhalt], ?_⟩
  intro j hj q' reg' out' hji r
  rcases Nat.lt_or_eq_of_le hj with hlt | rfl
  · obtain ⟨qj, regj, outj, h1, h2⟩ := rmIter_loop_lt M next inp hlt hiter
    rw [h2] at hji; cases hji
    exact hbnd j (le_of_lt hlt) q' reg' out' h1 r
  · rw [hl] at hji; cases hji
    exact hbnd j (Nat.le_refl j) q₁ reg₁ out hiter r

theorem rmLoop_step {R : ℕ} {Q : Type} {M : RMProg R Q} {next : Q → Option Q}
    {V₁ V₂ : ℕ} {inp : List Bool} {q₀ q₁ q_next q₂ : Q}
    {reg₀ reg₁ reg₂ : RegState R} {out₁ out₂ : List Bool} {T₁ T₂ : ℕ}
    (hactive : M q₀ ≠ none)
    (h₁ : RMExec M V₁ inp q₀ reg₀ q₁ reg₁ out₁ T₁)
    (hcont : next q₁ = some q_next)
    (h₂ : RMExec (rmLoop M next) V₂ inp q_next reg₁ q₂ reg₂ out₂ T₂) :
    RMExec (rmLoop M next) (max V₁ V₂) inp q₀ reg₀ q₂ reg₂ (out₁ ++ out₂) (T₁ + T₂) := by
  rcases h₁ with ⟨k₁, hk₁, hiter₁, hhalt₁, hbnd₁⟩
  rcases h₂ with ⟨k₂, hk₂, hiter₂, hhalt₂, hbnd₂⟩
  have hk₁_pos : ∃ k₁', k₁ = k₁' + 1 := by
    cases k₁ with
    | zero => cases hiter₁; exact absurd hhalt₁ hactive
    | succ k₁' => exact ⟨k₁', rfl⟩
  rcases hk₁_pos with ⟨k₁', hk₁_eq⟩
  have htgt : rmLoopTarget M next q₁ = q_next := by simp [rmLoopTarget, hhalt₁, hcont]
  have hl₁ : rmIter (rmLoop M next) inp k₁ q₀ reg₀ = some (q_next, reg₁, out₁) := by
    rw [hk₁_eq] at hiter₁ ⊢
    have := rmIter_loop_pos M next inp k₁' q₀ reg₀ q₁ reg₁ out₁ hiter₁
    rwa [htgt] at this
  refine ⟨k₁ + k₂, Nat.add_le_add hk₁ hk₂, ?_, hhalt₂, ?_⟩
  · exact rmIter_add (rmLoop M next) inp k₁ k₂ q₀ reg₀ q_next reg₁ out₁ q₂ reg₂ out₂ hl₁ hiter₂
  · intro j hj q' reg' out' hji r
    by_cases hj1 : j < k₁
    · obtain ⟨qj, regj, outj, h1, h2⟩ := rmIter_loop_lt M next inp hj1 hiter₁
      rw [h2] at hji; cases hji
      exact le_trans (hbnd₁ j (le_of_lt hj1) q' reg' out' h1 r) (le_max_left V₁ V₂)
    · have hj2 : j - k₁ ≤ k₂ := by omega
      obtain ⟨qj, regj, outj, hsub⟩ := rmIter_le_some hj2 hiter₂
      have hcomb := rmIter_add (rmLoop M next) inp k₁ (j - k₁) q₀ reg₀ q_next reg₁ out₁ qj regj outj hl₁ hsub
      have hjeq : k₁ + (j - k₁) = j := by omega
      rw [hjeq] at hcomb
      rw [hcomb] at hji; cases hji
      exact le_trans (hbnd₂ (j - k₁) hj2 q' reg' outj hsub r) (le_max_right V₁ V₂)

/-- Counting while-loop: while `reg r > 0`, decrement `r` and execute `body`. -/
def rmWhileDec {R : ℕ} {Q : Type} (r : Fin R) (body : RMProg R Q) (q₀ : Q) :
    RMProg R (Option Bool ⊕ (Unit ⊕ Q)) :=
  rmLoop (rmDecBranch r rmNop body () q₀)
    (fun s => match s with
      | Sum.inr (Sum.inr _) => some rmDecBranchEntry
      | _ => none)

def rmWhileDecEntry {Q : Type} : Option Bool ⊕ (Unit ⊕ Q) :=
  rmDecBranchEntry

def rmWhileDecExit {Q : Type} : Option Bool ⊕ (Unit ⊕ Q) :=
  Sum.inr (Sum.inl ())

theorem rmWhileDec_zero {R : ℕ} {Q : Type} (r : Fin R) (body : RMProg R Q) (q₀ : Q)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hr : reg r = 0) (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmWhileDec r body q₀) V inp rmWhileDecEntry reg rmWhileDecExit reg [] 1 := by
  have h0 := rmDecBranch_zero_spec r body q₀ hr (rmNop_spec V inp reg hreg)
  exact rmLoop_done h0 rfl

theorem rmWhileDec_step {R : ℕ} {Q : Type} (r : Fin R) (body : RMProg R Q) {q₀ q₁ : Q}
    {V₁ V₂ : ℕ} {inp : List Bool} {reg₀ reg₁ reg₂ : RegState R}
    {out₁ out₂ : List Bool} {T₁ T₂ : ℕ}
    (hr : reg₀ r ≠ 0) (hreg₀ : ∀ i, reg₀ i ≤ V₁)
    (hbody : RMExec body V₁ inp q₀ (regUpd reg₀ r (reg₀ r - 1)) q₁ reg₁ out₁ T₁)
    (hrest : RMExec (rmWhileDec r body q₀) V₂ inp rmWhileDecEntry reg₁ rmWhileDecExit reg₂ out₂ T₂) :
    RMExec (rmWhileDec r body q₀) (max V₁ V₂) inp rmWhileDecEntry reg₀
      rmWhileDecExit reg₂ (out₁ ++ out₂) (1 + T₁ + T₂) := by
  have h1 := rmDecBranch_pos_spec r rmNop () hr hreg₀ hbody
  have hact : rmDecBranch r rmNop body () q₀ rmDecBranchEntry ≠ none := by
    simp [rmDecBranch, rmDecBranchEntry, rmSeq, rmDecJzProg]
  exact rmLoop_step hact h1 rfl hrest

/-- Non-destructive while-loop: while `reg r ≠ 0`, execute `body`. -/
def rmWhile {R : ℕ} {Q : Type} (r : Fin R) (body : RMProg R Q) (q₀ : Q) :
    RMProg R (Option Bool ⊕ (Unit ⊕ (Bool ⊕ Q))) :=
  rmLoop (rmIfZero r rmNop body () q₀)
    (fun s => match s with
      | Sum.inr (Sum.inr _) => some rmIfZeroEntry
      | _ => none)

def rmWhileEntry {Q : Type} : Option Bool ⊕ (Unit ⊕ (Bool ⊕ Q)) :=
  rmIfZeroEntry

def rmWhileExit {Q : Type} : Option Bool ⊕ (Unit ⊕ (Bool ⊕ Q)) :=
  Sum.inr (Sum.inl ())

theorem rmWhile_zero {R : ℕ} {Q : Type} (r : Fin R) (body : RMProg R Q) (q₀ : Q)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hr : reg r = 0) (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmWhile r body q₀) V inp rmWhileEntry reg rmWhileExit reg [] 2 := by
  have h0 := rmIfZero_zero_spec r body q₀ hr (rmNop_spec V inp reg hreg)
  exact rmLoop_done h0 rfl

theorem rmWhile_step {R : ℕ} {Q : Type} (r : Fin R) (body : RMProg R Q) {q₀ q₁ : Q}
    {V₁ V₂ : ℕ} {inp : List Bool} {reg₀ reg₁ reg₂ : RegState R}
    {out₁ out₂ : List Bool} {T₁ T₂ : ℕ}
    (hr : reg₀ r ≠ 0)
    (hbody : RMExec body V₁ inp q₀ reg₀ q₁ reg₁ out₁ T₁)
    (hrest : RMExec (rmWhile r body q₀) V₂ inp rmWhileEntry reg₁ rmWhileExit reg₂ out₂ T₂) :
    RMExec (rmWhile r body q₀) (max V₁ V₂) inp rmWhileEntry reg₀
      rmWhileExit reg₂ (out₁ ++ out₂) (2 + T₁ + T₂) := by
  have h1 := rmIfZero_pos_spec r rmNop () hr hbody
  have hact : rmIfZero r rmNop body () q₀ rmIfZeroEntry ≠ none := by
    simp [rmIfZero, rmIfZeroEntry, rmDecBranch, rmDecBranchEntry, rmSeq, rmDecJzProg]
  exact rmLoop_step hact h1 rfl hrest

/-- Input-scanning while-loop: while `inp.getD (reg rIdx) false = true`, execute `body`. -/
def rmWhileReadIn {R : ℕ} {Q : Type} (rIdx : Fin R) (body : RMProg R Q) (q₀ : Q) :
    RMProg R (Option Bool ⊕ (Unit ⊕ Q)) :=
  rmLoop (rmIfReadIn rIdx rmNop body () q₀)
    (fun s => match s with
      | Sum.inr (Sum.inr _) => some rmIfReadInEntry
      | _ => none)

def rmWhileReadInEntry {Q : Type} : Option Bool ⊕ (Unit ⊕ Q) :=
  rmIfReadInEntry

def rmWhileReadInExit {Q : Type} : Option Bool ⊕ (Unit ⊕ Q) :=
  Sum.inr (Sum.inl ())

theorem rmWhileReadIn_false {R : ℕ} {Q : Type} (rIdx : Fin R) (body : RMProg R Q) (q₀ : Q)
    (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hb : inp.getD (reg rIdx) false = false) (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmWhileReadIn rIdx body q₀) V inp rmWhileReadInEntry reg rmWhileReadInExit reg [] 1 := by
  have h0 := rmIfReadIn_false_spec rIdx body q₀ hb (rmNop_spec V inp reg hreg)
  exact rmLoop_done h0 rfl

theorem rmWhileReadIn_step {R : ℕ} {Q : Type} (rIdx : Fin R) (body : RMProg R Q) {q₀ q₁ : Q}
    {V₁ V₂ : ℕ} {inp : List Bool} {reg₀ reg₁ reg₂ : RegState R}
    {out₁ out₂ : List Bool} {T₁ T₂ : ℕ}
    (hb : inp.getD (reg₀ rIdx) false = true)
    (hbody : RMExec body V₁ inp q₀ reg₀ q₁ reg₁ out₁ T₁)
    (hrest : RMExec (rmWhileReadIn rIdx body q₀) V₂ inp rmWhileReadInEntry reg₁
      rmWhileReadInExit reg₂ out₂ T₂) :
    RMExec (rmWhileReadIn rIdx body q₀) (max V₁ V₂) inp rmWhileReadInEntry reg₀
      rmWhileReadInExit reg₂ (out₁ ++ out₂) (1 + T₁ + T₂) := by
  have h1 := rmIfReadIn_true_spec rIdx rmNop () hb hbody
  have hact : rmIfReadIn rIdx rmNop body () q₀ rmIfReadInEntry ≠ none := by
    simp [rmIfReadIn, rmIfReadInEntry, rmSeq, rmReadInProg]
  exact rmLoop_step hact h1 rfl hrest

/-- Register-embedding combinator: lifts an `R₁`-register program into `R₂` registers via `g`. -/
def rmLift {R₁ R₂ : ℕ} {Q : Type} (g : Fin R₁ → Fin R₂) (M : RMProg R₁ Q) : RMProg R₂ Q :=
  fun q => (M q).map (rmOpMapR g)

lemma rmStep_lift {R₁ R₂ : ℕ} {Q : Type} (g : Fin R₁ → Fin R₂) (hg : Function.Injective g)
    (M : RMProg R₁ Q) (inp : List Bool) {q q' : Q}
    {regB : RegState R₂} {regS regS' : RegState R₁} {b : List Bool}
    (hagree : ∀ j, regB (g j) = regS j)
    (hstep : rmStep M inp q regS = some (q', regS', b)) :
    ∃ regB' : RegState R₂,
      rmStep (rmLift g M) inp q regB = some (q', regB', b) ∧
      (∀ j, regB' (g j) = regS' j) ∧
      (∀ i, (∀ j, g j ≠ i) → regB' i = regB i) := by
  unfold rmStep at hstep ⊢
  simp only [rmLift]
  cases hM : M q with
  | none => rw [hM] at hstep; cases hstep
  | some op =>
    rw [hM] at hstep
    rcases op with ⟨r, next⟩ | ⟨r, next⟩ | ⟨r, qz, qnz⟩ | ⟨d, s, next⟩ | ⟨r, qf, qt⟩ | ⟨bit, next⟩
    · simp only [Option.map_some, rmOpMapR, opZero] at hstep ⊢; cases hstep
      refine ⟨regUpd regB (g r) 0, rfl, ?_, ?_⟩
      · intro j; by_cases hj : j = r
        · subst hj; simp
        · rw [regUpd_ne _ (fun h => hj (hg h)), regUpd_ne _ hj, hagree]
      · intro i hi; rw [regUpd_ne _ (Ne.symm (hi r))]
    · simp only [Option.map_some, rmOpMapR, opInc] at hstep ⊢; cases hstep
      refine ⟨regUpd regB (g r) (regB (g r) + 1), rfl, ?_, ?_⟩
      · intro j; by_cases hj : j = r
        · subst hj; simp [hagree]
        · rw [regUpd_ne _ (fun h => hj (hg h)), regUpd_ne _ hj, hagree]
      · intro i hi; rw [regUpd_ne _ (Ne.symm (hi r))]
    · simp only [Option.map_some, rmOpMapR, opDecJz] at hstep ⊢
      rw [hagree r]
      split_ifs at hstep ⊢ with h0
      · cases hstep; exact ⟨regB, rfl, hagree, fun _ _ => rfl⟩
      · cases hstep
        refine ⟨regUpd regB (g r) (regS r - 1), rfl, ?_, ?_⟩
        · intro j; by_cases hj : j = r
          · subst hj; simp
          · rw [regUpd_ne _ (fun h => hj (hg h)), regUpd_ne _ hj, hagree]
        · intro i hi; rw [regUpd_ne _ (Ne.symm (hi r))]
    · simp only [Option.map_some, rmOpMapR, opCopy] at hstep ⊢; cases hstep
      refine ⟨regUpd regB (g d) (regB (g s)), rfl, ?_, ?_⟩
      · intro j; by_cases hj : j = d
        · subst hj; simp [hagree]
        · rw [regUpd_ne _ (fun h => hj (hg h)), regUpd_ne _ hj, hagree]
      · intro i hi; rw [regUpd_ne _ (Ne.symm (hi d))]
    · simp only [Option.map_some, rmOpMapR, opReadIn] at hstep ⊢
      rw [hagree r]
      split_ifs at hstep ⊢ with hbit <;> cases hstep <;>
        exact ⟨regB, rfl, hagree, fun _ _ => rfl⟩
    · simp only [Option.map_some, rmOpMapR, opEmit] at hstep ⊢; cases hstep
      exact ⟨regB, rfl, hagree, fun _ _ => rfl⟩

lemma rmIter_lift {R₁ R₂ : ℕ} {Q : Type} (g : Fin R₁ → Fin R₂) (hg : Function.Injective g)
    (M : RMProg R₁ Q) (inp : List Bool) :
    ∀ k q₀ regB₀ regS₀ q₁ regS₁ out,
      (∀ j, regB₀ (g j) = regS₀ j) →
      rmIter M inp k q₀ regS₀ = some (q₁, regS₁, out) →
      ∃ regB₁ : RegState R₂,
        rmIter (rmLift g M) inp k q₀ regB₀ = some (q₁, regB₁, out) ∧
        (∀ j, regB₁ (g j) = regS₁ j) ∧
        (∀ i, (∀ j, g j ≠ i) → regB₁ i = regB₀ i)
  | 0, q₀, regB₀, regS₀, q₁, regS₁, out, hagree, h => by
    cases h; exact ⟨regB₀, rfl, hagree, fun _ _ => rfl⟩
  | k + 1, q₀, regB₀, regS₀, q₁, regS₁, out, hagree, h => by
    simp only [rmIter] at h ⊢
    cases hs : rmStep M inp q₀ regS₀ with
    | none => rw [hs] at h; cases h
    | some val =>
      rcases val with ⟨q', regS', bit⟩
      simp only [hs] at h
      cases hr : rmIter M inp k q' regS' with
      | none => simp only [hr] at h; cases h
      | some val2 =>
        rcases val2 with ⟨q'', regS'', out'⟩
        simp only [hr] at h; cases h
        obtain ⟨regB', hstepB, hagree', hframe'⟩ := rmStep_lift g hg M inp hagree hs
        obtain ⟨regB₁, hiterB, hagree₁, hframe₁⟩ :=
          rmIter_lift g hg M inp k q' regB' regS' q₁ regS₁ out' hagree' hr
        refine ⟨regB₁, by simp only [hstepB, hiterB], hagree₁, fun i hi => (hframe₁ i hi).trans (hframe' i hi)⟩

theorem rmLift_spec {R₁ R₂ : ℕ} {Q : Type} (g : Fin R₁ → Fin R₂) (hg : Function.Injective g)
    (M : RMProg R₁ Q) (V₁ V₂ : ℕ) (inp : List Bool) (q₀ q₁ : Q)
    (reg₀ : RegState R₂) (reg₁' : RegState R₁) (out : List Bool) (T : ℕ)
    (hbound : ∀ i : Fin R₂, (∀ j : Fin R₁, g j ≠ i) → reg₀ i ≤ V₂)
    (hexec : RMExec M V₁ inp q₀ (fun j => reg₀ (g j)) q₁ reg₁' out T) :
    ∃ reg₁ : RegState R₂,
      (∀ j : Fin R₁, reg₁ (g j) = reg₁' j) ∧
      (∀ i : Fin R₂, (∀ j : Fin R₁, g j ≠ i) → reg₁ i = reg₀ i) ∧
      RMExec (rmLift g M) (max V₁ V₂) inp q₀ reg₀ q₁ reg₁ out T := by
  rcases hexec with ⟨k, hk, hiter, hhalt, hbnd⟩
  obtain ⟨reg₁, hiterB, hagree₁, hframe₁⟩ :=
    rmIter_lift g hg M inp k q₀ reg₀ (fun j => reg₀ (g j)) q₁ reg₁' out (fun _ => rfl) hiter
  refine ⟨reg₁, hagree₁, hframe₁, k, hk, hiterB, by simp [rmLift, hhalt], ?_⟩
  intro j hj q' reg' out' hji i
  obtain ⟨qj, regSj, outj, hsub⟩ := rmIter_le_some hj hiter
  obtain ⟨regBj, hiterBj, hagreej, hframej⟩ :=
    rmIter_lift g hg M inp j q₀ reg₀ (fun l => reg₀ (g l)) qj regSj outj (fun _ => rfl) hsub
  rw [hiterBj] at hji; cases hji
  by_cases him : ∃ l : Fin R₁, g l = i
  · rcases him with ⟨l, rfl⟩
    rw [hagreej l]
    exact le_trans (hbnd j hj q' regSj out' hsub l) (le_max_left V₁ V₂)
  · push Not at him
    rw [hframej i him]
    exact le_trans (hbound i him) (le_max_right V₁ V₂)

/-!
## Section 2: Verified Polynomial-Time Arithmetic & Bit-Emission Macros
-/

/-- Exact copy of `Branch3.minPowExpAux` / `Branch2Algebra.minPowExpAux` (definitionally identical). -/
def minPowExpAux (b target : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | fuel + 1, acc =>
    if target ≤ b ^ acc then acc else minPowExpAux b target fuel (acc + 1)

/-- Exact copy of `Branch3.minPowExp` / `Branch2Algebra.minPowExp` (definitionally identical). -/
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
    target ≤ b ^ minPowExp b target :=
  (minPowExpAux_spec target 0 (by simpa using self_le_pow_of_two_le hb target)
    (by intro r hr; omega)).1

lemma lt_of_lt_minPowExp {b : ℕ} (hb : 2 ≤ b) {target r : ℕ}
    (hr : r < minPowExp b target) : b ^ r < target :=
  (minPowExpAux_spec target 0 (by simpa using self_le_pow_of_two_le hb target)
    (by intro x hx; omega)).2 r hr

lemma minPowExp_min {b : ℕ} (hb : 2 ≤ b) {target r : ℕ} (hr : target ≤ b ^ r) :
    minPowExp b target ≤ r := by
  by_contra hgt
  have hlt : b ^ r < target := lt_of_lt_minPowExp hb (Nat.lt_of_not_ge hgt)
  omega

lemma minPowExp_unique {b target e : ℕ} (hb : 2 ≤ b)
    (hle : target ≤ b ^ e) (hlt : ∀ r < e, b ^ r < target) :
    e = minPowExp b target := by
  apply le_antisymm
  · by_contra hgt
    have := hlt (minPowExp b target) (Nat.lt_of_not_ge hgt)
    have := minPowExp_le_pow hb target
    omega
  · exact minPowExp_min hb hle

lemma minPowExp_le_self {b : ℕ} (hb : 2 ≤ b) (target : ℕ) :
    minPowExp b target ≤ target :=
  minPowExp_min hb (self_le_pow_of_two_le hb target)

/-! ### Helper Macros: `rmDec1`, `rmAddConst`, `rmSetConst` -/

/-- Saturating decrement by 1 (`reg r := reg r - 1`) in 1 step. -/
def rmDec1 {R : ℕ} (r : Fin R) : RMProg R Bool
  | false => some (opDecJz r true true)
  | true => none

theorem rmDec1_spec {R : ℕ} (r : Fin R) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmDec1 r) V inp false reg true (regUpd reg r (reg r - 1)) [] 1 := by
  by_cases h0 : reg r = 0
  · have hupd : regUpd reg r (reg r - 1) = reg := by
      have : reg r - 1 = reg r := by omega
      rw [this, regUpd_eq_self]
    rw [hupd]
    exact rmExec_one_step (by simp [rmStep, rmDec1, opDecJz, h0]) rfl hreg hreg
  · exact rmExec_one_step (by simp [rmStep, rmDec1, opDecJz, h0]) rfl hreg
      (regUpd_le hreg r (le_trans (Nat.sub_le _ _) (hreg r)))

/-- Add a compile-time constant `c` to register `r` in `c` steps. -/
def rmAddConst {R : ℕ} (r : Fin R) (c : ℕ) : RMProg R (Fin (c + 1)) :=
  fun q =>
    if h : q.val < c then some (opInc r ⟨q.val + 1, by omega⟩)
    else none

lemma rmAddConst_aux {R : ℕ} (r : Fin R) (c : ℕ) (V : ℕ) (inp : List Bool) :
    ∀ (rem i : ℕ) (hi : i + rem = c) (reg : RegState R),
      (∀ j, reg j ≤ V) → reg r + rem ≤ V →
      RMExec (rmAddConst r c) V inp ⟨i, by omega⟩ reg ⟨c, by omega⟩
        (regUpd reg r (reg r + rem)) [] rem
  | 0, i, hi, reg, hreg, _ => by
    obtain rfl : i = c := by omega
    refine ⟨0, Nat.le_refl 0, by simp [rmIter], by simp [rmAddConst], ?_⟩
    intro j hj q' reg' out' hji
    obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
    cases hji; exact hreg
  | rem + 1, i, hi, reg, hreg, hle => by
    have hilt : i < c := by omega
    have hstep : rmStep (rmAddConst r c) inp ⟨i, by omega⟩ reg =
        some (⟨i + 1, by omega⟩, regUpd reg r (reg r + 1), []) := by
      simp [rmStep, rmAddConst, opInc, hilt]
    have hreg1 : ∀ j, regUpd reg r (reg r + 1) j ≤ V := regUpd_le hreg r (by omega)
    have hle1 : regUpd reg r (reg r + 1) r + rem ≤ V := by rw [regUpd_self]; omega
    rcases rmAddConst_aux r c V inp rem (i + 1) (by omega) (regUpd reg r (reg r + 1)) hreg1 hle1
      with ⟨k, hk, hiter, hhalt, hbnd⟩
    have hupd : regUpd (regUpd reg r (reg r + 1)) r (regUpd reg r (reg r + 1) r + rem) =
        regUpd reg r (reg r + (rem + 1)) := by
      rw [regUpd_self, regUpd_idem]; congr 1; omega
    rw [hupd] at hiter
    refine ⟨k + 1, by omega, ?_, hhalt, ?_⟩
    · conv => lhs; unfold rmIter
      simp only [hstep, hiter, List.nil_append]
    · intro j hj q' reg' out' hji
      cases j with
      | zero => cases hji; exact hreg
      | succ j' =>
        conv at hji => lhs; unfold rmIter
        simp only [hstep] at hji
        cases hr : rmIter (rmAddConst r c) inp j' ⟨i + 1, by omega⟩ (regUpd reg r (reg r + 1)) with
        | none => simp only [hr] at hji; cases hji
        | some val =>
          rcases val with ⟨q'', reg'', out''⟩
          simp only [hr] at hji; cases hji
          exact hbnd j' (by omega) q' reg' out'' hr

theorem rmAddConst_spec {R : ℕ} (r : Fin R) (c : ℕ) (V : ℕ) (inp : List Bool)
    (reg : RegState R) (hreg : ∀ j, reg j ≤ V) (hle : reg r + c ≤ V) :
    RMExec (rmAddConst r c) V inp ⟨0, by omega⟩ reg ⟨c, by omega⟩
      (regUpd reg r (reg r + c)) [] c :=
  rmAddConst_aux r c V inp c 0 (by omega) reg hreg hle

/-- Set register `r` to a compile-time constant `c` in `c + 1` steps. -/
abbrev RMSetConstQ (c : ℕ) : Type := Bool ⊕ Fin (c + 1)

def rmSetConst {R : ℕ} (r : Fin R) (c : ℕ) : RMProg R (RMSetConstQ c) :=
  rmChain (rmZero r) (rmAddConst r c) ⟨0, by omega⟩

def rmSetConstEntry {c : ℕ} : RMSetConstQ c := Sum.inl false
def rmSetConstExit {c : ℕ} : RMSetConstQ c := Sum.inr ⟨c, by omega⟩

theorem rmSetConst_spec {R : ℕ} (r : Fin R) (c : ℕ) (V : ℕ) (inp : List Bool)
    (reg : RegState R) (hreg : ∀ j, reg j ≤ V) (hc : c ≤ V) :
    RMExec (rmSetConst r c) V inp rmSetConstEntry reg rmSetConstExit
      (regUpd reg r c) [] (1 + c) := by
  have h1 := rmZero_spec r V inp reg hreg
  have h2 := rmAddConst_spec r c V inp (regUpd reg r 0) (regUpd_le hreg r (Nat.zero_le V))
    (by rw [regUpd_self]; omega)
  have hupd : regUpd (regUpd reg r 0) r (regUpd reg r 0 r + c) = regUpd reg r c := by
    rw [regUpd_self, Nat.zero_add, regUpd_idem]
  rw [hupd] at h2
  have hcomb := rmChain_spec h1 h2
  simpa [rmSetConst, rmSetConstEntry, rmSetConstExit, rmChainEntry, rmSeqEntry,
    rmRedirect, rmZero, max_self] using hcomb

/-! ### `rmAdd` and `rmSub` -/

abbrev RMAddQ : Type := Bool ⊕ (Option Bool ⊕ (Unit ⊕ Bool))

/-- `rmAdd dst src tmp`: sets `dst := dst + src`, clears `tmp := 0` (allows `dst = src`). -/
def rmAdd {R : ℕ} (dst src tmp : Fin R) : RMProg R RMAddQ :=
  rmChain (rmCopy tmp src) (rmWhileDec tmp (rmInc dst) false) rmWhileDecEntry

def rmAddEntry : RMAddQ := Sum.inl false
def rmAddExit : RMAddQ := Sum.inr rmWhileDecExit

lemma rmAdd_loop_spec {R : ℕ} (dst tmp : Fin R) (hdt : dst ≠ tmp) (V : ℕ) (inp : List Bool) :
    ∀ (k : ℕ) (reg : RegState R),
      reg tmp = k → (∀ i, reg i ≤ V) → reg dst + k ≤ V →
      RMExec (rmWhileDec tmp (rmInc dst) false) V inp rmWhileDecEntry reg rmWhileDecExit
        (regUpd (regUpd reg dst (reg dst + k)) tmp 0) [] (2 * k + 1)
  | 0, reg, htmp, hreg, _ => by
    have hupd : regUpd (regUpd reg dst (reg dst + 0)) tmp 0 = reg := by
      simp only [Nat.add_zero, regUpd_eq_self]
      rw [← htmp, regUpd_eq_self]
    rw [hupd]
    exact rmWhileDec_zero tmp (rmInc dst) false V inp reg htmp hreg
  | k + 1, reg, htmp, hreg, hle => by
    have hne : reg tmp ≠ 0 := by omega
    set reg1 := regUpd reg tmp (reg tmp - 1)
    have hreg1_le : ∀ i, reg1 i ≤ V := regUpd_le hreg tmp (by omega)
    have hreg1_dst : reg1 dst = reg dst := regUpd_ne reg hdt _
    have hinc := rmInc_spec dst V inp reg1 hreg1_le (by rw [hreg1_dst]; omega)
    set reg2 := regUpd reg1 dst (reg1 dst + 1)
    have hreg2_le : ∀ i, reg2 i ≤ V := hinc.reg₁_le
    have hreg2_tmp : reg2 tmp = k := by
      dsimp only [reg2, reg1]; rw [regUpd_ne _ hdt.symm, regUpd_self]; omega
    have hreg2_dst : reg2 dst = reg dst + 1 := by
      dsimp only [reg2]; rw [regUpd_self, hreg1_dst]
    have hrest := rmAdd_loop_spec dst tmp hdt V inp k reg2 hreg2_tmp hreg2_le
      (by rw [hreg2_dst]; omega)
    have hfinal : regUpd (regUpd reg2 dst (reg2 dst + k)) tmp 0 =
        regUpd (regUpd reg dst (reg dst + (k + 1))) tmp 0 := by
      funext i
      by_cases hit : i = tmp
      · subst hit; simp
      · by_cases hid : i = dst
        · subst hid; simp only [regUpd_ne _ hit, regUpd_self, hreg2_dst]; omega
        · simp [regUpd, hit, hid, reg2, reg1]
    rw [hfinal] at hrest
    have hstep := rmWhileDec_step tmp (rmInc dst) hne hreg hinc hrest
    simpa [max_self, show 1 + 1 + (2 * k + 1) = 2 * (k + 1) + 1 by omega] using hstep

theorem rmAdd_spec {R : ℕ} (dst src tmp : Fin R) (hdt : dst ≠ tmp) (hst : src ≠ tmp)
    (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) (hle : reg dst + reg src ≤ V) :
    RMExec (rmAdd dst src tmp) V inp rmAddEntry reg rmAddExit
      (regUpd (regUpd reg dst (reg dst + reg src)) tmp 0) [] (2 * reg src + 2) := by
  have hcp := rmCopy_spec tmp src V inp reg hreg
  set reg1 := regUpd reg tmp (reg src)
  have h1_tmp : reg1 tmp = reg src := regUpd_self reg tmp (reg src)
  have h1_dst : reg1 dst = reg dst := regUpd_ne reg hdt _
  have hloop := rmAdd_loop_spec dst tmp hdt V inp (reg src) reg1 h1_tmp hcp.reg₁_le
    (by rw [h1_dst]; exact hle)
  have hfinal : regUpd (regUpd reg1 dst (reg1 dst + reg src)) tmp 0 =
      regUpd (regUpd reg dst (reg dst + reg src)) tmp 0 := by
    funext i
    by_cases hit : i = tmp
    · subst hit; simp
    · by_cases hid : i = dst
      · subst hid; simp only [regUpd_ne _ hit, regUpd_self, h1_dst]
      · simp [regUpd, hit, hid, reg1]
  rw [hfinal] at hloop
  have _ := hst
  have hcomb := rmChain_spec hcp hloop
  simpa [rmAdd, rmAddEntry, rmAddExit, rmChainEntry, rmSeqEntry, rmRedirect, rmCopy,
    max_self, show 1 + (2 * reg src + 1) = 2 * reg src + 2 by omega] using hcomb

abbrev RMSubQ : Type := Bool ⊕ (Option Bool ⊕ (Unit ⊕ Bool))

/-- `rmSub dst src tmp`: saturating subtraction `dst := dst - src`, clears `tmp := 0`. -/
def rmSub {R : ℕ} (dst src tmp : Fin R) : RMProg R RMSubQ :=
  rmChain (rmCopy tmp src) (rmWhileDec tmp (rmDec1 dst) false) rmWhileDecEntry

def rmSubEntry : RMSubQ := Sum.inl false
def rmSubExit : RMSubQ := Sum.inr rmWhileDecExit

lemma rmSub_loop_spec {R : ℕ} (dst tmp : Fin R) (hdt : dst ≠ tmp) (V : ℕ) (inp : List Bool) :
    ∀ (k : ℕ) (reg : RegState R),
      reg tmp = k → (∀ i, reg i ≤ V) →
      RMExec (rmWhileDec tmp (rmDec1 dst) false) V inp rmWhileDecEntry reg rmWhileDecExit
        (regUpd (regUpd reg dst (reg dst - k)) tmp 0) [] (2 * k + 1)
  | 0, reg, htmp, hreg => by
    have hupd : regUpd (regUpd reg dst (reg dst - 0)) tmp 0 = reg := by
      simp only [Nat.sub_zero, regUpd_eq_self]
      rw [← htmp, regUpd_eq_self]
    rw [hupd]
    exact rmWhileDec_zero tmp (rmDec1 dst) false V inp reg htmp hreg
  | k + 1, reg, htmp, hreg => by
    have hne : reg tmp ≠ 0 := by omega
    set reg1 := regUpd reg tmp (reg tmp - 1)
    have hreg1_le : ∀ i, reg1 i ≤ V := regUpd_le hreg tmp (le_trans (Nat.sub_le _ _) (hreg tmp))
    have hreg1_dst : reg1 dst = reg dst := regUpd_ne reg hdt _
    have hdec := rmDec1_spec dst V inp reg1 hreg1_le
    set reg2 := regUpd reg1 dst (reg1 dst - 1)
    have hreg2_tmp : reg2 tmp = k := by
      dsimp only [reg2, reg1]; rw [regUpd_ne _ hdt.symm, regUpd_self]; omega
    have hreg2_dst : reg2 dst = reg dst - 1 := by
      dsimp only [reg2]; rw [regUpd_self, hreg1_dst]
    have hrest := rmSub_loop_spec dst tmp hdt V inp k reg2 hreg2_tmp hdec.reg₁_le
    have hfinal : regUpd (regUpd reg2 dst (reg2 dst - k)) tmp 0 =
        regUpd (regUpd reg dst (reg dst - (k + 1))) tmp 0 := by
      funext i
      by_cases hit : i = tmp
      · subst hit; simp
      · by_cases hid : i = dst
        · subst hid; simp only [regUpd_ne _ hit, regUpd_self, hreg2_dst]; omega
        · simp [regUpd, hit, hid, reg2, reg1]
    rw [hfinal] at hrest
    have hstep := rmWhileDec_step tmp (rmDec1 dst) hne hreg hdec hrest
    simpa [max_self, show 1 + 1 + (2 * k + 1) = 2 * (k + 1) + 1 by omega] using hstep

theorem rmSub_spec {R : ℕ} (dst src tmp : Fin R) (hdt : dst ≠ tmp)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmSub dst src tmp) V inp rmSubEntry reg rmSubExit
      (regUpd (regUpd reg dst (reg dst - reg src)) tmp 0) [] (2 * reg src + 2) := by
  have hcp := rmCopy_spec tmp src V inp reg hreg
  set reg1 := regUpd reg tmp (reg src)
  have h1_tmp : reg1 tmp = reg src := regUpd_self reg tmp (reg src)
  have h1_dst : reg1 dst = reg dst := regUpd_ne reg hdt _
  have hloop := rmSub_loop_spec dst tmp hdt V inp (reg src) reg1 h1_tmp hcp.reg₁_le
  have hfinal : regUpd (regUpd reg1 dst (reg1 dst - reg src)) tmp 0 =
      regUpd (regUpd reg dst (reg dst - reg src)) tmp 0 := by
    funext i
    by_cases hit : i = tmp
    · subst hit; simp
    · by_cases hid : i = dst
      · subst hid; simp only [regUpd_ne _ hit, regUpd_self, h1_dst]
      · simp [regUpd, hit, hid, reg1]
  rw [hfinal] at hloop
  have hcomb := rmChain_spec hcp hloop
  simpa [rmSub, rmSubEntry, rmSubExit, rmChainEntry, rmSeqEntry, rmRedirect, rmCopy,
    max_self, show 1 + (2 * reg src + 1) = 2 * reg src + 2 by omega] using hcomb

/-! ### `rmCmpLt` and `rmCmpGe` (Simultaneous Decrement in `O(min a b)` Steps) -/

/-- `rmCmp (strict : Bool) flag a b tA tB`:
if `strict = true`, sets `flag := if a < b then 1 else 0`;
if `strict = false`, sets `flag := if b ≤ a then 1 else 0`. -/
def rmCmp {R : ℕ} (strict : Bool) (flag a b tA tB : Fin R) : RMProg R (Fin 8) :=
  fun q =>
    if q.val = 0 then some (opCopy tA a 1)
    else if q.val = 1 then some (opCopy tB b 2)
    else if q.val = 2 then some (opDecJz tB (if strict then 4 else 5) 3)
    else if q.val = 3 then some (opDecJz tA (if strict then 5 else 4) 2)
    else if q.val = 4 then some (opZero flag 7)
    else if q.val = 5 then some (opZero flag 6)
    else if q.val = 6 then some (opInc flag 7)
    else none

lemma rmCmp_set0 {R : ℕ} (strict : Bool) (flag a b tA tB : Fin R)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmCmp strict flag a b tA tB) V inp 4 reg 7 (regUpd reg flag 0) [] 1 :=
  rmExec_one_step (by simp [rmStep, rmCmp, opZero]) (by simp [rmCmp]) hreg
    (regUpd_le hreg flag (Nat.zero_le V))

lemma rmCmp_set1 {R : ℕ} (strict : Bool) (flag a b tA tB : Fin R)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V) (h1 : 1 ≤ V) :
    RMExec (rmCmp strict flag a b tA tB) V inp 5 reg 7 (regUpd reg flag 1) [] 2 := by
  have hs1 : rmStep (rmCmp strict flag a b tA tB) inp 5 reg = some (6, regUpd reg flag 0, []) := by
    simp [rmStep, rmCmp, opZero]
  have hs2 : rmStep (rmCmp strict flag a b tA tB) inp 6 (regUpd reg flag 0) =
      some (7, regUpd (regUpd reg flag 0) flag (regUpd reg flag 0 flag + 1), []) := by
    simp [rmStep, rmCmp, opInc]
  have hupd : regUpd (regUpd reg flag 0) flag (regUpd reg flag 0 flag + 1) = regUpd reg flag 1 := by
    simp
  rw [hupd] at hs2
  refine ⟨2, Nat.le_refl 2, ?_, by simp [rmCmp], ?_⟩
  · simp [rmIter, hs1, hs2]
  · intro j hj q' reg' out' hji
    match j with
    | 0 => cases hji; exact hreg
    | 1 => simp only [rmIter, hs1] at hji; cases hji; exact regUpd_le hreg flag (Nat.zero_le V)
    | 2 => simp only [rmIter, hs1, hs2] at hji; cases hji; exact regUpd_le hreg flag h1
    | n + 3 => omega

lemma rmCmp_step_prepend {R : ℕ} {Q : Type} {M : RMProg R Q} {V : ℕ} {inp : List Bool}
    {q₀ q₁ q₂ : Q} {reg₀ reg₁ reg₂ : RegState R} {out : List Bool} {T : ℕ}
    (hstep : rmStep M inp q₀ reg₀ = some (q₁, reg₁, []))
    (hreg₀ : ∀ i, reg₀ i ≤ V)
    (hrest : RMExec M V inp q₁ reg₁ q₂ reg₂ out T) :
    RMExec M V inp q₀ reg₀ q₂ reg₂ out (1 + T) := by
  rcases hrest with ⟨k, hk, hiter, hhalt, hbnd⟩
  refine ⟨k + 1, by omega, ?_, hhalt, ?_⟩
  · conv => lhs; unfold rmIter
    simp only [hstep, hiter, List.nil_append]
  · intro j hj q' reg' out' hji
    cases j with
    | zero => cases hji; exact hreg₀
    | succ j' =>
      conv at hji => lhs; unfold rmIter
      simp only [hstep] at hji
      cases hr : rmIter M inp j' q₁ reg₁ with
      | none => simp only [hr] at hji; cases hji
      | some val =>
        rcases val with ⟨q'', reg'', out''⟩
        simp only [hr] at hji; cases hji
        exact hbnd j' (by omega) q' reg' out'' hr

lemma rmCmp_loop {R : ℕ} (strict : Bool) (flag a b tA tB : Fin R)
    (hAB : tA ≠ tB) (hfA : flag ≠ tA) (hfB : flag ≠ tB)
    (V : ℕ) (inp : List Bool) (h1 : 1 ≤ V) :
    ∀ (va vb : ℕ) (reg : RegState R),
      reg tA = va → reg tB = vb → (∀ i, reg i ≤ V) →
      ∃ reg₁ : RegState R,
        reg₁ flag = (if (if strict then decide (va < vb) else decide (vb ≤ va)) then 1 else 0) ∧
        (∀ i, i ≠ flag → i ≠ tA → i ≠ tB → reg₁ i = reg i) ∧
        RMExec (rmCmp strict flag a b tA tB) V inp 2 reg 7 reg₁ [] (2 * min va vb + 4)
  | va, 0, reg, hA, hB, hreg => by
    have hs2 : rmStep (rmCmp strict flag a b tA tB) inp 2 reg =
        some (if strict then 4 else 5, reg, []) := by
      simp [rmStep, rmCmp, opDecJz, hB]
    cases strict
    · have hrest := rmCmp_set1 false flag a b tA tB V inp reg hreg h1
      have hex := (rmCmp_step_prepend hs2 hreg hrest).weaken (V₂ := V) (T₂ := 2 * min va 0 + 4)
        (Nat.le_refl V) (by omega)
      refine ⟨regUpd reg flag 1, by simp, fun i hi _ _ => regUpd_ne reg hi 1, hex⟩
    · have hrest := rmCmp_set0 true flag a b tA tB V inp reg hreg
      have hex := (rmCmp_step_prepend hs2 hreg hrest).weaken (V₂ := V) (T₂ := 2 * min va 0 + 4)
        (Nat.le_refl V) (by omega)
      refine ⟨regUpd reg flag 0, by simp, fun i hi _ _ => regUpd_ne reg hi 0, hex⟩
  | 0, vb + 1, reg, hA, hB, hreg => by
    have hBne : reg tB ≠ 0 := by omega
    set reg1 := regUpd reg tB (reg tB - 1)
    have hreg1 : ∀ i, reg1 i ≤ V := regUpd_le hreg tB (le_trans (Nat.sub_le _ _) (hreg tB))
    have hs2 : rmStep (rmCmp strict flag a b tA tB) inp 2 reg = some (3, reg1, []) := by
      simp [rmStep, rmCmp, opDecJz, hBne, reg1]
    have h1A : reg1 tA = 0 := by dsimp only [reg1]; rw [regUpd_ne reg hAB, hA]
    have hs3 : rmStep (rmCmp strict flag a b tA tB) inp 3 reg1 =
        some (if strict then 5 else 4, reg1, []) := by
      simp [rmStep, rmCmp, opDecJz, h1A]
    cases strict
    · have hrest := rmCmp_set0 false flag a b tA tB V inp reg1 hreg1
      have hex := (rmCmp_step_prepend hs2 hreg (rmCmp_step_prepend hs3 hreg1 hrest)).weaken
        (V₂ := V) (T₂ := 2 * min 0 (vb + 1) + 4) (Nat.le_refl V) (by omega)
      refine ⟨regUpd reg1 flag 0, by simp, fun i hif _ hib => by
        dsimp only [reg1]; rw [regUpd_ne _ hif, regUpd_ne _ hib], hex⟩
    · have hrest := rmCmp_set1 true flag a b tA tB V inp reg1 hreg1 h1
      have hex := (rmCmp_step_prepend hs2 hreg (rmCmp_step_prepend hs3 hreg1 hrest)).weaken
        (V₂ := V) (T₂ := 2 * min 0 (vb + 1) + 4) (Nat.le_refl V) (by omega)
      refine ⟨regUpd reg1 flag 1, by simp, fun i hif _ hib => by
        dsimp only [reg1]; rw [regUpd_ne _ hif, regUpd_ne _ hib], hex⟩
  | va + 1, vb + 1, reg, hA, hB, hreg => by
    have hBne : reg tB ≠ 0 := by omega
    set reg1 := regUpd reg tB (reg tB - 1)
    have hreg1 : ∀ i, reg1 i ≤ V := regUpd_le hreg tB (le_trans (Nat.sub_le _ _) (hreg tB))
    have hs2 : rmStep (rmCmp strict flag a b tA tB) inp 2 reg = some (3, reg1, []) := by
      simp [rmStep, rmCmp, opDecJz, hBne, reg1]
    have h1A : reg1 tA = va + 1 := by dsimp only [reg1]; rw [regUpd_ne reg hAB, hA]
    have h1Ane : reg1 tA ≠ 0 := by omega
    set reg2 := regUpd reg1 tA (reg1 tA - 1)
    have hreg2 : ∀ i, reg2 i ≤ V := regUpd_le hreg1 tA (le_trans (Nat.sub_le _ _) (hreg1 tA))
    have hs3 : rmStep (rmCmp strict flag a b tA tB) inp 3 reg1 = some (2, reg2, []) := by
      simp [rmStep, rmCmp, opDecJz, h1Ane, reg2]
    have h2A : reg2 tA = va := by dsimp only [reg2]; rw [regUpd_self]; omega
    have h2B : reg2 tB = vb := by
      dsimp only [reg2, reg1]; rw [regUpd_ne _ hAB.symm, regUpd_self]; omega
    rcases rmCmp_loop strict flag a b tA tB hAB hfA hfB V inp h1 va vb reg2 h2A h2B hreg2
      with ⟨reg_end, hfl, hfr, hex_rest⟩
    have hmin : min (va + 1) (vb + 1) = min va vb + 1 := by omega
    have hex := (rmCmp_step_prepend hs2 hreg (rmCmp_step_prepend hs3 hreg1 hex_rest)).weaken
      (V₂ := V) (T₂ := 2 * min (va + 1) (vb + 1) + 4) (Nat.le_refl V) (by rw [hmin]; omega)
    refine ⟨reg_end, ?_, ?_, hex⟩
    · rw [hfl]; cases strict <;> simp
    · intro i hif hia hib
      rw [hfr i hif hia hib]
      dsimp only [reg2, reg1]
      rw [regUpd_ne _ hia, regUpd_ne _ hib]

def rmCmpLt {R : ℕ} (flag a b tA tB : Fin R) : RMProg R (Fin 8) :=
  rmCmp true flag a b tA tB

def rmCmpGe {R : ℕ} (flag a b tA tB : Fin R) : RMProg R (Fin 8) :=
  rmCmp false flag a b tA tB

theorem rmCmp_spec {R : ℕ} (strict : Bool) (flag a b tA tB : Fin R)
    (hAB : tA ≠ tB) (hfA : flag ≠ tA) (hfB : flag ≠ tB) (hbA : b ≠ tA)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V) (h1 : 1 ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ flag = (if (if strict then decide (reg a < reg b) else decide (reg b ≤ reg a)) then 1 else 0) ∧
      (∀ i, i ≠ flag → i ≠ tA → i ≠ tB → reg₁ i = reg i) ∧
      RMExec (rmCmp strict flag a b tA tB) V inp 0 reg 7 reg₁ [] (2 * min (reg a) (reg b) + 6) := by
  set reg1 := regUpd reg tA (reg a)
  have hreg1 : ∀ i, reg1 i ≤ V := regUpd_le hreg tA (hreg a)
  have hs0 : rmStep (rmCmp strict flag a b tA tB) inp 0 reg = some (1, reg1, []) := by
    simp [rmStep, rmCmp, opCopy, reg1]
  have h1b : reg1 b = reg b := regUpd_ne reg hbA _
  set reg2 := regUpd reg1 tB (reg1 b)
  have hreg2 : ∀ i, reg2 i ≤ V := regUpd_le hreg1 tB (hreg1 b)
  have hs1 : rmStep (rmCmp strict flag a b tA tB) inp 1 reg1 = some (2, reg2, []) := by
    simp [rmStep, rmCmp, opCopy, reg2]
  have h2A : reg2 tA = reg a := by dsimp only [reg2, reg1]; rw [regUpd_ne _ hAB, regUpd_self]
  have h2B : reg2 tB = reg b := by dsimp only [reg2]; rw [regUpd_self, h1b]
  rcases rmCmp_loop strict flag a b tA tB hAB hfA hfB V inp h1 (reg a) (reg b) reg2 h2A h2B hreg2
    with ⟨reg_end, hfl, hfr, hex_loop⟩
  have hex := (rmCmp_step_prepend hs0 hreg (rmCmp_step_prepend hs1 hreg1 hex_loop)).weaken
    (V₂ := V) (T₂ := 2 * min (reg a) (reg b) + 6) (Nat.le_refl V) (by omega)
  refine ⟨reg_end, hfl, ?_, hex⟩
  intro i hif hia hib
  rw [hfr i hif hia hib]
  dsimp only [reg2, reg1]
  rw [regUpd_ne _ hib, regUpd_ne _ hia]

theorem rmCmpLt_spec {R : ℕ} (flag a b tA tB : Fin R)
    (hAB : tA ≠ tB) (hfA : flag ≠ tA) (hfB : flag ≠ tB) (hbA : b ≠ tA)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V) (h1 : 1 ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ flag = (if reg a < reg b then 1 else 0) ∧
      (∀ i, i ≠ flag → i ≠ tA → i ≠ tB → reg₁ i = reg i) ∧
      RMExec (rmCmpLt flag a b tA tB) V inp 0 reg 7 reg₁ [] (2 * min (reg a) (reg b) + 6) := by
  simpa [rmCmpLt] using rmCmp_spec true flag a b tA tB hAB hfA hfB hbA V inp reg hreg h1

theorem rmCmpGe_spec {R : ℕ} (flag a b tA tB : Fin R)
    (hAB : tA ≠ tB) (hfA : flag ≠ tA) (hfB : flag ≠ tB) (hbA : b ≠ tA)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V) (h1 : 1 ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ flag = (if reg b ≤ reg a then 1 else 0) ∧
      (∀ i, i ≠ flag → i ≠ tA → i ≠ tB → reg₁ i = reg i) ∧
      RMExec (rmCmpGe flag a b tA tB) V inp 0 reg 7 reg₁ [] (2 * min (reg a) (reg b) + 6) := by
  simpa [rmCmpGe] using rmCmp_spec false flag a b tA tB hAB hfA hfB hbA V inp reg hreg h1

/-! ### `rmMul` (Exact Polynomial-Time Multiplication) -/

abbrev RMMulQ : Type := Bool ⊕ (Bool ⊕ (Option Bool ⊕ (Unit ⊕ RMAddQ)))

/-- `rmMul dst a b tmp1 tmp2`: sets `dst := a * b` (allows `a = b`). -/
def rmMul {R : ℕ} (dst a b tmp1 tmp2 : Fin R) : RMProg R RMMulQ :=
  rmChain (rmZero dst)
    (rmChain (rmCopy tmp1 a)
      (rmWhileDec tmp1 (rmAdd dst b tmp2) rmAddEntry) rmWhileDecEntry)
    (Sum.inl false)

def rmMulEntry : RMMulQ := Sum.inl false
def rmMulExit : RMMulQ := Sum.inr (Sum.inr rmWhileDecExit)

lemma rmMul_loop_spec {R : ℕ} (dst b tmp1 tmp2 : Fin R)
    (hdb : dst ≠ b) (hdt1 : dst ≠ tmp1) (hdt2 : dst ≠ tmp2)
    (hbt1 : b ≠ tmp1) (hbt2 : b ≠ tmp2) (ht12 : tmp1 ≠ tmp2)
    (V : ℕ) (inp : List Bool) :
    ∀ (k : ℕ) (reg : RegState R),
      reg tmp1 = k → (∀ i, reg i ≤ V) → reg dst + k * reg b ≤ V →
      ∃ reg₁ : RegState R,
        reg₁ dst = reg dst + k * reg b ∧
        reg₁ tmp1 = 0 ∧
        (∀ i, i ≠ dst → i ≠ tmp1 → i ≠ tmp2 → reg₁ i = reg i) ∧
        RMExec (rmWhileDec tmp1 (rmAdd dst b tmp2) rmAddEntry) V inp rmWhileDecEntry reg
          rmWhileDecExit reg₁ [] (k * (2 * reg b + 3) + 1)
  | 0, reg, htmp1, hreg, _ =>
    ⟨reg, by simp, htmp1, fun _ _ _ _ => rfl, by
      simpa using rmWhileDec_zero tmp1 (rmAdd dst b tmp2) rmAddEntry V inp reg htmp1 hreg⟩
  | k + 1, reg, htmp1, hreg, hle => by
    have hne : reg tmp1 ≠ 0 := by omega
    set reg1 := regUpd reg tmp1 (reg tmp1 - 1)
    have hreg1 : ∀ i, reg1 i ≤ V := regUpd_le hreg tmp1 (le_trans (Nat.sub_le _ _) (hreg tmp1))
    have h1_dst : reg1 dst = reg dst := regUpd_ne reg hdt1 _
    have h1_b : reg1 b = reg b := regUpd_ne reg hbt1 _
    have h1_t1 : reg1 tmp1 = k := by dsimp only [reg1]; rw [regUpd_self]; omega
    have hadd_le : reg1 dst + reg1 b ≤ V := by
      rw [h1_dst, h1_b]
      have : (k + 1) * reg b = reg b + k * reg b := by ring
      omega
    have hadd := rmAdd_spec dst b tmp2 hdt2 hbt2 V inp reg1 hreg1 hadd_le
    set reg2 := regUpd (regUpd reg1 dst (reg1 dst + reg1 b)) tmp2 0
    have h2_dst : reg2 dst = reg dst + reg b := by
      dsimp only [reg2]; rw [regUpd_ne _ hdt2, regUpd_self, h1_dst, h1_b]
    have h2_b : reg2 b = reg b := by
      dsimp only [reg2]; rw [regUpd_ne _ hbt2, regUpd_ne _ hdb.symm, h1_b]
    have h2_t1 : reg2 tmp1 = k := by
      dsimp only [reg2]; rw [regUpd_ne _ ht12, regUpd_ne _ hdt1.symm, h1_t1]
    have h2_le : reg2 dst + k * reg2 b ≤ V := by
      rw [h2_dst, h2_b]; have : (k + 1) * reg b = reg b + k * reg b := by ring
      omega
    rcases rmMul_loop_spec dst b tmp1 tmp2 hdb hdt1 hdt2 hbt1 hbt2 ht12 V inp k reg2 h2_t1 hadd.reg₁_le h2_le
      with ⟨reg_end, hdst_e, ht1_e, hfr_e, hex_rest⟩
    have hstep := rmWhileDec_step tmp1 (rmAdd dst b tmp2) hne hreg hadd hex_rest
    have hT : 1 + (2 * reg1 b + 2) + (k * (2 * reg2 b + 3) + 1) = (k + 1) * (2 * reg b + 3) + 1 := by
      rw [h1_b, h2_b]; ring
    rw [max_self, List.nil_append, hT] at hstep
    refine ⟨reg_end, ?_, ht1_e, ?_, hstep⟩
    · rw [hdst_e, h2_dst, h2_b]; ring
    · intro i hid hit1 hit2
      rw [hfr_e i hid hit1 hit2]
      dsimp only [reg2, reg1]
      rw [regUpd_ne _ hit2, regUpd_ne _ hid, regUpd_ne _ hit1]

theorem rmMul_spec {R : ℕ} (dst a b tmp1 tmp2 : Fin R)
    (hda : dst ≠ a) (hdb : dst ≠ b) (hdt1 : dst ≠ tmp1) (hdt2 : dst ≠ tmp2)
    (hbt1 : b ≠ tmp1) (hbt2 : b ≠ tmp2) (ht12 : tmp1 ≠ tmp2)
    (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) (hle : reg a * reg b ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ dst = reg a * reg b ∧
      (∀ i, i ≠ dst → i ≠ tmp1 → i ≠ tmp2 → reg₁ i = reg i) ∧
      RMExec (rmMul dst a b tmp1 tmp2) V inp rmMulEntry reg rmMulExit reg₁ []
        (reg a * (2 * reg b + 3) + 3) := by
  have hz := rmZero_spec dst V inp reg hreg
  set reg1 := regUpd reg dst 0
  have h1_a : reg1 a = reg a := regUpd_ne reg hda.symm _
  have h1_b : reg1 b = reg b := regUpd_ne reg hdb.symm _
  have hcp := rmCopy_spec tmp1 a V inp reg1 hz.reg₁_le
  set reg2 := regUpd reg1 tmp1 (reg1 a)
  have h2_dst : reg2 dst = 0 := by dsimp only [reg2, reg1]; rw [regUpd_ne _ hdt1, regUpd_self]
  have h2_b : reg2 b = reg b := by dsimp only [reg2]; rw [regUpd_ne _ hbt1, h1_b]
  have h2_t1 : reg2 tmp1 = reg a := by dsimp only [reg2]; rw [regUpd_self, h1_a]
  rcases rmMul_loop_spec dst b tmp1 tmp2 hdb hdt1 hdt2 hbt1 hbt2 ht12 V inp (reg a) reg2
      h2_t1 hcp.reg₁_le (by rw [h2_dst, h2_b, Nat.zero_add]; exact hle)
    with ⟨reg_end, hdst_e, _, hfr_e, hex_loop⟩
  have hchain2 := rmChain_spec hcp hex_loop
  have hchain1 := rmChain_spec hz hchain2
  have hT : 1 + (1 + (reg a * (2 * reg2 b + 3) + 1)) = reg a * (2 * reg b + 3) + 3 := by
    rw [h2_b]; ring
  rw [max_self, max_self, List.nil_append, List.nil_append, hT] at hchain1
  refine ⟨reg_end, by rw [hdst_e, h2_dst, h2_b, Nat.zero_add], ?_, ?_⟩
  · intro i hid hit1 hit2
    rw [hfr_e i hid hit1 hit2]
    dsimp only [reg2, reg1]
    rw [regUpd_ne _ hit1, regUpd_ne _ hid]
  · simpa [rmMul, rmMulEntry, rmMulExit, rmChainEntry, rmSeqEntry, rmRedirect, rmZero, rmCopy] using hchain1

/-! ### `rmDivMod` (Linear-Time Division & Remainder `O(a + b)` for `0 < b`) -/

abbrev RMDivBodyQ : Type := RMSubQ ⊕ (Bool ⊕ Fin 8)
abbrev RMDivModQ : Type := Bool ⊕ (Bool ⊕ (Fin 8 ⊕ (Option Bool ⊕ (Unit ⊕ (Bool ⊕ RMDivBodyQ)))))

def rmDivBody {R : ℕ} (qOut rOut b flag tA tB : Fin R) : RMProg R RMDivBodyQ :=
  rmChain (rmSub rOut b tA)
    (rmChain (rmInc qOut) (rmCmpGe flag rOut b tA tB) 0)
    (Sum.inl false)

def rmDivBodyEntry : RMDivBodyQ := Sum.inl rmSubEntry

/-- `rmDivMod qOut rOut a b flag tA tB`: computes `qOut := a / b`, `rOut := a % b` for `0 < b`. -/
def rmDivMod {R : ℕ} (qOut rOut a b flag tA tB : Fin R) : RMProg R RMDivModQ :=
  rmChain (rmZero qOut)
    (rmChain (rmCopy rOut a)
      (rmChain (rmCmpGe flag rOut b tA tB)
        (rmWhile flag (rmDivBody qOut rOut b flag tA tB) rmDivBodyEntry) rmWhileEntry)
      (Sum.inl 0))
    (Sum.inl false)

def rmDivModEntry : RMDivModQ := Sum.inl false
def rmDivModExit : RMDivModQ := Sum.inr (Sum.inr (Sum.inr rmWhileExit))

lemma rmDivMod_loop_spec {R : ℕ} (qOut rOut b flag tA tB : Fin R)
    (hqr : qOut ≠ rOut) (hqb : qOut ≠ b) (hqf : qOut ≠ flag) (hqA : qOut ≠ tA) (hqB : qOut ≠ tB)
    (hrb : rOut ≠ b) (hrf : rOut ≠ flag) (hrA : rOut ≠ tA) (hrB : rOut ≠ tB)
    (hbf : b ≠ flag) (hbA : b ≠ tA) (hbB : b ≠ tB)
    (hfA : flag ≠ tA) (hfB : flag ≠ tB) (hAB : tA ≠ tB)
    (V : ℕ) (inp : List Bool) (h1 : 1 ≤ V) :
    ∀ (rem q : ℕ) (reg : RegState R),
      0 < reg b →
      reg rOut = rem → reg qOut = q →
      reg flag = (if reg b ≤ rem then 1 else 0) →
      (∀ i, reg i ≤ V) → q + rem / reg b ≤ V →
      ∃ reg₁ : RegState R,
        reg₁ qOut = q + rem / reg b ∧
        reg₁ rOut = rem % reg b ∧
        (∀ i, i ≠ qOut → i ≠ rOut → i ≠ flag → i ≠ tA → i ≠ tB → reg₁ i = reg i) ∧
        RMExec (rmWhile flag (rmDivBody qOut rOut b flag tA tB) rmDivBodyEntry) V inp
          rmWhileEntry reg rmWhileExit reg₁ []
          ((rem / reg b) * (4 * reg b + 11) + 2) := by
  intro rem
  induction rem using Nat.strong_induction_on with
  | h rem ih =>
    intro q reg hbpos hr hq hfl hreg hqle
    by_cases hge : reg b ≤ rem
    · have hfl1 : reg flag = 1 := by rw [hfl]; simp [hge]
      have hflne : reg flag ≠ 0 := by omega
      have hsub := rmSub_spec rOut b tA hrA V inp reg hreg
      set reg1 := regUpd (regUpd reg rOut (reg rOut - reg b)) tA 0
      have h1_r : reg1 rOut = rem - reg b := by
        dsimp only [reg1]; rw [regUpd_ne _ hrA, regUpd_self, hr]
      have h1_b : reg1 b = reg b := by
        dsimp only [reg1]; rw [regUpd_ne _ hbA, regUpd_ne _ hrb.symm]
      have h1_q : reg1 qOut = q := by
        dsimp only [reg1]; rw [regUpd_ne _ hqA, regUpd_ne _ hqr, hq]
      have hq_succ_le : q + 1 ≤ V := by
        have : 1 ≤ rem / reg b := Nat.div_pos hge hbpos
        omega
      have hinc := rmInc_spec qOut V inp reg1 hsub.reg₁_le (by rw [h1_q]; exact hq_succ_le)
      set reg2 := regUpd reg1 qOut (reg1 qOut + 1)
      have h2_r : reg2 rOut = rem - reg b := by dsimp only [reg2]; rw [regUpd_ne _ hqr.symm, h1_r]
      have h2_b : reg2 b = reg b := by dsimp only [reg2]; rw [regUpd_ne _ hqb.symm, h1_b]
      have h2_q : reg2 qOut = q + 1 := by dsimp only [reg2]; rw [regUpd_self, h1_q]
      rcases rmCmpGe_spec flag rOut b tA tB hAB hfA hfB hbA V inp reg2 hinc.reg₁_le h1
        with ⟨reg3, h3_fl, h3_fr, hcmp⟩
      have h3_r : reg3 rOut = rem - reg b := by rw [h3_fr rOut hrf hrA hrB, h2_r]
      have h3_b : reg3 b = reg b := by rw [h3_fr b hbf hbA hbB, h2_b]
      have h3_q : reg3 qOut = q + 1 := by rw [h3_fr qOut hqf hqA hqB, h2_q]
      have h3_fl' : reg3 flag = (if reg3 b ≤ rem - reg b then 1 else 0) := by
        rw [h3_fl, h2_r, h2_b, h3_b]
      have hbody := rmChain_spec hsub (rmChain_spec hinc hcmp)
      have hmin_le : min (reg2 rOut) (reg2 b) ≤ reg b := by rw [h2_b]; exact Nat.min_le_right _ _
      have hbody' : RMExec (rmDivBody qOut rOut b flag tA tB) V inp rmDivBodyEntry reg
          (Sum.inr (Sum.inr 7)) reg3 [] (4 * reg b + 9) := by
        have hstep := hbody.weaken (V₂ := V) (T₂ := 4 * reg b + 9) (by simp) (by omega)
        simpa [rmDivBody, rmDivBodyEntry, rmChainEntry, rmSeqEntry, rmRedirect, rmSub, rmSubEntry,
          rmInc, rmCopy, rmChain, rmSeq] using hstep
      have hrem_lt : rem - reg b < rem := by omega
      have hdiv_step : rem / reg b = (rem - reg b) / reg b + 1 := by
        rw [Nat.div_eq_sub_div hbpos hge]
      have hmod_step : rem % reg b = (rem - reg b) % reg b := Nat.mod_eq_sub_mod hge
      rcases ih (rem - reg b) hrem_lt (q + 1) reg3 (by rw [h3_b]; exact hbpos)
          h3_r h3_q h3_fl' hcmp.reg₁_le (by rw [h3_b]; omega)
        with ⟨reg_end, hq_e, hr_e, hfr_e, hex_rest⟩
      have hloop := rmWhile_step flag (rmDivBody qOut rOut b flag tA tB) hflne hbody' hex_rest
      have hT : 2 + (4 * reg b + 9) + (((rem - reg b) / reg3 b) * (4 * reg3 b + 11) + 2) =
          (rem / reg b) * (4 * reg b + 11) + 2 := by
        rw [h3_b, hdiv_step]; ring
      rw [max_self, List.nil_append, hT] at hloop
      refine ⟨reg_end, ?_, ?_, ?_, hloop⟩
      · rw [hq_e, h3_b, hdiv_step]; omega
      · rw [hr_e, h3_b, hmod_step]
      · intro i hiq hir hif hiA hiB
        rw [hfr_e i hiq hir hif hiA hiB, h3_fr i hif hiA hiB]
        dsimp only [reg2, reg1]
        rw [regUpd_ne _ hiq, regUpd_ne _ hiA, regUpd_ne _ hir]
    · have hlt : rem < reg b := Nat.lt_of_not_ge hge
      have hfl0 : reg flag = 0 := by rw [hfl]; simp [hge]
      have hdiv0 : rem / reg b = 0 := Nat.div_eq_of_lt hlt
      have hmod0 : rem % reg b = rem := Nat.mod_eq_of_lt hlt
      refine ⟨reg, by rw [hq, hdiv0, Nat.add_zero], by rw [hr, hmod0],
        fun _ _ _ _ _ _ => rfl, ?_⟩
      simpa [hdiv0] using rmWhile_zero flag (rmDivBody qOut rOut b flag tA tB) rmDivBodyEntry
        V inp reg hfl0 hreg

theorem rmDivMod_spec {R : ℕ} (qOut rOut a b flag tA tB : Fin R)
    (hqr : qOut ≠ rOut) (hqa : qOut ≠ a) (hqb : qOut ≠ b) (hqf : qOut ≠ flag)
    (hqA : qOut ≠ tA) (hqB : qOut ≠ tB)
    (hrb : rOut ≠ b) (hrf : rOut ≠ flag) (hrA : rOut ≠ tA) (hrB : rOut ≠ tB)
    (hbf : b ≠ flag) (hbA : b ≠ tA) (hbB : b ≠ tB)
    (hfA : flag ≠ tA) (hfB : flag ≠ tB) (hAB : tA ≠ tB)
    (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hbpos : 0 < reg b) (hreg : ∀ i, reg i ≤ V) (h1 : 1 ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ qOut = reg a / reg b ∧
      reg₁ rOut = reg a % reg b ∧
      (∀ i, i ≠ qOut → i ≠ rOut → i ≠ flag → i ≠ tA → i ≠ tB → reg₁ i = reg i) ∧
      RMExec (rmDivMod qOut rOut a b flag tA tB) V inp rmDivModEntry reg rmDivModExit reg₁ []
        (15 * reg a + 2 * reg b + 10) := by
  have hz := rmZero_spec qOut V inp reg hreg
  set reg1 := regUpd reg qOut 0
  have h1_a : reg1 a = reg a := regUpd_ne reg hqa.symm _
  have h1_b : reg1 b = reg b := regUpd_ne reg hqb.symm _
  have hcp := rmCopy_spec rOut a V inp reg1 hz.reg₁_le
  set reg2 := regUpd reg1 rOut (reg1 a)
  have h2_r : reg2 rOut = reg a := by dsimp only [reg2]; rw [regUpd_self, h1_a]
  have h2_b : reg2 b = reg b := by dsimp only [reg2]; rw [regUpd_ne _ hrb.symm, h1_b]
  have h2_q : reg2 qOut = 0 := by dsimp only [reg2, reg1]; rw [regUpd_ne _ hqr, regUpd_self]
  rcases rmCmpGe_spec flag rOut b tA tB hAB hfA hfB hbA V inp reg2 hcp.reg₁_le h1
    with ⟨reg3, h3_fl, h3_fr, hcmp⟩
  have h3_r : reg3 rOut = reg a := by rw [h3_fr rOut hrf hrA hrB, h2_r]
  have h3_b : reg3 b = reg b := by rw [h3_fr b hbf hbA hbB, h2_b]
  have h3_q : reg3 qOut = 0 := by rw [h3_fr qOut hqf hqA hqB, h2_q]
  have h3_fl' : reg3 flag = (if reg3 b ≤ reg a then 1 else 0) := by
    rw [h3_fl, h2_r, h2_b, h3_b]
  have hdiv_le : 0 + reg a / reg3 b ≤ V := by
    rw [Nat.zero_add]; exact le_trans (Nat.div_le_self _ _) (hreg a)
  rcases rmDivMod_loop_spec qOut rOut b flag tA tB hqr hqb hqf hqA hqB hrb hrf hrA hrB hbf hbA hbB
      hfA hfB hAB V inp h1 (reg a) 0 reg3 (by rw [h3_b]; exact hbpos) h3_r h3_q h3_fl'
      hcmp.reg₁_le hdiv_le
    with ⟨reg_end, hq_e, hr_e, hfr_e, hloop⟩
  have hcomb := rmChain_spec hz (rmChain_spec hcp (rmChain_spec hcmp hloop))
  have hT_le : 1 + (1 + ((2 * min (reg2 rOut) (reg2 b) + 6) +
      ((reg a / reg3 b) * (4 * reg3 b + 11) + 2))) ≤ 15 * reg a + 2 * reg b + 10 := by
    rw [h2_r, h2_b, h3_b]
    have hmin : min (reg a) (reg b) ≤ reg b := Nat.min_le_right _ _
    have hmul : (reg a / reg b) * reg b ≤ reg a := Nat.div_mul_le_self (reg a) (reg b)
    have hdiv : reg a / reg b ≤ reg a := Nat.div_le_self (reg a) (reg b)
    have hexp : (reg a / reg b) * (4 * reg b + 11) = 4 * ((reg a / reg b) * reg b) + 11 * (reg a / reg b) := by ring
    omega
  have hcomb' := hcomb.weaken (V₂ := V) (T₂ := 15 * reg a + 2 * reg b + 10) (by simp) hT_le
  refine ⟨reg_end, by rw [hq_e, h3_b, Nat.zero_add], by rw [hr_e, h3_b], ?_, ?_⟩
  · intro i hiq hir hif hiA hiB
    rw [hfr_e i hiq hir hif hiA hiB, h3_fr i hif hiA hiB]
    dsimp only [reg2, reg1]
    rw [regUpd_ne _ hir, regUpd_ne _ hiq]
  · simpa [rmDivMod, rmDivModEntry, rmDivModExit, rmChainEntry, rmSeqEntry, rmRedirect,
      rmZero, rmCopy, rmCmpGe, rmCmp, rmChain, rmSeq] using hcomb'

/-! ### `rmPow` (Exponentiation `dst := base ^ exp`) -/

abbrev RMPowBodyQ : Type := RMMulQ ⊕ Bool
abbrev RMPowQ : Type := RMSetConstQ 1 ⊕ (Bool ⊕ (Option Bool ⊕ (Unit ⊕ RMPowBodyQ)))

def rmPowBody {R : ℕ} (dst base tmpProd tmp1 tmp2 : Fin R) : RMProg R RMPowBodyQ :=
  rmChain (rmMul tmpProd dst base tmp1 tmp2) (rmCopy dst tmpProd) false

def rmPowBodyEntry : RMPowBodyQ := Sum.inl rmMulEntry

/-- `rmPow dst base exp tmpExp tmpProd tmp1 tmp2`: sets `dst := base ^ exp`. -/
def rmPow {R : ℕ} (dst base exp tmpExp tmpProd tmp1 tmp2 : Fin R) : RMProg R RMPowQ :=
  rmChain (rmSetConst dst 1)
    (rmChain (rmCopy tmpExp exp)
      (rmWhileDec tmpExp (rmPowBody dst base tmpProd tmp1 tmp2) rmPowBodyEntry) rmWhileDecEntry)
    (Sum.inl false)

def rmPowEntry : RMPowQ := Sum.inl rmSetConstEntry
def rmPowExit : RMPowQ := Sum.inr (Sum.inr rmWhileDecExit)

lemma rmPow_loop_spec {R : ℕ} (dst base tmpExp tmpProd tmp1 tmp2 : Fin R)
    (hdb : dst ≠ base) (hdE : dst ≠ tmpExp) (hdP : dst ≠ tmpProd) (hd1 : dst ≠ tmp1) (hd2 : dst ≠ tmp2)
    (hbE : base ≠ tmpExp) (hbP : base ≠ tmpProd) (hb1 : base ≠ tmp1) (hb2 : base ≠ tmp2)
    (hEP : tmpExp ≠ tmpProd) (hE1 : tmpExp ≠ tmp1) (hE2 : tmpExp ≠ tmp2)
    (hP1 : tmpProd ≠ tmp1) (hP2 : tmpProd ≠ tmp2) (h12 : tmp1 ≠ tmp2)
    (V : ℕ) (inp : List Bool) :
    ∀ (k : ℕ) (reg : RegState R),
      reg tmpExp = k → (∀ i, reg i ≤ V) →
      (∀ m ≤ k, reg dst * reg base ^ m ≤ V) →
      ∃ reg₁ : RegState R,
        reg₁ dst = reg dst * reg base ^ k ∧
        (∀ i, i ≠ dst → i ≠ tmpExp → i ≠ tmpProd → i ≠ tmp1 → i ≠ tmp2 → reg₁ i = reg i) ∧
        RMExec (rmWhileDec tmpExp (rmPowBody dst base tmpProd tmp1 tmp2) rmPowBodyEntry) V inp
          rmWhileDecEntry reg rmWhileDecExit reg₁ []
          (k * (V * (2 * reg base + 3) + 5) + 1)
  | 0, reg, hE, hreg, _ =>
    ⟨reg, by simp, fun _ _ _ _ _ _ => rfl, by
      simpa using rmWhileDec_zero tmpExp (rmPowBody dst base tmpProd tmp1 tmp2) rmPowBodyEntry V inp reg hE hreg⟩
  | k + 1, reg, hE, hreg, hpow => by
    have hne : reg tmpExp ≠ 0 := by omega
    set reg1 := regUpd reg tmpExp (reg tmpExp - 1)
    have hreg1 : ∀ i, reg1 i ≤ V := regUpd_le hreg tmpExp (le_trans (Nat.sub_le _ _) (hreg tmpExp))
    have h1_d : reg1 dst = reg dst := regUpd_ne reg hdE _
    have h1_b : reg1 base = reg base := regUpd_ne reg hbE _
    have h1_E : reg1 tmpExp = k := by dsimp only [reg1]; rw [regUpd_self]; omega
    have hmul_le : reg1 dst * reg1 base ≤ V := by
      rw [h1_d, h1_b]; simpa using hpow 1 (by omega)
    rcases rmMul_spec tmpProd dst base tmp1 tmp2 hdP.symm hbP.symm hP1 hP2 hb1 hb2 h12 V inp reg1 hreg1 hmul_le
      with ⟨reg2, h2_P, h2_fr, hmul⟩
    have h2_d : reg2 dst = reg dst := by rw [h2_fr dst hdP hd1 hd2, h1_d]
    have h2_b : reg2 base = reg base := by rw [h2_fr base hbP hb1 hb2, h1_b]
    have h2_E : reg2 tmpExp = k := by rw [h2_fr tmpExp hEP hE1 hE2, h1_E]
    have hcp := rmCopy_spec dst tmpProd V inp reg2 hmul.reg₁_le
    set reg3 := regUpd reg2 dst (reg2 tmpProd)
    have h3_d : reg3 dst = reg dst * reg base := by
      dsimp only [reg3]; rw [regUpd_self, h2_P, h1_d, h1_b]
    have h3_b : reg3 base = reg base := by dsimp only [reg3]; rw [regUpd_ne _ hdb.symm, h2_b]
    have h3_E : reg3 tmpExp = k := by dsimp only [reg3]; rw [regUpd_ne _ hdE.symm, h2_E]
    have hbody := rmChain_spec hmul hcp
    have hbody_T : reg1 dst * (2 * reg1 base + 3) + 3 + 1 ≤ V * (2 * reg base + 3) + 4 := by
      rw [h1_d, h1_b]
      have hdV : reg dst ≤ V := hreg dst
      have := Nat.mul_le_mul_right (2 * reg base + 3) hdV
      omega
    have hbody' : RMExec (rmPowBody dst base tmpProd tmp1 tmp2) V inp rmPowBodyEntry reg1
        (Sum.inr true) reg3 [] (V * (2 * reg base + 3) + 4) := by
      have hw := hbody.weaken (V₂ := V) (T₂ := V * (2 * reg base + 3) + 4) (by simp) hbody_T
      simpa [rmPowBody, rmPowBodyEntry, rmChainEntry, rmSeqEntry, rmRedirect, rmMul, rmMulEntry,
        rmZero, rmChain, rmSeq] using hw
    have hpow3 : ∀ m ≤ k, reg3 dst * reg3 base ^ m ≤ V := by
      intro m hm
      rw [h3_d, h3_b]
      have heq : reg dst * reg base * reg base ^ m = reg dst * reg base ^ (m + 1) := by
        rw [pow_succ', mul_assoc]
      rw [heq]
      exact hpow (m + 1) (by omega)
    rcases rmPow_loop_spec dst base tmpExp tmpProd tmp1 tmp2
        hdb hdE hdP hd1 hd2 hbE hbP hb1 hb2 hEP hE1 hE2 hP1 hP2 h12 V inp k reg3 h3_E hcp.reg₁_le hpow3
      with ⟨reg_end, hd_e, hfr_e, hex_rest⟩
    have hstep := rmWhileDec_step tmpExp (rmPowBody dst base tmpProd tmp1 tmp2) hne hreg hbody' hex_rest
    have hT : 1 + (V * (2 * reg base + 3) + 4) + (k * (V * (2 * reg3 base + 3) + 5) + 1) =
        (k + 1) * (V * (2 * reg base + 3) + 5) + 1 := by
      rw [h3_b]; ring
    rw [max_self, List.nil_append, hT] at hstep
    refine ⟨reg_end, ?_, ?_, hstep⟩
    · rw [hd_e, h3_d, h3_b, pow_succ', mul_assoc]
    · intro i hid hiE hiP hi1 hi2
      rw [hfr_e i hid hiE hiP hi1 hi2]
      dsimp only [reg3]
      rw [regUpd_ne _ hid, h2_fr i hiP hi1 hi2]
      dsimp only [reg1]
      rw [regUpd_ne _ hiE]

theorem rmPow_spec {R : ℕ} (dst base exp tmpExp tmpProd tmp1 tmp2 : Fin R)
    (hdb : dst ≠ base) (hde : dst ≠ exp) (hdE : dst ≠ tmpExp) (hdP : dst ≠ tmpProd)
    (hd1 : dst ≠ tmp1) (hd2 : dst ≠ tmp2)
    (hbE : base ≠ tmpExp) (hbP : base ≠ tmpProd) (hb1 : base ≠ tmp1) (hb2 : base ≠ tmp2)
    (hEP : tmpExp ≠ tmpProd) (hE1 : tmpExp ≠ tmp1) (hE2 : tmpExp ≠ tmp2)
    (hP1 : tmpProd ≠ tmp1) (hP2 : tmpProd ≠ tmp2) (h12 : tmp1 ≠ tmp2)
    (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) (h1 : 1 ≤ V) (hpow : reg base ^ reg exp ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ dst = reg base ^ reg exp ∧
      (∀ i, i ≠ dst → i ≠ tmpExp → i ≠ tmpProd → i ≠ tmp1 → i ≠ tmp2 → reg₁ i = reg i) ∧
      RMExec (rmPow dst base exp tmpExp tmpProd tmp1 tmp2) V inp rmPowEntry reg rmPowExit reg₁ []
        (reg exp * (V * (2 * reg base + 3) + 5) + 4) := by
  have hs1 := rmSetConst_spec dst 1 V inp reg hreg h1
  set reg1 := regUpd reg dst 1
  have h1_e : reg1 exp = reg exp := regUpd_ne reg hde.symm _
  have h1_b : reg1 base = reg base := regUpd_ne reg hdb.symm _
  have hcp := rmCopy_spec tmpExp exp V inp reg1 hs1.reg₁_le
  set reg2 := regUpd reg1 tmpExp (reg1 exp)
  have h2_d : reg2 dst = 1 := by dsimp only [reg2, reg1]; rw [regUpd_ne _ hdE, regUpd_self]
  have h2_b : reg2 base = reg base := by dsimp only [reg2]; rw [regUpd_ne _ hbE, h1_b]
  have h2_E : reg2 tmpExp = reg exp := by dsimp only [reg2]; rw [regUpd_self, h1_e]
  have hpow2 : ∀ m ≤ reg exp, reg2 dst * reg2 base ^ m ≤ V := by
    intro m hm
    rw [h2_d, h2_b, Nat.one_mul]
    rcases Nat.eq_zero_or_pos (reg base) with hb0 | hbpos
    · rw [hb0]; cases m with | zero => simpa using h1 | succ _ => simp
    · exact le_trans (Nat.pow_le_pow_right hbpos hm) hpow
  rcases rmPow_loop_spec dst base tmpExp tmpProd tmp1 tmp2
      hdb hdE hdP hd1 hd2 hbE hbP hb1 hb2 hEP hE1 hE2 hP1 hP2 h12 V inp (reg exp) reg2
      h2_E hcp.reg₁_le hpow2
    with ⟨reg_end, hd_e, hfr_e, hloop⟩
  have hcomb := rmChain_spec hs1 (rmChain_spec hcp hloop)
  have hT : 1 + 1 + (1 + (reg exp * (V * (2 * reg2 base + 3) + 5) + 1)) =
      reg exp * (V * (2 * reg base + 3) + 5) + 4 := by
    rw [h2_b]; ring
  rw [max_self, max_self, List.nil_append, List.nil_append, hT] at hcomb
  refine ⟨reg_end, by rw [hd_e, h2_d, h2_b, Nat.one_mul], ?_, ?_⟩
  · intro i hid hiE hiP hi1 hi2
    rw [hfr_e i hid hiE hiP hi1 hi2]
    dsimp only [reg2, reg1]
    rw [regUpd_ne _ hiE, regUpd_ne _ hid]
  · simpa [rmPow, rmPowEntry, rmPowExit, rmChainEntry, rmSeqEntry, rmRedirect,
      rmSetConst, rmSetConstEntry, rmZero, rmCopy, rmChain, rmSeq] using hcomb

/-! ### `rmMinPowExp` (`dst := minPowExp base target`) -/

abbrev RMMinPowBodyQ : Type := Bool ⊕ (RMMulQ ⊕ (Bool ⊕ Fin 8))
abbrev RMMinPowExpQ : Type :=
  Bool ⊕ (RMSetConstQ 1 ⊕ (Fin 8 ⊕ (Option Bool ⊕ (Unit ⊕ (Bool ⊕ RMMinPowBodyQ)))))

def rmMinPowBody {R : ℕ} (dst base target powReg flag tmpProd tmp1 tmp2 : Fin R) :
    RMProg R RMMinPowBodyQ :=
  rmChain (rmInc dst)
    (rmChain (rmMul tmpProd powReg base tmp1 tmp2)
      (rmChain (rmCopy powReg tmpProd) (rmCmpLt flag powReg target tmp1 tmp2) 0)
      (Sum.inl false))
    (Sum.inl rmMulEntry)

def rmMinPowBodyEntry : RMMinPowBodyQ := Sum.inl false

/-- `rmMinPowExp dst base target powReg flag tmpProd tmp1 tmp2`:
computes `dst := minPowExp base target` and `powReg := base ^ (minPowExp base target)` for `2 ≤ base`. -/
def rmMinPowExp {R : ℕ} (dst base target powReg flag tmpProd tmp1 tmp2 : Fin R) :
    RMProg R RMMinPowExpQ :=
  rmChain (rmZero dst)
    (rmChain (rmSetConst powReg 1)
      (rmChain (rmCmpLt flag powReg target tmp1 tmp2)
        (rmWhile flag (rmMinPowBody dst base target powReg flag tmpProd tmp1 tmp2) rmMinPowBodyEntry)
        rmWhileEntry)
      (Sum.inl 0))
    (Sum.inl rmSetConstEntry)

def rmMinPowExpEntry : RMMinPowExpQ := Sum.inl false
def rmMinPowExpExit : RMMinPowExpQ := Sum.inr (Sum.inr (Sum.inr rmWhileExit))

lemma rmMinPowExp_loop_spec {R : ℕ} (dst base target powReg flag tmpProd tmp1 tmp2 : Fin R)
    (hdb : dst ≠ base) (hdt : dst ≠ target) (hdP : dst ≠ powReg) (hdf : dst ≠ flag)
    (hdPr : dst ≠ tmpProd) (hd1 : dst ≠ tmp1) (hd2 : dst ≠ tmp2)
    (hbP : base ≠ powReg) (hbf : base ≠ flag) (hbPr : base ≠ tmpProd) (hb1 : base ≠ tmp1) (hb2 : base ≠ tmp2)
    (htP : target ≠ powReg) (htf : target ≠ flag) (htPr : target ≠ tmpProd) (ht1 : target ≠ tmp1) (ht2 : target ≠ tmp2)
    (hPf : powReg ≠ flag) (hPPr : powReg ≠ tmpProd) (hP1 : powReg ≠ tmp1) (hP2 : powReg ≠ tmp2)
    (hfPr : flag ≠ tmpProd) (hf1 : flag ≠ tmp1) (hf2 : flag ≠ tmp2)
    (hPr1 : tmpProd ≠ tmp1) (hPr2 : tmpProd ≠ tmp2) (h12 : tmp1 ≠ tmp2)
    (V : ℕ) (inp : List Bool) (h1 : 1 ≤ V) :
    ∀ (rem e : ℕ) (reg : RegState R),
      2 ≤ reg base →
      e + rem = minPowExp (reg base) (reg target) →
      reg dst = e → reg powReg = reg base ^ e →
      reg flag = (if reg base ^ e < reg target then 1 else 0) →
      (∀ i, reg i ≤ V) → reg base * reg target ≤ V →
      ∃ reg₁ : RegState R,
        reg₁ dst = minPowExp (reg base) (reg target) ∧
        reg₁ powReg = reg base ^ minPowExp (reg base) (reg target) ∧
        (∀ i, i ≠ dst → i ≠ powReg → i ≠ flag → i ≠ tmpProd → i ≠ tmp1 → i ≠ tmp2 → reg₁ i = reg i) ∧
        RMExec (rmWhile flag (rmMinPowBody dst base target powReg flag tmpProd tmp1 tmp2) rmMinPowBodyEntry)
          V inp rmWhileEntry reg rmWhileExit reg₁ []
          (rem * (reg target * (2 * reg base + 5) + 13) + 2)
  | 0, e, reg, hb2le, her, hd, hP, hfl, hreg, _ => by
    have he_eq : e = minPowExp (reg base) (reg target) := by omega
    have hge : reg target ≤ reg base ^ e := by rw [he_eq]; exact minPowExp_le_pow hb2le (reg target)
    have hfl0 : reg flag = 0 := by rw [hfl]; simp [Nat.not_lt.mpr hge]
    refine ⟨reg, by rw [hd, he_eq], by rw [hP, he_eq], fun _ _ _ _ _ _ _ => rfl, ?_⟩
    simpa using rmWhile_zero flag _ _ V inp reg hfl0 hreg
  | rem + 1, e, reg, hb2le, her, hd, hP, hfl, hreg, hbtV => by
    have hlt_e : e < minPowExp (reg base) (reg target) := by omega
    have hpow_lt : reg base ^ e < reg target := lt_of_lt_minPowExp hb2le hlt_e
    have hfl1 : reg flag = 1 := by rw [hfl]; simp [hpow_lt]
    have hflne : reg flag ≠ 0 := by omega
    have he1_le : e + 1 ≤ V := by
      have hm := minPowExp_le_self hb2le (reg target)
      have htb : reg target ≤ reg base * reg target := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hinc := rmInc_spec dst V inp reg hreg (by rw [hd]; exact he1_le)
    set reg1 := regUpd reg dst (reg dst + 1)
    have h1_d : reg1 dst = e + 1 := by dsimp only [reg1]; rw [regUpd_self, hd]
    have h1_b : reg1 base = reg base := regUpd_ne reg hdb.symm _
    have h1_t : reg1 target = reg target := regUpd_ne reg hdt.symm _
    have h1_P : reg1 powReg = reg base ^ e := by dsimp only [reg1]; rw [regUpd_ne _ hdP.symm, hP]
    have hmul_le : reg1 powReg * reg1 base ≤ V := by
      rw [h1_P, h1_b]
      have : reg base ^ e * reg base ≤ reg target * reg base := Nat.mul_le_mul_right _ (le_of_lt hpow_lt)
      have hcomm : reg target * reg base = reg base * reg target := Nat.mul_comm _ _
      omega
    rcases rmMul_spec tmpProd powReg base tmp1 tmp2 hPPr.symm hbPr.symm hPr1 hPr2 hb1 hb2 h12 V inp reg1
        hinc.reg₁_le hmul_le
      with ⟨reg2, h2_Pr, h2_fr, hmul⟩
    have h2_d : reg2 dst = e + 1 := by rw [h2_fr dst hdPr hd1 hd2, h1_d]
    have h2_b : reg2 base = reg base := by rw [h2_fr base hbPr hb1 hb2, h1_b]
    have h2_t : reg2 target = reg target := by rw [h2_fr target htPr ht1 ht2, h1_t]
    have hcp := rmCopy_spec powReg tmpProd V inp reg2 hmul.reg₁_le
    set reg3 := regUpd reg2 powReg (reg2 tmpProd)
    have h3_P : reg3 powReg = reg base ^ (e + 1) := by
      dsimp only [reg3]; rw [regUpd_self, h2_Pr, h1_P, h1_b, pow_succ]
    have h3_d : reg3 dst = e + 1 := by dsimp only [reg3]; rw [regUpd_ne _ hdP, h2_d]
    have h3_b : reg3 base = reg base := by dsimp only [reg3]; rw [regUpd_ne _ hbP, h2_b]
    have h3_t : reg3 target = reg target := by dsimp only [reg3]; rw [regUpd_ne _ htP, h2_t]
    rcases rmCmpLt_spec flag powReg target tmp1 tmp2 h12 hf1 hf2 ht1 V inp reg3 hcp.reg₁_le h1
      with ⟨reg4, h4_fl, h4_fr, hcmp⟩
    have h4_d : reg4 dst = e + 1 := by rw [h4_fr dst hdf hd1 hd2, h3_d]
    have h4_b : reg4 base = reg base := by rw [h4_fr base hbf hb1 hb2, h3_b]
    have h4_t : reg4 target = reg target := by rw [h4_fr target htf ht1 ht2, h3_t]
    have h4_P : reg4 powReg = reg base ^ (e + 1) := by rw [h4_fr powReg hPf hP1 hP2, h3_P]
    have h4_fl' : reg4 flag = (if reg4 base ^ (e + 1) < reg4 target then 1 else 0) := by
      rw [h4_fl, h3_P, h3_t, h4_b, h4_t]
    have hbody := rmChain_spec hinc (rmChain_spec hmul (rmChain_spec hcp hcmp))
    have hbody_T : 1 + (reg1 powReg * (2 * reg1 base + 3) + 3 + (1 + (2 * min (reg3 powReg) (reg3 target) + 6))) ≤
        reg target * (2 * reg base + 5) + 11 := by
      rw [h1_P, h1_b, h3_t]
      have hmin : min (reg3 powReg) (reg target) ≤ reg target := Nat.min_le_right _ _
      have hmul1 : reg base ^ e * (2 * reg base + 3) ≤ reg target * (2 * reg base + 3) :=
        Nat.mul_le_mul_right _ (le_of_lt hpow_lt)
      have hlin : reg target * (2 * reg base + 5) = reg target * (2 * reg base + 3) + 2 * reg target := by ring
      omega
    have hbody' : RMExec (rmMinPowBody dst base target powReg flag tmpProd tmp1 tmp2) V inp
        rmMinPowBodyEntry reg (Sum.inr (Sum.inr (Sum.inr 7))) reg4 []
        (reg target * (2 * reg base + 5) + 11) := by
      have hw := hbody.weaken (V₂ := V) (T₂ := reg target * (2 * reg base + 5) + 11) (by simp) hbody_T
      simpa [rmMinPowBody, rmMinPowBodyEntry, rmChainEntry, rmSeqEntry, rmRedirect,
        rmInc, rmMul, rmMulEntry, rmZero, rmCopy, rmChain, rmSeq] using hw
    rcases rmMinPowExp_loop_spec dst base target powReg flag tmpProd tmp1 tmp2
        hdb hdt hdP hdf hdPr hd1 hd2 hbP hbf hbPr hb1 hb2 htP htf htPr ht1 ht2
        hPf hPPr hP1 hP2 hfPr hf1 hf2 hPr1 hPr2 h12 V inp h1 rem (e + 1) reg4
        (by rw [h4_b]; exact hb2le) (by rw [h4_b, h4_t]; omega) h4_d (by rw [h4_b]; exact h4_P)
        h4_fl' hcmp.reg₁_le (by rw [h4_b, h4_t]; exact hbtV)
      with ⟨reg_end, hd_e, hP_e, hfr_e, hex_rest⟩
    have hstep := rmWhile_step flag (rmMinPowBody dst base target powReg flag tmpProd tmp1 tmp2)
      hflne hbody' hex_rest
    have hT : 2 + (reg target * (2 * reg base + 5) + 11) +
        (rem * (reg4 target * (2 * reg4 base + 5) + 13) + 2) =
        (rem + 1) * (reg target * (2 * reg base + 5) + 13) + 2 := by
      rw [h4_b, h4_t]; ring
    rw [max_self, List.nil_append, hT] at hstep
    refine ⟨reg_end, by rw [hd_e, h4_b, h4_t], by rw [hP_e, h4_b, h4_t], ?_, hstep⟩
    intro i hid hiP hif hiPr hi1 hi2
    rw [hfr_e i hid hiP hif hiPr hi1 hi2, h4_fr i hif hi1 hi2]
    dsimp only [reg3]
    rw [regUpd_ne _ hiP, h2_fr i hiPr hi1 hi2]
    dsimp only [reg1]
    rw [regUpd_ne _ hid]

theorem rmMinPowExp_spec {R : ℕ} (dst base target powReg flag tmpProd tmp1 tmp2 : Fin R)
    (hdb : dst ≠ base) (hdt : dst ≠ target) (hdP : dst ≠ powReg) (hdf : dst ≠ flag)
    (hdPr : dst ≠ tmpProd) (hd1 : dst ≠ tmp1) (hd2 : dst ≠ tmp2)
    (hbP : base ≠ powReg) (hbf : base ≠ flag) (hbPr : base ≠ tmpProd) (hb1 : base ≠ tmp1) (hb2 : base ≠ tmp2)
    (htP : target ≠ powReg) (htf : target ≠ flag) (htPr : target ≠ tmpProd) (ht1 : target ≠ tmp1) (ht2 : target ≠ tmp2)
    (hPf : powReg ≠ flag) (hPPr : powReg ≠ tmpProd) (hP1 : powReg ≠ tmp1) (hP2 : powReg ≠ tmp2)
    (hfPr : flag ≠ tmpProd) (hf1 : flag ≠ tmp1) (hf2 : flag ≠ tmp2)
    (hPr1 : tmpProd ≠ tmp1) (hPr2 : tmpProd ≠ tmp2) (h12 : tmp1 ≠ tmp2)
    (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hb2le : 2 ≤ reg base) (hreg : ∀ i, reg i ≤ V) (h1 : 1 ≤ V) (hbtV : reg base * reg target ≤ V) :
    ∃ reg₁ : RegState R,
      reg₁ dst = minPowExp (reg base) (reg target) ∧
      reg₁ powReg = reg base ^ minPowExp (reg base) (reg target) ∧
      (∀ i, i ≠ dst → i ≠ powReg → i ≠ flag → i ≠ tmpProd → i ≠ tmp1 → i ≠ tmp2 → reg₁ i = reg i) ∧
      RMExec (rmMinPowExp dst base target powReg flag tmpProd tmp1 tmp2) V inp
        rmMinPowExpEntry reg rmMinPowExpExit reg₁ []
        (reg target * (reg target * (2 * reg base + 5) + 15) + 11) := by
  have hz := rmZero_spec dst V inp reg hreg
  set reg1 := regUpd reg dst 0
  have hs1 := rmSetConst_spec powReg 1 V inp reg1 hz.reg₁_le h1
  set reg2 := regUpd reg1 powReg 1
  have h2_d : reg2 dst = 0 := by dsimp only [reg2, reg1]; rw [regUpd_ne _ hdP, regUpd_self]
  have h2_b : reg2 base = reg base := by dsimp only [reg2, reg1]; rw [regUpd_ne _ hbP, regUpd_ne _ hdb.symm]
  have h2_t : reg2 target = reg target := by dsimp only [reg2, reg1]; rw [regUpd_ne _ htP, regUpd_ne _ hdt.symm]
  have h2_P : reg2 powReg = 1 := regUpd_self _ _ _
  rcases rmCmpLt_spec flag powReg target tmp1 tmp2 h12 hf1 hf2 ht1 V inp reg2 hs1.reg₁_le h1
    with ⟨reg3, h3_fl, h3_fr, hcmp⟩
  have h3_d : reg3 dst = 0 := by rw [h3_fr dst hdf hd1 hd2, h2_d]
  have h3_b : reg3 base = reg base := by rw [h3_fr base hbf hb1 hb2, h2_b]
  have h3_t : reg3 target = reg target := by rw [h3_fr target htf ht1 ht2, h2_t]
  have h3_P : reg3 powReg = reg3 base ^ 0 := by
    rw [pow_zero, h3_fr powReg hPf hP1 hP2, h2_P]
  have h3_fl' : reg3 flag = (if reg3 base ^ 0 < reg3 target then 1 else 0) := by
    rw [h3_fl, h2_P, h2_t, h3_t, pow_zero]
  rcases rmMinPowExp_loop_spec dst base target powReg flag tmpProd tmp1 tmp2
      hdb hdt hdP hdf hdPr hd1 hd2 hbP hbf hbPr hb1 hb2 htP htf htPr ht1 ht2
      hPf hPPr hP1 hP2 hfPr hf1 hf2 hPr1 hPr2 h12 V inp h1
      (minPowExp (reg base) (reg target)) 0 reg3
      (by rw [h3_b]; exact hb2le) (by rw [h3_b, h3_t]; omega)
      h3_d h3_P h3_fl' hcmp.reg₁_le (by rw [h3_b, h3_t]; exact hbtV)
    with ⟨reg_end, hd_e, hP_e, hfr_e, hloop⟩
  have hcomb := rmChain_spec hz (rmChain_spec hs1 (rmChain_spec hcmp hloop))
  have hT_le : 1 + (1 + 1 + ((2 * min (reg2 powReg) (reg2 target) + 6) +
      (minPowExp (reg base) (reg target) * (reg3 target * (2 * reg3 base + 5) + 13) + 2))) ≤
      reg target * (reg target * (2 * reg base + 5) + 15) + 11 := by
    rw [h2_t, h3_b, h3_t]
    have hmin : min (reg2 powReg) (reg target) ≤ reg target := Nat.min_le_right _ _
    have hmle : minPowExp (reg base) (reg target) ≤ reg target := minPowExp_le_self hb2le (reg target)
    have hmul : minPowExp (reg base) (reg target) * (reg target * (2 * reg base + 5) + 13) ≤
        reg target * (reg target * (2 * reg base + 5) + 13) :=
      Nat.mul_le_mul_right _ hmle
    have hlin : reg target * (reg target * (2 * reg base + 5) + 15) =
        reg target * (reg target * (2 * reg base + 5) + 13) + 2 * reg target := by ring
    omega
  have hcomb' := hcomb.weaken (V₂ := V) (T₂ := reg target * (reg target * (2 * reg base + 5) + 15) + 11)
    (by simp) hT_le
  refine ⟨reg_end, by rw [hd_e, h3_b, h3_t], by rw [hP_e, h3_b, h3_t], ?_, ?_⟩
  · intro i hid hiP hif hiPr hi1 hi2
    rw [hfr_e i hid hiP hif hiPr hi1 hi2, h3_fr i hif hi1 hi2]
    dsimp only [reg2, reg1]
    rw [regUpd_ne _ hiP, regUpd_ne _ hid]
  · simpa [rmMinPowExp, rmMinPowExpEntry, rmMinPowExpExit, rmChainEntry, rmSeqEntry,
      rmRedirect, rmZero, rmSetConst, rmSetConstEntry, rmCmpLt, rmCmp, rmChain, rmSeq] using hcomb'

/-! ### Bit-Emission Macros (`rmEmitTrueRepeat`, `rmEmitUnary`, `rmEmitBits`, `rmEmitGate`) -/

abbrev RMEmitRepeatQ : Type := Bool ⊕ (Option Bool ⊕ (Unit ⊕ Bool))

/-- `rmEmitTrueRepeat r tmp`: emits `List.replicate (reg r) true`, preserves `r`, clears `tmp := 0`. -/
def rmEmitTrueRepeat {R : ℕ} (r tmp : Fin R) : RMProg R RMEmitRepeatQ :=
  rmChain (rmCopy tmp r) (rmWhileDec tmp (rmEmit true) false) rmWhileDecEntry

def rmEmitTrueRepeatEntry : RMEmitRepeatQ := Sum.inl false
def rmEmitTrueRepeatExit : RMEmitRepeatQ := Sum.inr rmWhileDecExit

lemma rmEmitTrueRepeat_loop {R : ℕ} (tmp : Fin R) (V : ℕ) (inp : List Bool) :
    ∀ (k : ℕ) (reg : RegState R),
      reg tmp = k → (∀ i, reg i ≤ V) →
      RMExec (rmWhileDec tmp (rmEmit true) false) V inp rmWhileDecEntry reg rmWhileDecExit
        (regUpd reg tmp 0) (List.replicate k true) (2 * k + 1)
  | 0, reg, htmp, hreg => by
    have hupd : regUpd reg tmp 0 = reg := by rw [← htmp, regUpd_eq_self]
    rw [hupd]
    exact rmWhileDec_zero tmp (rmEmit true) false V inp reg htmp hreg
  | k + 1, reg, htmp, hreg => by
    have hne : reg tmp ≠ 0 := by omega
    set reg1 := regUpd reg tmp (reg tmp - 1)
    have hreg1 : ∀ i, reg1 i ≤ V := regUpd_le hreg tmp (le_trans (Nat.sub_le _ _) (hreg tmp))
    have h1_tmp : reg1 tmp = k := by dsimp only [reg1]; rw [regUpd_self]; omega
    have hem := rmEmit_spec true V inp reg1 hreg1
    have hrest := rmEmitTrueRepeat_loop tmp V inp k reg1 h1_tmp hreg1
    have hupd : regUpd reg1 tmp 0 = regUpd reg tmp 0 := by dsimp only [reg1]; simp
    rw [hupd] at hrest
    have hstep := rmWhileDec_step tmp (rmEmit true) hne hreg hem hrest
    simpa [max_self, List.replicate_succ, show 1 + 1 + (2 * k + 1) = 2 * (k + 1) + 1 by omega] using hstep

theorem rmEmitTrueRepeat_spec {R : ℕ} (r tmp : Fin R) (hrt : r ≠ tmp)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmEmitTrueRepeat r tmp) V inp rmEmitTrueRepeatEntry reg rmEmitTrueRepeatExit
      (regUpd reg tmp 0) (List.replicate (reg r) true) (2 * reg r + 2) := by
  have _ := hrt
  have hcp := rmCopy_spec tmp r V inp reg hreg
  set reg1 := regUpd reg tmp (reg r)
  have hloop := rmEmitTrueRepeat_loop tmp V inp (reg r) reg1 (regUpd_self _ _ _) hcp.reg₁_le
  have hupd : regUpd reg1 tmp 0 = regUpd reg tmp 0 := by dsimp only [reg1]; simp
  rw [hupd] at hloop
  have hcomb := rmChain_spec hcp hloop
  simpa [rmEmitTrueRepeat, rmEmitTrueRepeatEntry, rmEmitTrueRepeatExit, rmChainEntry,
    rmSeqEntry, rmRedirect, rmCopy, max_self, show 1 + (2 * reg r + 1) = 2 * reg r + 2 by omega] using hcomb

abbrev RMEmitUnaryQ : Type := RMEmitRepeatQ ⊕ Bool

/-- `rmEmitUnary r tmp`: emits `QCSD_natToUnary (reg r)`, preserves `r`, clears `tmp := 0`. -/
def rmEmitUnary {R : ℕ} (r tmp : Fin R) : RMProg R RMEmitUnaryQ :=
  rmChain (rmEmitTrueRepeat r tmp) (rmEmit false) false

def rmEmitUnaryEntry : RMEmitUnaryQ := Sum.inl rmEmitTrueRepeatEntry
def rmEmitUnaryExit : RMEmitUnaryQ := Sum.inr true

theorem rmEmitUnary_spec {R : ℕ} (r tmp : Fin R) (hrt : r ≠ tmp)
    (V : ℕ) (inp : List Bool) (reg : RegState R) (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmEmitUnary r tmp) V inp rmEmitUnaryEntry reg rmEmitUnaryExit
      (regUpd reg tmp 0) (QCSD_natToUnary (reg r)) (2 * reg r + 3) := by
  have hrep := rmEmitTrueRepeat_spec r tmp hrt V inp reg hreg
  have hf := rmEmit_spec false V inp (regUpd reg tmp 0) hrep.reg₁_le
  have hcomb := rmChain_spec hrep hf
  simpa [rmEmitUnary, rmEmitUnaryEntry, rmEmitUnaryExit, rmChainEntry, rmSeqEntry,
    rmRedirect, rmEmitTrueRepeat, rmEmitTrueRepeatEntry, rmCopy, rmChain, rmSeq,
    QCSD_natToUnary, max_self] using hcomb

/-- `rmEmitBits bs`: emits a compile-time constant bit list `bs` in `bs.length` steps, preserving all registers. -/
def rmEmitBits {R : ℕ} (bs : List Bool) : RMProg R (Fin (bs.length + 1)) :=
  fun q =>
    if h : q.val < bs.length then some (opEmit (bs.get ⟨q.val, h⟩) ⟨q.val + 1, by omega⟩)
    else none

lemma rmEmitBits_aux {R : ℕ} (bs : List Bool) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    ∀ (rem i : ℕ) (hi : i + rem = bs.length),
      RMExec (rmEmitBits bs) V inp ⟨i, by omega⟩ reg ⟨bs.length, by omega⟩ reg (bs.drop i) rem
  | 0, i, hi => by
    obtain rfl : i = bs.length := by omega
    refine ⟨0, Nat.le_refl 0, by simp [rmIter, List.drop_length], by simp [rmEmitBits], ?_⟩
    intro j hj q' reg' out' hji
    obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
    cases hji; exact hreg
  | rem + 1, i, hi => by
    have hilt : i < bs.length := by omega
    have hstep : rmStep (rmEmitBits bs) inp ⟨i, by omega⟩ reg =
        some (⟨i + 1, by omega⟩, reg, [bs.get ⟨i, hilt⟩]) := by
      simp [rmStep, rmEmitBits, opEmit, hilt]
    rcases rmEmitBits_aux bs V inp reg hreg rem (i + 1) (by omega) with ⟨k, hk, hiter, hhalt, hbnd⟩
    have hdrop : bs.drop i = bs.get ⟨i, hilt⟩ :: bs.drop (i + 1) :=
      List.drop_eq_getElem_cons hilt
    refine ⟨k + 1, by omega, ?_, hhalt, ?_⟩
    · conv => lhs; unfold rmIter
      simp only [hstep, hiter, hdrop, List.singleton_append]
    · intro j hj q' reg' out' hji
      cases j with
      | zero => cases hji; exact hreg
      | succ j' =>
        conv at hji => lhs; unfold rmIter
        simp only [hstep] at hji
        cases hr : rmIter (rmEmitBits bs) inp j' ⟨i + 1, by omega⟩ reg with
        | none => simp only [hr] at hji; cases hji
        | some val =>
          rcases val with ⟨q'', reg'', out''⟩
          simp only [hr] at hji; cases hji
          exact hbnd j' (by omega) q' reg' out'' hr

theorem rmEmitBits_spec {R : ℕ} (bs : List Bool) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmEmitBits bs) V inp ⟨0, by omega⟩ reg ⟨bs.length, by omega⟩ reg bs bs.length := by
  simpa using rmEmitBits_aux bs V inp reg hreg bs.length 0 (by omega)

/-- Fixed-length 3-bit emitter for gate opcodes (uniform state type `Fin 4`). -/
def rmEmitBits3 {R : ℕ} (b0 b1 b2 : Bool) : RMProg R (Fin 4) :=
  fun q =>
    if q.val = 0 then some (opEmit b0 1)
    else if q.val = 1 then some (opEmit b1 2)
    else if q.val = 2 then some (opEmit b2 3)
    else none

theorem rmEmitBits3_spec {R : ℕ} (b0 b1 b2 : Bool) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    RMExec (rmEmitBits3 b0 b1 b2) V inp 0 reg 3 reg [b0, b1, b2] 3 := by
  have hs0 : rmStep (rmEmitBits3 b0 b1 b2) inp 0 reg = some (1, reg, [b0]) := by
    simp [rmStep, rmEmitBits3, opEmit]
  have hs1 : rmStep (rmEmitBits3 b0 b1 b2) inp 1 reg = some (2, reg, [b1]) := by
    simp [rmStep, rmEmitBits3, opEmit]
  have hs2 : rmStep (rmEmitBits3 b0 b1 b2) inp 2 reg = some (3, reg, [b2]) := by
    simp [rmStep, rmEmitBits3, opEmit]
  refine ⟨3, Nat.le_refl 3, ?_, by simp [rmEmitBits3], ?_⟩
  · simp [rmIter, hs0, hs1, hs2]
  · intro j hj q' reg' out' hji
    match j with
    | 0 => cases hji; exact hreg
    | 1 => simp only [rmIter, hs0] at hji; cases hji; exact hreg
    | 2 => simp only [rmIter, hs0, hs1] at hji; cases hji; exact hreg
    | 3 => simp only [rmIter, hs0, hs1, hs2] at hji; cases hji; exact hreg
    | n + 4 => omega

/-- Gate-payload emitter with uniform state space across all 6 `QCSD_GateOp` constructors. -/
abbrev RMEmitGateArgsQ : Type := Unit ⊕ (RMEmitUnaryQ ⊕ (RMEmitUnaryQ ⊕ RMEmitUnaryQ))
abbrev RMEmitGateQ : Type := Fin 4 ⊕ RMEmitGateArgsQ

def rmEmitGateTag {R : ℕ} : QCSD_GateOp → RMProg R (Fin 4)
  | QCSD_GateOp.input => rmEmitBits3 false false false
  | QCSD_GateOp.tt => rmEmitBits3 false false true
  | QCSD_GateOp.ff => rmEmitBits3 false true false
  | QCSD_GateOp.neg => rmEmitBits3 false true true
  | QCSD_GateOp.conj => rmEmitBits3 true false false
  | QCSD_GateOp.disj => rmEmitBits3 true false true

def rmEmitGateArgs {R : ℕ} (rA rB tmp : Fin R) : RMProg R RMEmitGateArgsQ :=
  rmBranch rmNop
    (rmBranch (rmEmitUnary rA tmp)
      (rmChain (rmEmitUnary rA tmp) (rmEmitUnary rB tmp) rmEmitUnaryEntry))

def rmEmitGateArgsEntry : QCSD_GateOp → RMEmitGateArgsQ
  | QCSD_GateOp.input => Sum.inr (Sum.inl rmEmitUnaryEntry)
  | QCSD_GateOp.tt => Sum.inl ()
  | QCSD_GateOp.ff => Sum.inl ()
  | QCSD_GateOp.neg => Sum.inr (Sum.inl rmEmitUnaryEntry)
  | QCSD_GateOp.conj => Sum.inr (Sum.inr (Sum.inl rmEmitUnaryEntry))
  | QCSD_GateOp.disj => Sum.inr (Sum.inr (Sum.inl rmEmitUnaryEntry))

def rmEmitGate {R : ℕ} (op : QCSD_GateOp) (rA rB tmp : Fin R) : RMProg R RMEmitGateQ :=
  rmChain (rmEmitGateTag op) (rmEmitGateArgs rA rB tmp) (rmEmitGateArgsEntry op)

def rmEmitGateEntry : RMEmitGateQ := Sum.inl 0

theorem rmEmitGate_spec {R : ℕ} (op : QCSD_GateOp) (rA rB tmp : Fin R)
    (hAt : rA ≠ tmp) (hBt : rB ≠ tmp) (V : ℕ) (inp : List Bool) (reg : RegState R)
    (hreg : ∀ i, reg i ≤ V) :
    ∃ q₁ reg₁,
      (∀ i, i ≠ tmp → reg₁ i = reg i) ∧
      RMExec (rmEmitGate op rA rB tmp) V inp rmEmitGateEntry reg
        q₁ reg₁ (QCSD_encodeGate ⟨op, reg rA, reg rB⟩) (2 * reg rA + 2 * reg rB + 9) := by
  cases op
  · have ht := rmEmitBits3_spec false false false V inp reg hreg
    have ha := rmEmitUnary_spec rA tmp hAt V inp reg hreg
    have hbr := rmBranch_inr_spec (rmNop (R := R))
      (rmBranch_inl_spec (rmChain (rmEmitUnary rA tmp) (rmEmitUnary rB tmp) rmEmitUnaryEntry) ha)
    have hcomb := (rmChain_spec ht hbr).weaken (V₂ := V) (T₂ := 2 * reg rA + 2 * reg rB + 9)
      (by simp) (by omega)
    refine ⟨Sum.inr (Sum.inr (Sum.inl rmEmitUnaryExit)), regUpd reg tmp 0, fun i hi => regUpd_ne reg hi 0, ?_⟩
    simpa [rmEmitGate, rmEmitGateEntry, rmEmitGateTag, rmEmitGateArgs, rmEmitGateArgsEntry,
      rmChainEntry, rmSeqEntry, rmRedirect, rmEmitBits3, QCSD_encodeGate, QCSD_gateTag] using hcomb
  · have ht := rmEmitBits3_spec false false true V inp reg hreg
    have hn := rmBranch_inl_spec
      (rmBranch (rmEmitUnary rA tmp) (rmChain (rmEmitUnary rA tmp) (rmEmitUnary rB tmp) rmEmitUnaryEntry))
      (rmNop_spec V inp reg hreg)
    have hcomb := (rmChain_spec ht hn).weaken (V₂ := V) (T₂ := 2 * reg rA + 2 * reg rB + 9)
      (by simp) (by omega)
    refine ⟨Sum.inr (Sum.inl ()), reg, fun _ _ => rfl, ?_⟩
    simpa [rmEmitGate, rmEmitGateEntry, rmEmitGateTag, rmEmitGateArgs, rmEmitGateArgsEntry,
      rmChainEntry, rmSeqEntry, rmRedirect, rmEmitBits3, QCSD_encodeGate, QCSD_gateTag] using hcomb
  · have ht := rmEmitBits3_spec false true false V inp reg hreg
    have hn := rmBranch_inl_spec
      (rmBranch (rmEmitUnary rA tmp) (rmChain (rmEmitUnary rA tmp) (rmEmitUnary rB tmp) rmEmitUnaryEntry))
      (rmNop_spec V inp reg hreg)
    have hcomb := (rmChain_spec ht hn).weaken (V₂ := V) (T₂ := 2 * reg rA + 2 * reg rB + 9)
      (by simp) (by omega)
    refine ⟨Sum.inr (Sum.inl ()), reg, fun _ _ => rfl, ?_⟩
    simpa [rmEmitGate, rmEmitGateEntry, rmEmitGateTag, rmEmitGateArgs, rmEmitGateArgsEntry,
      rmChainEntry, rmSeqEntry, rmRedirect, rmEmitBits3, QCSD_encodeGate, QCSD_gateTag] using hcomb
  · have ht := rmEmitBits3_spec false true true V inp reg hreg
    have ha := rmEmitUnary_spec rA tmp hAt V inp reg hreg
    have hbr := rmBranch_inr_spec (rmNop (R := R))
      (rmBranch_inl_spec (rmChain (rmEmitUnary rA tmp) (rmEmitUnary rB tmp) rmEmitUnaryEntry) ha)
    have hcomb := (rmChain_spec ht hbr).weaken (V₂ := V) (T₂ := 2 * reg rA + 2 * reg rB + 9)
      (by simp) (by omega)
    refine ⟨Sum.inr (Sum.inr (Sum.inl rmEmitUnaryExit)), regUpd reg tmp 0, fun i hi => regUpd_ne reg hi 0, ?_⟩
    simpa [rmEmitGate, rmEmitGateEntry, rmEmitGateTag, rmEmitGateArgs, rmEmitGateArgsEntry,
      rmChainEntry, rmSeqEntry, rmRedirect, rmEmitBits3, QCSD_encodeGate, QCSD_gateTag] using hcomb
  · have ht := rmEmitBits3_spec true false false V inp reg hreg
    have ha := rmEmitUnary_spec rA tmp hAt V inp reg hreg
    have hb := rmEmitUnary_spec rB tmp hBt V inp (regUpd reg tmp 0) ha.reg₁_le
    rw [regUpd_ne reg hBt 0, regUpd_idem] at hb
    have hpair := rmChain_spec ha hb
    have hbr := rmBranch_inr_spec (rmNop (R := R)) (rmBranch_inr_spec (rmEmitUnary rA tmp) hpair)
    have hcomb := (rmChain_spec ht hbr).weaken (V₂ := V) (T₂ := 2 * reg rA + 2 * reg rB + 9)
      (by simp) (by omega)
    refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr rmEmitUnaryExit))), regUpd reg tmp 0, fun i hi => regUpd_ne reg hi 0, ?_⟩
    simpa [rmEmitGate, rmEmitGateEntry, rmEmitGateTag, rmEmitGateArgs, rmEmitGateArgsEntry,
      rmChainEntry, rmSeqEntry, rmRedirect, rmEmitBits3, rmEmitUnary, rmEmitUnaryEntry,
      rmEmitTrueRepeat, rmEmitTrueRepeatEntry, rmCopy, rmChain, rmSeq, QCSD_encodeGate, QCSD_gateTag] using hcomb
  · have ht := rmEmitBits3_spec true false true V inp reg hreg
    have ha := rmEmitUnary_spec rA tmp hAt V inp reg hreg
    have hb := rmEmitUnary_spec rB tmp hBt V inp (regUpd reg tmp 0) ha.reg₁_le
    rw [regUpd_ne reg hBt 0, regUpd_idem] at hb
    have hpair := rmChain_spec ha hb
    have hbr := rmBranch_inr_spec (rmNop (R := R)) (rmBranch_inr_spec (rmEmitUnary rA tmp) hpair)
    have hcomb := (rmChain_spec ht hbr).weaken (V₂ := V) (T₂ := 2 * reg rA + 2 * reg rB + 9)
      (by simp) (by omega)
    refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr rmEmitUnaryExit))), regUpd reg tmp 0, fun i hi => regUpd_ne reg hi 0, ?_⟩
    simpa [rmEmitGate, rmEmitGateEntry, rmEmitGateTag, rmEmitGateArgs, rmEmitGateArgsEntry,
      rmChainEntry, rmSeqEntry, rmRedirect, rmEmitBits3, rmEmitUnary, rmEmitUnaryEntry,
      rmEmitTrueRepeat, rmEmitTrueRepeatEntry, rmCopy, rmChain, rmSeq, QCSD_encodeGate, QCSD_gateTag] using hcomb

/-!
## Section 3a: Loop Combinators, Input Parser (`rmParseInput`), and Parameters (`rmComputeParams`)
-/

/-- Helper: `rmChain_spec` with explicit `Sum.inl q₁₀` entry when `M₁ q₁₀ ≠ none`. -/
theorem rmChain_spec_inl {R : ℕ} {Q₁ Q₂ : Type}
    {M₁ : RMProg R Q₁} {M₂ : RMProg R Q₂} {V₁ V₂ : ℕ} {inp : List Bool}
    {q₁₀ q₁₁ : Q₁} {q₂₀ q₂₁ : Q₂} {reg₀ reg₁ reg₂ : RegState R}
    {out₁ out₂ : List Bool} {T₁ T₂ : ℕ}
    (hact : M₁ q₁₀ ≠ none)
    (h₁ : RMExec M₁ V₁ inp q₁₀ reg₀ q₁₁ reg₁ out₁ T₁)
    (h₂ : RMExec M₂ V₂ inp q₂₀ reg₁ q₂₁ reg₂ out₂ T₂) :
    RMExec (rmChain M₁ M₂ q₂₀) (max V₁ V₂) inp (Sum.inl q₁₀) reg₀
      (Sum.inr q₂₁) reg₂ (out₁ ++ out₂) (T₁ + T₂) := by
  have hentry : rmChainEntry M₁ q₁₀ q₂₀ = Sum.inl q₁₀ := by
    unfold rmChainEntry rmSeqEntry rmRedirect
    cases h : M₁ q₁₀ with
    | none => exact absurd h hact
    | some _ => rfl
  rw [← hentry]
  exact rmChain_spec h₁ h₂

/-- Ascending range loop: runs `body` with `rIdx = 0, 1, ..., reg rCount - 1`,
collecting emitted bits `(List.range (reg rCount)).flatMap emitFn`. -/
abbrev RMForRangeQ (Q : Type) : Type :=
  Bool ⊕ (Bool ⊕ (Option Bool ⊕ (Unit ⊕ (Q ⊕ Bool))))

def rmForRange {R : ℕ} {Q : Type} (rIdx rRem rCount : Fin R) (body : RMProg R Q) (q₀ : Q) :
    RMProg R (RMForRangeQ Q) :=
  rmChain (rmZero rIdx)
    (rmChain (rmCopy rRem rCount)
      (rmWhileDec rRem (rmChain body (rmInc rIdx) false) (rmChainEntry body q₀ false))
      rmWhileDecEntry)
    (Sum.inl false)

def rmForRangeEntry {Q : Type} : RMForRangeQ Q := Sum.inl false
def rmForRangeExit {Q : Type} : RMForRangeQ Q := Sum.inr (Sum.inr rmWhileDecExit)

lemma list_range_succ_flatMap_shift {α : Type*} (f : ℕ → List α) :
    ∀ (rem i : ℕ),
      (List.range (rem + 1)).flatMap (fun d => f (i + d)) =
        f i ++ (List.range rem).flatMap (fun d => f (i + 1 + d))
  | 0, i => by simp
  | rem + 1, i => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [list_range_succ_flatMap_shift f rem i, List.append_assoc]
    congr 1
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hadd : i + (rem + 1) = i + 1 + rem := by omega
    rw [hadd]

lemma rmForRange_loop_spec {R : ℕ} {Q : Type} (rIdx rRem : Fin R) (hir : rIdx ≠ rRem)
    (body : RMProg R Q) (q₀ : Q) (V T_step count : ℕ) (inp : List Bool)
    (Inv : ℕ → RegState R → Prop) (emitFn : ℕ → List Bool)
    (hInv_le : ∀ i reg, Inv i reg → ∀ j, reg j ≤ V)
    (hInv_idx : ∀ i reg, Inv i reg → reg rIdx = i)
    (hInv_rem : ∀ i reg v, v ≤ V → Inv i reg → Inv i (regUpd reg rRem v))
    (hstep_spec : ∀ i reg, i < count → Inv i reg →
      ∃ q₁ reg₁,
        reg₁ rIdx = i ∧
        reg₁ rRem = reg rRem ∧
        Inv (i + 1) (regUpd reg₁ rIdx (i + 1)) ∧
        RMExec body V inp q₀ reg q₁ reg₁ (emitFn i) T_step) :
    ∀ (rem i : ℕ) (reg : RegState R),
      i + rem = count →
      count ≤ V →
      reg rRem = rem →
      Inv i reg →
      ∃ reg_end : RegState R,
        reg_end rIdx = count ∧
        reg_end rRem = 0 ∧
        Inv count reg_end ∧
        RMExec (rmWhileDec rRem (rmChain body (rmInc rIdx) false) (rmChainEntry body q₀ false))
          V inp rmWhileDecEntry reg rmWhileDecExit reg_end
          ((List.range rem).flatMap (fun d => emitFn (i + d)))
          (rem * (T_step + 2) + 1)
  | 0, i, reg, hic, _, hrem, hInv => by
    obtain rfl : i = count := by omega
    exact ⟨reg, hInv_idx i reg hInv, hrem, hInv, by
      simpa using rmWhileDec_zero rRem _ _ V inp reg hrem (hInv_le i reg hInv)⟩
  | rem + 1, i, reg, hic, hcV, hrem, hInv => by
    have hne : reg rRem ≠ 0 := by omega
    have hreg_le : ∀ j, reg j ≤ V := hInv_le i reg hInv
    set reg1 := regUpd reg rRem (reg rRem - 1)
    have h1_Inv : Inv i reg1 := hInv_rem i reg (reg rRem - 1) (le_trans (Nat.sub_le _ _) (hreg_le rRem)) hInv
    have h1_rem : reg1 rRem = rem := by dsimp only [reg1]; rw [regUpd_self]; omega
    rcases hstep_spec i reg1 (by omega) h1_Inv with ⟨q₁, reg2, h2_idx, h2_rem, h2_Inv, hbody⟩
    have hinc := rmInc_spec rIdx V inp reg2 hbody.reg₁_le (by rw [h2_idx]; omega)
    set reg3 := regUpd reg2 rIdx (reg2 rIdx + 1)
    have h3_eq : reg3 = regUpd reg2 rIdx (i + 1) := by dsimp only [reg3]; rw [h2_idx]
    have h3_Inv : Inv (i + 1) reg3 := by rw [h3_eq]; exact h2_Inv
    have h3_rem : reg3 rRem = rem := by dsimp only [reg3]; rw [regUpd_ne _ hir.symm, h2_rem, h1_rem]
    have hchain := rmChain_spec hbody hinc
    simp only [max_self, List.append_nil] at hchain
    rcases rmForRange_loop_spec rIdx rRem hir body q₀ V T_step count inp Inv emitFn
        hInv_le hInv_idx hInv_rem hstep_spec rem (i + 1) reg3 (by omega) hcV h3_rem h3_Inv
      with ⟨reg_end, hend_idx, hend_rem, hend_Inv, hrest⟩
    have hstep := rmWhileDec_step rRem (rmChain body (rmInc rIdx) false) hne hreg_le hchain hrest
    have hT : 1 + (T_step + 1) + (rem * (T_step + 2) + 1) = (rem + 1) * (T_step + 2) + 1 := by ring
    rw [max_self, hT, ← list_range_succ_flatMap_shift emitFn rem i] at hstep
    exact ⟨reg_end, hend_idx, hend_rem, hend_Inv, hstep⟩

theorem rmForRange_spec {R : ℕ} {Q : Type} (rIdx rRem rCount : Fin R)
    (hir : rIdx ≠ rRem) (hic : rIdx ≠ rCount)
    (body : RMProg R Q) (q₀ : Q) (V T_step : ℕ) (inp : List Bool) (reg₀ : RegState R)
    (Inv : ℕ → RegState R → Prop) (emitFn : ℕ → List Bool)
    (hreg₀ : ∀ j, reg₀ j ≤ V)
    (hInv_init : Inv 0 (regUpd (regUpd reg₀ rIdx 0) rRem (reg₀ rCount)))
    (hInv_le : ∀ i reg, Inv i reg → ∀ j, reg j ≤ V)
    (hInv_idx : ∀ i reg, Inv i reg → reg rIdx = i)
    (hInv_rem : ∀ i reg v, v ≤ V → Inv i reg → Inv i (regUpd reg rRem v))
    (hstep_spec : ∀ i reg, i < reg₀ rCount → Inv i reg →
      ∃ q₁ reg₁,
        reg₁ rIdx = i ∧
        reg₁ rRem = reg rRem ∧
        Inv (i + 1) (regUpd reg₁ rIdx (i + 1)) ∧
        RMExec body V inp q₀ reg q₁ reg₁ (emitFn i) T_step) :
    ∃ reg_end : RegState R,
      reg_end rIdx = reg₀ rCount ∧
      reg_end rRem = 0 ∧
      Inv (reg₀ rCount) reg_end ∧
      RMExec (rmForRange rIdx rRem rCount body q₀) V inp rmForRangeEntry reg₀ rmForRangeExit reg_end
        ((List.range (reg₀ rCount)).flatMap emitFn)
        (reg₀ rCount * (T_step + 2) + 3) := by
  have hz := rmZero_spec rIdx V inp reg₀ hreg₀
  set reg1 := regUpd reg₀ rIdx 0
  have h1_cnt : reg1 rCount = reg₀ rCount := regUpd_ne reg₀ hic.symm 0
  have hcp := rmCopy_spec rRem rCount V inp reg1 hz.reg₁_le
  set reg2 := regUpd reg1 rRem (reg1 rCount)
  have h2_eq : reg2 = regUpd (regUpd reg₀ rIdx 0) rRem (reg₀ rCount) := by
    dsimp only [reg2]; rw [h1_cnt]
  have h2_Inv : Inv 0 reg2 := by rw [h2_eq]; exact hInv_init
  have h2_rem : reg2 rRem = reg₀ rCount := by dsimp only [reg2]; rw [regUpd_self, h1_cnt]
  rcases rmForRange_loop_spec rIdx rRem hir body q₀ V T_step (reg₀ rCount) inp Inv emitFn
      hInv_le hInv_idx hInv_rem hstep_spec (reg₀ rCount) 0 reg2
      (Nat.zero_add _) (hreg₀ rCount) h2_rem h2_Inv
    with ⟨reg_end, hend_idx, hend_rem, hend_Inv, hloop⟩
  have hcomb := rmChain_spec_inl (by simp [rmZero]) hz
    (rmChain_spec_inl (by simp [rmCopy]) hcp hloop)
  have hT : 1 + (1 + (reg₀ rCount * (T_step + 2) + 1)) = reg₀ rCount * (T_step + 2) + 3 := by ring
  rw [max_self, max_self, List.nil_append, List.nil_append, hT] at hcomb
  simp only [Nat.zero_add] at hcomb
  exact ⟨reg_end, hend_idx, hend_rem, hend_Inv, hcomb⟩

end Branch6Encoder
