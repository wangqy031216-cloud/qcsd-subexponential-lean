import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import QCSD.Defs
import Branch5_PadAndSep
import Branch6_EncoderMacros
import Branch7_EncodeNetSpec

namespace Branch4

open QCSD.Defs
open Branch5PadAndSep
open Branch6Encoder
open Branch7EncodeSpec

/-!
## Layer 1: Exact Tape Laws, Execution Calculus, and Modular `StepFn` Combinators
All types are constructed exclusively from `Fin`, `Bool`, `ℕ`, `×`, `⊕`, `Option`, `List`
(zero custom `inductive` or `structure` declarations).
-/

theorem nat_max_eq_max (a b : ℕ) : Nat.max a b = max a b := rfl

instance instFintypeQCSDHeadDir : Fintype QCSD_HeadDir where
  elems := {QCSD_HeadDir.left, QCSD_HeadDir.right}
  complete := fun x => by cases x <;> simp

instance instDecidableEqSumLocal {α β : Type} [DecidableEq α] [DecidableEq β] : DecidableEq (α ⊕ β)
  | Sum.inl a₁, Sum.inl a₂ => decidable_of_iff (a₁ = a₂) (by simp)
  | Sum.inr b₁, Sum.inr b₂ => decidable_of_iff (b₁ = b₂) (by simp)
  | Sum.inl _, Sum.inr _ => isFalse nofun
  | Sum.inr _, Sum.inl _ => isFalse nofun

theorem QCSD_tapeWrite2_length (t : List Bool) (i : ℕ) (b : Bool) :
    (QCSD_tapeWrite2 t i b).length = max t.length (i + 1) := by
  unfold QCSD_tapeWrite2
  split_ifs with h
  · simp only [List.length_set]
    omega
  · simp only [List.length_set, List.length_append, List.length_replicate]
    omega

theorem getD_set_eq (l : List Bool) (i j : ℕ) (b d : Bool) (hi : i < l.length) :
    (l.set i b).getD j d = if j = i then b else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hij : j = i
  · subst hij
    simp [hi]
  · have hij' : i ≠ j := fun h => hij h.symm
    simp [hij, hij']

theorem QCSD_tapeRead_tapeWrite2 (t : List Bool) (i : ℕ) (b : Bool) (j : ℕ) :
    QCSD_tapeRead (QCSD_tapeWrite2 t i b) j =
      if j = i then b else QCSD_tapeRead t j := by
  unfold QCSD_tapeRead QCSD_tapeWrite2
  by_cases hi : i < t.length
  · simp only [hi, ↓reduceIte]
    exact getD_set_eq t i j b false hi
  · simp only [hi, ↓reduceIte]
    have hlen : i < (t ++ List.replicate (i + 1 - t.length) false).length := by
      simp only [List.length_append, List.length_replicate]
      omega
    rw [getD_set_eq _ i j b false hlen]
    by_cases hj : j = i
    · simp [hj]
    · simp only [hj, ↓reduceIte, List.getD_eq_getElem?_getD]
      by_cases hjt : j < t.length
      · rw [List.getElem?_append_left hjt]
      · have hjt' : t.length ≤ j := Nat.le_of_not_lt hjt
        rw [List.getElem?_append_right hjt', List.getElem?_eq_none hjt']
        simp only [Option.getD_none, List.getElem?_replicate]
        split_ifs <;> rfl

theorem tape_eq_of_length_and_read {t₁ t₂ : List Bool}
    (hlen : t₁.length = t₂.length)
    (hread : ∀ j < t₁.length, QCSD_tapeRead t₁ j = QCSD_tapeRead t₂ j) :
    t₁ = t₂ := by
  apply List.ext_getElem hlen
  intro j hj₁ hj₂
  have h := hread j hj₁
  unfold QCSD_tapeRead at h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₁,
    List.getElem?_eq_getElem hj₂, Option.getD_some] at h
  exact h

theorem QCSD_tapeRead_of_ge (t : List Bool) {j : ℕ} (hj : t.length ≤ j) :
    QCSD_tapeRead t j = false := by
  unfold QCSD_tapeRead
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem QCSD_tapeRead_append_left (t₁ t₂ : List Bool) {j : ℕ} (hj : j < t₁.length) :
    QCSD_tapeRead (t₁ ++ t₂) j = QCSD_tapeRead t₁ j := by
  unfold QCSD_tapeRead
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem QCSD_tapeRead_append_right (t₁ t₂ : List Bool) {j : ℕ} (hj : t₁.length ≤ j) :
    QCSD_tapeRead (t₁ ++ t₂) j = QCSD_tapeRead t₂ (j - t₁.length) := by
  unfold QCSD_tapeRead
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hj]

theorem QCSD_tapeRead_replicate (n : ℕ) (b : Bool) {j : ℕ} (hj : j < n) :
    QCSD_tapeRead (List.replicate n b) j = b := by
  unfold QCSD_tapeRead
  simp [List.getD_eq_getElem?_getD, hj]

/-- Multi-step execution starting from an arbitrary configuration `c`. -/
noncomputable def runFrom (M : QCSD_DetTM) (c : QCSD_Config M) : ℕ → QCSD_Config M
  | 0 => c
  | n + 1 =>
    match QCSD_stepConfig2 M (runFrom M c n) with
    | none => runFrom M c n
    | some c' => c'

theorem configAt2_eq_runFrom (M : QCSD_DetTM) (x : List Bool) (k : ℕ) :
    QCSD_configAt2 M x k = runFrom M ⟨M.q0, x, 0⟩ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold QCSD_configAt2 runFrom
    rw [ih]
    rfl

theorem runFrom_add (M : QCSD_DetTM) (c : QCSD_Config M) (a b : ℕ) :
    runFrom M c (a + b) = runFrom M (runFrom M c a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Nat.add_succ]
    unfold runFrom
    rw [ih]

theorem stepConfig2_of_halt (M : QCSD_DetTM) (c : QCSD_Config M) (h : c.state = M.qhalt) :
    QCSD_stepConfig2 M c = none := by
  unfold QCSD_stepConfig2
  have hd : @decide (c.state = M.qhalt) (M.decEqQ c.state M.qhalt) = true :=
    @decide_eq_true _ (M.decEqQ c.state M.qhalt) h
  rw [hd]
  rfl

theorem stepConfig2_of_ne_halt (M : QCSD_DetTM) (c : QCSD_Config M) (h : c.state ≠ M.qhalt) :
    QCSD_stepConfig2 M c =
      let r := M.step c.state (QCSD_tapeRead c.tape c.head)
      some ⟨r.1, QCSD_tapeWrite2 c.tape c.head r.2.1,
        match r.2.2 with
        | QCSD_HeadDir.left => c.head - 1
        | QCSD_HeadDir.right => c.head + 1⟩ := by
  unfold QCSD_stepConfig2
  have hd : @decide (c.state = M.qhalt) (M.decEqQ c.state M.qhalt) = false :=
    @decide_eq_false _ (M.decEqQ c.state M.qhalt) h
  rw [hd]
  rfl

theorem runFrom_of_halt (M : QCSD_DetTM) (c : QCSD_Config M) (h : c.state = M.qhalt) (k : ℕ) :
    runFrom M c k = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [runFrom, ih, stepConfig2_of_halt M c h]

/-- Next head position helper. -/
def moveHead (h : ℕ) (d : QCSD_HeadDir) : ℕ :=
  match d with
  | QCSD_HeadDir.left => h - 1
  | QCSD_HeadDir.right => h + 1

/-- `c₁` reaches `c₂` in `steps` transitions while keeping `QCSD_spaceUse2 ≤ B` throughout. -/
def ReachesWithin (M : QCSD_DetTM) (B : ℕ) (c₁ c₂ : QCSD_Config M) (steps : ℕ) : Prop :=
  runFrom M c₁ steps = c₂ ∧ ∀ j ≤ steps, QCSD_spaceUse2 (runFrom M c₁ j) ≤ B

theorem ReachesWithin.refl {M : QCSD_DetTM} {B : ℕ} {c : QCSD_Config M}
    (hsp : QCSD_spaceUse2 c ≤ B) : ReachesWithin M B c c 0 := by
  refine ⟨rfl, ?_⟩
  intro j hj
  obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
  exact hsp

theorem ReachesWithin.trans {M : QCSD_DetTM} {B : ℕ} {c₁ c₂ c₃ : QCSD_Config M} {s₁ s₂ : ℕ}
    (h₁ : ReachesWithin M B c₁ c₂ s₁) (h₂ : ReachesWithin M B c₂ c₃ s₂) :
    ReachesWithin M B c₁ c₃ (s₁ + s₂) := by
  refine ⟨?_, ?_⟩
  · rw [runFrom_add, h₁.1, h₂.1]
  · intro j hj
    by_cases hjs : j ≤ s₁
    · exact h₁.2 j hjs
    · have hj' : j - s₁ ≤ s₂ := by omega
      have heq : j = s₁ + (j - s₁) := by omega
      rw [heq, runFrom_add, h₁.1]
      exact h₂.2 (j - s₁) hj'

theorem ReachesWithin.step_eq {M : QCSD_DetTM} {B : ℕ} {c c' : QCSD_Config M}
    {q' : M.Q} {b' : Bool} {d : QCSD_HeadDir}
    (hne : c.state ≠ M.qhalt)
    (hstep_tm : M.step c.state (QCSD_tapeRead c.tape c.head) = (q', b', d))
    (hc' : c' = ⟨q', QCSD_tapeWrite2 c.tape c.head b', moveHead c.head d⟩)
    (hlen : c.tape.length ≤ B)
    (hh₁ : c.head + 1 ≤ B)
    (hh₂ : moveHead c.head d + 1 ≤ B) :
    ReachesWithin M B c c' 1 := by
  have h1 : runFrom M c 1 = c' := by
    change (match QCSD_stepConfig2 M c with | none => c | some c'' => c'') = c'
    rw [stepConfig2_of_ne_halt M c hne]
    simp only [hstep_tm, hc', moveHead]
  refine ⟨h1, ?_⟩
  intro j hj
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · simp only [runFrom, QCSD_spaceUse2, nat_max_eq_max]
    omega
  · rw [h1, hc']
    simp only [QCSD_spaceUse2, nat_max_eq_max, QCSD_tapeWrite2_length]
    omega

/-- Partial transition function of a modular submachine (`none` = exit). -/
abbrev StepFn (Q : Type) : Type := Q → Bool → Option (Q × Bool × QCSD_HeadDir)

/-- Turn a top-level `StepFn Q` into a `QCSD_DetTM` by adding `none` as `qhalt`. -/
def toDetTM {Q : Type} [Fintype Q] [DecidableEq Q] (q_init : Q) (s : StepFn Q) : QCSD_DetTM :=
  { Q := Option Q
    q0 := some q_init
    qhalt := none
    step := fun qOpt b =>
      match qOpt with
      | none => (none, b, QCSD_HeadDir.left)
      | some q =>
        match s q b with
        | some (q', b', d) => (some q', b', d)
        | none => (none, b, QCSD_HeadDir.left) }

def stepFnOnce {Q : Type} (s : StepFn Q)
    (cfg : Q × ℕ × (ℕ → Bool) × ℕ) : Option (Q × ℕ × (ℕ → Bool) × ℕ) :=
  let (q, len, τ, h) := cfg
  match s q (τ h) with
  | none => none
  | some (q', b', d) =>
      some (q', max len (h + 1), Function.update τ h b', moveHead h d)

def stepFnIter {Q : Type} (s : StepFn Q)
    (cfg : Q × ℕ × (ℕ → Bool) × ℕ) : ℕ → Option (Q × ℕ × (ℕ → Bool) × ℕ)
  | 0 => some cfg
  | k + 1 =>
      match stepFnOnce s cfg with
      | none => none
      | some cfg' => stepFnIter s cfg' k

def StepExec {Q : Type} (s : StepFn Q) (B : ℕ)
    (q₁ : Q) (len₁ : ℕ) (τ₁ : ℕ → Bool) (h₁ : ℕ)
    (q₂ : Q) (len₂ : ℕ) (τ₂ : ℕ → Bool) (h₂ : ℕ) (T : ℕ) : Prop :=
  ∃ k ≤ T,
    stepFnIter s (q₁, len₁, τ₁, h₁) k = some (q₂, len₂, τ₂, h₂) ∧
    (∀ b, s q₂ b = none) ∧
    (∀ j ≤ k, ∀ q' l' τ' h',
      stepFnIter s (q₁, len₁, τ₁, h₁) j = some (q', l', τ', h') →
      l' ≤ B ∧ h' + 1 ≤ B)

theorem stepFnIter_add {Q : Type} (s : StepFn Q) (cfg : Q × ℕ × (ℕ → Bool) × ℕ) (a b : ℕ) :
    stepFnIter s cfg (a + b) = (stepFnIter s cfg a).bind (fun cfg' => stepFnIter s cfg' b) := by
  induction a generalizing cfg with
  | zero => simp [stepFnIter]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [stepFnIter]
    cases stepFnOnce s cfg with
    | none => rfl
    | some cfg' => exact ih cfg'

theorem stepFnIter_le_some {Q : Type} {s : StepFn Q} {cfg cfg₂ : Q × ℕ × (ℕ → Bool) × ℕ}
    {k j : ℕ} (hjk : j ≤ k) (hk : stepFnIter s cfg k = some cfg₂) :
    ∃ cfg_j, stepFnIter s cfg j = some cfg_j := by
  have heq : k = j + (k - j) := by omega
  rw [heq, stepFnIter_add] at hk
  cases h : stepFnIter s cfg j with
  | none => rw [h] at hk; simp at hk
  | some cfg_j => exact ⟨cfg_j, rfl⟩

/-- Sequential composition of two `StepFn`s that hand off at `head = 0` via 1 no-op step. -/
def seq0 {Q₁ Q₂ : Type} (s₁ : StepFn Q₁) (s₂ : StepFn Q₂) (f : Q₁ → Q₂) : StepFn (Q₁ ⊕ Q₂)
  | Sum.inl q₁, b =>
      match s₁ q₁ b with
      | some (q₁', b', d) => some (Sum.inl q₁', b', d)
      | none => some (Sum.inr (f q₁), b, QCSD_HeadDir.left)
  | Sum.inr q₂, b =>
      match s₂ q₂ b with
      | some (q₂', b', d) => some (Sum.inr q₂', b', d)
      | none => none

theorem stepFnIter_seq0_left {Q₁ Q₂ : Type} (s₁ : StepFn Q₁) (s₂ : StepFn Q₂) (f : Q₁ → Q₂) :
    ∀ k (q₁ : Q₁) len₁ τ₁ h₁ (q₂ : Q₁) len₂ τ₂ h₂,
      stepFnIter s₁ (q₁, len₁, τ₁, h₁) k = some (q₂, len₂, τ₂, h₂) →
      stepFnIter (seq0 s₁ s₂ f) (Sum.inl q₁, len₁, τ₁, h₁) k =
        some (Sum.inl q₂, len₂, τ₂, h₂) := by
  intro k
  induction k with
  | zero =>
    intro q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ h
    cases h
    rfl
  | succ k ih =>
    intro q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ h
    simp only [stepFnIter, stepFnOnce] at h ⊢
    cases hs : s₁ q₁ (τ₁ h₁) with
    | none => rw [hs] at h; simp at h
    | some val =>
      rcases val with ⟨q₁', b', d⟩
      rw [hs] at h
      simp only [seq0, hs]
      exact ih q₁' _ _ _ q₂ len₂ τ₂ h₂ h

theorem stepFnIter_seq0_right {Q₁ Q₂ : Type} (s₁ : StepFn Q₁) (s₂ : StepFn Q₂) (f : Q₁ → Q₂) :
    ∀ k (q₁ : Q₂) len₁ τ₁ h₁,
      stepFnIter (seq0 s₁ s₂ f) (Sum.inr q₁, len₁, τ₁, h₁) k =
        (stepFnIter s₂ (q₁, len₁, τ₁, h₁) k).map
          (fun (q', l', τ', h') => (Sum.inr q', l', τ', h')) := by
  intro k
  induction k with
  | zero => intro q₁ len₁ τ₁ h₁; rfl
  | succ k ih =>
    intro q₁ len₁ τ₁ h₁
    simp only [stepFnIter, stepFnOnce, seq0]
    cases s₂ q₁ (τ₁ h₁) with
    | none => rfl
    | some val =>
      rcases val with ⟨q₁', b', d⟩
      exact ih q₁' _ _ _

theorem seq0_spec {Q₁ Q₂ : Type} {s₁ : StepFn Q₁} {s₂ : StepFn Q₂} {f : Q₁ → Q₂} {B : ℕ}
    {q₁ : Q₁} {len₁ : ℕ} {τ₁ : ℕ → Bool} {h₁ : ℕ}
    {q_mid : Q₁} {len₂ : ℕ} {τ₂ : ℕ → Bool}
    {q₃ : Q₂} {len₃ : ℕ} {τ₃ : ℕ → Bool} {h₃ : ℕ}
    {T₁ T₂ : ℕ}
    (hlen₂_pos : 1 ≤ len₂)
    (he₁ : StepExec s₁ B q₁ len₁ τ₁ h₁ q_mid len₂ τ₂ 0 T₁)
    (he₂ : StepExec s₂ B (f q_mid) len₂ τ₂ 0 q₃ len₃ τ₃ h₃ T₂) :
    StepExec (seq0 s₁ s₂ f) B (Sum.inl q₁) len₁ τ₁ h₁ (Sum.inr q₃) len₃ τ₃ h₃
      (T₁ + 1 + T₂) := by
  rcases he₁ with ⟨k₁, hk₁, hiter₁, hexit₁, hbnd₁⟩
  rcases he₂ with ⟨k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
  have hl₁ := stepFnIter_seq0_left s₁ s₂ f k₁ q₁ len₁ τ₁ h₁ q_mid len₂ τ₂ 0 hiter₁
  have hmid_step : stepFnIter (seq0 s₁ s₂ f) (Sum.inl q_mid, len₂, τ₂, 0) 1 =
      some (Sum.inr (f q_mid), len₂, τ₂, 0) := by
    simp only [stepFnIter, stepFnOnce, seq0, hexit₁ (τ₂ 0), moveHead]
    have hmax : max len₂ 1 = len₂ := by omega
    have hupd : Function.update τ₂ 0 (τ₂ 0) = τ₂ := Function.update_eq_self 0 τ₂
    rw [hmax, hupd]
  have hr₂ : stepFnIter (seq0 s₁ s₂ f) (Sum.inr (f q_mid), len₂, τ₂, 0) k₂ =
      some (Sum.inr q₃, len₃, τ₃, h₃) := by
    rw [stepFnIter_seq0_right, hiter₂]; rfl
  refine ⟨k₁ + 1 + k₂, by omega, ?_, ?_, ?_⟩
  · rw [stepFnIter_add, stepFnIter_add, hl₁, Option.bind_some, hmid_step, Option.bind_some, hr₂]
  · intro b
    simp [seq0, hexit₂ b]
  · intro j hj q' l' τ' h' hj_eq
    by_cases hj₁ : j ≤ k₁
    · rcases stepFnIter_le_some hj₁ hiter₁ with ⟨⟨qj, lj, τj, hj_pos⟩, hsub⟩
      have hl_sub := stepFnIter_seq0_left s₁ s₂ f j q₁ len₁ τ₁ h₁ qj lj τj hj_pos hsub
      rw [hl_sub] at hj_eq
      cases hj_eq
      exact hbnd₁ j hj₁ qj l' τ' h' hsub
    · have heq_j : j = k₁ + 1 + (j - (k₁ + 1)) := by omega
      rw [heq_j, stepFnIter_add, stepFnIter_add, hl₁, Option.bind_some, hmid_step,
        Option.bind_some, stepFnIter_seq0_right] at hj_eq
      cases hsub2 : stepFnIter s₂ (f q_mid, len₂, τ₂, 0) (j - (k₁ + 1)) with
      | none => rw [hsub2] at hj_eq; simp at hj_eq
      | some cfg2 =>
        rcases cfg2 with ⟨q2, l2, τ2, h2⟩
        rw [hsub2] at hj_eq
        cases hj_eq
        exact hbnd₂ (j - (k₁ + 1)) (by omega) q2 l' τ' h' hsub2

/-- Loop combinator at `head = 0`: when `body` exits at `q`, if `next q = some q'` it restarts
`q'` via 1 no-op step at `head = 0`; if `next q = none` it exits. -/
def loop0 {Q : Type} (body : StepFn Q) (next : Q → Option Q) : StepFn Q :=
  fun q b =>
    match body q b with
    | some step => some step
    | none =>
        match next q with
        | some q' => some (q', b, QCSD_HeadDir.left)
        | none => none

theorem stepFnIter_loop0_body {Q : Type} (body : StepFn Q) (next : Q → Option Q) :
    ∀ k (q₁ : Q) len₁ τ₁ h₁ (q₂ : Q) len₂ τ₂ h₂,
      stepFnIter body (q₁, len₁, τ₁, h₁) k = some (q₂, len₂, τ₂, h₂) →
      stepFnIter (loop0 body next) (q₁, len₁, τ₁, h₁) k = some (q₂, len₂, τ₂, h₂) := by
  intro k
  induction k with
  | zero =>
    intro q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ h
    exact h
  | succ k ih =>
    intro q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ h
    simp only [stepFnIter, stepFnOnce] at h ⊢
    cases hb : body q₁ (τ₁ h₁) with
    | none => rw [hb] at h; simp at h
    | some val =>
      rcases val with ⟨q₁', b', d⟩
      rw [hb] at h
      simp only [loop0, hb]
      exact ih q₁' _ _ _ q₂ len₂ τ₂ h₂ h

theorem loop0_done {Q : Type} {body : StepFn Q} {next : Q → Option Q} {B : ℕ}
    {q₁ : Q} {len₁ : ℕ} {τ₁ : ℕ → Bool} {h₁ : ℕ}
    {q₂ : Q} {len₂ : ℕ} {τ₂ : ℕ → Bool} {h₂ : ℕ} {T : ℕ}
    (hb : StepExec body B q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ T)
    (hdone : next q₂ = none) :
    StepExec (loop0 body next) B q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ T := by
  rcases hb with ⟨k, hk, hiter, hexit, hbnd⟩
  refine ⟨k, hk, stepFnIter_loop0_body body next k q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ hiter, ?_, ?_⟩
  · intro b
    simp [loop0, hexit b, hdone]
  · intro j hj q' l' τ' h' hj_eq
    rcases stepFnIter_le_some hj hiter with ⟨⟨qj, lj, τj, hj_pos⟩, hsub⟩
    have hl_sub := stepFnIter_loop0_body body next j q₁ len₁ τ₁ h₁ qj lj τj hj_pos hsub
    rw [hl_sub] at hj_eq
    cases hj_eq
    exact hbnd j hj q' l' τ' h' hsub

theorem loop0_step {Q : Type} {body : StepFn Q} {next : Q → Option Q} {B : ℕ}
    {q₁ : Q} {len₁ : ℕ} {τ₁ : ℕ → Bool} {h₁ : ℕ}
    {q_mid q_next : Q} {len₂ : ℕ} {τ₂ : ℕ → Bool}
    {q₃ : Q} {len₃ : ℕ} {τ₃ : ℕ → Bool} {h₃ : ℕ}
    {T₁ T₂ : ℕ}
    (hlen₂_pos : 1 ≤ len₂)
    (hb : StepExec body B q₁ len₁ τ₁ h₁ q_mid len₂ τ₂ 0 T₁)
    (hnext : next q_mid = some q_next)
    (hrest : StepExec (loop0 body next) B q_next len₂ τ₂ 0 q₃ len₃ τ₃ h₃ T₂) :
    StepExec (loop0 body next) B q₁ len₁ τ₁ h₁ q₃ len₃ τ₃ h₃ (T₁ + 1 + T₂) := by
  rcases hb with ⟨k₁, hk₁, hiter₁, hexit₁, hbnd₁⟩
  rcases hrest with ⟨k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
  have hl₁ := stepFnIter_loop0_body body next k₁ q₁ len₁ τ₁ h₁ q_mid len₂ τ₂ 0 hiter₁
  have hmid : stepFnIter (loop0 body next) (q_mid, len₂, τ₂, 0) 1 =
      some (q_next, len₂, τ₂, 0) := by
    simp only [stepFnIter, stepFnOnce, loop0, hexit₁ (τ₂ 0), hnext, moveHead]
    have hmax : max len₂ 1 = len₂ := by omega
    have hupd : Function.update τ₂ 0 (τ₂ 0) = τ₂ := Function.update_eq_self 0 τ₂
    rw [hmax, hupd]
  refine ⟨k₁ + 1 + k₂, by omega, ?_, hexit₂, ?_⟩
  · rw [stepFnIter_add, stepFnIter_add, hl₁, Option.bind_some, hmid, Option.bind_some, hiter₂]
  · intro j hj q' l' τ' h' hj_eq
    by_cases hj₁ : j ≤ k₁
    · rcases stepFnIter_le_some hj₁ hiter₁ with ⟨⟨qj, lj, τj, hj_pos⟩, hsub⟩
      have hl_sub := stepFnIter_loop0_body body next j q₁ len₁ τ₁ h₁ qj lj τj hj_pos hsub
      rw [hl_sub] at hj_eq
      cases hj_eq
      exact hbnd₁ j hj₁ q' l' τ' h' hsub
    · have heq_j : j = k₁ + 1 + (j - (k₁ + 1)) := by omega
      rw [heq_j, stepFnIter_add, stepFnIter_add, hl₁, Option.bind_some, hmid,
        Option.bind_some] at hj_eq
      exact hbnd₂ (j - (k₁ + 1)) (by omega) q' l' τ' h' hj_eq

theorem stepFnIter_to_ReachesWithin {Q : Type} [Fintype Q] [DecidableEq Q]
    (q_init : Q) (s : StepFn Q) (B : ℕ) :
    ∀ k (q₁ : Q) len₁ τ₁ h₁ (q₂ : Q) len₂ τ₂ h₂ (c₁ : QCSD_Config (toDetTM q_init s)),
      stepFnIter s (q₁, len₁, τ₁, h₁) k = some (q₂, len₂, τ₂, h₂) →
      (∀ j ≤ k, ∀ q' l' τ' h',
        stepFnIter s (q₁, len₁, τ₁, h₁) j = some (q', l', τ', h') → l' ≤ B ∧ h' + 1 ≤ B) →
      c₁.state = some q₁ → c₁.head = h₁ → c₁.tape.length = len₁ →
      (∀ idx, QCSD_tapeRead c₁.tape idx = τ₁ idx) →
      ∃ c₂ : QCSD_Config (toDetTM q_init s),
        ReachesWithin (toDetTM q_init s) B c₁ c₂ k ∧
        c₂.state = some q₂ ∧ c₂.head = h₂ ∧ c₂.tape.length = len₂ ∧
        (∀ idx, QCSD_tapeRead c₂.tape idx = τ₂ idx) := by
  intro k
  induction k with
  | zero =>
    intro q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ c₁ hiter hbnd hst hhd hlen hread
    cases hiter
    have hb0 := hbnd 0 (Nat.le_refl 0) q₁ len₁ τ₁ h₁ rfl
    refine ⟨c₁, ReachesWithin.refl ?_, hst, hhd, hlen, hread⟩
    simp only [QCSD_spaceUse2, nat_max_eq_max, hlen, hhd]
    omega
  | succ k ih =>
    intro q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ c₁ hiter hbnd hst hhd hlen hread
    simp only [stepFnIter, stepFnOnce] at hiter
    cases hs : s q₁ (τ₁ h₁) with
    | none => rw [hs] at hiter; simp at hiter
    | some val =>
      rcases val with ⟨q₁', b', d⟩
      rw [hs] at hiter
      have hb0 := hbnd 0 (Nat.zero_le _) q₁ len₁ τ₁ h₁ rfl
      have hb1 : max len₁ (h₁ + 1) ≤ B ∧ moveHead h₁ d + 1 ≤ B := by
        refine hbnd 1 (Nat.succ_le_succ (Nat.zero_le _))
          q₁' (max len₁ (h₁ + 1)) (Function.update τ₁ h₁ b') (moveHead h₁ d) ?_
        simp [stepFnIter, stepFnOnce, hs]
      have hne : c₁.state ≠ (toDetTM q_init s).qhalt := by
        rw [hst]; simp [toDetTM]
      have hread_h : QCSD_tapeRead c₁.tape c₁.head = τ₁ h₁ := by
        rw [hhd, hread]
      have hstep_tm : (toDetTM q_init s).step c₁.state (QCSD_tapeRead c₁.tape c₁.head) =
          (some q₁', b', d) := by
        rw [hst, hread_h]
        simp [toDetTM, hs]
      let c_mid : QCSD_Config (toDetTM q_init s) :=
        ⟨some q₁', QCSD_tapeWrite2 c₁.tape c₁.head b', moveHead h₁ d⟩
      have hrw1 : ReachesWithin (toDetTM q_init s) B c₁ c_mid 1 :=
        ReachesWithin.step_eq hne hstep_tm (by simp [c_mid, hhd])
          (hlen ▸ hb0.1) (hhd ▸ hb0.2) (hhd ▸ hb1.2)
      have hbnd' : ∀ j ≤ k, ∀ q' l' τ' h',
          stepFnIter s (q₁', max len₁ (h₁ + 1), Function.update τ₁ h₁ b', moveHead h₁ d) j =
            some (q', l', τ', h') → l' ≤ B ∧ h' + 1 ≤ B := by
        intro j hj q' l' τ' h' hj_eq
        refine hbnd (j + 1) (Nat.succ_le_succ hj) q' l' τ' h' ?_
        simp [stepFnIter, stepFnOnce, hs, hj_eq]
      rcases ih q₁' (max len₁ (h₁ + 1)) (Function.update τ₁ h₁ b') (moveHead h₁ d)
          q₂ len₂ τ₂ h₂ c_mid hiter hbnd' rfl rfl
          (by simp [c_mid, QCSD_tapeWrite2_length, hlen, hhd])
          (fun idx => by
            simp only [c_mid, QCSD_tapeRead_tapeWrite2, hhd, hread, Function.update_apply])
        with ⟨c₂, hrw2, hst2, hhd2, hlen2, hread2⟩
      refine ⟨c₂, ?_, hst2, hhd2, hlen2, hread2⟩
      rw [Nat.add_comm k 1]
      exact hrw1.trans hrw2

theorem toDetTM_spec {Q : Type} [Fintype Q] [DecidableEq Q]
    (q_init : Q) (s : StepFn Q) (inp out : List Bool) (B T : ℕ)
    {q_end : Q} {τ_end : ℕ → Bool}
    (hout_pos : 1 ≤ out.length)
    (hout_le_B : out.length ≤ B)
    (hexec : StepExec s B q_init inp.length (fun i => QCSD_tapeRead inp i) 0
      q_end out.length τ_end 0 T)
    (hmatch : ∀ j < out.length, τ_end j = QCSD_tapeRead out j) :
    ∃ k ≤ T + 1,
      QCSD_configAt2 (toDetTM q_init s) inp k = ⟨(toDetTM q_init s).qhalt, out, 0⟩ ∧
      (∀ j ≤ k, QCSD_spaceUse2 (QCSD_configAt2 (toDetTM q_init s) inp j) ≤ B) := by
  rcases hexec with ⟨k, hk, hiter, hexit, hbnd⟩
  let c₀ : QCSD_Config (toDetTM q_init s) := ⟨(toDetTM q_init s).q0, inp, 0⟩
  rcases stepFnIter_to_ReachesWithin q_init s B k q_init inp.length
      (fun i => QCSD_tapeRead inp i) 0 q_end out.length τ_end 0 c₀
      hiter hbnd rfl rfl rfl (fun _ => rfl)
    with ⟨c₂, hrw, hst₂, hhd₂, hlen₂, hread₂⟩
  have htape₂ : c₂.tape = out := by
    apply tape_eq_of_length_and_read hlen₂
    intro j hj
    rw [hread₂ j, hmatch j (hlen₂ ▸ hj)]
  have hne₂ : c₂.state ≠ (toDetTM q_init s).qhalt := by
    rw [hst₂]; simp [toDetTM]
  have hstep_end : (toDetTM q_init s).step c₂.state (QCSD_tapeRead c₂.tape c₂.head) =
      (none, QCSD_tapeRead c₂.tape 0, QCSD_HeadDir.left) := by
    rw [hst₂, hhd₂]
    simp [toDetTM, hexit]
  have htw : QCSD_tapeWrite2 c₂.tape 0 (QCSD_tapeRead c₂.tape 0) = out := by
    rw [htape₂]
    apply tape_eq_of_length_and_read
    · rw [QCSD_tapeWrite2_length]; omega
    · intro j hj
      rw [QCSD_tapeRead_tapeWrite2]
      split_ifs with hj0
      · subst hj0; rfl
      · rfl
  have hrw_end : ReachesWithin (toDetTM q_init s) B c₂
      ⟨(toDetTM q_init s).qhalt, out, 0⟩ 1 :=
    ReachesWithin.step_eq hne₂ hstep_end
      (by simp [hhd₂, htw, moveHead, toDetTM])
      (hlen₂ ▸ hout_le_B) (by rw [hhd₂]; omega) (by rw [hhd₂, moveHead]; omega)
  have htot := hrw.trans hrw_end
  refine ⟨k + 1, by omega, ?_, ?_⟩
  · rw [configAt2_eq_runFrom]
    exact htot.1
  · intro j hj
    rw [configAt2_eq_runFrom]
    exact htot.2 j hj

/-- Sequential composition of any two `QCSD_DetTM` machines where `M₁` halts at `head = 0`. -/
def QCSD_seqTM (M₁ M₂ : QCSD_DetTM) : QCSD_DetTM :=
  letI := M₁.fintypeQ
  letI := M₁.decEqQ
  letI := M₂.fintypeQ
  letI := M₂.decEqQ
  { Q := M₁.Q ⊕ M₂.Q
    q0 := if @decide (M₁.q0 = M₁.qhalt) (M₁.decEqQ M₁.q0 M₁.qhalt)
          then Sum.inr M₂.q0 else Sum.inl M₁.q0
    qhalt := Sum.inr M₂.qhalt
    step := fun q b =>
      match q with
      | Sum.inl q₁ =>
          let (q₁', b', d) := M₁.step q₁ b
          if @decide (q₁' = M₁.qhalt) (M₁.decEqQ q₁' M₁.qhalt)
          then (Sum.inr M₂.q0, b', d) else (Sum.inl q₁', b', d)
      | Sum.inr q₂ =>
          let (q₂', b', d) := M₂.step q₂ b
          (Sum.inr q₂', b', d) }

theorem runFrom_one (M : QCSD_DetTM) (c : QCSD_Config M) :
    runFrom M c 1 =
      match QCSD_stepConfig2 M c with
      | none => c
      | some c' => c' := rfl

theorem runFrom_seqTM_right (M₁ M₂ : QCSD_DetTM) :
    ∀ k (c₂ : QCSD_Config M₂),
      runFrom (QCSD_seqTM M₁ M₂) ⟨Sum.inr c₂.state, c₂.tape, c₂.head⟩ k =
        let c₂' := runFrom M₂ c₂ k
        ⟨Sum.inr c₂'.state, c₂'.tape, c₂'.head⟩ := by
  intro k
  induction k with
  | zero => intro c₂; rfl
  | succ k ih =>
    intro c₂
    rw [Nat.add_comm k 1, runFrom_add, runFrom_add]
    by_cases hh : c₂.state = M₂.qhalt
    · have h1 : runFrom M₂ c₂ 1 = c₂ := runFrom_of_halt M₂ c₂ hh 1
      have hh_seq : (⟨Sum.inr c₂.state, c₂.tape, c₂.head⟩ : QCSD_Config (QCSD_seqTM M₁ M₂)).state =
          (QCSD_seqTM M₁ M₂).qhalt := by
        simp [QCSD_seqTM, hh]
      have h2 : runFrom (QCSD_seqTM M₁ M₂) ⟨Sum.inr c₂.state, c₂.tape, c₂.head⟩ 1 =
          ⟨Sum.inr c₂.state, c₂.tape, c₂.head⟩ :=
        runFrom_of_halt (QCSD_seqTM M₁ M₂) _ hh_seq 1
      rw [h1, h2]
      exact ih c₂
    · have hh_seq : (⟨Sum.inr c₂.state, c₂.tape, c₂.head⟩ : QCSD_Config (QCSD_seqTM M₁ M₂)).state ≠
          (QCSD_seqTM M₁ M₂).qhalt := by
        simp [QCSD_seqTM, hh]
      let r := M₂.step c₂.state (QCSD_tapeRead c₂.tape c₂.head)
      let c₂_next : QCSD_Config M₂ :=
        ⟨r.1, QCSD_tapeWrite2 c₂.tape c₂.head r.2.1, moveHead c₂.head r.2.2⟩
      have h1 : runFrom M₂ c₂ 1 = c₂_next := by
        rw [runFrom_one, stepConfig2_of_ne_halt M₂ c₂ hh]
        rfl
      have h2 : runFrom (QCSD_seqTM M₁ M₂) ⟨Sum.inr c₂.state, c₂.tape, c₂.head⟩ 1 =
          ⟨Sum.inr c₂_next.state, c₂_next.tape, c₂_next.head⟩ := by
        rw [runFrom_one, stepConfig2_of_ne_halt (QCSD_seqTM M₁ M₂) _ hh_seq]
        simp [QCSD_seqTM, moveHead, r, c₂_next]
      rw [h1, h2]
      exact ih c₂_next

theorem runFrom_seqTM_left (M₁ M₂ : QCSD_DetTM) :
    ∀ k (c₁ : QCSD_Config M₁),
      c₁.state ≠ M₁.qhalt →
      (∀ j < k, (runFrom M₁ c₁ j).state ≠ M₁.qhalt) →
      runFrom (QCSD_seqTM M₁ M₂) ⟨Sum.inl c₁.state, c₁.tape, c₁.head⟩ k =
        let c₁' := runFrom M₁ c₁ k
        if @decide (c₁'.state = M₁.qhalt) (M₁.decEqQ c₁'.state M₁.qhalt)
        then ⟨Sum.inr M₂.q0, c₁'.tape, c₁'.head⟩
        else ⟨Sum.inl c₁'.state, c₁'.tape, c₁'.head⟩ := by
  intro k
  induction k with
  | zero =>
    intro c₁ hne _
    have hd : @decide (c₁.state = M₁.qhalt) (M₁.decEqQ c₁.state M₁.qhalt) = false :=
      @decide_eq_false _ (M₁.decEqQ c₁.state M₁.qhalt) hne
    change _ = (if @decide (c₁.state = M₁.qhalt) (M₁.decEqQ c₁.state M₁.qhalt)
      then _ else _)
    rw [hd]
    rfl
  | succ k ih =>
    intro c₁ hne hprev
    rw [Nat.add_comm k 1, runFrom_add, runFrom_add]
    have hne_seq : (⟨Sum.inl c₁.state, c₁.tape, c₁.head⟩ : QCSD_Config (QCSD_seqTM M₁ M₂)).state ≠
        (QCSD_seqTM M₁ M₂).qhalt := by
      simp [QCSD_seqTM]
    let r := M₁.step c₁.state (QCSD_tapeRead c₁.tape c₁.head)
    let c_next : QCSD_Config M₁ :=
      ⟨r.1, QCSD_tapeWrite2 c₁.tape c₁.head r.2.1, moveHead c₁.head r.2.2⟩
    have hstep1 : runFrom M₁ c₁ 1 = c_next := by
      rw [runFrom_one, stepConfig2_of_ne_halt M₁ c₁ hne]
      rfl
    rw [hstep1]
    by_cases hr_halt : r.1 = M₁.qhalt
    · cases k with
      | zero =>
        have hd : @decide (r.1 = M₁.qhalt) (M₁.decEqQ r.1 M₁.qhalt) = true :=
          @decide_eq_true _ (M₁.decEqQ r.1 M₁.qhalt) hr_halt
        have hseq1 : runFrom (QCSD_seqTM M₁ M₂) ⟨Sum.inl c₁.state, c₁.tape, c₁.head⟩ 1 =
            ⟨Sum.inr M₂.q0, c_next.tape, c_next.head⟩ := by
          rw [runFrom_one, stepConfig2_of_ne_halt (QCSD_seqTM M₁ M₂) _ hne_seq]
          simp [QCSD_seqTM, r, c_next, hd, moveHead]
        rw [hseq1]
        change _ = (if @decide (c_next.state = M₁.qhalt) (M₁.decEqQ c_next.state M₁.qhalt)
          then _ else _)
        have hd' : @decide (c_next.state = M₁.qhalt) (M₁.decEqQ c_next.state M₁.qhalt) = true :=
          hd
        rw [hd']
        rfl
      | succ k' =>
        exfalso
        have hlt : 1 < k' + 1 + 1 := by omega
        have hne1 := hprev 1 hlt
        rw [hstep1] at hne1
        exact hne1 hr_halt
    · have hd : @decide (r.1 = M₁.qhalt) (M₁.decEqQ r.1 M₁.qhalt) = false :=
        @decide_eq_false _ (M₁.decEqQ r.1 M₁.qhalt) hr_halt
      have hstep_seq : runFrom (QCSD_seqTM M₁ M₂) ⟨Sum.inl c₁.state, c₁.tape, c₁.head⟩ 1 =
          ⟨Sum.inl c_next.state, c_next.tape, c_next.head⟩ := by
        rw [runFrom_one, stepConfig2_of_ne_halt (QCSD_seqTM M₁ M₂) _ hne_seq]
        simp [QCSD_seqTM, r, c_next, hd, moveHead]
      rw [hstep_seq]
      refine ih c_next hr_halt ?_
      intro j hj
      have hlt : 1 + j < k + 1 := by omega
      have h := hprev (1 + j) hlt
      rw [runFrom_add, hstep1] at h
      exact h

/-- First halting step minimization: if `M₁` reaches `qhalt` at `head = 0` with `tape = mid` in
`≤ T₁` steps (within space `Sp₁`), and `M₂` on `mid` reaches `qhalt` in `≤ T₂` steps (within
space `Sp₂`), then `QCSD_seqTM M₁ M₂` reaches `qhalt` with `M₂`'s halting configuration in
`≤ T₁ + T₂` steps and space `≤ max Sp₁ Sp₂`. -/
theorem QCSD_seqTM_spec (M₁ M₂ : QCSD_DetTM) (inp mid out : List Bool)
    (T₁ T₂ Sp₁ Sp₂ h_out : ℕ)
    (h₁ : ∃ k₁ ≤ T₁,
      QCSD_configAt2 M₁ inp k₁ = ⟨M₁.qhalt, mid, 0⟩ ∧
      ∀ j ≤ k₁, QCSD_spaceUse2 (QCSD_configAt2 M₁ inp j) ≤ Sp₁)
    (h₂ : ∃ k₂ ≤ T₂,
      QCSD_configAt2 M₂ mid k₂ = ⟨M₂.qhalt, out, h_out⟩ ∧
      ∀ j ≤ k₂, QCSD_spaceUse2 (QCSD_configAt2 M₂ mid j) ≤ Sp₂) :
    ∃ k ≤ T₁ + T₂,
      QCSD_configAt2 (QCSD_seqTM M₁ M₂) inp k = ⟨(QCSD_seqTM M₁ M₂).qhalt, out, h_out⟩ ∧
      ∀ j ≤ k, QCSD_spaceUse2 (QCSD_configAt2 (QCSD_seqTM M₁ M₂) inp j) ≤ max Sp₁ Sp₂ := by
  rcases h₁ with ⟨k₁_raw, hk₁_raw, hcfg₁_raw, hsp₁_raw⟩
  rcases h₂ with ⟨k₂, hk₂, hcfg₂, hsp₂⟩
  let P : ℕ → Prop := fun k => (QCSD_configAt2 M₁ inp k).state = M₁.qhalt
  have hP_dec : DecidablePred P := fun k => M₁.decEqQ _ _
  have hexP : ∃ k, P k := ⟨k₁_raw, by simp [P, hcfg₁_raw]⟩
  let k₁ := @Nat.find P hP_dec hexP
  have hk₁_spec : P k₁ := @Nat.find_spec P hP_dec hexP
  have hk₁_le_raw : k₁ ≤ k₁_raw := @Nat.find_min' P hP_dec hexP k₁_raw (by simp [P, hcfg₁_raw])
  have hk₁_min : ∀ j < k₁, ¬ P j := fun j hj => @Nat.find_min P hP_dec hexP j hj
  have hcfg₁ : QCSD_configAt2 M₁ inp k₁ = ⟨M₁.qhalt, mid, 0⟩ := by
    have heq : k₁_raw = k₁ + (k₁_raw - k₁) := by omega
    rw [configAt2_eq_runFrom, heq, runFrom_add, ← configAt2_eq_runFrom,
      runFrom_of_halt M₁ _ hk₁_spec] at hcfg₁_raw
    exact hcfg₁_raw
  by_cases hk₁0 : k₁ = 0
  · have hcfg₀ : QCSD_configAt2 M₁ inp 0 = ⟨M₁.qhalt, mid, 0⟩ := hk₁0 ▸ hcfg₁
    have hq0 : M₁.q0 = M₁.qhalt := congrArg QCSD_Config.state hcfg₀
    have hmid : inp = mid := congrArg QCSD_Config.tape hcfg₀
    subst hmid
    have hq0_seq : (QCSD_seqTM M₁ M₂).q0 = Sum.inr M₂.q0 := by
      have hd := @decide_eq_true _ (M₁.decEqQ M₁.q0 M₁.qhalt) hq0
      simp [QCSD_seqTM, hd]
    refine ⟨k₂, by omega, ?_, ?_⟩
    · rw [configAt2_eq_runFrom, hq0_seq,
        runFrom_seqTM_right M₁ M₂ k₂ ⟨M₂.q0, inp, 0⟩, ← configAt2_eq_runFrom, hcfg₂]
      rfl
    · intro j hj
      rw [configAt2_eq_runFrom, hq0_seq,
        runFrom_seqTM_right M₁ M₂ j ⟨M₂.q0, inp, 0⟩, ← configAt2_eq_runFrom]
      have h := hsp₂ j hj
      simp only [QCSD_spaceUse2, nat_max_eq_max] at h ⊢
      omega
  · have hq0_ne : M₁.q0 ≠ M₁.qhalt := by
      have := hk₁_min 0 (Nat.pos_of_ne_zero hk₁0)
      simpa [P, QCSD_configAt2] using this
    have hq0_seq : (QCSD_seqTM M₁ M₂).q0 = Sum.inl M₁.q0 := by
      have hd := @decide_eq_false _ (M₁.decEqQ M₁.q0 M₁.qhalt) hq0_ne
      simp [QCSD_seqTM, hd]
    have hleft_k₁ : runFrom (QCSD_seqTM M₁ M₂) ⟨(QCSD_seqTM M₁ M₂).q0, inp, 0⟩ k₁ =
        ⟨Sum.inr M₂.q0, mid, 0⟩ := by
      rw [hq0_seq, runFrom_seqTM_left M₁ M₂ k₁ ⟨M₁.q0, inp, 0⟩ hq0_ne
        (fun j hj => by simpa [P, configAt2_eq_runFrom] using hk₁_min j hj)]
      rw [← configAt2_eq_runFrom, hcfg₁]
      have hd := @decide_eq_true _ (M₁.decEqQ M₁.qhalt M₁.qhalt) rfl
      change (if @decide (M₁.qhalt = M₁.qhalt) (M₁.decEqQ M₁.qhalt M₁.qhalt)
        then _ else _) = _
      rw [hd]
      rfl
    refine ⟨k₁ + k₂, by omega, ?_, ?_⟩
    · rw [configAt2_eq_runFrom, runFrom_add, hleft_k₁,
        runFrom_seqTM_right M₁ M₂ k₂ ⟨M₂.q0, mid, 0⟩, ← configAt2_eq_runFrom, hcfg₂]
      rfl
    · intro j hj
      rw [configAt2_eq_runFrom]
      by_cases hjk₁ : j < k₁
      · rw [hq0_seq, runFrom_seqTM_left M₁ M₂ j ⟨M₁.q0, inp, 0⟩ hq0_ne
          (fun i hi => by simpa [P, configAt2_eq_runFrom] using hk₁_min i (Nat.lt_trans hi hjk₁))]
        have hne_j : (runFrom M₁ ⟨M₁.q0, inp, 0⟩ j).state ≠ M₁.qhalt := by
          simpa [P, configAt2_eq_runFrom] using hk₁_min j hjk₁
        have hd := @decide_eq_false _ (M₁.decEqQ _ M₁.qhalt) hne_j
        simp only [hd, Bool.false_eq_true, ↓reduceIte, QCSD_spaceUse2, nat_max_eq_max]
        have h := hsp₁_raw j (by omega)
        rw [configAt2_eq_runFrom] at h
        simp only [QCSD_spaceUse2, nat_max_eq_max] at h
        omega
      · have heq : j = k₁ + (j - k₁) := by omega
        rw [heq, runFrom_add, hleft_k₁,
          runFrom_seqTM_right M₁ M₂ (j - k₁) ⟨M₂.q0, mid, 0⟩, ← configAt2_eq_runFrom]
        have h := hsp₂ (j - k₁) (by omega)
        simp only [QCSD_spaceUse2, nat_max_eq_max] at h ⊢
        omega

/-!
## Layer 2: 3-Cell Block Lifting (`liftBlockStep`)
Physical cells `0 .. 3 * M_blk - 1` encode `M_blk` virtual 3-bit symbols `BlkSym = Bool × Bool × Bool`.
-/

abbrev BlkSym : Type := Bool × Bool × Bool
abbrev BlkStepFn (Q : Type) : Type := Q → BlkSym → Option (Q × BlkSym × QCSD_HeadDir)

def blkHome : BlkSym := (true, true, true)
def blkSep : BlkSym := (true, false, false)
def blkWall : BlkSym := (true, false, true)
def blkData (mark bit : Bool) : BlkSym := (false, mark, bit)

def readBlk (τ : ℕ → Bool) (j : ℕ) : BlkSym :=
  (τ (3 * j), τ (3 * j + 1), τ (3 * j + 2))

def writeBlk (τ : ℕ → Bool) (j : ℕ) (s : BlkSym) : ℕ → Bool :=
  Function.update (Function.update (Function.update τ (3 * j + 2) s.2.2) (3 * j + 1) s.2.1) (3 * j) s.1

theorem readBlk_writeBlk (τ : ℕ → Bool) (j i : ℕ) (s : BlkSym) :
    readBlk (writeBlk τ j s) i = if i = j then s else readBlk τ i := by
  rcases s with ⟨s0, s1, s2⟩
  unfold readBlk writeBlk
  by_cases hij : i = j
  · subst hij
    have h01 : 3 * i + 1 ≠ 3 * i := by omega
    have h02 : 3 * i + 2 ≠ 3 * i := by omega
    have h12 : 3 * i + 2 ≠ 3 * i + 1 := by omega
    rw [Function.update_self]
    rw [Function.update_of_ne h01, Function.update_self]
    rw [Function.update_of_ne h02, Function.update_of_ne h12, Function.update_self]
    simp
  · simp only [hij, ↓reduceIte]
    have h0a : 3 * i ≠ 3 * j := by omega
    have h0b : 3 * i ≠ 3 * j + 1 := by omega
    have h0c : 3 * i ≠ 3 * j + 2 := by omega
    have h1a : 3 * i + 1 ≠ 3 * j := by omega
    have h1b : 3 * i + 1 ≠ 3 * j + 1 := by omega
    have h1c : 3 * i + 1 ≠ 3 * j + 2 := by omega
    have h2a : 3 * i + 2 ≠ 3 * j := by omega
    have h2b : 3 * i + 2 ≠ 3 * j + 1 := by omega
    have h2c : 3 * i + 2 ≠ 3 * j + 2 := by omega
    rw [Function.update_of_ne h0a, Function.update_of_ne h0b, Function.update_of_ne h0c,
        Function.update_of_ne h1a, Function.update_of_ne h1b, Function.update_of_ne h1c,
        Function.update_of_ne h2a, Function.update_of_ne h2b, Function.update_of_ne h2c]

theorem writeBlk_outside (τ : ℕ → Bool) (j k : ℕ) (s : BlkSym)
    (hk : k < 3 * j ∨ 3 * j + 3 ≤ k) :
    writeBlk τ j s k = τ k := by
  unfold writeBlk
  have h0 : k ≠ 3 * j := by omega
  have h1 : k ≠ 3 * j + 1 := by omega
  have h2 : k ≠ 3 * j + 2 := by omega
  rw [Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2]

abbrev LiftBlkQ (Q : Type) : Type :=
  Q × Fin 9 × Bool × Bool × Bool × QCSD_HeadDir

def liftBlkEntry {Q : Type} (q : Q) : LiftBlkQ Q :=
  (q, 0, false, false, false, QCSD_HeadDir.left)

def liftBlkExit {Q : Type} (q : Q) : LiftBlkQ Q :=
  (q, 4, false, false, false, QCSD_HeadDir.left)

def liftBlockStep {Q : Type} (bs : BlkStepFn Q) : StepFn (LiftBlkQ Q) :=
  fun (q, ph, c0, c1, _c2, d) b =>
    if ph = 0 then
      some ((q, 1, b, false, false, QCSD_HeadDir.left), b, QCSD_HeadDir.right)
    else if ph = 1 then
      some ((q, 2, c0, b, false, QCSD_HeadDir.left), b, QCSD_HeadDir.right)
    else if ph = 2 then
      match bs q (c0, c1, b) with
      | none =>
          some ((q, 3, c0, c1, b, QCSD_HeadDir.left), b, QCSD_HeadDir.left)
      | some (q', (w0, w1, w2), d') =>
          some ((q', 5, w0, w1, false, d'), w2, QCSD_HeadDir.left)
    else if ph = 3 then
      some ((q, 4, false, false, false, QCSD_HeadDir.left), b, QCSD_HeadDir.left)
    else if ph = 4 then
      none
    else if ph = 5 then
      some ((q, 6, c0, false, false, d), c1, QCSD_HeadDir.left)
    else if ph = 6 then
      match d with
      | QCSD_HeadDir.right =>
          some ((q, 7, false, false, false, QCSD_HeadDir.right), c0, QCSD_HeadDir.right)
      | QCSD_HeadDir.left =>
          some ((q, 7, false, false, false, QCSD_HeadDir.left), c0, QCSD_HeadDir.left)
    else if ph = 7 then
      some ((q, 8, false, false, false, d), b, d)
    else
      some ((q, 0, false, false, false, QCSD_HeadDir.left), b, d)

def blkOnce {Q : Type} (bs : BlkStepFn Q)
    (cfg : Q × (ℕ → BlkSym) × ℕ) : Option (Q × (ℕ → BlkSym) × ℕ) :=
  let (q, σ, j) := cfg
  match bs q (σ j) with
  | none => none
  | some (q', sym', d) => some (q', Function.update σ j sym', moveHead j d)

def blkIter {Q : Type} (bs : BlkStepFn Q)
    (cfg : Q × (ℕ → BlkSym) × ℕ) : ℕ → Option (Q × (ℕ → BlkSym) × ℕ)
  | 0 => some cfg
  | k + 1 =>
      match blkOnce bs cfg with
      | none => none
      | some cfg' => blkIter bs cfg' k

theorem liftBlockStep_exit {Q : Type} (bs : BlkStepFn Q) (B M_blk len : ℕ)
    (τ : ℕ → Bool) (q : Q) (j : ℕ)
    (hj : j < M_blk) (hM : 3 * M_blk ≤ len) (hlen : len ≤ B)
    (hnone : bs q (readBlk τ j) = none) :
    StepExec (liftBlockStep bs) B (liftBlkEntry q) len τ (3 * j)
      (liftBlkExit q) len τ (3 * j) 4 := by
  have hm0 : max len (3 * j + 1) = len := by omega
  have hm1 : max len (3 * j + 2) = len := by omega
  have hm2 : max len (3 * j + 3) = len := by omega
  have h3j2_sub : (3 * j + 2) - 1 = 3 * j + 1 := by omega
  have h3j1_sub : (3 * j + 1) - 1 = 3 * j := by omega
  have hread : (τ (3 * j), τ (3 * j + 1), τ (3 * j + 2)) = readBlk τ j := rfl
  have hs0 : stepFnOnce (liftBlockStep bs) (liftBlkEntry q, len, τ, 3 * j) =
      some ((q, 1, τ (3 * j), false, false, QCSD_HeadDir.left), len, τ, 3 * j + 1) := by
    simp [stepFnOnce, liftBlockStep, liftBlkEntry, moveHead, hm0]
  have hs1 : stepFnOnce (liftBlockStep bs)
      ((q, 1, τ (3 * j), false, false, QCSD_HeadDir.left), len, τ, 3 * j + 1) =
      some ((q, 2, τ (3 * j), τ (3 * j + 1), false, QCSD_HeadDir.left), len, τ, 3 * j + 2) := by
    simp [stepFnOnce, liftBlockStep, moveHead, hm1]
  have hs2 : stepFnOnce (liftBlockStep bs)
      ((q, 2, τ (3 * j), τ (3 * j + 1), false, QCSD_HeadDir.left), len, τ, 3 * j + 2) =
      some ((q, 3, τ (3 * j), τ (3 * j + 1), τ (3 * j + 2), QCSD_HeadDir.left), len, τ, 3 * j + 1) := by
    simp [stepFnOnce, liftBlockStep, hread, hnone, moveHead, hm2, h3j2_sub]
  have hs3 : stepFnOnce (liftBlockStep bs)
      ((q, 3, τ (3 * j), τ (3 * j + 1), τ (3 * j + 2), QCSD_HeadDir.left), len, τ, 3 * j + 1) =
      some (liftBlkExit q, len, τ, 3 * j) := by
    simp [stepFnOnce, liftBlockStep, liftBlkExit, moveHead, hm1, h3j1_sub]
  refine ⟨4, Nat.le_refl 4, ?_, ?_, ?_⟩
  · simp [stepFnIter, hs0, hs1, hs2, hs3]
  · intro b
    simp [liftBlockStep, liftBlkExit]
  · intro m hm q' l' τ' h' hm_eq
    have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · simp [stepFnIter] at hm_eq
      rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
    · simp [stepFnIter, hs0] at hm_eq
      rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
    · simp [stepFnIter, hs0, hs1] at hm_eq
      rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
    · simp [stepFnIter, hs0, hs1, hs2] at hm_eq
      rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
    · simp [stepFnIter, hs0, hs1, hs2, hs3] at hm_eq
      rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega

theorem liftBlockStep_one {Q : Type} (bs : BlkStepFn Q) (B M_blk len : ℕ)
    (τ : ℕ → Bool) (q q' : Q) (sym' : BlkSym) (d : QCSD_HeadDir) (j : ℕ)
    (hj : j < M_blk) (hM : 3 * M_blk ≤ len) (hlen : len ≤ B)
    (hd_valid : (d = QCSD_HeadDir.left → 1 ≤ j) ∧ (d = QCSD_HeadDir.right → j + 1 < M_blk))
    (hsome : bs q (readBlk τ j) = some (q', sym', d)) :
    stepFnIter (liftBlockStep bs) (liftBlkEntry q, len, τ, 3 * j) 7 =
      some (liftBlkEntry q', len, writeBlk τ j sym', 3 * moveHead j d) ∧
    (∀ m ≤ 7, ∀ q_m l_m τ_m h_m,
      stepFnIter (liftBlockStep bs) (liftBlkEntry q, len, τ, 3 * j) m =
        some (q_m, l_m, τ_m, h_m) → l_m ≤ B ∧ h_m + 1 ≤ B) := by
  rcases sym' with ⟨w0, w1, w2⟩
  have hm0 : max len (3 * j + 1) = len := by omega
  have hm1 : max len (3 * j + 2) = len := by omega
  have hm2 : max len (3 * j + 3) = len := by omega
  have h3j2_sub : (3 * j + 2) - 1 = 3 * j + 1 := by omega
  have h3j1_sub : (3 * j + 1) - 1 = 3 * j := by omega
  have hread : (τ (3 * j), τ (3 * j + 1), τ (3 * j + 2)) = readBlk τ j := rfl
  let τ₁ := Function.update τ (3 * j + 2) w2
  let τ₂ := Function.update τ₁ (3 * j + 1) w1
  let τ₃ := writeBlk τ j (w0, w1, w2)
  have hτ₃_def : Function.update τ₂ (3 * j) w0 = τ₃ := rfl
  have hs0 : stepFnOnce (liftBlockStep bs) (liftBlkEntry q, len, τ, 3 * j) =
      some ((q, 1, τ (3 * j), false, false, QCSD_HeadDir.left), len, τ, 3 * j + 1) := by
    simp [stepFnOnce, liftBlockStep, liftBlkEntry, moveHead, hm0]
  have hs1 : stepFnOnce (liftBlockStep bs)
      ((q, 1, τ (3 * j), false, false, QCSD_HeadDir.left), len, τ, 3 * j + 1) =
      some ((q, 2, τ (3 * j), τ (3 * j + 1), false, QCSD_HeadDir.left), len, τ, 3 * j + 2) := by
    simp [stepFnOnce, liftBlockStep, moveHead, hm1]
  have hs2 : stepFnOnce (liftBlockStep bs)
      ((q, 2, τ (3 * j), τ (3 * j + 1), false, QCSD_HeadDir.left), len, τ, 3 * j + 2) =
      some ((q', 5, w0, w1, false, d), len, τ₁, 3 * j + 1) := by
    simp [stepFnOnce, liftBlockStep, hread, hsome, moveHead, hm2, h3j2_sub, τ₁]
  have hs3 : stepFnOnce (liftBlockStep bs)
      ((q', 5, w0, w1, false, d), len, τ₁, 3 * j + 1) =
      some ((q', 6, w0, false, false, d), len, τ₂, 3 * j) := by
    simp [stepFnOnce, liftBlockStep, moveHead, hm1, h3j1_sub, τ₂]
  cases d with
  | right =>
    have hj_next : j + 1 < M_blk := hd_valid.2 rfl
    have hs4 : stepFnOnce (liftBlockStep bs) ((q', 6, w0, false, false, QCSD_HeadDir.right), len, τ₂, 3 * j) =
        some ((q', 7, false, false, false, QCSD_HeadDir.right), len, τ₃, 3 * j + 1) := by
      simp [stepFnOnce, liftBlockStep, moveHead, hm0, hτ₃_def]
    have hs5 : stepFnOnce (liftBlockStep bs)
        ((q', 7, false, false, false, QCSD_HeadDir.right), len, τ₃, 3 * j + 1) =
        some ((q', 8, false, false, false, QCSD_HeadDir.right), len, τ₃, 3 * j + 2) := by
      simp [stepFnOnce, liftBlockStep, moveHead, hm1]
    have hs6 : stepFnOnce (liftBlockStep bs)
        ((q', 8, false, false, false, QCSD_HeadDir.right), len, τ₃, 3 * j + 2) =
        some (liftBlkEntry q', len, τ₃, 3 * (j + 1)) := by
      have h3j3 : 3 * j + 2 + 1 = 3 * (j + 1) := by omega
      have hm2' : max len (3 * (j + 1)) = len := by omega
      simp [stepFnOnce, liftBlockStep, liftBlkEntry, moveHead, h3j3, hm2']
    refine ⟨?_, ?_⟩
    · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4, hs5, hs6, moveHead, τ₃]
    · intro m hm q_m l_m τ_m h_m hm_eq
      have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [stepFnIter] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0, hs1] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0, hs1, hs2] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0, hs1, hs2, hs3] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4, hs5] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
  | left =>
    have hj_pos : 1 ≤ j := hd_valid.1 rfl
    have hml1 : max len (3 * j - 1 + 1) = len := by omega
    have hml2 : max len (3 * j - 2 + 1) = len := by omega
    have hs4 : stepFnOnce (liftBlockStep bs) ((q', 6, w0, false, false, QCSD_HeadDir.left), len, τ₂, 3 * j) =
        some ((q', 7, false, false, false, QCSD_HeadDir.left), len, τ₃, 3 * j - 1) := by
      simp [stepFnOnce, liftBlockStep, moveHead, hm0, hτ₃_def]
    have hs5 : stepFnOnce (liftBlockStep bs)
        ((q', 7, false, false, false, QCSD_HeadDir.left), len, τ₃, 3 * j - 1) =
        some ((q', 8, false, false, false, QCSD_HeadDir.left), len, τ₃, 3 * j - 2) := by
      have hsub : 3 * j - 1 - 1 = 3 * j - 2 := by omega
      simp [stepFnOnce, liftBlockStep, moveHead, hml1, hsub]
    have hs6 : stepFnOnce (liftBlockStep bs)
        ((q', 8, false, false, false, QCSD_HeadDir.left), len, τ₃, 3 * j - 2) =
        some (liftBlkEntry q', len, τ₃, 3 * (j - 1)) := by
      have hsub : 3 * j - 2 - 1 = 3 * (j - 1) := by omega
      simp [stepFnOnce, liftBlockStep, liftBlkEntry, moveHead, hml2, hsub]
    refine ⟨?_, ?_⟩
    · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4, hs5, hs6, moveHead, τ₃]
    · intro m hm q_m l_m τ_m h_m hm_eq
      have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [stepFnIter] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0, hs1] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0, hs1, hs2] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0, hs1, hs2, hs3] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4, hs5] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
      · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega

/-- Multi-step soundness of `liftBlockStep`: `K` block steps inside `0 .. M_blk - 1` followed by
exit run in `≤ 7 * K + 4` physical TM steps, preserving `len` (`3 * M_blk ≤ len ≤ B`) and all
tape cells outside `0 .. 3 * M_blk - 1`. -/
def BlkExec {Q : Type} (bs : BlkStepFn Q) (M_blk : ℕ)
    (q₁ : Q) (σ₁ : ℕ → BlkSym) (j₁ : ℕ)
    (q₂ : Q) (σ₂ : ℕ → BlkSym) (j₂ : ℕ) (K : ℕ) : Prop :=
  ∃ k ≤ K,
    blkIter bs (q₁, σ₁, j₁) k = some (q₂, σ₂, j₂) ∧
    bs q₂ (σ₂ j₂) = none ∧
    (∀ i ≤ k, ∀ q' σ' j', blkIter bs (q₁, σ₁, j₁) i = some (q', σ', j') → j' < M_blk) ∧
    (∀ i < k, ∀ q' σ' j' q'' sym' d,
      blkIter bs (q₁, σ₁, j₁) i = some (q', σ', j') →
      bs q' (σ' j') = some (q'', sym', d) →
      (d = QCSD_HeadDir.left → 1 ≤ j') ∧ (d = QCSD_HeadDir.right → j' + 1 < M_blk))

theorem liftBlockStep_iter_aux {Q : Type} (bs : BlkStepFn Q) (B M_blk len : ℕ)
    (hM : 3 * M_blk ≤ len) (hlen : len ≤ B) :
    ∀ k (q₁ : Q) (τ₁ : ℕ → Bool) (j₁ : ℕ) (q₂ : Q) (σ₂ : ℕ → BlkSym) (j₂ : ℕ),
      blkIter bs (q₁, readBlk τ₁, j₁) k = some (q₂, σ₂, j₂) →
      bs q₂ (σ₂ j₂) = none →
      (∀ i ≤ k, ∀ q' σ' j',
        blkIter bs (q₁, readBlk τ₁, j₁) i = some (q', σ', j') → j' < M_blk) →
      (∀ i < k, ∀ q' σ' j' q'' sym' d,
        blkIter bs (q₁, readBlk τ₁, j₁) i = some (q', σ', j') →
        bs q' (σ' j') = some (q'', sym', d) →
        (d = QCSD_HeadDir.left → 1 ≤ j') ∧ (d = QCSD_HeadDir.right → j' + 1 < M_blk)) →
      ∃ τ₂ : ℕ → Bool,
        readBlk τ₂ = σ₂ ∧
        (∀ p, 3 * M_blk ≤ p → τ₂ p = τ₁ p) ∧
        StepExec (liftBlockStep bs) B (liftBlkEntry q₁) len τ₁ (3 * j₁)
          (liftBlkExit q₂) len τ₂ (3 * j₂) (7 * k + 4) := by
  intro k
  induction k with
  | zero =>
    intro q₁ τ₁ j₁ q₂ σ₂ j₂ hiter hnone hbnd _
    cases hiter
    have hj₁ : j₁ < M_blk := hbnd 0 (Nat.zero_le 0) q₁ (readBlk τ₁) j₁ rfl
    exact ⟨τ₁, rfl, fun _ _ => rfl, liftBlockStep_exit bs B M_blk len τ₁ q₁ j₁ hj₁ hM hlen hnone⟩
  | succ k ih =>
    intro q₁ τ₁ j₁ q₂ σ₂ j₂ hiter hnone hbnd hdir
    simp only [blkIter, blkOnce] at hiter
    cases hbs : bs q₁ (readBlk τ₁ j₁) with
    | none => rw [hbs] at hiter; simp at hiter
    | some val =>
      rcases val with ⟨q_mid, sym', d⟩
      rw [hbs] at hiter
      simp only at hiter
      have hj₁ : j₁ < M_blk := hbnd 0 (Nat.zero_le _) q₁ (readBlk τ₁) j₁ rfl
      have hd_v := hdir 0 (Nat.zero_lt_succ k) q₁ (readBlk τ₁) j₁ q_mid sym' d rfl hbs
      have hone := liftBlockStep_one bs B M_blk len τ₁ q₁ q_mid sym' d j₁ hj₁ hM hlen hd_v hbs
      let τ_mid := writeBlk τ₁ j₁ sym'
      have hread_mid : readBlk τ_mid = Function.update (readBlk τ₁) j₁ sym' := by
        funext idx
        rw [readBlk_writeBlk, Function.update_apply]
      have hiter_mid : blkIter bs (q_mid, readBlk τ_mid, moveHead j₁ d) k = some (q₂, σ₂, j₂) := by
        rw [hread_mid]
        exact hiter
      have hbnd' : ∀ i ≤ k, ∀ q' σ' j',
          blkIter bs (q_mid, readBlk τ_mid, moveHead j₁ d) i = some (q', σ', j') → j' < M_blk := by
        intro i hi q' σ' j' hi_eq
        refine hbnd (i + 1) (Nat.succ_le_succ hi) q' σ' j' ?_
        rw [hread_mid] at hi_eq
        simp [blkIter, blkOnce, hbs, hi_eq]
      have hdir' : ∀ i < k, ∀ q' σ' j' q'' sym'' d',
          blkIter bs (q_mid, readBlk τ_mid, moveHead j₁ d) i = some (q', σ', j') →
          bs q' (σ' j') = some (q'', sym'', d') →
          (d' = QCSD_HeadDir.left → 1 ≤ j') ∧ (d' = QCSD_HeadDir.right → j' + 1 < M_blk) := by
        intro i hi q' σ' j' q'' sym'' d' hi_eq hbs'
        refine hdir (i + 1) (Nat.succ_lt_succ hi) q' σ' j' q'' sym'' d' ?_ hbs'
        rw [hread_mid] at hi_eq
        simp [blkIter, blkOnce, hbs, hi_eq]
      rcases ih q_mid τ_mid (moveHead j₁ d) q₂ σ₂ j₂ hiter_mid hnone hbnd' hdir' with
        ⟨τ₂, hσ₂, hout_mid, k_rest, hk_rest, hiter_rest, hexit_rest, hbnd_rest⟩
      refine ⟨τ₂, hσ₂, ?_, 7 + k_rest, by omega, ?_, hexit_rest, ?_⟩
      · intro p hp
        rw [hout_mid p hp]
        exact writeBlk_outside τ₁ j₁ p sym' (Or.inr (by omega))
      · rw [stepFnIter_add, hone.1, Option.bind_some, hiter_rest]
      · intro m hm q_m l_m τ_m h_m hm_eq
        by_cases hm7 : m ≤ 7
        · rcases stepFnIter_le_some hm7 hone.1 with ⟨⟨qm', lm', τm', hm'⟩, hsub⟩
          rw [hsub] at hm_eq
          cases hm_eq
          exact hone.2 m hm7 q_m l_m τ_m h_m hsub
        · have heq : m = 7 + (m - 7) := by omega
          rw [heq, stepFnIter_add, hone.1, Option.bind_some] at hm_eq
          exact hbnd_rest (m - 7) (by omega) q_m l_m τ_m h_m hm_eq

theorem liftBlockStep_spec {Q : Type} (bs : BlkStepFn Q) (B M_blk len : ℕ)
    (τ₁ : ℕ → Bool) (q₁ q₂ : Q) (σ₂ : ℕ → BlkSym) (j₁ j₂ K : ℕ)
    (hM : 3 * M_blk ≤ len) (hlen : len ≤ B)
    (hexec : BlkExec bs M_blk q₁ (readBlk τ₁) j₁ q₂ σ₂ j₂ K) :
    ∃ τ₂ : ℕ → Bool,
      readBlk τ₂ = σ₂ ∧
      (∀ p, 3 * M_blk ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (liftBlockStep bs) B (liftBlkEntry q₁) len τ₁ (3 * j₁)
        (liftBlkExit q₂) len τ₂ (3 * j₂) (7 * K + 4) := by
  rcases hexec with ⟨k, hk, hiter, hnone, hbnd, hdir⟩
  rcases liftBlockStep_iter_aux bs B M_blk len hM hlen k q₁ τ₁ j₁ q₂ σ₂ j₂ hiter hnone hbnd hdir
    with ⟨τ₂, hσ₂, hout, s_k, hs_k, hs_iter, hs_exit, hs_bnd⟩
  exact ⟨τ₂, hσ₂, hout, s_k, by omega, hs_iter, hs_exit, hs_bnd⟩

/-!
## Layer 2B: Little-Endian Binary Registers, Segment Workspace, and Block Gadgets
-/

theorem blkIter_add {Q : Type} (bs : BlkStepFn Q) (cfg : Q × (ℕ → BlkSym) × ℕ) (a b : ℕ) :
    blkIter bs cfg (a + b) = (blkIter bs cfg a).bind (fun cfg' => blkIter bs cfg' b) := by
  induction a generalizing cfg with
  | zero => simp [blkIter]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [blkIter]
    cases blkOnce bs cfg with
    | none => rfl
    | some cfg' => exact ih cfg'

theorem blkIter_le_some {Q : Type} {bs : BlkStepFn Q} {cfg cfg₂ : Q × (ℕ → BlkSym) × ℕ}
    {k i : ℕ} (hik : i ≤ k) (hk : blkIter bs cfg k = some cfg₂) :
    ∃ cfg_i, blkIter bs cfg i = some cfg_i := by
  have heq : k = i + (k - i) := by omega
  rw [heq, blkIter_add] at hk
  cases h : blkIter bs cfg i with
  | none => rw [h] at hk; simp at hk
  | some cfg_i => exact ⟨cfg_i, rfl⟩

/-- Little-endian `B`-bit binary representation of `v`. -/
def natToBitsLE : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, v => decide (v % 2 = 1) :: natToBitsLE w (v / 2)

theorem length_natToBitsLE (w v : ℕ) : (natToBitsLE w v).length = w := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih => simp [natToBitsLE, ih]

theorem natToBitsLE_zero (w : ℕ) : natToBitsLE w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [natToBitsLE, List.replicate_succ, ih]

theorem all_false_natToBitsLE_iff :
    ∀ {w v : ℕ}, v < 2 ^ w → ((∀ b ∈ natToBitsLE w v, b = false) ↔ v = 0)
  | 0, v, hv => by
      have hv0 : v = 0 := by simp at hv; omega
      subst hv0
      simp [natToBitsLE]
  | w + 1, v, hv => by
      have hv2 : v / 2 < 2 ^ w := by
        rw [Nat.pow_succ] at hv
        omega
      simp only [natToBitsLE, List.mem_cons, forall_eq_or_imp, decide_eq_false_iff_not,
        all_false_natToBitsLE_iff hv2]
      omega

def incBits : List Bool → List Bool
  | [] => []
  | false :: bs => true :: bs
  | true :: bs => false :: incBits bs

theorem length_incBits (bs : List Bool) : (incBits bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [incBits, ih]

theorem incBits_natToBitsLE :
    ∀ {w v : ℕ}, v + 1 < 2 ^ w → incBits (natToBitsLE w v) = natToBitsLE w (v + 1)
  | 0, v, hv => by simp at hv
  | w + 1, v, hv => by
      rw [Nat.pow_succ] at hv
      by_cases hp : v % 2 = 1
      · have hd1 : decide (v % 2 = 1) = true := decide_eq_true hp
        have hd2 : decide ((v + 1) % 2 = 1) = false := decide_eq_false (by omega)
        have hdiv : (v + 1) / 2 = v / 2 + 1 := by omega
        have hv2 : v / 2 + 1 < 2 ^ w := by omega
        simp only [natToBitsLE, hd1, hd2, hdiv, incBits, incBits_natToBitsLE hv2]
      · have hd1 : decide (v % 2 = 1) = false := decide_eq_false hp
        have hd2 : decide ((v + 1) % 2 = 1) = true := decide_eq_true (by omega)
        have hdiv : (v + 1) / 2 = v / 2 := by omega
        simp only [natToBitsLE, hd1, hd2, hdiv, incBits]

def decBits : List Bool → List Bool
  | [] => []
  | true :: bs => false :: bs
  | false :: bs => true :: decBits bs

theorem length_decBits (bs : List Bool) : (decBits bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [decBits, ih]

theorem decBits_natToBitsLE :
    ∀ {w v : ℕ}, 1 ≤ v → v < 2 ^ w → decBits (natToBitsLE w v) = natToBitsLE w (v - 1)
  | 0, v, hv1, hv2 => by simp at hv2; omega
  | w + 1, v, hv1, hv2 => by
      rw [Nat.pow_succ] at hv2
      by_cases hp : v % 2 = 1
      · have hd1 : decide (v % 2 = 1) = true := decide_eq_true hp
        have hd2 : decide ((v - 1) % 2 = 1) = false := decide_eq_false (by omega)
        have hdiv : (v - 1) / 2 = v / 2 := by omega
        simp only [natToBitsLE, hd1, hd2, hdiv, decBits]
      · have hd1 : decide (v % 2 = 1) = false := decide_eq_false hp
        have hd2 : decide ((v - 1) % 2 = 1) = true := decide_eq_true (by omega)
        have hdiv : (v - 1) / 2 = v / 2 - 1 := by omega
        have hv_pos : 1 ≤ v / 2 := by omega
        have hv_lt : v / 2 < 2 ^ w := by omega
        simp only [natToBitsLE, hd1, hd2, hdiv, decBits, decBits_natToBitsLE hv_pos hv_lt]

/-- Encode a non-empty list of bit-segments into 3-cell block symbols. -/
def encodeSegmentsAux : List (List Bool) → List BlkSym
  | [] => []
  | [lastSeg] => lastSeg.map (blkData false) ++ [blkWall]
  | seg :: next :: rest => seg.map (blkData false) ++ [blkSep] ++ encodeSegmentsAux (next :: rest)

def encodeWorkspace (segs : List (List Bool)) : List BlkSym :=
  blkHome :: encodeSegmentsAux segs

def segStart : List (List Bool) → ℕ → ℕ
  | _, 0 => 1
  | [], _ + 1 => 1
  | seg :: rest, s + 1 => seg.length + 1 + segStart rest s

def isSepOrWall (sym : BlkSym) : Bool := sym.1 && !sym.2.1

theorem length_encodeSegmentsAux :
    ∀ (segs : List (List Bool)), segs ≠ [] →
      (encodeSegmentsAux segs).length = (segs.map (fun s => s.length + 1)).sum
  | [], h => absurd rfl h
  | [lastSeg], _ => by simp [encodeSegmentsAux]
  | seg :: next :: rest, _ => by
      have ih := length_encodeSegmentsAux (next :: rest) (List.cons_ne_nil _ _)
      have hcons : encodeSegmentsAux (seg :: next :: rest) =
          (seg.map (blkData false) ++ [blkSep]) ++ encodeSegmentsAux (next :: rest) := rfl
      rw [hcons, List.length_append, ih]
      simp [Nat.add_assoc]

theorem segStart_pos (segs : List (List Bool)) (s : ℕ) : 1 ≤ segStart segs s := by
  induction s generalizing segs with
  | zero => simp [segStart]
  | succ s ih =>
    cases segs with
    | nil => simp [segStart]
    | cons seg rest =>
      have := ih rest
      simp only [segStart]; omega

theorem segStart_bound :
    ∀ (segs : List (List Bool)) (s : ℕ), s < segs.length →
      segStart segs s + (segs.getD s []).length < (encodeWorkspace segs).length
  | [], _, hs => by simp at hs
  | [lastSeg], 0, _ => by
      simp only [segStart, List.getD_cons_zero, encodeWorkspace, encodeSegmentsAux,
        List.length_cons, List.length_append, List.length_map]
      omega
  | [lastSeg], s + 1, hs => by simp at hs
  | seg :: next :: rest, 0, _ => by
      have hlen := length_encodeSegmentsAux (next :: rest) (List.cons_ne_nil _ _)
      simp only [segStart, List.getD_cons_zero, encodeWorkspace, encodeSegmentsAux,
        List.length_cons, List.length_append, List.length_map, hlen, List.map_cons, List.sum_cons]
      omega
  | seg :: next :: rest, s + 1, hs => by
      have hs' : s < (next :: rest).length := by simpa using hs
      have ih := segStart_bound (next :: rest) s hs'
      simp only [encodeWorkspace, List.length_cons] at ih ⊢
      simp only [segStart, List.getD_cons_succ, encodeSegmentsAux,
        List.length_append, List.length_map, List.length_singleton]
      omega

theorem encodeSegmentsAux_ne_home :
    ∀ (segs : List (List Bool)) (sym : BlkSym),
      sym ∈ encodeSegmentsAux segs → sym ≠ blkHome
  | [], _, h => by simp [encodeSegmentsAux] at h
  | [lastSeg], sym, h => by
      simp only [encodeSegmentsAux, List.mem_append, List.mem_map, List.mem_singleton] at h
      rcases h with ⟨b, _, rfl⟩ | rfl <;> simp [blkData, blkWall, blkHome]
  | seg :: next :: rest, sym, h => by
      simp only [encodeSegmentsAux, List.mem_append, List.mem_map, List.mem_singleton] at h
      rcases h with (⟨b, _, rfl⟩ | rfl) | hrest
      · simp [blkData, blkHome]
      · simp [blkSep, blkHome]
      · exact encodeSegmentsAux_ne_home (next :: rest) sym hrest

theorem getD_append_left {α : Type} (l₁ l₂ : List α) (d : α) {k : ℕ} (hk : k < l₁.length) :
    (l₁ ++ l₂).getD k d = l₁.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getD_append_right {α : Type} (l₁ l₂ : List α) (d : α) {k : ℕ} (hk : l₁.length ≤ k) :
    (l₁ ++ l₂).getD k d = l₂.getD (k - l₁.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hk]

theorem getD_map_blkData (l : List Bool) (m : Bool) {k : ℕ} (hk : k < l.length) :
    (l.map (blkData m)).getD k blkHome = blkData m (l.getD k false) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem encodeWorkspace_getD_zero (segs : List (List Bool)) :
    (encodeWorkspace segs).getD 0 blkHome = blkHome := rfl

theorem encodeWorkspace_ne_home (segs : List (List Bool)) {j : ℕ}
    (hj1 : 1 ≤ j) (hj2 : j < (encodeWorkspace segs).length) :
    (encodeWorkspace segs).getD j blkHome ≠ blkHome := by
  cases j with
  | zero => omega
  | succ j' =>
    have hj' : j' < (encodeSegmentsAux segs).length := by
      simpa [encodeWorkspace] using hj2
    have hgd : (encodeWorkspace segs).getD (j' + 1) blkHome = (encodeSegmentsAux segs)[j'] := by
      simp [encodeWorkspace, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    rw [hgd]
    exact encodeSegmentsAux_ne_home segs _ (List.getElem_mem hj')

theorem encodeSegmentsAux_wall_iff :
    ∀ (segs : List (List Bool)), segs ≠ [] →
      ∀ (k : ℕ), k < (encodeSegmentsAux segs).length →
        ((encodeSegmentsAux segs).getD k blkHome = blkWall ↔
          k = (encodeSegmentsAux segs).length - 1)
  | [], h, _, _ => absurd rfl h
  | [lastSeg], _, k, hk => by
      simp only [encodeSegmentsAux, List.length_append, List.length_map,
        List.length_singleton] at hk ⊢
      by_cases hkl : k < lastSeg.length
      · rw [getD_append_left _ _ _ (by simpa using hkl), getD_map_blkData _ _ hkl]
        simp [blkData, blkWall]; omega
      · have hkeq : k = lastSeg.length := by omega
        subst hkeq
        rw [getD_append_right _ _ _ (by simp)]
        simp
  | seg :: next :: rest, _, k, hk => by
      have hne : next :: rest ≠ [] := List.cons_ne_nil _ _
      have hlen_rest : 1 ≤ (encodeSegmentsAux (next :: rest)).length := by
        rw [length_encodeSegmentsAux _ hne]
        simp only [List.map_cons, List.sum_cons]; omega
      have hcons0 : encodeSegmentsAux (seg :: next :: rest) =
          (seg.map (blkData false) ++ [blkSep]) ++ encodeSegmentsAux (next :: rest) := by
        simp [encodeSegmentsAux]
      rw [hcons0] at hk ⊢
      generalize hpfx : seg.map (blkData false) ++ [blkSep] = pfx at hk ⊢
      generalize hrenc : encodeSegmentsAux (next :: rest) = r_enc at hk hlen_rest ⊢
      have hpfx_len : pfx.length = seg.length + 1 := by rw [← hpfx]; simp
      rw [List.length_append, hpfx_len] at hk ⊢
      by_cases hk1 : k < seg.length + 1
      · rw [getD_append_left _ _ _ (by rw [hpfx_len]; exact hk1), ← hpfx]
        by_cases hk0 : k < seg.length
        · rw [getD_append_left _ _ _ (by simpa using hk0), getD_map_blkData _ _ hk0]
          simp [blkData, blkWall]
          omega
        · have hkeq : k = seg.length := by omega
          subst hkeq
          rw [getD_append_right _ _ _ (by simp)]
          rw [← hrenc] at hlen_rest
          have hne_len : seg.length ≠ seg.length + 1 + (encodeSegmentsAux (next :: rest)).length - 1 := by omega
          rw [← hrenc]
          simp only [List.length_map, Nat.sub_self, List.getD_cons_zero, blkSep, blkWall, hne_len]
          decide
      · rw [getD_append_right _ _ _ (by rw [hpfx_len]; omega), hpfx_len]
        have hk_sub : k - (seg.length + 1) < r_enc.length := by omega
        rw [← hrenc] at hk_sub ⊢
        rw [encodeSegmentsAux_wall_iff (next :: rest) hne (k - (seg.length + 1)) hk_sub]
        rw [hrenc]
        omega

theorem encodeWorkspace_wall_iff (segs : List (List Bool)) (h : segs ≠ [])
    {j : ℕ} (hj : j < (encodeWorkspace segs).length) :
    (encodeWorkspace segs).getD j blkHome = blkWall ↔ j = (encodeWorkspace segs).length - 1 := by
  have hlen_pos : 1 ≤ (encodeSegmentsAux segs).length := by
    rw [length_encodeSegmentsAux segs h]
    cases segs with
    | nil => contradiction
    | cons s l => simp only [List.map_cons, List.sum_cons]; omega
  have hw_len : (encodeWorkspace segs).length = (encodeSegmentsAux segs).length + 1 := rfl
  cases j with
  | zero =>
    simp only [encodeWorkspace, List.getD_cons_zero]
    constructor
    · intro h0; simp [blkHome, blkWall] at h0
    · intro h0
      simp only [List.length_cons, Nat.add_sub_cancel] at h0
      omega
  | succ j' =>
    have hj' : j' < (encodeSegmentsAux segs).length := by omega
    simp only [encodeWorkspace, List.getD_cons_succ, List.length_cons, Nat.add_sub_cancel]
    rw [encodeSegmentsAux_wall_iff segs h j' hj']
    omega

theorem encodeSegmentsAux_seg_data :
    ∀ (segs : List (List Bool)) (s : ℕ), s < segs.length →
      ∀ (i : ℕ), i < (segs.getD s []).length →
        (encodeSegmentsAux segs).getD (segStart segs s - 1 + i) blkHome =
          blkData false ((segs.getD s []).getD i false)
  | [], _, hs, _, _ => by simp at hs
  | [lastSeg], 0, _, i, hi => by
      simp only [List.getD_cons_zero] at hi
      simp only [segStart, List.getD_cons_zero, Nat.sub_self, Nat.zero_add, encodeSegmentsAux]
      rw [getD_append_left _ _ _ (by simpa using hi), getD_map_blkData _ _ hi]
  | [lastSeg], s + 1, hs, _, _ => by simp at hs
  | seg :: next :: rest, 0, _, i, hi => by
      simp only [List.getD_cons_zero] at hi
      simp only [segStart, List.getD_cons_zero, Nat.sub_self, Nat.zero_add, encodeSegmentsAux]
      rw [getD_append_left _ _ _ (by simp; omega),
          getD_append_left _ _ _ (by simpa using hi), getD_map_blkData _ _ hi]
  | seg :: next :: rest, s + 1, hs, i, hi => by
      have hs' : s < (next :: rest).length := by simpa using hs
      have hi' : i < ((next :: rest).getD s []).length := by simpa using hi
      have hs1 := segStart_pos (next :: rest) s
      have ih := encodeSegmentsAux_seg_data (next :: rest) s hs' i hi'
      simp only [segStart, List.getD_cons_succ, encodeSegmentsAux]
      rw [getD_append_right _ _ _ (by simp; omega)]
      simp only [List.length_append, List.length_map, List.length_singleton]
      have hsub : seg.length + 1 + segStart (next :: rest) s - 1 + i - (seg.length + 1) =
          segStart (next :: rest) s - 1 + i := by omega
      rw [hsub, ih]

theorem encodeSegmentsAux_seg_end :
    ∀ (segs : List (List Bool)) (s : ℕ), s < segs.length →
      (encodeSegmentsAux segs).getD (segStart segs s - 1 + (segs.getD s []).length) blkHome =
        (if s + 1 < segs.length then blkSep else blkWall)
  | [], _, hs => by simp at hs
  | [lastSeg], 0, _ => by
      simp only [segStart, List.getD_cons_zero, Nat.sub_self, Nat.zero_add,
        List.length_singleton, Nat.lt_irrefl, ↓reduceIte, encodeSegmentsAux]
      rw [getD_append_right _ _ _ (by simp)]
      simp
  | [lastSeg], s + 1, hs => by simp at hs
  | seg :: next :: rest, 0, _ => by
      have hlt : 0 + 1 < (seg :: next :: rest).length := by simp
      simp only [segStart, List.getD_cons_zero, Nat.sub_self, Nat.zero_add,
        hlt, ↓reduceIte, encodeSegmentsAux]
      rw [getD_append_left _ _ _ (by simp), getD_append_right _ _ _ (by simp)]
      simp
  | seg :: next :: rest, s + 1, hs => by
      have hs' : s < (next :: rest).length := by simpa using hs
      have hs1 := segStart_pos (next :: rest) s
      have ih := encodeSegmentsAux_seg_end (next :: rest) s hs'
      have hite : (if s + 1 + 1 < (seg :: next :: rest).length then blkSep else blkWall) =
          (if s + 1 < (next :: rest).length then blkSep else blkWall) := by simp
      rw [hite]
      have hcons0 : encodeSegmentsAux (seg :: next :: rest) =
          (seg.map (blkData false) ++ [blkSep]) ++ encodeSegmentsAux (next :: rest) := rfl
      simp only [segStart, List.getD_cons_succ]
      rw [hcons0, getD_append_right _ _ _ (by simp; omega)]
      simp only [List.length_append, List.length_map, List.length_singleton]
      have hsub : seg.length + 1 + segStart (next :: rest) s - 1 +
          ((next :: rest).getD s []).length - (seg.length + 1) =
          segStart (next :: rest) s - 1 + ((next :: rest).getD s []).length := by omega
      rw [hsub, ih]

theorem encodeWorkspace_seg_data (segs : List (List Bool)) {s : ℕ} (hs : s < segs.length)
    {i : ℕ} (hi : i < (segs.getD s []).length) :
    (encodeWorkspace segs).getD (segStart segs s + i) blkHome =
      blkData false ((segs.getD s []).getD i false) := by
  have hs1 := segStart_pos segs s
  have hidx : segStart segs s + i = (segStart segs s - 1 + i) + 1 := by omega
  rw [hidx]
  simp only [encodeWorkspace, List.getD_cons_succ]
  exact encodeSegmentsAux_seg_data segs s hs i hi

theorem encodeWorkspace_seg_end (segs : List (List Bool)) {s : ℕ} (hs : s < segs.length) :
    (encodeWorkspace segs).getD (segStart segs s + (segs.getD s []).length) blkHome =
      (if s + 1 < segs.length then blkSep else blkWall) := by
  have hs1 := segStart_pos segs s
  have hidx : segStart segs s + (segs.getD s []).length =
      (segStart segs s - 1 + (segs.getD s []).length) + 1 := by omega
  rw [hidx]
  simp only [encodeWorkspace, List.getD_cons_succ]
  exact encodeSegmentsAux_seg_end segs s hs

theorem segStart_succ_eq (segs : List (List Bool)) {s : ℕ} (hs : s + 1 < segs.length) :
    segStart segs (s + 1) = segStart segs s + (segs.getD s []).length + 1 := by
  induction s generalizing segs with
  | zero =>
    cases segs with
    | nil => simp at hs
    | cons seg rest => simp [segStart]; omega
  | succ s ih =>
    cases segs with
    | nil => simp at hs
    | cons seg rest =>
      have hs' : s + 1 < rest.length := by simpa using hs
      have h := ih rest hs'
      simp only [segStart, List.getD_cons_succ] at h ⊢
      omega

/-- Predicate stating that `σ` agrees with `encodeWorkspace segs` on `0 .. M_blk - 1`. -/
def MatchesWS (σ : ℕ → BlkSym) (segs : List (List Bool)) : Prop :=
  ∀ j, j < (encodeWorkspace segs).length → σ j = (encodeWorkspace segs).getD j blkHome

theorem map_len_set_eq :
    ∀ (segs : List (List Bool)) (s : ℕ) (newSeg : List Bool),
      s < segs.length → newSeg.length = (segs.getD s []).length →
      (segs.set s newSeg).map (fun x => x.length + 1) = segs.map (fun x => x.length + 1)
  | [], _, _, hs, _ => by simp at hs
  | _ :: _, 0, newSeg, _, hlen => by simp [hlen]
  | seg :: rest, s + 1, newSeg, hs, hlen => by
      have hs' : s < rest.length := by simpa using hs
      have hlen' : newSeg.length = (rest.getD s []).length := by simpa using hlen
      simp [map_len_set_eq rest s newSeg hs' hlen']

theorem length_encodeWorkspace_set {segs : List (List Bool)} {s : ℕ} {newSeg : List Bool}
    (hs : s < segs.length) (hlen : newSeg.length = (segs.getD s []).length) :
    (encodeWorkspace (segs.set s newSeg)).length = (encodeWorkspace segs).length := by
  have hne1 : segs ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hne2 : segs.set s newSeg ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_set, List.length_nil] at this
    omega
  simp only [encodeWorkspace, List.length_cons,
    length_encodeSegmentsAux segs hne1, length_encodeSegmentsAux _ hne2,
    map_len_set_eq segs s newSeg hs hlen]

theorem segStart_set_eq :
    ∀ (segs : List (List Bool)) (s k : ℕ) (newSeg : List Bool),
      s < segs.length → newSeg.length = (segs.getD s []).length →
      segStart (segs.set s newSeg) k = segStart segs k
  | [], _, _, _, hs, _ => by simp at hs
  | _ :: _, 0, 0, _, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _, _ => rfl
  | seg :: rest, 0, k + 1, newSeg, _, hlen => by
      simp only [List.getD_cons_zero] at hlen
      simp [segStart, hlen]
  | seg :: rest, s + 1, k + 1, newSeg, hs, hlen => by
      have hs' : s < rest.length := by simpa using hs
      have hlen' : newSeg.length = (rest.getD s []).length := by simpa using hlen
      simp only [List.set_cons_succ, segStart]
      rw [segStart_set_eq rest s k newSeg hs' hlen']

theorem encodeSegmentsAux_set_outside :
    ∀ (segs : List (List Bool)) (s : ℕ) (newSeg : List Bool),
      s < segs.length → newSeg.length = (segs.getD s []).length →
      ∀ (p : ℕ), p < (encodeSegmentsAux segs).length →
        (p < segStart segs s - 1 ∨ segStart segs s - 1 + (segs.getD s []).length ≤ p) →
        (encodeSegmentsAux (segs.set s newSeg)).getD p blkHome =
          (encodeSegmentsAux segs).getD p blkHome
  | [], _, _, hs, _, _, _, _ => by simp at hs
  | [lastSeg], 0, newSeg, _, hlen, p, hp, hout => by
      simp only [List.getD_cons_zero] at hlen hout
      simp only [segStart, Nat.sub_self, Nat.zero_add, Nat.not_lt_zero, false_or] at hout
      simp only [encodeSegmentsAux, List.length_append, List.length_map,
        List.length_singleton] at hp
      have hpeq : p = lastSeg.length := by omega
      subst hpeq
      simp only [List.set_cons_zero, encodeSegmentsAux]
      rw [getD_append_right _ _ _ (by simp [hlen]), getD_append_right _ _ _ (by simp)]
      simp [hlen]
  | [lastSeg], s + 1, _, hs, _, _, _, _ => by simp at hs
  | seg :: next :: rest, 0, newSeg, _, hlen, p, hp, hout => by
      simp only [List.getD_cons_zero] at hlen hout
      simp only [segStart, Nat.sub_self, Nat.zero_add, Nat.not_lt_zero, false_or] at hout
      simp only [List.set_cons_zero, encodeSegmentsAux]
      by_cases hpeq : p = seg.length
      · subst hpeq
        rw [getD_append_left _ _ _ (by simp [hlen]), getD_append_right _ _ _ (by simp [hlen])]
        rw [getD_append_left _ _ _ (by simp), getD_append_right _ _ _ (by simp)]
        simp [hlen]
      · have hp_gt : seg.length + 1 ≤ p := by omega
        rw [getD_append_right _ _ _ (by simp [hlen]; omega),
            getD_append_right _ _ _ (by simp; omega)]
        simp [hlen]
  | seg :: next :: rest, s + 1, newSeg, hs, hlen, p, hp, hout => by
      have hs' : s < (next :: rest).length := by simpa using hs
      have hlen' : newSeg.length = ((next :: rest).getD s []).length := by simpa using hlen
      have hs1 := segStart_pos (next :: rest) s
      have hset_ne : (next :: rest).set s newSeg ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
      have hcons : encodeSegmentsAux (seg :: ((next :: rest).set s newSeg)) =
          (seg.map (blkData false) ++ [blkSep]) ++ encodeSegmentsAux ((next :: rest).set s newSeg) := by
        cases h : (next :: rest).set s newSeg with
        | nil => exact absurd h hset_ne
        | cons a l => simp [encodeSegmentsAux]
      have hcons0 : encodeSegmentsAux (seg :: next :: rest) =
          (seg.map (blkData false) ++ [blkSep]) ++ encodeSegmentsAux (next :: rest) := by
        simp [encodeSegmentsAux]
      simp only [List.set_cons_succ]
      rw [hcons, hcons0]
      rw [hcons0] at hp
      generalize hpfx : seg.map (blkData false) ++ [blkSep] = pfx at hp ⊢
      have hpfx_len : pfx.length = seg.length + 1 := by rw [← hpfx]; simp
      by_cases hp1 : p < seg.length + 1
      · rw [getD_append_left _ _ _ (by rw [hpfx_len]; exact hp1),
            getD_append_left _ _ _ (by rw [hpfx_len]; exact hp1)]
      · rw [getD_append_right _ _ _ (by rw [hpfx_len]; omega),
            getD_append_right _ _ _ (by rw [hpfx_len]; omega), hpfx_len]
        have hp_sub : p - (seg.length + 1) < (encodeSegmentsAux (next :: rest)).length := by
          rw [List.length_append, hpfx_len] at hp
          omega
        refine encodeSegmentsAux_set_outside (next :: rest) s newSeg hs' hlen'
          (p - (seg.length + 1)) hp_sub ?_
        simp only [segStart, List.getD_cons_succ] at hout
        omega

theorem encodeWorkspace_set_outside (segs : List (List Bool)) {s : ℕ} {newSeg : List Bool}
    (hs : s < segs.length) (hlen : newSeg.length = (segs.getD s []).length)
    {j : ℕ} (hj : j < (encodeWorkspace segs).length)
    (hout : j < segStart segs s ∨ segStart segs s + (segs.getD s []).length ≤ j) :
    (encodeWorkspace (segs.set s newSeg)).getD j blkHome =
      (encodeWorkspace segs).getD j blkHome := by
  have hs1 := segStart_pos segs s
  cases j with
  | zero => rfl
  | succ p =>
    have hp : p < (encodeSegmentsAux segs).length := by simpa [encodeWorkspace] using hj
    simp only [encodeWorkspace, List.getD_cons_succ]
    refine encodeSegmentsAux_set_outside segs s newSeg hs hlen p hp ?_
    omega

/-- Generic `RewindToHome` helper for any `BlkStepFn` state `q_rw`. -/
theorem blkRewind_aux {Q : Type} (bs : BlkStepFn Q) (M_blk : ℕ) (q_rw : Q)
    (h_home : bs q_rw blkHome = none)
    (h_other : ∀ sym, sym ≠ blkHome → bs q_rw sym = some (q_rw, sym, QCSD_HeadDir.left)) :
    ∀ j (σ : ℕ → BlkSym),
      j < M_blk →
      σ 0 = blkHome →
      (∀ i, 1 ≤ i → i ≤ j → σ i ≠ blkHome) →
      blkIter bs (q_rw, σ, j) j = some (q_rw, σ, 0) ∧
      bs q_rw (σ 0) = none ∧
      (∀ i ≤ j, ∀ q' σ' j', blkIter bs (q_rw, σ, j) i = some (q', σ', j') → j' < M_blk) ∧
      (∀ i < j, ∀ q' σ' j' q'' sym' dir,
        blkIter bs (q_rw, σ, j) i = some (q', σ', j') →
        bs q' (σ' j') = some (q'', sym', dir) →
        (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
  intro j
  induction j with
  | zero =>
    intro σ hj0 h0 _
    refine ⟨rfl, by rw [h0]; exact h_home, ?_, ?_⟩
    · intro i hi _ _ j' hi_eq
      obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
      cases hi_eq; exact hj0
    · intro i hi; omega
  | succ j ih =>
    intro σ hj_lt h0 hne
    have hnej : σ (j + 1) ≠ blkHome := hne (j + 1) (by omega) (Nat.le_refl _)
    have hbs : bs q_rw (σ (j + 1)) = some (q_rw, σ (j + 1), QCSD_HeadDir.left) :=
      h_other _ hnej
    rcases ih σ (by omega) h0 (fun i hi1 hij => hne i hi1 (by omega))
      with ⟨hiter, hnone, hbnd, hdir⟩
    refine ⟨?_, hnone, ?_, ?_⟩
    · simp [blkIter, blkOnce, hbs, moveHead, hiter]
    · intro i hi q' σ' j' hi_eq
      cases i with
      | zero => cases hi_eq; exact hj_lt
      | succ i =>
        simp only [blkIter, blkOnce, hbs, moveHead, Function.update_eq_self] at hi_eq
        exact hbnd i (Nat.le_of_succ_le_succ hi) q' σ' j' hi_eq
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      cases i with
      | zero =>
        cases hi_eq
        rw [hbs] at hbs'; cases hbs'
        exact ⟨fun _ => by omega, by simp⟩
      | succ i =>
        simp only [blkIter, blkOnce, hbs, moveHead, Function.update_eq_self] at hi_eq
        exact hdir i (Nat.lt_of_succ_lt_succ hi) q' σ' j' q'' sym' dir hi_eq hbs'

/-- Generic `GoToSeg` helper: walks from `0` across `s` separators to `segStart segs s`. -/
theorem blkSkipData_aux {Q : Type} (bs : BlkStepFn Q) (M_blk : ℕ) (q_go : Q)
    (h_data : ∀ m b, bs q_go (blkData m b) = some (q_go, blkData m b, QCSD_HeadDir.right)) :
    ∀ len start (σ : ℕ → BlkSym),
      start + len < M_blk →
      (∀ i < len, ∃ m b, σ (start + i) = blkData m b) →
      blkIter bs (q_go, σ, start) len = some (q_go, σ, start + len) ∧
      (∀ i ≤ len, ∀ q' σ' j',
        blkIter bs (q_go, σ, start) i = some (q', σ', j') → j' < M_blk) ∧
      (∀ i < len, ∀ q' σ' j' q'' sym' dir,
        blkIter bs (q_go, σ, start) i = some (q', σ', j') →
        bs q' (σ' j') = some (q'', sym', dir) →
        (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
  intro len
  induction len with
  | zero =>
    intro start σ hlt _
    refine ⟨by simp [blkIter], ?_, ?_⟩
    · intro i hi _ _ j' hi_eq
      obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
      cases hi_eq; omega
    · intro i hi; omega
  | succ len ih =>
    intro start σ hlt hdat
    rcases hdat 0 (Nat.zero_lt_succ len) with ⟨m0, b0, h0⟩
    rw [Nat.add_zero] at h0
    have hbs : bs q_go (σ start) = some (q_go, σ start, QCSD_HeadDir.right) := by
      rw [h0]; exact h_data m0 b0
    rcases ih (start + 1) σ (by omega) (fun i hi => by
        have := hdat (i + 1) (Nat.succ_lt_succ hi)
        rwa [Nat.add_assoc, Nat.add_comm 1 i] ) with ⟨hiter, hbnd, hdir⟩
    have hadd : start + 1 + len = start + (len + 1) := by omega
    rw [hadd] at hiter
    refine ⟨?_, ?_, ?_⟩
    · simp [blkIter, blkOnce, hbs, moveHead, hiter]
    · intro i hi q' σ' j' hi_eq
      cases i with
      | zero => cases hi_eq; omega
      | succ i =>
        simp only [blkIter, blkOnce, hbs, moveHead, Function.update_eq_self] at hi_eq
        exact hbnd i (Nat.le_of_succ_le_succ hi) q' σ' j' hi_eq
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      cases i with
      | zero =>
        cases hi_eq; rw [hbs] at hbs'; cases hbs'
        exact ⟨by simp, fun _ => by omega⟩
      | succ i =>
        simp only [blkIter, blkOnce, hbs, moveHead, Function.update_eq_self] at hi_eq
        exact hdir i (Nat.lt_of_succ_lt_succ hi) q' σ' j' q'' sym' dir hi_eq hbs'

theorem segStart_mono (segs : List (List Bool)) :
    ∀ {a b : ℕ}, a ≤ b → b < segs.length → segStart segs a ≤ segStart segs b := by
  intro a b hab hblt
  induction b with
  | zero =>
    obtain rfl : a = 0 := Nat.eq_zero_of_le_zero hab
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hab' : a ≤ b
    · have h1 := ih hab' (by omega)
      have h2 := segStart_succ_eq segs hblt
      omega
    · have haeq : a = b + 1 := by omega
      subst haeq
      exact Nat.le_refl _

theorem blkGoToSeg_from_one {Q : Type} (bs : BlkStepFn Q) (segs : List (List Bool))
    (σ : ℕ → BlkSym) (hws : MatchesWS σ segs)
    (go : ℕ → Q) (S_max : ℕ)
    (h_data : ∀ r < S_max, ∀ m b, bs (go (r + 1)) (blkData m b) =
      some (go (r + 1), blkData m b, QCSD_HeadDir.right))
    (h_sep : ∀ r < S_max, bs (go (r + 1)) blkSep = some (go r, blkSep, QCSD_HeadDir.right)) :
    let M_blk := (encodeWorkspace segs).length
    ∀ k s, k ≤ S_max → k + s < segs.length →
      blkIter bs (go k, σ, segStart segs s) (segStart segs (s + k) - segStart segs s) =
        some (go 0, σ, segStart segs (s + k)) ∧
      (∀ i ≤ segStart segs (s + k) - segStart segs s, ∀ q' σ' j',
        blkIter bs (go k, σ, segStart segs s) i = some (q', σ', j') → j' < M_blk) ∧
      (∀ i < segStart segs (s + k) - segStart segs s, ∀ q' σ' j' q'' sym' dir,
        blkIter bs (go k, σ, segStart segs s) i = some (q', σ', j') →
        bs q' (σ' j') = some (q'', sym', dir) →
        (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
  intro M_blk k
  induction k with
  | zero =>
    intro s _ hs
    have hsb := segStart_bound segs s (by omega)
    simp only [Nat.add_zero, Nat.sub_self]
    refine ⟨rfl, ?_, ?_⟩
    · intro i hi _ _ j' hi_eq
      obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
      cases hi_eq; omega
    · intro i hi; omega
  | succ k ih =>
    intro s hkS hs
    have hk_lt : k < S_max := by omega
    have hs_lt : s < segs.length := by omega
    have hs1_lt : s + 1 < segs.length := by omega
    have hsb := segStart_bound segs s hs_lt
    have hsucc := segStart_succ_eq segs hs1_lt
    let L_s := (segs.getD s []).length
    have hdat_s : ∀ i < L_s, ∃ m b, σ (segStart segs s + i) = blkData m b := by
      intro i hi
      refine ⟨false, (segs.getD s []).getD i false, ?_⟩
      rw [hws _ (by omega)]
      exact encodeWorkspace_seg_data segs hs_lt hi
    rcases blkSkipData_aux bs M_blk (go (k + 1)) (h_data k hk_lt) L_s (segStart segs s) σ hsb hdat_s
      with ⟨hiter_d, hbnd_d, hdir_d⟩
    have hsep_at : σ (segStart segs s + L_s) = blkSep := by
      rw [hws _ hsb]
      have hend := encodeWorkspace_seg_end segs hs_lt
      simpa [L_s, hs1_lt] using hend
    have hbs_sep : bs (go (k + 1)) (σ (segStart segs s + L_s)) =
        some (go k, σ (segStart segs s + L_s), QCSD_HeadDir.right) := by
      rw [hsep_at]; exact h_sep k hk_lt
    have hsep_step : blkIter bs (go (k + 1), σ, segStart segs s + L_s) 1 =
        some (go k, σ, segStart segs (s + 1)) := by
      have hsucc' : segStart segs s + L_s + 1 = segStart segs (s + 1) := by
        dsimp only [L_s]; omega
      simp [blkIter, blkOnce, hbs_sep, moveHead, hsucc']
    have hsk_eq : s + (k + 1) = (s + 1) + k := by omega
    rcases ih (s + 1) (by omega) (by omega) with ⟨hiter_rest, hbnd_rest, hdir_rest⟩
    rw [← hsk_eq] at hiter_rest hbnd_rest hdir_rest
    have hsk_mono : segStart segs (s + 1) ≤ segStart segs (s + (k + 1)) :=
      segStart_mono segs (by omega) (by omega)
    have htot_len : segStart segs (s + (k + 1)) - segStart segs s =
        L_s + 1 + (segStart segs (s + (k + 1)) - segStart segs (s + 1)) := by omega
    rw [htot_len]
    refine ⟨?_, ?_, ?_⟩
    · rw [blkIter_add, blkIter_add, hiter_d, Option.bind_some, hsep_step, Option.bind_some, hiter_rest]
    · intro i hi q' σ' j' hi_eq
      by_cases hi1 : i ≤ L_s
      · rcases blkIter_le_some hi1 hiter_d with ⟨⟨qi, σi, ji⟩, hsub⟩
        rw [hsub] at hi_eq; cases hi_eq
        exact hbnd_d i hi1 q' σ' j' hsub
      · have heq : i = L_s + 1 + (i - (L_s + 1)) := by omega
        rw [heq, blkIter_add, blkIter_add, hiter_d, Option.bind_some, hsep_step,
          Option.bind_some] at hi_eq
        exact hbnd_rest (i - (L_s + 1)) (by omega) q' σ' j' hi_eq
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      by_cases hi1 : i < L_s
      · exact hdir_d i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
      · by_cases hi2 : i = L_s
        · subst hi2
          rw [hiter_d] at hi_eq; cases hi_eq
          rw [hbs_sep] at hbs'; cases hbs'
          have hsb1 := segStart_bound segs (s + 1) hs1_lt
          exact ⟨by simp, fun _ => by omega⟩
        · have heq : i = L_s + 1 + (i - (L_s + 1)) := by omega
          rw [heq, blkIter_add, blkIter_add, hiter_d, Option.bind_some, hsep_step,
            Option.bind_some] at hi_eq
          exact hdir_rest (i - (L_s + 1)) (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

theorem blkGoToSeg_aux {Q : Type} (bs : BlkStepFn Q) (segs : List (List Bool))
    (σ : ℕ → BlkSym) (hws : MatchesWS σ segs)
    (go : ℕ → Q) {s : ℕ} (hs : s < segs.length)
    (h_home : bs (go s) blkHome = some (go s, blkHome, QCSD_HeadDir.right))
    (h_data : ∀ r < s, ∀ m b, bs (go (r + 1)) (blkData m b) =
      some (go (r + 1), blkData m b, QCSD_HeadDir.right))
    (h_sep : ∀ r < s, bs (go (r + 1)) blkSep = some (go r, blkSep, QCSD_HeadDir.right)) :
    let M_blk := (encodeWorkspace segs).length
    blkIter bs (go s, σ, 0) (segStart segs s) = some (go 0, σ, segStart segs s) ∧
    (∀ i ≤ segStart segs s, ∀ q' σ' j',
      blkIter bs (go s, σ, 0) i = some (q', σ', j') → j' < M_blk) ∧
    (∀ i < segStart segs s, ∀ q' σ' j' q'' sym' dir,
      blkIter bs (go s, σ, 0) i = some (q', σ', j') →
      bs q' (σ' j') = some (q'', sym', dir) →
      (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
  intro M_blk
  have hsb := segStart_bound segs s hs
  have hs1 := segStart_pos segs s
  have h0_at : σ 0 = blkHome := (hws 0 (by omega)).trans (encodeWorkspace_getD_zero segs)
  have hbs0 : bs (go s) (σ 0) = some (go s, σ 0, QCSD_HeadDir.right) := by
    rw [h0_at]; exact h_home
  have hstep0 : blkIter bs (go s, σ, 0) 1 = some (go s, σ, 1) := by
    simp [blkIter, blkOnce, hbs0, moveHead]
  rcases blkGoToSeg_from_one bs segs σ hws go s h_data h_sep s 0 (Nat.le_refl s) (by omega)
    with ⟨hiter_r, hbnd_r, hdir_r⟩
  simp only [Nat.zero_add, segStart] at hiter_r hbnd_r hdir_r
  have hlen : segStart segs s = 1 + (segStart segs s - 1) := by omega
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [hlen]
    rw [blkIter_add, hstep0, Option.bind_some, hiter_r]
  · intro i hi q' σ' j' hi_eq
    cases i with
    | zero => cases hi_eq; omega
    | succ i' =>
      rw [Nat.add_comm i' 1, blkIter_add, hstep0, Option.bind_some] at hi_eq
      exact hbnd_r i' (by omega) q' σ' j' hi_eq
  · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
    cases i with
    | zero =>
      cases hi_eq; rw [hbs0] at hbs'; cases hbs'
      exact ⟨by simp, fun _ => by omega⟩
    | succ i' =>
      rw [Nat.add_comm i' 1, blkIter_add, hstep0, Option.bind_some] at hi_eq
      exact hdir_r i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

/-- Sweep every workspace block `0 .. M_blk - 1` to `blkHome = (true, true, true)` and exit at `0`. -/
def blkSweepTrue : BlkStepFn Bool :=
  fun sweeping sym =>
    if !sweeping then
      if sym = blkWall then some (true, blkHome, QCSD_HeadDir.left)
      else some (false, sym, QCSD_HeadDir.right)
    else
      if sym = blkHome then none
      else some (true, blkHome, QCSD_HeadDir.left)

theorem blkSweepTrue_right_aux (M_blk : ℕ) (σ : ℕ → BlkSym)
    (hwall : ∀ j < M_blk, (σ j = blkWall ↔ j = M_blk - 1)) :
    ∀ d j, j + d = M_blk - 1 → j < M_blk →
      blkIter blkSweepTrue (false, σ, j) d = some (false, σ, M_blk - 1) ∧
      (∀ i ≤ d, ∀ q' σ' j',
        blkIter blkSweepTrue (false, σ, j) i = some (q', σ', j') → j' < M_blk) ∧
      (∀ i < d, ∀ q' σ' j' q'' sym' dir,
        blkIter blkSweepTrue (false, σ, j) i = some (q', σ', j') →
        blkSweepTrue q' (σ' j') = some (q'', sym', dir) →
        (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
  intro d
  induction d with
  | zero =>
    intro j hjd hj
    have hjeq : j = M_blk - 1 := by omega
    subst hjeq
    refine ⟨rfl, ?_, ?_⟩
    · intro i hi _ _ j' hi_eq
      obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
      cases hi_eq; exact hj
    · intro i hi; omega
  | succ d ih =>
    intro j hjd hj
    have hj_ne : j ≠ M_blk - 1 := by omega
    have hnw : σ j ≠ blkWall := fun h => hj_ne ((hwall j hj).mp h)
    have hbs : blkSweepTrue false (σ j) = some (false, σ j, QCSD_HeadDir.right) := by
      simp [blkSweepTrue, hnw]
    rcases ih (j + 1) (by omega) (by omega) with ⟨hiter, hbnd, hdir⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [blkIter, blkOnce, hbs, moveHead, hiter]
    · intro i hi q' σ' j' hi_eq
      cases i with
      | zero => cases hi_eq; exact hj
      | succ i =>
        simp only [blkIter, blkOnce, hbs, moveHead, Function.update_eq_self] at hi_eq
        exact hbnd i (Nat.le_of_succ_le_succ hi) q' σ' j' hi_eq
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      cases i with
      | zero =>
        cases hi_eq
        rw [hbs] at hbs'
        cases hbs'
        exact ⟨by simp, fun _ => by omega⟩
      | succ i =>
        simp only [blkIter, blkOnce, hbs, moveHead, Function.update_eq_self] at hi_eq
        exact hdir i (Nat.lt_of_succ_lt_succ hi) q' σ' j' q'' sym' dir hi_eq hbs'

theorem blkSweepTrue_left_aux (M_blk : ℕ) :
    ∀ j (σ : ℕ → BlkSym),
      j < M_blk →
      σ 0 = blkHome →
      (∀ i, 1 ≤ i → i ≤ j → σ i ≠ blkHome) →
      ∃ σ_end : ℕ → BlkSym,
        (∀ i ≤ j, σ_end i = blkHome) ∧
        (∀ i, j < i → σ_end i = σ i) ∧
        blkIter blkSweepTrue (true, σ, j) j = some (true, σ_end, 0) ∧
        blkSweepTrue true (σ_end 0) = none ∧
        (∀ i ≤ j, ∀ q' σ' j',
          blkIter blkSweepTrue (true, σ, j) i = some (q', σ', j') → j' < M_blk) ∧
        (∀ i < j, ∀ q' σ' j' q'' sym' dir,
          blkIter blkSweepTrue (true, σ, j) i = some (q', σ', j') →
          blkSweepTrue q' (σ' j') = some (q'', sym', dir) →
          (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
  intro j
  induction j with
  | zero =>
    intro σ hj0 h0 _
    refine ⟨σ, ?_, fun _ _ => rfl, rfl, ?_, ?_, ?_⟩
    · intro i hi
      obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
      exact h0
    · simp [blkSweepTrue, h0]
    · intro i hi _ _ j' hi_eq
      obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
      cases hi_eq; exact hj0
    · intro i hi; omega
  | succ j ih =>
    intro σ hj_lt h0 hne
    have hnej : σ (j + 1) ≠ blkHome := hne (j + 1) (by omega) (Nat.le_refl _)
    have hbs : blkSweepTrue true (σ (j + 1)) = some (true, blkHome, QCSD_HeadDir.left) := by
      simp [blkSweepTrue, hnej]
    let σ₁ := Function.update σ (j + 1) blkHome
    have h0' : σ₁ 0 = blkHome := by
      dsimp only [σ₁]
      rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ j + 1)]
      exact h0
    have hne' : ∀ i, 1 ≤ i → i ≤ j → σ₁ i ≠ blkHome := by
      intro i hi1 hij
      dsimp only [σ₁]
      rw [Function.update_of_ne (by omega : i ≠ j + 1)]
      exact hne i hi1 (by omega)
    rcases ih σ₁ (by omega) h0' hne' with ⟨σ_end, hall, hout, hiter, hnone, hbnd, hdir⟩
    refine ⟨σ_end, ?_, ?_, ?_, hnone, ?_, ?_⟩
    · intro i hi
      by_cases hij : i ≤ j
      · exact hall i hij
      · have hieq : i = j + 1 := by omega
        subst hieq
        rw [hout (j + 1) (by omega)]
        simp [σ₁]
    · intro i hi
      rw [hout i (by omega)]
      exact Function.update_of_ne (by omega : i ≠ j + 1) _ _
    · simp [blkIter, blkOnce, hbs, moveHead, σ₁, hiter]
    · intro i hi q' σ' j' hi_eq
      cases i with
      | zero => cases hi_eq; exact hj_lt
      | succ i =>
        simp only [blkIter, blkOnce, hbs, moveHead] at hi_eq
        exact hbnd i (Nat.le_of_succ_le_succ hi) q' σ' j' hi_eq
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      cases i with
      | zero =>
        cases hi_eq
        rw [hbs] at hbs'
        cases hbs'
        exact ⟨fun _ => by omega, by simp⟩
      | succ i =>
        simp only [blkIter, blkOnce, hbs, moveHead] at hi_eq
        exact hdir i (Nat.lt_of_succ_lt_succ hi) q' σ' j' q'' sym' dir hi_eq hbs'

theorem blkSweepTrue_spec (segs : List (List Bool)) (hsegs : segs ≠ [])
    (σ : ℕ → BlkSym) (hws : MatchesWS σ segs) :
    let M_blk := (encodeWorkspace segs).length
    ∃ σ_end : ℕ → BlkSym,
      (∀ j < M_blk, σ_end j = blkHome) ∧
      BlkExec blkSweepTrue M_blk false σ 0 true σ_end 0 (2 * M_blk) := by
  intro M_blk
  have hM_ge2 : 2 ≤ M_blk := by
    have := length_encodeSegmentsAux segs hsegs
    cases segs with
    | nil => contradiction
    | cons s l =>
      simp only [M_blk, encodeWorkspace, List.length_cons, this, List.map_cons, List.sum_cons]
      omega
  have hwall : ∀ j < M_blk, (σ j = blkWall ↔ j = M_blk - 1) := by
    intro j hj
    rw [hws j hj]
    exact encodeWorkspace_wall_iff segs hsegs hj
  rcases blkSweepTrue_right_aux M_blk σ hwall (M_blk - 1) 0 (by omega) (by omega)
    with ⟨hiter_r, hbnd_r, hdir_r⟩
  have hw_at : σ (M_blk - 1) = blkWall := (hwall (M_blk - 1) (by omega)).mpr rfl
  have hbs_turn : blkSweepTrue false (σ (M_blk - 1)) =
      some (true, blkHome, QCSD_HeadDir.left) := by
    simp [blkSweepTrue, hw_at]
  let σ_mid := Function.update σ (M_blk - 1) blkHome
  have h0_mid : σ_mid 0 = blkHome := by
    have hne0 : (0 : ℕ) ≠ M_blk - 1 := by omega
    dsimp only [σ_mid]
    rw [Function.update_of_ne hne0]
    exact (hws 0 (by omega)).trans (encodeWorkspace_getD_zero segs)
  have hne_mid : ∀ i, 1 ≤ i → i ≤ M_blk - 2 → σ_mid i ≠ blkHome := by
    intro i hi1 hi2
    have hnei : i ≠ M_blk - 1 := by omega
    dsimp only [σ_mid]
    rw [Function.update_of_ne hnei, hws i (by omega)]
    exact encodeWorkspace_ne_home segs hi1 (by omega)
  rcases blkSweepTrue_left_aux M_blk (M_blk - 2) σ_mid (by omega) h0_mid hne_mid
    with ⟨σ_end, hall_l, hout_l, hiter_l, hnone_l, hbnd_l, hdir_l⟩
  have hturn_step : blkIter blkSweepTrue (false, σ, M_blk - 1) 1 =
      some (true, σ_mid, M_blk - 2) := by
    have hsub : M_blk - 1 - 1 = M_blk - 2 := by omega
    simp [blkIter, blkOnce, hbs_turn, moveHead, hsub, σ_mid]
  refine ⟨σ_end, ?_, (M_blk - 1) + 1 + (M_blk - 2), by omega, ?_, hnone_l, ?_, ?_⟩
  · intro j hj
    by_cases hj2 : j ≤ M_blk - 2
    · exact hall_l j hj2
    · have hjeq : j = M_blk - 1 := by omega
      subst hjeq
      rw [hout_l (M_blk - 1) (by omega)]
      simp [σ_mid]
  · rw [blkIter_add, blkIter_add, hiter_r, Option.bind_some, hturn_step, Option.bind_some, hiter_l]
  · intro i hi q' σ' j' hi_eq
    by_cases hi1 : i ≤ M_blk - 1
    · rcases blkIter_le_some hi1 hiter_r with ⟨⟨qi, σi, ji⟩, hsub⟩
      rw [hsub] at hi_eq; cases hi_eq
      exact hbnd_r i hi1 q' σ' j' hsub
    · have heq : i = (M_blk - 1) + 1 + (i - ((M_blk - 1) + 1)) := by omega
      rw [heq, blkIter_add, blkIter_add, hiter_r, Option.bind_some, hturn_step,
        Option.bind_some] at hi_eq
      exact hbnd_l (i - ((M_blk - 1) + 1)) (by omega) q' σ' j' hi_eq
  · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
    by_cases hi1 : i < M_blk - 1
    · exact hdir_r i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
    · by_cases hi2 : i = M_blk - 1
      · subst hi2
        rw [hiter_r] at hi_eq; cases hi_eq
        rw [hbs_turn] at hbs'; cases hbs'
        exact ⟨fun _ => by omega, by simp⟩
      · have heq : i = (M_blk - 1) + 1 + (i - ((M_blk - 1) + 1)) := by omega
        rw [heq, blkIter_add, blkIter_add, hiter_r, Option.bind_some, hturn_step,
          Option.bind_some] at hi_eq
        exact hdir_l (i - ((M_blk - 1) + 1)) (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

/-- Generic single-pass segment transformer (`incBits`, `decBits`, `zeroBits`). -/
def applyTransform (stepBit : Bool → Bool × Bool) : List Bool → List Bool
  | [] => []
  | b :: bs =>
      let (b', stop) := stepBit b
      if stop then b' :: bs else b' :: applyTransform stepBit bs

theorem length_applyTransform (stepBit : Bool → Bool × Bool) (bs : List Bool) :
    (applyTransform stepBit bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [applyTransform]
    split_ifs <;> simp [ih]

def stepBitInc (b : Bool) : Bool × Bool := (!b, !b)
def stepBitDec (b : Bool) : Bool × Bool := (!b, b)
def stepBitZero (_ : Bool) : Bool × Bool := (false, false)

theorem applyTransform_inc (bs : List Bool) :
    applyTransform stepBitInc bs = incBits bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [applyTransform, stepBitInc, incBits, ih]

theorem applyTransform_dec (bs : List Bool) :
    applyTransform stepBitDec bs = decBits bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [applyTransform, stepBitDec, decBits, ih]

theorem applyTransform_zero (bs : List Bool) :
    applyTransform stepBitZero bs = List.replicate bs.length false := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [applyTransform, stepBitZero, List.replicate_succ, ih]

def blkTransformSeg (MaxSeg : ℕ) (stepBit : Bool → Bool × Bool) :
    BlkStepFn (Fin (MaxSeg + 1) × Bool) :=
  fun (rem, rewinding) sym =>
    if rewinding then
      if sym = blkHome then none
      else some ((rem, true), sym, QCSD_HeadDir.left)
    else if sym = blkHome then
      some ((rem, false), blkHome, QCSD_HeadDir.right)
    else if hrem : 0 < rem.val then
      let prev : Fin (MaxSeg + 1) := ⟨rem.val - 1, by omega⟩
      if sym = blkSep then some ((prev, false), blkSep, QCSD_HeadDir.right)
      else some ((rem, false), sym, QCSD_HeadDir.right)
    else
      if !sym.1 then
        let (b', stop) := stepBit sym.2.2
        if stop then some ((0, true), blkData false b', QCSD_HeadDir.left)
        else some ((0, false), blkData false b', QCSD_HeadDir.right)
      else
        some ((0, true), sym, QCSD_HeadDir.left)

theorem MatchesWS_update_seg_bit (segs : List (List Bool)) {s : ℕ} (hs : s < segs.length)
    (pre' : List Bool) (b b' : Bool) (rest : List Bool)
    (hlen_seg : (pre' ++ b :: rest).length = (segs.getD s []).length)
    {σ : ℕ → BlkSym} (hws : MatchesWS σ (segs.set s (pre' ++ b :: rest))) :
    MatchesWS (Function.update σ (segStart segs s + pre'.length) (blkData false b'))
      (segs.set s (pre' ++ b' :: rest)) := by
  have hlen1 : (pre' ++ b' :: rest).length = (segs.getD s []).length := by
    simp only [List.length_append, List.length_cons] at hlen_seg ⊢; exact hlen_seg
  have hM1 := length_encodeWorkspace_set hs hlen_seg
  have hM2 := length_encodeWorkspace_set hs hlen1
  have hs_set : segStart (segs.set s (pre' ++ b' :: rest)) s = segStart segs s :=
    segStart_set_eq segs s s _ hs hlen1
  have hs_set0 : segStart (segs.set s (pre' ++ b :: rest)) s = segStart segs s :=
    segStart_set_eq segs s s _ hs hlen_seg
  intro j hj
  rw [hM2] at hj
  by_cases hjeq : j = segStart segs s + pre'.length
  · subst hjeq
    rw [Function.update_self]
    have hs_lt' : s < (segs.set s (pre' ++ b' :: rest)).length := by simpa using hs
    have hget_set : (segs.set s (pre' ++ b' :: rest)).getD s [] = pre' ++ b' :: rest := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hs]
    have hi_lt : pre'.length < ((segs.set s (pre' ++ b' :: rest)).getD s []).length := by
      rw [hget_set]; simp
    have hd := encodeWorkspace_seg_data (segs.set s (pre' ++ b' :: rest)) hs_lt' hi_lt
    rw [hs_set, hget_set] at hd
    rw [hd, getD_append_right _ _ _ (Nat.le_refl _), Nat.sub_self]
    rfl
  · rw [Function.update_of_ne hjeq, hws j (by omega)]
    by_cases hin : segStart segs s ≤ j ∧ j < segStart segs s + (segs.getD s []).length
    · let idx := j - segStart segs s
      have hj_idx : j = segStart segs s + idx := by omega
      have hidx_ne : idx ≠ pre'.length := by omega
      have hget1 : (segs.set s (pre' ++ b :: rest)).getD s [] = pre' ++ b :: rest := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hs]
      have hget2 : (segs.set s (pre' ++ b' :: rest)).getD s [] = pre' ++ b' :: rest := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hs]
      have hs1' : s < (segs.set s (pre' ++ b :: rest)).length := by simpa using hs
      have hs2' : s < (segs.set s (pre' ++ b' :: rest)).length := by simpa using hs
      have hi1 : idx < ((segs.set s (pre' ++ b :: rest)).getD s []).length := by
        rw [hget1]; omega
      have hi2 : idx < ((segs.set s (pre' ++ b' :: rest)).getD s []).length := by
        rw [hget2]; omega
      have hd1 := encodeWorkspace_seg_data (segs.set s (pre' ++ b :: rest)) hs1' hi1
      have hd2 := encodeWorkspace_seg_data (segs.set s (pre' ++ b' :: rest)) hs2' hi2
      rw [hs_set0, hget1, ← hj_idx] at hd1
      rw [hs_set, hget2, ← hj_idx] at hd2
      rw [hd1, hd2]
      congr 1
      by_cases hlt_p : idx < pre'.length
      · rw [getD_append_left _ _ _ hlt_p, getD_append_left _ _ _ hlt_p]
      · have hgt_p : pre'.length + 1 ≤ idx := by omega
        rw [getD_append_right _ _ _ (by omega), getD_append_right _ _ _ (by omega)]
        have hpos : 1 ≤ idx - pre'.length := by omega
        cases hdiff : idx - pre'.length with
        | zero => omega
        | succ m => simp
    · have hout : j < segStart segs s ∨ segStart segs s + (segs.getD s []).length ≤ j := by omega
      rw [encodeWorkspace_set_outside segs hs hlen_seg hj hout,
          encodeWorkspace_set_outside segs hs hlen1 hj hout]

theorem blkTransformSeg_scan_aux (MaxSeg : ℕ) (stepBit : Bool → Bool × Bool)
    (segs : List (List Bool)) {s : ℕ} (hs : s < segs.length) :
    let M_blk := (encodeWorkspace segs).length
    ∀ (suf pre' : List Bool) (σ : ℕ → BlkSym),
      (pre' ++ suf).length = (segs.getD s []).length →
      MatchesWS σ (segs.set s (pre' ++ suf)) →
      ∃ σ_end : ℕ → BlkSym,
        MatchesWS σ_end (segs.set s (pre' ++ applyTransform stepBit suf)) ∧
        BlkExec (blkTransformSeg MaxSeg stepBit) M_blk
          (0, false) σ (segStart segs s + pre'.length)
          (0, true) σ_end 0 (suf.length + 1 + M_blk) := by
  intro M_blk suf
  induction suf with
  | nil =>
    intro pre' σ hlen hws
    simp only [List.append_nil, applyTransform] at hlen hws ⊢
    have hM := length_encodeWorkspace_set hs hlen
    have hs_set := segStart_set_eq segs s s pre' hs hlen
    have hs' : s < (segs.set s pre').length := by simpa using hs
    have hget : (segs.set s pre').getD s [] = pre' := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hs]
    have hsb := segStart_bound segs s hs
    have hend_sym : (σ (segStart segs s + pre'.length)).1 = true := by
      rw [hws _ (by omega)]
      have he := encodeWorkspace_seg_end (segs.set s pre') hs'
      rw [hs_set, hget] at he
      rw [he]
      split_ifs <;> rfl
    have hbs : blkTransformSeg MaxSeg stepBit (0, false) (σ (segStart segs s + pre'.length)) =
        some ((0, true), σ (segStart segs s + pre'.length), QCSD_HeadDir.left) := by
      rcases hsym : σ (segStart segs s + pre'.length) with ⟨c0, c1, c2⟩
      rw [hsym] at hend_sym; simp only at hend_sym; subst hend_sym
      cases c1 with
      | true =>
        exfalso
        have hne_h := encodeWorkspace_ne_home (segs.set s pre')
          (by have := segStart_pos segs s; omega) (j := segStart segs s + pre'.length) (by omega)
        have hws_at := hws (segStart segs s + pre'.length) (by omega)
        rw [hsym] at hws_at
        cases c2
        · have he := encodeWorkspace_seg_end (segs.set s pre') hs'
          rw [hs_set, hget, ← hws_at] at he
          split_ifs at he <;> simp [blkSep, blkWall] at he
        · exact hne_h hws_at.symm
      | false =>
        simp [blkTransformSeg, blkHome]
    have hs1 := segStart_pos segs s
    let j_prev := segStart segs s + pre'.length - 1
    have hstep1 : blkIter (blkTransformSeg MaxSeg stepBit)
        ((0, false), σ, segStart segs s + pre'.length) 1 = some ((0, true), σ, j_prev) := by
      simp [blkIter, blkOnce, hbs, moveHead, j_prev]
    have h0_at : σ 0 = blkHome := (hws 0 (by omega)).trans (encodeWorkspace_getD_zero _)
    have hne_at : ∀ i, 1 ≤ i → i ≤ j_prev → σ i ≠ blkHome := by
      intro i hi1 hi2
      rw [hws i (by omega)]
      exact encodeWorkspace_ne_home _ hi1 (by omega)
    rcases blkRewind_aux (blkTransformSeg MaxSeg stepBit) M_blk (0, true)
        (by simp [blkTransformSeg])
        (fun sym hne => by simp [blkTransformSeg, hne])
        j_prev σ (by omega) h0_at hne_at
      with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
    refine ⟨σ, hws, 1 + j_prev, by omega, ?_, hnone_rw, ?_, ?_⟩
    · rw [blkIter_add, hstep1, Option.bind_some, hiter_rw]
    · intro i hi q' σ' j' hi_eq
      cases i with
      | zero => cases hi_eq; omega
      | succ i' =>
        rw [Nat.add_comm i' 1, blkIter_add, hstep1, Option.bind_some] at hi_eq
        exact hbnd_rw i' (by omega) q' σ' j' hi_eq
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      cases i with
      | zero =>
        cases hi_eq; rw [hbs] at hbs'; cases hbs'
        exact ⟨fun _ => by omega, by simp⟩
      | succ i' =>
        rw [Nat.add_comm i' 1, blkIter_add, hstep1, Option.bind_some] at hi_eq
        exact hdir_rw i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
  | cons b rest ih =>
    intro pre' σ hlen hws
    have hM := length_encodeWorkspace_set hs hlen
    have hs_set := segStart_set_eq segs s s (pre' ++ b :: rest) hs hlen
    have hs' : s < (segs.set s (pre' ++ b :: rest)).length := by simpa using hs
    have hget : (segs.set s (pre' ++ b :: rest)).getD s [] = pre' ++ b :: rest := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hs]
    have hsb := segStart_bound segs s hs
    have hs1 := segStart_pos segs s
    have hlen_seg_gt : pre'.length < (segs.getD s []).length := by
      simp only [List.length_append, List.length_cons] at hlen; omega
    have hsym_at : σ (segStart segs s + pre'.length) = blkData false b := by
      rw [hws _ (by omega)]
      have hd := encodeWorkspace_seg_data (segs.set s (pre' ++ b :: rest)) hs'
        (i := pre'.length) (by rw [hget]; simp)
      rw [hs_set, hget, getD_append_right _ _ _ (Nat.le_refl _), Nat.sub_self] at hd
      exact hd
    let b' := (stepBit b).1
    let stop := (stepBit b).2
    let σ₁ := Function.update σ (segStart segs s + pre'.length) (blkData false b')
    have hws₁ : MatchesWS σ₁ (segs.set s (pre' ++ b' :: rest)) :=
      MatchesWS_update_seg_bit segs hs pre' b b' rest hlen hws
    have hlen₁ : (pre' ++ b' :: rest).length = (segs.getD s []).length := by
      simp only [List.length_append, List.length_cons] at hlen ⊢; exact hlen
    have hM₁ := length_encodeWorkspace_set hs hlen₁
    by_cases hstop : stop = true
    · have hbs : blkTransformSeg MaxSeg stepBit (0, false) (σ (segStart segs s + pre'.length)) =
          some ((0, true), blkData false b', QCSD_HeadDir.left) := by
        rw [hsym_at]
        have hsb_eq : stepBit b = (b', true) := Prod.ext rfl hstop
        simp [blkTransformSeg, blkData, blkHome, hsb_eq]
      let j_prev := segStart segs s + pre'.length - 1
      have hstep1 : blkIter (blkTransformSeg MaxSeg stepBit)
          ((0, false), σ, segStart segs s + pre'.length) 1 = some ((0, true), σ₁, j_prev) := by
        simp [blkIter, blkOnce, hbs, moveHead, j_prev, σ₁]
      have h0_at : σ₁ 0 = blkHome := (hws₁ 0 (by omega)).trans (encodeWorkspace_getD_zero _)
      have hne_at : ∀ i, 1 ≤ i → i ≤ j_prev → σ₁ i ≠ blkHome := by
        intro i hi1 hi2
        rw [hws₁ i (by omega)]
        exact encodeWorkspace_ne_home _ hi1 (by omega)
      rcases blkRewind_aux (blkTransformSeg MaxSeg stepBit) M_blk (0, true)
          (by simp [blkTransformSeg])
          (fun sym hne => by simp [blkTransformSeg, hne])
          j_prev σ₁ (by omega) h0_at hne_at
        with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
      have happly : applyTransform stepBit (b :: rest) = b' :: rest := by
        have hsb_eq : stepBit b = (b', true) := Prod.ext rfl hstop
        simp [applyTransform, hsb_eq]
      rw [happly]
      refine ⟨σ₁, hws₁, 1 + j_prev, by simp; omega, ?_, hnone_rw, ?_, ?_⟩
      · rw [blkIter_add, hstep1, Option.bind_some, hiter_rw]
      · intro i hi q' σ' j' hi_eq
        cases i with
        | zero => cases hi_eq; omega
        | succ i' =>
          rw [Nat.add_comm i' 1, blkIter_add, hstep1, Option.bind_some] at hi_eq
          exact hbnd_rw i' (by omega) q' σ' j' hi_eq
      · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
        cases i with
        | zero =>
          cases hi_eq; rw [hbs] at hbs'; cases hbs'
          exact ⟨fun _ => by omega, by simp⟩
        | succ i' =>
          rw [Nat.add_comm i' 1, blkIter_add, hstep1, Option.bind_some] at hi_eq
          exact hdir_rw i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
    · have hstop_f : stop = false := Bool.eq_false_iff.mpr hstop
      have hbs : blkTransformSeg MaxSeg stepBit (0, false) (σ (segStart segs s + pre'.length)) =
          some ((0, false), blkData false b', QCSD_HeadDir.right) := by
        rw [hsym_at]
        have hsb_eq : stepBit b = (b', false) := Prod.ext rfl hstop_f
        simp [blkTransformSeg, blkData, blkHome, hsb_eq]
      have hstep1 : blkIter (blkTransformSeg MaxSeg stepBit)
          ((0, false), σ, segStart segs s + pre'.length) 1 =
          some ((0, false), σ₁, segStart segs s + (pre' ++ [b']).length) := by
        have hadd : segStart segs s + pre'.length + 1 =
            segStart segs s + (pre' ++ [b']).length := by simp; omega
        simp [blkIter, blkOnce, hbs, moveHead, hadd, σ₁]
      have hassoc : (pre' ++ [b']) ++ rest = pre' ++ b' :: rest := by simp
      have hlen_next : ((pre' ++ [b']) ++ rest).length = (segs.getD s []).length := by
        rw [hassoc]; exact hlen₁
      have hws_next : MatchesWS σ₁ (segs.set s ((pre' ++ [b']) ++ rest)) := by
        rw [hassoc]; exact hws₁
      rcases ih (pre' ++ [b']) σ₁ hlen_next hws_next
        with ⟨σ_end, hws_end, k_rest, hk_rest, hiter_rest, hnone_rest, hbnd_rest, hdir_rest⟩
      have happly : pre' ++ applyTransform stepBit (b :: rest) =
          (pre' ++ [b']) ++ applyTransform stepBit rest := by
        have hsb_eq : stepBit b = (b', false) := Prod.ext rfl hstop_f
        simp [applyTransform, hsb_eq]
      rw [happly]
      refine ⟨σ_end, hws_end, 1 + k_rest, by simp; omega, ?_, hnone_rest, ?_, ?_⟩
      · rw [blkIter_add, hstep1, Option.bind_some, hiter_rest]
      · intro i hi q' σ' j' hi_eq
        cases i with
        | zero => cases hi_eq; omega
        | succ i' =>
          rw [Nat.add_comm i' 1, blkIter_add, hstep1, Option.bind_some] at hi_eq
          exact hbnd_rest i' (by omega) q' σ' j' hi_eq
      · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
        cases i with
        | zero =>
          cases hi_eq; rw [hbs] at hbs'; cases hbs'
          exact ⟨by simp, fun _ => by omega⟩
        | succ i' =>
          rw [Nat.add_comm i' 1, blkIter_add, hstep1, Option.bind_some] at hi_eq
          exact hdir_rest i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

theorem blkTransformSeg_spec (MaxSeg : ℕ) (stepBit : Bool → Bool × Bool)
    (segs : List (List Bool)) {s : ℕ} (hs : s < segs.length) (hs_max : s ≤ MaxSeg)
    (σ : ℕ → BlkSym) (hws : MatchesWS σ segs) :
    let M_blk := (encodeWorkspace segs).length
    ∃ σ_end : ℕ → BlkSym,
      MatchesWS σ_end (segs.set s (applyTransform stepBit (segs.getD s []))) ∧
      BlkExec (blkTransformSeg MaxSeg stepBit) M_blk
        (⟨s, by omega⟩, false) σ 0 (0, true) σ_end 0 (3 * M_blk) := by
  intro M_blk
  let go : ℕ → Fin (MaxSeg + 1) × Bool := fun r =>
    (⟨if h : r ≤ MaxSeg then r else 0, by split_ifs <;> omega⟩, false)
  have hgo_s : go s = (⟨s, by omega⟩, false) := by simp [go, hs_max]
  have hgo_0 : go 0 = (0, false) := by ext <;> simp [go]
  rcases blkGoToSeg_aux (blkTransformSeg MaxSeg stepBit) segs σ hws go hs
      (by simp [go, hs_max, blkTransformSeg])
      (fun r hr m b => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        simp [go, hr1, blkTransformSeg, blkHome, blkData, blkSep])
      (fun r hr => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        have hr0 : r ≤ MaxSeg := by omega
        have hpos : 0 < (if h : r + 1 ≤ MaxSeg then r + 1 else 0) := by simp [hr1]
        simp only [go, blkTransformSeg, Bool.false_eq_true, ↓reduceIte,
          show blkSep ≠ blkHome by decide, dite_true, hpos]
        congr 1; ext <;> simp [hr1, hr0])
    with ⟨hiter_go, hbnd_go, hdir_go⟩
  rw [hgo_s, hgo_0] at hiter_go
  rw [hgo_s] at hbnd_go hdir_go
  have hset_self : segs.set s ([] ++ segs.getD s []) = segs := by
    apply List.ext_getElem (by simp)
    intro k hk1 hk2
    rw [List.getElem_set]
    split_ifs with hsk
    · subst hsk
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2]
    · rfl
  have hws0 : MatchesWS σ (segs.set s ([] ++ segs.getD s [])) := by rwa [hset_self]
  rcases blkTransformSeg_scan_aux MaxSeg stepBit segs hs (segs.getD s []) [] σ (by simp) hws0
    with ⟨σ_end, hws_end, k_sc, hk_sc, hiter_sc, hnone_sc, hbnd_sc, hdir_sc⟩
  simp only [List.nil_append, List.length_nil, Nat.add_zero] at hws_end hiter_sc hbnd_sc hdir_sc
  have hsb := segStart_bound segs s hs
  refine ⟨σ_end, hws_end, segStart segs s + k_sc, by omega, ?_, hnone_sc, ?_, ?_⟩
  · rw [blkIter_add, hiter_go, Option.bind_some, hiter_sc]
  · intro i hi q' σ' j' hi_eq
    by_cases hi1 : i ≤ segStart segs s
    · rcases blkIter_le_some hi1 hiter_go with ⟨⟨qi, σi, ji⟩, hsub⟩
      rw [hsub] at hi_eq; cases hi_eq
      exact hbnd_go i hi1 q' σ' j' hsub
    · have heq : i = segStart segs s + (i - segStart segs s) := by omega
      rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
      exact hbnd_sc (i - segStart segs s) (by omega) q' σ' j' hi_eq
  · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
    by_cases hi1 : i < segStart segs s
    · exact hdir_go i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
    · have heq : i = segStart segs s + (i - segStart segs s) := by omega
      rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
      exact hdir_sc (i - segStart segs s) (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

/-- Non-destructive zero test on segment `s` (`all (· = false)`). -/
def isAllFalse : List Bool → Bool
  | [] => true
  | false :: bs => isAllFalse bs
  | true :: _ => false

theorem isAllFalse_iff (bs : List Bool) :
    isAllFalse bs = true ↔ ∀ b ∈ bs, b = false := by
  induction bs with
  | nil => simp [isAllFalse]
  | cons b bs ih =>
    cases b <;> simp [isAllFalse, ih]

def blkCheckZeroSeg (MaxSeg : ℕ) : BlkStepFn (Fin (MaxSeg + 1) × Bool × Bool) :=
  fun (rem, rewinding, res) sym =>
    if rewinding then
      if sym = blkHome then none
      else some ((rem, true, res), sym, QCSD_HeadDir.left)
    else if sym = blkHome then
      some ((rem, false, res), blkHome, QCSD_HeadDir.right)
    else if hrem : 0 < rem.val then
      let prev : Fin (MaxSeg + 1) := ⟨rem.val - 1, by omega⟩
      if sym = blkSep then some ((prev, false, res), blkSep, QCSD_HeadDir.right)
      else some ((rem, false, res), sym, QCSD_HeadDir.right)
    else
      if !sym.1 then
        if sym.2.2 then some ((0, true, false), sym, QCSD_HeadDir.left)
        else some ((0, false, true), sym, QCSD_HeadDir.right)
      else
        some ((0, true, true), sym, QCSD_HeadDir.left)

theorem blkCheckZeroSeg_scan_aux (MaxSeg : ℕ) (segs : List (List Bool))
    {s : ℕ} (hs : s < segs.length) (σ : ℕ → BlkSym) (hws : MatchesWS σ segs) :
    let M_blk := (encodeWorkspace segs).length
    ∀ (suf pre : List Bool),
      pre ++ suf = segs.getD s [] →
      BlkExec (blkCheckZeroSeg MaxSeg) M_blk
        (0, false, true) σ (segStart segs s + pre.length)
        (0, true, isAllFalse suf) σ 0 (suf.length + 1 + M_blk) := by
  intro M_blk suf
  induction suf with
  | nil =>
    intro pre heq
    simp only [List.append_nil, isAllFalse] at heq ⊢
    have hsb := segStart_bound segs s hs
    have hs1 := segStart_pos segs s
    have hlen_p : pre.length = (segs.getD s []).length := by rw [heq]
    have hend_sym : σ (segStart segs s + pre.length) =
        (if s + 1 < segs.length then blkSep else blkWall) := by
      rw [hlen_p, hws _ hsb]
      exact encodeWorkspace_seg_end segs hs
    have hbs : blkCheckZeroSeg MaxSeg (0, false, true) (σ (segStart segs s + pre.length)) =
        some ((0, true, true), σ (segStart segs s + pre.length), QCSD_HeadDir.left) := by
      rw [hend_sym]
      split_ifs <;> simp [blkCheckZeroSeg, blkSep, blkWall, blkHome]
    let j_prev := segStart segs s + pre.length - 1
    have hstep1 : blkIter (blkCheckZeroSeg MaxSeg)
        ((0, false, true), σ, segStart segs s + pre.length) 1 =
        some ((0, true, true), σ, j_prev) := by
      simp [blkIter, blkOnce, hbs, moveHead, j_prev]
    have h0_at : σ 0 = blkHome := (hws 0 (by omega)).trans (encodeWorkspace_getD_zero _)
    have hne_at : ∀ i, 1 ≤ i → i ≤ j_prev → σ i ≠ blkHome := by
      intro i hi1 hi2; rw [hws i (by omega)]; exact encodeWorkspace_ne_home _ hi1 (by omega)
    rcases blkRewind_aux (blkCheckZeroSeg MaxSeg) M_blk (0, true, true)
        (by simp [blkCheckZeroSeg])
        (fun sym hne => by simp [blkCheckZeroSeg, hne])
        j_prev σ (by omega) h0_at hne_at
      with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
    refine ⟨1 + j_prev, by omega, ?_, hnone_rw, ?_, ?_⟩
    · rw [blkIter_add, hstep1, Option.bind_some, hiter_rw]
    · intro i hi q' σ' j' hi_eq
      cases i with
      | zero => cases hi_eq; omega
      | succ i' =>
        rw [Nat.add_comm i' 1, blkIter_add, hstep1, Option.bind_some] at hi_eq
        exact hbnd_rw i' (by omega) q' σ' j' hi_eq
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      cases i with
      | zero =>
        cases hi_eq; rw [hbs] at hbs'; cases hbs'
        exact ⟨fun _ => by omega, by simp⟩
      | succ i' =>
        rw [Nat.add_comm i' 1, blkIter_add, hstep1, Option.bind_some] at hi_eq
        exact hdir_rw i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
  | cons b rest ih =>
    intro pre heq
    have hsb := segStart_bound segs s hs
    have hs1 := segStart_pos segs s
    have hlt_p : pre.length < (segs.getD s []).length := by
      rw [← heq]; simp
    have hsym_at : σ (segStart segs s + pre.length) = blkData false b := by
      rw [hws _ (by omega), encodeWorkspace_seg_data segs hs hlt_p, ← heq,
        getD_append_right _ _ _ (Nat.le_refl _), Nat.sub_self]
      rfl
    cases b with
    | true =>
      simp only [isAllFalse]
      have hbs : blkCheckZeroSeg MaxSeg (0, false, true) (σ (segStart segs s + pre.length)) =
          some ((0, true, false), σ (segStart segs s + pre.length), QCSD_HeadDir.left) := by
        rw [hsym_at]; simp [blkCheckZeroSeg, blkData, blkHome]
      let j_prev := segStart segs s + pre.length - 1
      have hstep1 : blkIter (blkCheckZeroSeg MaxSeg)
          ((0, false, true), σ, segStart segs s + pre.length) 1 =
          some ((0, true, false), σ, j_prev) := by
        simp [blkIter, blkOnce, hbs, moveHead, j_prev]
      have h0_at : σ 0 = blkHome := (hws 0 (by omega)).trans (encodeWorkspace_getD_zero _)
      have hne_at : ∀ i, 1 ≤ i → i ≤ j_prev → σ i ≠ blkHome := by
        intro i hi1 hi2; rw [hws i (by omega)]; exact encodeWorkspace_ne_home _ hi1 (by omega)
      rcases blkRewind_aux (blkCheckZeroSeg MaxSeg) M_blk (0, true, false)
          (by simp [blkCheckZeroSeg])
          (fun sym hne => by simp [blkCheckZeroSeg, hne])
          j_prev σ (by omega) h0_at hne_at
        with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
      refine ⟨1 + j_prev, by simp; omega, ?_, hnone_rw, ?_, ?_⟩
      · rw [blkIter_add, hstep1, Option.bind_some, hiter_rw]
      · intro i hi q' σ' j' hi_eq
        cases i with
        | zero => cases hi_eq; omega
        | succ i' =>
          rw [Nat.add_comm i' 1, blkIter_add, hstep1, Option.bind_some] at hi_eq
          exact hbnd_rw i' (by omega) q' σ' j' hi_eq
      · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
        cases i with
        | zero =>
          cases hi_eq; rw [hbs] at hbs'; cases hbs'
          exact ⟨fun _ => by omega, by simp⟩
        | succ i' =>
          rw [Nat.add_comm i' 1, blkIter_add, hstep1, Option.bind_some] at hi_eq
          exact hdir_rw i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
    | false =>
      simp only [isAllFalse]
      have hbs : blkCheckZeroSeg MaxSeg (0, false, true) (σ (segStart segs s + pre.length)) =
          some ((0, false, true), σ (segStart segs s + pre.length), QCSD_HeadDir.right) := by
        rw [hsym_at]; simp [blkCheckZeroSeg, blkData, blkHome]
      have hstep1 : blkIter (blkCheckZeroSeg MaxSeg)
          ((0, false, true), σ, segStart segs s + pre.length) 1 =
          some ((0, false, true), σ, segStart segs s + (pre ++ [false]).length) := by
        have hadd : segStart segs s + pre.length + 1 =
            segStart segs s + (pre ++ [false]).length := by simp; omega
        simp [blkIter, blkOnce, hbs, moveHead, hadd]
      have heq_next : (pre ++ [false]) ++ rest = segs.getD s [] := by simpa using heq
      rcases ih (pre ++ [false]) heq_next with ⟨k_rest, hk_rest, hiter_rest, hnone_rest, hbnd_rest, hdir_rest⟩
      refine ⟨1 + k_rest, by simp; omega, ?_, hnone_rest, ?_, ?_⟩
      · rw [blkIter_add, hstep1, Option.bind_some, hiter_rest]
      · intro i hi q' σ' j' hi_eq
        cases i with
        | zero => cases hi_eq; omega
        | succ i' =>
          rw [Nat.add_comm i' 1, blkIter_add, hstep1, Option.bind_some] at hi_eq
          exact hbnd_rest i' (by omega) q' σ' j' hi_eq
      · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
        cases i with
        | zero =>
          cases hi_eq; rw [hbs] at hbs'; cases hbs'
          exact ⟨by simp, fun _ => by omega⟩
        | succ i' =>
          rw [Nat.add_comm i' 1, blkIter_add, hstep1, Option.bind_some] at hi_eq
          exact hdir_rest i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

theorem blkCheckZeroSeg_spec (MaxSeg : ℕ) (segs : List (List Bool))
    {s : ℕ} (hs : s < segs.length) (hs_max : s ≤ MaxSeg)
    (σ : ℕ → BlkSym) (hws : MatchesWS σ segs) :
    let M_blk := (encodeWorkspace segs).length
    BlkExec (blkCheckZeroSeg MaxSeg) M_blk
      (⟨s, by omega⟩, false, true) σ 0
      (0, true, isAllFalse (segs.getD s [])) σ 0 (3 * M_blk) := by
  intro M_blk
  let go : ℕ → Fin (MaxSeg + 1) × Bool × Bool := fun r =>
    (⟨if h : r ≤ MaxSeg then r else 0, by split_ifs <;> omega⟩, false, true)
  have hgo_s : go s = (⟨s, by omega⟩, false, true) := by simp [go, hs_max]
  have hgo_0 : go 0 = (0, false, true) := by ext <;> simp [go]
  rcases blkGoToSeg_aux (blkCheckZeroSeg MaxSeg) segs σ hws go hs
      (by simp [go, hs_max, blkCheckZeroSeg])
      (fun r hr m b => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        simp [go, hr1, blkCheckZeroSeg, blkHome, blkData, blkSep])
      (fun r hr => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        have hr0 : r ≤ MaxSeg := by omega
        have hpos : 0 < (if h : r + 1 ≤ MaxSeg then r + 1 else 0) := by simp [hr1]
        simp only [go, blkCheckZeroSeg, Bool.false_eq_true, ↓reduceIte,
          show blkSep ≠ blkHome by decide, dite_true, hpos]
        congr 1; ext <;> simp [hr1, hr0])
    with ⟨hiter_go, hbnd_go, hdir_go⟩
  rw [hgo_s, hgo_0] at hiter_go
  rw [hgo_s] at hbnd_go hdir_go
  rcases blkCheckZeroSeg_scan_aux MaxSeg segs hs σ hws (segs.getD s []) [] (by simp)
    with ⟨k_sc, hk_sc, hiter_sc, hnone_sc, hbnd_sc, hdir_sc⟩
  simp only [List.length_nil, Nat.add_zero] at hiter_sc hbnd_sc hdir_sc
  have hsb := segStart_bound segs s hs
  refine ⟨segStart segs s + k_sc, by omega, ?_, hnone_sc, ?_, ?_⟩
  · rw [blkIter_add, hiter_go, Option.bind_some, hiter_sc]
  · intro i hi q' σ' j' hi_eq
    by_cases hi1 : i ≤ segStart segs s
    · rcases blkIter_le_some hi1 hiter_go with ⟨⟨qi, σi, ji⟩, hsub⟩
      rw [hsub] at hi_eq; cases hi_eq
      exact hbnd_go i hi1 q' σ' j' hsub
    · have heq : i = segStart segs s + (i - segStart segs s) := by omega
      rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
      exact hbnd_sc (i - segStart segs s) (by omega) q' σ' j' hi_eq
  · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
    by_cases hi1 : i < segStart segs s
    · exact hdir_go i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
    · have heq : i = segStart segs s + (i - segStart segs s) := by omega
      rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
      exact hdir_sc (i - segStart segs s) (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

/-!
### Physical `StepFn` Register Primitives (`wsInc`, `wsZero`, `wsDecJz`, `wsCopy`, `wsReadBit`)
-/

/-- Physical tape invariant: `τ` encodes `segs` on `0 .. 3 * M_blk - 1` (`W = 3 * M_blk ≤ len ≤ B`). -/
def TapeWS (τ : ℕ → Bool) (len B : ℕ) (segs : List (List Bool)) : Prop :=
  segs ≠ [] ∧ 3 * (encodeWorkspace segs).length ≤ len ∧ len ≤ B ∧ MatchesWS (readBlk τ) segs

theorem TapeWS_pos {τ : ℕ → Bool} {len B : ℕ} {segs : List (List Bool)}
    (h : TapeWS τ len B segs) : 1 ≤ len := by
  rcases h with ⟨h1, h2, _, _⟩
  have : 1 ≤ (encodeWorkspace segs).length := by simp [encodeWorkspace]
  omega

def wsInc (MaxSeg : ℕ) : StepFn (LiftBlkQ (Fin (MaxSeg + 1) × Bool)) :=
  liftBlockStep (blkTransformSeg MaxSeg stepBitInc)

def wsIncEntry (MaxSeg : ℕ) (s : Fin (MaxSeg + 1)) : LiftBlkQ (Fin (MaxSeg + 1) × Bool) :=
  liftBlkEntry (s, false)

theorem wsInc_spec (MaxSeg B : ℕ) (segs : List (List Bool)) {s w v : ℕ}
    (hs : s < segs.length) (hs_max : s ≤ MaxSeg)
    (hseg : segs.getD s [] = natToBitsLE w v) (hv : v + 1 < 2 ^ w)
    {len : ℕ} {τ₁ : ℕ → Bool} (htw : TapeWS τ₁ len B segs) :
    ∃ τ₂ : ℕ → Bool,
      TapeWS τ₂ len B (segs.set s (natToBitsLE w (v + 1))) ∧
      (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (wsInc MaxSeg) B (wsIncEntry MaxSeg ⟨s, by omega⟩) len τ₁ 0
        (liftBlkExit (0, true)) len τ₂ 0 (21 * (encodeWorkspace segs).length + 4) := by
  rcases htw with ⟨hsegs, hW_le, hlen_B, hws⟩
  rcases blkTransformSeg_spec MaxSeg stepBitInc segs hs hs_max (readBlk τ₁) hws
    with ⟨σ_end, hws_end, hexec⟩
  rw [hseg, applyTransform_inc, incBits_natToBitsLE hv] at hws_end
  rcases liftBlockStep_spec (blkTransformSeg MaxSeg stepBitInc) B
      (encodeWorkspace segs).length len τ₁ (⟨s, by omega⟩, false) (0, true) σ_end 0 0
      (3 * (encodeWorkspace segs).length) hW_le hlen_B hexec
    with ⟨τ₂, hread₂, hout₂, k, hk, hiter, hexit, hbnd⟩
  rw [← hread₂] at hws_end
  have hlen_set : (encodeWorkspace (segs.set s (natToBitsLE w (v + 1)))).length =
      (encodeWorkspace segs).length := by
    apply length_encodeWorkspace_set hs
    rw [hseg, length_natToBitsLE, length_natToBitsLE]
  have hne_set : segs.set s (natToBitsLE w (v + 1)) ≠ [] := by simp [hsegs]
  have hk' : k ≤ 21 * (encodeWorkspace segs).length + 4 := by omega
  exact ⟨τ₂, ⟨hne_set, by rw [hlen_set]; exact hW_le, hlen_B, hws_end⟩, hout₂,
    k, hk', hiter, hexit, hbnd⟩

def wsZero (MaxSeg : ℕ) : StepFn (LiftBlkQ (Fin (MaxSeg + 1) × Bool)) :=
  liftBlockStep (blkTransformSeg MaxSeg stepBitZero)

def wsZeroEntry (MaxSeg : ℕ) (s : Fin (MaxSeg + 1)) : LiftBlkQ (Fin (MaxSeg + 1) × Bool) :=
  liftBlkEntry (s, false)

theorem wsZero_spec (MaxSeg B : ℕ) (segs : List (List Bool)) {s w : ℕ}
    (hs : s < segs.length) (hs_max : s ≤ MaxSeg)
    (hseg : (segs.getD s []).length = w)
    {len : ℕ} {τ₁ : ℕ → Bool} (htw : TapeWS τ₁ len B segs) :
    ∃ τ₂ : ℕ → Bool,
      TapeWS τ₂ len B (segs.set s (natToBitsLE w 0)) ∧
      (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (wsZero MaxSeg) B (wsZeroEntry MaxSeg ⟨s, by omega⟩) len τ₁ 0
        (liftBlkExit (0, true)) len τ₂ 0 (21 * (encodeWorkspace segs).length + 4) := by
  rcases htw with ⟨hsegs, hW_le, hlen_B, hws⟩
  rcases blkTransformSeg_spec MaxSeg stepBitZero segs hs hs_max (readBlk τ₁) hws
    with ⟨σ_end, hws_end, hexec⟩
  rw [applyTransform_zero, hseg, ← natToBitsLE_zero] at hws_end
  rcases liftBlockStep_spec (blkTransformSeg MaxSeg stepBitZero) B
      (encodeWorkspace segs).length len τ₁ (⟨s, by omega⟩, false) (0, true) σ_end 0 0
      (3 * (encodeWorkspace segs).length) hW_le hlen_B hexec
    with ⟨τ₂, hread₂, hout₂, k, hk, hiter, hexit, hbnd⟩
  rw [← hread₂] at hws_end
  have hlen_set : (encodeWorkspace (segs.set s (natToBitsLE w 0))).length =
      (encodeWorkspace segs).length := by
    apply length_encodeWorkspace_set hs
    rw [hseg, length_natToBitsLE]
  have hne_set : segs.set s (natToBitsLE w 0) ≠ [] := by simp [hsegs]
  have hk' : k ≤ 21 * (encodeWorkspace segs).length + 4 := by omega
  exact ⟨τ₂, ⟨hne_set, by rw [hlen_set]; exact hW_le, hlen_B, hws_end⟩, hout₂,
    k, hk', hiter, hexit, hbnd⟩

/-- Combinators `nopStep`, `familyStep`, `sumStep`, and `StepExec.weaken`. -/
def nopStep (Q : Type) : StepFn Q := fun _ _ => none

theorem nopStep_spec {Q : Type} (q : Q) {B : ℕ} (len : ℕ) (τ : ℕ → Bool) (h : ℕ)
    (hlen : len ≤ B) (hh : h + 1 ≤ B) :
    StepExec (nopStep Q) B q len τ h q len τ h 0 := by
  refine ⟨0, Nat.le_refl 0, rfl, fun _ => rfl, ?_⟩
  intro j hj _ l' _ h' hj_eq
  obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
  cases hj_eq
  exact ⟨hlen, hh⟩

theorem StepExec.weaken {Q : Type} {s : StepFn Q} {B : ℕ}
    {q₁ q₂ : Q} {len₁ len₂ h₁ h₂ T₁ : ℕ} {τ₁ τ₂ : ℕ → Bool}
    (T₂ : ℕ) (he : StepExec s B q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ T₁) (hT : T₁ ≤ T₂) :
    StepExec s B q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ T₂ := by
  rcases he with ⟨k, hk, hiter, hexit, hbnd⟩
  exact ⟨k, Nat.le_trans hk hT, hiter, hexit, hbnd⟩

def familyStep {P Q : Type} (s : P → StepFn Q) : StepFn (P × Q) :=
  fun (p, q) b => (s p q b).map (fun (q', b', d) => ((p, q'), b', d))

theorem stepFnIter_familyStep {P Q : Type} (s : P → StepFn Q) (p : P) :
    ∀ k (q₁ : Q) len₁ τ₁ h₁,
      stepFnIter (familyStep s) ((p, q₁), len₁, τ₁, h₁) k =
        (stepFnIter (s p) (q₁, len₁, τ₁, h₁) k).map
          (fun (q₂, len₂, τ₂, h₂) => ((p, q₂), len₂, τ₂, h₂)) := by
  intro k
  induction k with
  | zero => intro q₁ len₁ τ₁ h₁; rfl
  | succ k ih =>
    intro q₁ len₁ τ₁ h₁
    simp only [stepFnIter, stepFnOnce, familyStep]
    cases s p q₁ (τ₁ h₁) with
    | none => rfl
    | some val =>
      rcases val with ⟨q', b', d⟩
      exact ih q' _ _ _

theorem familyStep_spec {P Q : Type} (s : P → StepFn Q) (p : P) {B : ℕ}
    {q₁ q₂ : Q} {len₁ len₂ h₁ h₂ T : ℕ} {τ₁ τ₂ : ℕ → Bool}
    (he : StepExec (s p) B q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ T) :
    StepExec (familyStep s) B (p, q₁) len₁ τ₁ h₁ (p, q₂) len₂ τ₂ h₂ T := by
  rcases he with ⟨k, hk, hiter, hexit, hbnd⟩
  refine ⟨k, hk, by rw [stepFnIter_familyStep, hiter]; rfl,
    fun b => by simp [familyStep, hexit b], ?_⟩
  intro j hj _ l' τ' h' hj_eq
  rw [stepFnIter_familyStep] at hj_eq
  cases hsub : stepFnIter (s p) (q₁, len₁, τ₁, h₁) j with
  | none => rw [hsub] at hj_eq; simp at hj_eq
  | some cfg =>
    rcases cfg with ⟨qj, lj, τj, hj_pos⟩
    rw [hsub] at hj_eq; cases hj_eq
    exact hbnd j hj qj l' τ' h' hsub

def sumStep {Q₁ Q₂ : Type} (s₁ : StepFn Q₁) (s₂ : StepFn Q₂) : StepFn (Q₁ ⊕ Q₂)
  | Sum.inl q₁, b => (s₁ q₁ b).map (fun (q₁', b', d) => (Sum.inl q₁', b', d))
  | Sum.inr q₂, b => (s₂ q₂ b).map (fun (q₂', b', d) => (Sum.inr q₂', b', d))

theorem sumStep_inl_spec {Q₁ Q₂ : Type} (s₁ : StepFn Q₁) (s₂ : StepFn Q₂) {B : ℕ}
    {q₁ q₂ : Q₁} {len₁ len₂ h₁ h₂ T : ℕ} {τ₁ τ₂ : ℕ → Bool}
    (he : StepExec s₁ B q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ T) :
    StepExec (sumStep s₁ s₂) B (Sum.inl q₁) len₁ τ₁ h₁ (Sum.inl q₂) len₂ τ₂ h₂ T := by
  rcases he with ⟨k, hk, hiter, hexit, hbnd⟩
  have hmap : ∀ m (qa : Q₁) la τa ha,
      stepFnIter (sumStep s₁ s₂) (Sum.inl qa, la, τa, ha) m =
        (stepFnIter s₁ (qa, la, τa, ha) m).map (fun (qb, lb, τb, hb) => (Sum.inl qb, lb, τb, hb)) := by
    intro m; induction m with
    | zero => intros; rfl
    | succ m ih =>
      intro qa la τa ha
      simp only [stepFnIter, stepFnOnce, sumStep]
      cases s₁ qa (τa ha) with
      | none => rfl
      | some val => rcases val with ⟨q', b', d⟩; exact ih q' _ _ _
  refine ⟨k, hk, by rw [hmap, hiter]; rfl, fun b => by simp [sumStep, hexit b], ?_⟩
  intro j hj _ l' τ' h' hj_eq
  rw [hmap] at hj_eq
  cases hsub : stepFnIter s₁ (q₁, len₁, τ₁, h₁) j with
  | none => rw [hsub] at hj_eq; simp at hj_eq
  | some cfg =>
    rcases cfg with ⟨qj, lj, τj, hj_pos⟩
    rw [hsub] at hj_eq; cases hj_eq
    exact hbnd j hj qj l' τ' h' hsub

theorem sumStep_inr_spec {Q₁ Q₂ : Type} (s₁ : StepFn Q₁) (s₂ : StepFn Q₂) {B : ℕ}
    {q₁ q₂ : Q₂} {len₁ len₂ h₁ h₂ T : ℕ} {τ₁ τ₂ : ℕ → Bool}
    (he : StepExec s₂ B q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ T) :
    StepExec (sumStep s₁ s₂) B (Sum.inr q₁) len₁ τ₁ h₁ (Sum.inr q₂) len₂ τ₂ h₂ T := by
  rcases he with ⟨k, hk, hiter, hexit, hbnd⟩
  have hmap : ∀ m (qa : Q₂) la τa ha,
      stepFnIter (sumStep s₁ s₂) (Sum.inr qa, la, τa, ha) m =
        (stepFnIter s₂ (qa, la, τa, ha) m).map (fun (qb, lb, τb, hb) => (Sum.inr qb, lb, τb, hb)) := by
    intro m; induction m with
    | zero => intros; rfl
    | succ m ih =>
      intro qa la τa ha
      simp only [stepFnIter, stepFnOnce, sumStep]
      cases s₂ qa (τa ha) with
      | none => rfl
      | some val => rcases val with ⟨q', b', d⟩; exact ih q' _ _ _
  refine ⟨k, hk, by rw [hmap, hiter]; rfl, fun b => by simp [sumStep, hexit b], ?_⟩
  intro j hj _ l' τ' h' hj_eq
  rw [hmap] at hj_eq
  cases hsub : stepFnIter s₂ (q₁, len₁, τ₁, h₁) j with
  | none => rw [hsub] at hj_eq; simp at hj_eq
  | some cfg =>
    rcases cfg with ⟨qj, lj, τj, hj_pos⟩
    rw [hsub] at hj_eq; cases hj_eq
    exact hbnd j hj qj l' τ' h' hsub

/-- `wsDecJz MaxSeg`: checks if segment `s` is zero; if non-zero, decrements it; exits with
`wasZero : Bool` extractable via `wsDecJzWasZero`. -/
abbrev WsDecJzQ (MaxSeg : ℕ) : Type :=
  (Fin (MaxSeg + 1) × LiftBlkQ (Fin (MaxSeg + 1) × Bool × Bool)) ⊕
  (Bool ⊕ LiftBlkQ (Fin (MaxSeg + 1) × Bool))

def wsDecJzF (MaxSeg : ℕ) :
    Fin (MaxSeg + 1) × LiftBlkQ (Fin (MaxSeg + 1) × Bool × Bool) →
    Bool ⊕ LiftBlkQ (Fin (MaxSeg + 1) × Bool) :=
  fun (s_save, q_chk) =>
    if q_chk.1.2.2 then Sum.inl true
    else Sum.inr (liftBlkEntry (s_save, false))

def wsDecJz (MaxSeg : ℕ) : StepFn (WsDecJzQ MaxSeg) :=
  seq0
    (familyStep (fun _ => liftBlockStep (blkCheckZeroSeg MaxSeg)))
    (sumStep (nopStep Bool) (liftBlockStep (blkTransformSeg MaxSeg stepBitDec)))
    (wsDecJzF MaxSeg)

def wsDecJzEntry (MaxSeg : ℕ) (s : Fin (MaxSeg + 1)) : WsDecJzQ MaxSeg :=
  Sum.inl (s, liftBlkEntry (s, false, true))

def wsDecJzWasZero {MaxSeg : ℕ} : WsDecJzQ MaxSeg → Bool
  | Sum.inl _ => false
  | Sum.inr (Sum.inl z) => z
  | Sum.inr (Sum.inr _) => false

theorem wsDecJz_spec (MaxSeg B : ℕ) (segs : List (List Bool)) {s w v : ℕ}
    (hs : s < segs.length) (hs_max : s ≤ MaxSeg)
    (hseg : segs.getD s [] = natToBitsLE w v) (hv : v < 2 ^ w)
    {len : ℕ} {τ₁ : ℕ → Bool} (htw : TapeWS τ₁ len B segs) :
    ∃ q_out : WsDecJzQ MaxSeg, ∃ τ₂ : ℕ → Bool,
      wsDecJzWasZero q_out = decide (v = 0) ∧
      TapeWS τ₂ len B (if v = 0 then segs else segs.set s (natToBitsLE w (v - 1))) ∧
      (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (wsDecJz MaxSeg) B (wsDecJzEntry MaxSeg ⟨s, by omega⟩) len τ₁ 0
        q_out len τ₂ 0 (42 * (encodeWorkspace segs).length + 10) := by
  have hlen_pos : 1 ≤ len := TapeWS_pos htw
  rcases htw with ⟨hsegs, hW_le, hlen_B, hws⟩
  have hchk_blk := blkCheckZeroSeg_spec MaxSeg segs hs hs_max (readBlk τ₁) hws
  rcases liftBlockStep_spec (blkCheckZeroSeg MaxSeg) B
      (encodeWorkspace segs).length len τ₁
      (⟨s, by omega⟩, false, true) (0, true, isAllFalse (segs.getD s [])) (readBlk τ₁) 0 0
      (3 * (encodeWorkspace segs).length) hW_le hlen_B hchk_blk
    with ⟨τ_mid, hread_mid, hout_mid, k₁, hk₁, hiter₁, hexit₁, hbnd₁⟩
  have he₁ := familyStep_spec (fun (_ : Fin (MaxSeg + 1)) => liftBlockStep (blkCheckZeroSeg MaxSeg))
    ⟨s, by omega⟩ ⟨k₁, hk₁, hiter₁, hexit₁, hbnd₁⟩
  have hws_mid : MatchesWS (readBlk τ_mid) segs := by rwa [hread_mid]
  have hz_eq : isAllFalse (segs.getD s []) = decide (v = 0) := by
    rw [hseg]
    by_cases hv0 : v = 0
    · subst hv0
      simp only [decide_true]
      exact (isAllFalse_iff _).mpr ((all_false_natToBitsLE_iff hv).mpr rfl)
    · simp only [decide_eq_false hv0]
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hv0 ((all_false_natToBitsLE_iff hv).mp ((isAllFalse_iff _).mp htrue))
  by_cases hv0 : v = 0
  · subst hv0
    have hz_t : isAllFalse (segs.getD s []) = true := by simpa using hz_eq
    have hf_eq : wsDecJzF MaxSeg (⟨s, by omega⟩, liftBlkExit (0, true, isAllFalse (segs.getD s []))) =
        Sum.inl true := by
      dsimp only [wsDecJzF, liftBlkExit]
      rw [hz_t]; rfl
    have he₂_raw := sumStep_inl_spec (nopStep Bool)
      (liftBlockStep (blkTransformSeg MaxSeg stepBitDec))
      (nopStep_spec true len τ_mid 0 hlen_B (by omega))
    have hcomb := (seq0_spec (f := wsDecJzF MaxSeg) hlen_pos he₁ (by rw [hf_eq]; exact he₂_raw)).weaken
      (42 * (encodeWorkspace segs).length + 10) (by omega)
    exact ⟨Sum.inr (Sum.inl true), τ_mid, rfl,
      ⟨hsegs, hW_le, hlen_B, hws_mid⟩, hout_mid, hcomb⟩
  · have hz_f : isAllFalse (segs.getD s []) = false := by simpa [hv0] using hz_eq
    have hf_eq : wsDecJzF MaxSeg (⟨s, by omega⟩, liftBlkExit (0, true, isAllFalse (segs.getD s []))) =
        Sum.inr (liftBlkEntry (⟨s, by omega⟩, false)) := by
      dsimp only [wsDecJzF, liftBlkExit]
      rw [hz_f]; rfl
    have hv_pos : 1 ≤ v := by omega
    rcases blkTransformSeg_spec MaxSeg stepBitDec segs hs hs_max (readBlk τ_mid) hws_mid
      with ⟨σ_end, hws_end, hexec_dec⟩
    rw [hseg, applyTransform_dec, decBits_natToBitsLE hv_pos hv] at hws_end
    rcases liftBlockStep_spec (blkTransformSeg MaxSeg stepBitDec) B
        (encodeWorkspace segs).length len τ_mid
        (⟨s, by omega⟩, false) (0, true) σ_end 0 0
        (3 * (encodeWorkspace segs).length) hW_le hlen_B hexec_dec
      with ⟨τ₂, hread₂, hout₂, k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
    rw [← hread₂] at hws_end
    have he₂_raw := sumStep_inr_spec (nopStep Bool)
      (liftBlockStep (blkTransformSeg MaxSeg stepBitDec))
      ⟨k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
    rw [← hf_eq] at he₂_raw
    have hcomb := (seq0_spec hlen_pos he₁ he₂_raw).weaken
      (42 * (encodeWorkspace segs).length + 10) (by omega)
    have hlen_set : (encodeWorkspace (segs.set s (natToBitsLE w (v - 1)))).length =
        (encodeWorkspace segs).length := by
      apply length_encodeWorkspace_set hs
      rw [hseg, length_natToBitsLE, length_natToBitsLE]
    have hne_set : segs.set s (natToBitsLE w (v - 1)) ≠ [] := by simp [hsegs]
    have htw₂ : TapeWS τ₂ len B (if v = 0 then segs else segs.set s (natToBitsLE w (v - 1))) := by
      simp only [hv0, ↓reduceIte]
      exact ⟨hne_set, by rw [hlen_set]; exact hW_le, hlen_B, hws_end⟩
    exact ⟨Sum.inr (Sum.inr (liftBlkExit (0, true))), τ₂, by simp [wsDecJzWasZero, hv0],
      htw₂, fun p hp => (hout₂ p hp).trans (hout_mid p hp), hcomb⟩

/-!
### Non-destructive Binary Register Copy (`wsCopy`)
-/

abbrev SegTriple (MaxSeg : ℕ) : Type :=
  Fin (MaxSeg + 1) × Fin (MaxSeg + 1) × Fin (MaxSeg + 1)

abbrev WsDrainQ (MaxSeg : ℕ) : Type :=
  WsDecJzQ MaxSeg ⊕ (Unit ⊕ (LiftBlkQ (Fin (MaxSeg + 1) × Bool) ⊕ LiftBlkQ (Fin (MaxSeg + 1) × Bool)))

def wsDrainBody (MaxSeg : ℕ) (tr : SegTriple MaxSeg) : StepFn (WsDrainQ MaxSeg) :=
  seq0 (wsDecJz MaxSeg)
    (sumStep (nopStep Unit) (seq0 (wsInc MaxSeg) (wsInc MaxSeg) (fun _ => wsIncEntry MaxSeg tr.2.2)))
    (fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (Sum.inl (wsIncEntry MaxSeg tr.1)))

def wsDrainNext (MaxSeg : ℕ) (tr : SegTriple MaxSeg) : WsDrainQ MaxSeg → Option (WsDrainQ MaxSeg)
  | Sum.inr (Sum.inr _) => some (Sum.inl (wsDecJzEntry MaxSeg tr.2.1))
  | _ => none

def wsDrainLoop (MaxSeg : ℕ) (tr : SegTriple MaxSeg) : StepFn (WsDrainQ MaxSeg) :=
  loop0 (wsDrainBody MaxSeg tr) (wsDrainNext MaxSeg tr)

abbrev WsRestoreQ (MaxSeg : ℕ) : Type :=
  WsDecJzQ MaxSeg ⊕ (Unit ⊕ LiftBlkQ (Fin (MaxSeg + 1) × Bool))

def wsRestoreBody (MaxSeg : ℕ) (tr : SegTriple MaxSeg) : StepFn (WsRestoreQ MaxSeg) :=
  seq0 (wsDecJz MaxSeg)
    (sumStep (nopStep Unit) (wsInc MaxSeg))
    (fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (wsIncEntry MaxSeg tr.2.1))

def wsRestoreNext (MaxSeg : ℕ) (tr : SegTriple MaxSeg) : WsRestoreQ MaxSeg → Option (WsRestoreQ MaxSeg)
  | Sum.inr (Sum.inr _) => some (Sum.inl (wsDecJzEntry MaxSeg tr.2.2))
  | _ => none

def wsRestoreLoop (MaxSeg : ℕ) (tr : SegTriple MaxSeg) : StepFn (WsRestoreQ MaxSeg) :=
  loop0 (wsRestoreBody MaxSeg tr) (wsRestoreNext MaxSeg tr)

abbrev WsCopyInnerQ (MaxSeg : ℕ) : Type :=
  LiftBlkQ (Fin (MaxSeg + 1) × Bool) ⊕
  (LiftBlkQ (Fin (MaxSeg + 1) × Bool) ⊕ (WsDrainQ MaxSeg ⊕ WsRestoreQ MaxSeg))

def wsCopyFor (MaxSeg : ℕ) (tr : SegTriple MaxSeg) : StepFn (WsCopyInnerQ MaxSeg) :=
  seq0 (wsZero MaxSeg)
    (seq0 (wsZero MaxSeg)
      (seq0 (wsDrainLoop MaxSeg tr) (wsRestoreLoop MaxSeg tr)
        (fun _ => Sum.inl (wsDecJzEntry MaxSeg tr.2.2)))
      (fun _ => Sum.inl (Sum.inl (wsDecJzEntry MaxSeg tr.2.1))))
    (fun _ => Sum.inl (wsZeroEntry MaxSeg tr.2.2))

def wsCopy (MaxSeg : ℕ) : StepFn (SegTriple MaxSeg × WsCopyInnerQ MaxSeg) :=
  familyStep (wsCopyFor MaxSeg)

def wsCopyEntry (MaxSeg : ℕ) (tr : SegTriple MaxSeg) : SegTriple MaxSeg × WsCopyInnerQ MaxSeg :=
  (tr, Sum.inl (wsZeroEntry MaxSeg tr.1))

theorem getD_set_self_seg (segs : List (List Bool)) {s : ℕ} (hs : s < segs.length) (x : List Bool) :
    (segs.set s x).getD s [] = x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hs]

theorem getD_set_ne_seg (segs : List (List Bool)) {s₁ s₂ : ℕ} (hne : s₁ ≠ s₂) (x : List Bool) :
    (segs.set s₁ x).getD s₂ [] = segs.getD s₂ [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

theorem wsDrainLoop_spec (MaxSeg B w : ℕ) (tr : SegTriple MaxSeg)
    (h_ds : tr.1.val ≠ tr.2.1.val) (h_dt : tr.1.val ≠ tr.2.2.val) (h_st : tr.2.1.val ≠ tr.2.2.val) :
    ∀ rem acc (segs : List (List Bool)) len (τ₁ : ℕ → Bool),
      tr.1.val < segs.length → tr.2.1.val < segs.length → tr.2.2.val < segs.length →
      acc + rem < 2 ^ w →
      segs.getD tr.1.val [] = natToBitsLE w acc →
      segs.getD tr.2.1.val [] = natToBitsLE w rem →
      segs.getD tr.2.2.val [] = natToBitsLE w acc →
      TapeWS τ₁ len B segs →
      ∃ τ₂ : ℕ → Bool,
        TapeWS τ₂ len B (((segs.set tr.2.1.val (natToBitsLE w 0)).set tr.1.val (natToBitsLE w (acc + rem))).set
          tr.2.2.val (natToBitsLE w (acc + rem))) ∧
        (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
        StepExec (wsDrainLoop MaxSeg tr) B (Sum.inl (wsDecJzEntry MaxSeg tr.2.1)) len τ₁ 0
          (Sum.inr (Sum.inl ())) len τ₂ 0 ((rem + 1) * (84 * (encodeWorkspace segs).length + 25)) := by
  intro rem
  induction rem with
  | zero =>
    intro acc segs len τ₁ hd hs ht hbound hseg_d hseg_s hseg_t htw
    have hlen_pos := TapeWS_pos htw
    have hlen_B := htw.2.2.1
    rcases wsDecJz_spec MaxSeg B segs hs (Nat.le_of_lt_succ tr.2.1.isLt) hseg_s (by omega) htw
      with ⟨q_dec, τ_mid, hz_out, htw_mid, hout_mid, he_dec⟩
    simp only [decide_true, ↓reduceIte] at hz_out htw_mid
    have he_nop := sumStep_inl_spec (nopStep Unit)
      (seq0 (wsInc MaxSeg) (wsInc MaxSeg) (fun _ => wsIncEntry MaxSeg tr.2.2))
      (nopStep_spec () len τ_mid 0 hlen_B (by omega))
    have hbody := seq0_spec (f := fun q => if wsDecJzWasZero q then Sum.inl ()
      else Sum.inr (Sum.inl (wsIncEntry MaxSeg tr.1))) hlen_pos he_dec (by simpa [hz_out] using he_nop)
    have hdone := (loop0_done (next := wsDrainNext MaxSeg tr) hbody rfl).weaken
      ((0 + 1) * (84 * (encodeWorkspace segs).length + 25)) (by omega)
    have hset_noop : (((segs.set tr.2.1.val (natToBitsLE w 0)).set tr.1.val (natToBitsLE w (acc + 0))).set
        tr.2.2.val (natToBitsLE w (acc + 0))) = segs := by
      apply List.ext_getElem (by simp)
      intro k hk1 hk2
      simp only [Nat.add_zero, List.getElem_set]
      split_ifs with h1 h2 h3
      · subst h1; simp [List.getD_eq_getElem?_getD] at hseg_t; rw [List.getElem?_eq_getElem hk2] at hseg_t; exact (Option.getD_some .. ▸ hseg_t).symm
      · subst h2; simp [List.getD_eq_getElem?_getD] at hseg_d; rw [List.getElem?_eq_getElem hk2] at hseg_d; exact (Option.getD_some .. ▸ hseg_d).symm
      · subst h3; simp [List.getD_eq_getElem?_getD] at hseg_s; rw [List.getElem?_eq_getElem hk2] at hseg_s; exact (Option.getD_some .. ▸ hseg_s).symm
      · rfl
    rw [hset_noop]
    exact ⟨τ_mid, htw_mid, hout_mid, hdone⟩
  | succ rem ih =>
    intro acc segs len τ₁ hd hs ht hbound hseg_d hseg_s hseg_t htw
    have hlen_pos := TapeWS_pos htw
    rcases wsDecJz_spec MaxSeg B segs hs (Nat.le_of_lt_succ tr.2.1.isLt) hseg_s (by omega) htw
      with ⟨q_dec, τ₁', hz_out, htw₁, hout₁, he_dec⟩
    simp only [Nat.add_one_ne_zero, decide_false, ↓reduceIte,
      Nat.add_sub_cancel] at hz_out htw₁
    let segs₁ := segs.set tr.2.1.val (natToBitsLE w rem)
    have hM₁ : (encodeWorkspace segs₁).length = (encodeWorkspace segs).length :=
      length_encodeWorkspace_set hs (by rw [hseg_s, length_natToBitsLE, length_natToBitsLE])
    have hd₁ : tr.1.val < segs₁.length := by simpa [segs₁] using hd
    have hseg_d₁ : segs₁.getD tr.1.val [] = natToBitsLE w acc := by
      rw [getD_set_ne_seg segs h_ds.symm]; exact hseg_d
    rcases wsInc_spec MaxSeg B segs₁ hd₁ (Nat.le_of_lt_succ tr.1.isLt) hseg_d₁ (by omega) htw₁
      with ⟨τ₂', htw₂, hout₂, he_inc1⟩
    let segs₂ := segs₁.set tr.1.val (natToBitsLE w (acc + 1))
    have hM₂ : (encodeWorkspace segs₂).length = (encodeWorkspace segs).length :=
      (length_encodeWorkspace_set hd₁ (by rw [hseg_d₁, length_natToBitsLE, length_natToBitsLE])).trans hM₁
    have ht₂ : tr.2.2.val < segs₂.length := by simpa [segs₂, segs₁] using ht
    have hseg_t₂ : segs₂.getD tr.2.2.val [] = natToBitsLE w acc := by
      rw [getD_set_ne_seg segs₁ h_dt, getD_set_ne_seg segs h_st]; exact hseg_t
    rcases wsInc_spec MaxSeg B segs₂ ht₂ (Nat.le_of_lt_succ tr.2.2.isLt) hseg_t₂ (by omega) htw₂
      with ⟨τ₃', htw₃, hout₃, he_inc2⟩
    let segs₃ := segs₂.set tr.2.2.val (natToBitsLE w (acc + 1))
    have hM₃ : (encodeWorkspace segs₃).length = (encodeWorkspace segs).length :=
      (length_encodeWorkspace_set ht₂ (by rw [hseg_t₂, length_natToBitsLE, length_natToBitsLE])).trans hM₂
    rw [hM₁] at hout₂ he_inc1
    rw [hM₂] at hout₃ he_inc2
    have he_incs := seq0_spec (f := fun _ => wsIncEntry MaxSeg tr.2.2) hlen_pos he_inc1
      (by simpa using he_inc2)
    have he_right := sumStep_inr_spec (nopStep Unit) _ he_incs
    have hbody := seq0_spec (f := fun q => if wsDecJzWasZero q then Sum.inl ()
      else Sum.inr (Sum.inl (wsIncEntry MaxSeg tr.1))) hlen_pos he_dec (by simpa [hz_out] using he_right)
    rcases ih (acc + 1) segs₃ len τ₃'
        (by simpa [segs₃, segs₂, segs₁] using hd)
        (by simpa [segs₃, segs₂, segs₁] using hs)
        (by simpa [segs₃, segs₂, segs₁] using ht)
        (by omega)
        (by rw [getD_set_ne_seg _ h_dt.symm, getD_set_self_seg _ hd₁])
        (by rw [getD_set_ne_seg _ h_st.symm, getD_set_ne_seg _ h_ds, getD_set_self_seg _ hs])
        (by rw [getD_set_self_seg _ ht₂])
        htw₃
      with ⟨τ_end, htw_end, hout_end, he_rest⟩
    rw [hM₃] at hout_end he_rest
    let M := (encodeWorkspace segs).length
    have hstep := (loop0_step (next := wsDrainNext MaxSeg tr) hlen_pos hbody rfl he_rest).weaken
      ((rem + 1 + 1) * (84 * M + 25)) (by
        have : (rem + 1 + 1) * (84 * M + 25) = (84 * M + 25) + (rem + 1) * (84 * M + 25) := by ring
        dsimp only [M] at *; omega)
    have hsegs_eq : (((segs₃.set tr.2.1.val (natToBitsLE w 0)).set tr.1.val (natToBitsLE w (acc + 1 + rem))).set
        tr.2.2.val (natToBitsLE w (acc + 1 + rem))) =
      (((segs.set tr.2.1.val (natToBitsLE w 0)).set tr.1.val (natToBitsLE w (acc + (rem + 1)))).set
        tr.2.2.val (natToBitsLE w (acc + (rem + 1)))) := by
      have hadd : acc + 1 + rem = acc + (rem + 1) := by omega
      rw [hadd]
      apply List.ext_getElem (by simp [segs₃, segs₂, segs₁])
      intro k hk1 hk2
      simp only [segs₃, segs₂, segs₁, List.getElem_set]
      split_ifs <;> rfl
    rw [hsegs_eq] at htw_end
    refine ⟨τ_end, htw_end, fun p hp => ?_, hstep⟩
    exact (hout_end p hp).trans ((hout₃ p hp).trans ((hout₂ p hp).trans (hout₁ p hp)))

theorem wsRestoreLoop_spec (MaxSeg B w : ℕ) (tr : SegTriple MaxSeg)
    (h_st : tr.2.1.val ≠ tr.2.2.val) :
    ∀ rem acc (segs : List (List Bool)) len (τ₁ : ℕ → Bool),
      tr.2.1.val < segs.length → tr.2.2.val < segs.length →
      acc + rem < 2 ^ w →
      segs.getD tr.2.1.val [] = natToBitsLE w acc →
      segs.getD tr.2.2.val [] = natToBitsLE w rem →
      TapeWS τ₁ len B segs →
      ∃ τ₂ : ℕ → Bool,
        TapeWS τ₂ len B ((segs.set tr.2.2.val (natToBitsLE w 0)).set tr.2.1.val (natToBitsLE w (acc + rem))) ∧
        (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
        StepExec (wsRestoreLoop MaxSeg tr) B (Sum.inl (wsDecJzEntry MaxSeg tr.2.2)) len τ₁ 0
          (Sum.inr (Sum.inl ())) len τ₂ 0 ((rem + 1) * (63 * (encodeWorkspace segs).length + 20)) := by
  intro rem
  induction rem with
  | zero =>
    intro acc segs len τ₁ hs ht hbound hseg_s hseg_t htw
    have hlen_pos := TapeWS_pos htw
    have hlen_B := htw.2.2.1
    rcases wsDecJz_spec MaxSeg B segs ht (Nat.le_of_lt_succ tr.2.2.isLt) hseg_t (by omega) htw
      with ⟨q_dec, τ_mid, hz_out, htw_mid, hout_mid, he_dec⟩
    simp only [decide_true, ↓reduceIte] at hz_out htw_mid
    have he_nop := sumStep_inl_spec (nopStep Unit) (wsInc MaxSeg) (nopStep_spec () len τ_mid 0 hlen_B (by omega))
    have hbody := seq0_spec (f := fun q => if wsDecJzWasZero q then Sum.inl ()
      else Sum.inr (wsIncEntry MaxSeg tr.2.1)) hlen_pos he_dec (by simpa [hz_out] using he_nop)
    have hdone := (loop0_done (next := wsRestoreNext MaxSeg tr) hbody rfl).weaken
      ((0 + 1) * (63 * (encodeWorkspace segs).length + 20)) (by omega)
    have hset_noop : ((segs.set tr.2.2.val (natToBitsLE w 0)).set tr.2.1.val (natToBitsLE w (acc + 0))) = segs := by
      apply List.ext_getElem (by simp)
      intro k hk1 hk2
      simp only [Nat.add_zero, List.getElem_set]
      split_ifs with h1 h2
      · subst h1; simp [List.getD_eq_getElem?_getD] at hseg_s; rw [List.getElem?_eq_getElem hk2] at hseg_s; exact (Option.getD_some .. ▸ hseg_s).symm
      · subst h2; simp [List.getD_eq_getElem?_getD] at hseg_t; rw [List.getElem?_eq_getElem hk2] at hseg_t; exact (Option.getD_some .. ▸ hseg_t).symm
      · rfl
    rw [hset_noop]
    exact ⟨τ_mid, htw_mid, hout_mid, hdone⟩
  | succ rem ih =>
    intro acc segs len τ₁ hs ht hbound hseg_s hseg_t htw
    have hlen_pos := TapeWS_pos htw
    rcases wsDecJz_spec MaxSeg B segs ht (Nat.le_of_lt_succ tr.2.2.isLt) hseg_t (by omega) htw
      with ⟨q_dec, τ₁', hz_out, htw₁, hout₁, he_dec⟩
    simp only [Nat.add_one_ne_zero, decide_false, ↓reduceIte,
      Nat.add_sub_cancel] at hz_out htw₁
    let segs₁ := segs.set tr.2.2.val (natToBitsLE w rem)
    have hM₁ : (encodeWorkspace segs₁).length = (encodeWorkspace segs).length :=
      length_encodeWorkspace_set ht (by rw [hseg_t, length_natToBitsLE, length_natToBitsLE])
    have hs₁ : tr.2.1.val < segs₁.length := by simpa [segs₁] using hs
    have hseg_s₁ : segs₁.getD tr.2.1.val [] = natToBitsLE w acc := by
      rw [getD_set_ne_seg segs h_st.symm]; exact hseg_s
    rcases wsInc_spec MaxSeg B segs₁ hs₁ (Nat.le_of_lt_succ tr.2.1.isLt) hseg_s₁ (by omega) htw₁
      with ⟨τ₂', htw₂, hout₂, he_inc⟩
    let segs₂ := segs₁.set tr.2.1.val (natToBitsLE w (acc + 1))
    have hM₂ : (encodeWorkspace segs₂).length = (encodeWorkspace segs).length :=
      (length_encodeWorkspace_set hs₁ (by rw [hseg_s₁, length_natToBitsLE, length_natToBitsLE])).trans hM₁
    rw [hM₁] at hout₂ he_inc
    have he_right := sumStep_inr_spec (nopStep Unit) _ he_inc
    have hbody := seq0_spec (f := fun q => if wsDecJzWasZero q then Sum.inl ()
      else Sum.inr (wsIncEntry MaxSeg tr.2.1)) hlen_pos he_dec (by simpa [hz_out] using he_right)
    rcases ih (acc + 1) segs₂ len τ₂'
        (by simpa [segs₂, segs₁] using hs)
        (by simpa [segs₂, segs₁] using ht)
        (by omega)
        (by rw [getD_set_self_seg _ hs₁])
        (by rw [getD_set_ne_seg _ h_st, getD_set_self_seg _ ht])
        htw₂
      with ⟨τ_end, htw_end, hout_end, he_rest⟩
    rw [hM₂] at hout_end he_rest
    let M := (encodeWorkspace segs).length
    have hstep := (loop0_step (next := wsRestoreNext MaxSeg tr) hlen_pos hbody rfl he_rest).weaken
      ((rem + 1 + 1) * (63 * M + 20)) (by
        have : (rem + 1 + 1) * (63 * M + 20) = (63 * M + 20) + (rem + 1) * (63 * M + 20) := by ring
        dsimp only [M] at *; omega)
    have hsegs_eq : ((segs₂.set tr.2.2.val (natToBitsLE w 0)).set tr.2.1.val (natToBitsLE w (acc + 1 + rem))) =
        ((segs.set tr.2.2.val (natToBitsLE w 0)).set tr.2.1.val (natToBitsLE w (acc + (rem + 1)))) := by
      have hadd : acc + 1 + rem = acc + (rem + 1) := by omega
      rw [hadd]
      apply List.ext_getElem (by simp [segs₂, segs₁])
      intro k hk1 hk2
      simp only [segs₂, segs₁, List.getElem_set]
      split_ifs <;> rfl
    rw [hsegs_eq] at htw_end
    refine ⟨τ_end, htw_end, fun p hp => ?_, hstep⟩
    exact (hout_end p hp).trans ((hout₂ p hp).trans (hout₁ p hp))

theorem wsCopyFor_spec (MaxSeg B : ℕ) (segs : List (List Bool)) {dst src tmp w v : ℕ}
    (hd : dst < segs.length) (hs : src < segs.length) (ht : tmp < segs.length)
    (hd_m : dst ≤ MaxSeg) (hs_m : src ≤ MaxSeg) (ht_m : tmp ≤ MaxSeg)
    (h_ds : dst ≠ src) (h_dt : dst ≠ tmp) (h_st : src ≠ tmp)
    (hlen_d : (segs.getD dst []).length = w)
    (hseg_s : segs.getD src [] = natToBitsLE w v)
    (hlen_t : (segs.getD tmp []).length = w)
    (hv : v < 2 ^ w)
    {len : ℕ} {τ₁ : ℕ → Bool} (htw : TapeWS τ₁ len B segs) :
    let tr : SegTriple MaxSeg := (⟨dst, by omega⟩, ⟨src, by omega⟩, ⟨tmp, by omega⟩)
    ∃ q_end : WsCopyInnerQ MaxSeg, ∃ τ₂ : ℕ → Bool,
      TapeWS τ₂ len B ((segs.set dst (natToBitsLE w v)).set tmp (natToBitsLE w 0)) ∧
      (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (wsCopyFor MaxSeg tr) B (Sum.inl (wsZeroEntry MaxSeg tr.1)) len τ₁ 0
        q_end len τ₂ 0 ((v + 2) * (150 * (encodeWorkspace segs).length + 50)) := by
  intro tr
  have hlen_pos := TapeWS_pos htw
  rcases wsZero_spec MaxSeg B segs hd hd_m hlen_d htw with ⟨τ_z1, htw_z1, hout_z1, he_z1⟩
  let segs_z1 := segs.set dst (natToBitsLE w 0)
  have hM_z1 : (encodeWorkspace segs_z1).length = (encodeWorkspace segs).length :=
    length_encodeWorkspace_set hd (by rw [hlen_d, length_natToBitsLE])
  have ht_z1 : tmp < segs_z1.length := by simpa [segs_z1] using ht
  have hlen_t1 : (segs_z1.getD tmp []).length = w := by
    rw [getD_set_ne_seg segs h_dt]; exact hlen_t
  rcases wsZero_spec MaxSeg B segs_z1 ht_z1 ht_m hlen_t1 htw_z1 with ⟨τ_z2, htw_z2, hout_z2, he_z2⟩
  rw [hM_z1] at hout_z2 he_z2
  let segs_z2 := segs_z1.set tmp (natToBitsLE w 0)
  have hM_z2 : (encodeWorkspace segs_z2).length = (encodeWorkspace segs).length :=
    (length_encodeWorkspace_set ht_z1 (by rw [hlen_t1, length_natToBitsLE])).trans hM_z1
  rcases wsDrainLoop_spec MaxSeg B w tr h_ds h_dt h_st v 0 segs_z2 len τ_z2
      (by simpa [segs_z2, segs_z1] using hd)
      (by simpa [segs_z2, segs_z1] using hs)
      (by simpa [segs_z2, segs_z1] using ht)
      (by omega)
      (by rw [getD_set_ne_seg _ h_dt.symm, getD_set_self_seg _ hd])
      (by rw [getD_set_ne_seg _ h_st.symm, getD_set_ne_seg _ h_ds, hseg_s])
      (by rw [getD_set_self_seg _ ht_z1])
      htw_z2
    with ⟨τ_dr, htw_dr, hout_dr, he_dr⟩
  rw [hM_z2] at hout_dr he_dr
  simp only [Nat.zero_add] at htw_dr
  let segs_dr := ((segs_z2.set src (natToBitsLE w 0)).set dst (natToBitsLE w v)).set tmp (natToBitsLE w v)
  have hM_dr : (encodeWorkspace segs_dr).length = (encodeWorkspace segs).length := by
    dsimp only [segs_dr]
    have h1 := length_encodeWorkspace_set (segs := segs_z2) (s := src) (newSeg := natToBitsLE w 0)
      (by simpa [segs_z2, segs_z1] using hs)
      (by rw [getD_set_ne_seg _ h_st.symm, getD_set_ne_seg _ h_ds, hseg_s, length_natToBitsLE, length_natToBitsLE])
    have h2 := length_encodeWorkspace_set (segs := segs_z2.set src (natToBitsLE w 0)) (s := dst) (newSeg := natToBitsLE w v)
      (by simpa [segs_z2, segs_z1] using hd)
      (by rw [getD_set_ne_seg _ h_ds.symm, getD_set_ne_seg _ h_dt.symm, getD_set_self_seg _ hd, length_natToBitsLE, length_natToBitsLE])
    have h3 := length_encodeWorkspace_set (segs := (segs_z2.set src (natToBitsLE w 0)).set dst (natToBitsLE w v)) (s := tmp) (newSeg := natToBitsLE w v)
      (by simpa [segs_z2, segs_z1] using ht)
      (by rw [getD_set_ne_seg _ h_dt, getD_set_ne_seg _ h_st, getD_set_self_seg _ ht_z1, length_natToBitsLE, length_natToBitsLE])
    rw [h3, h2, h1, hM_z2]
  rcases wsRestoreLoop_spec MaxSeg B w tr h_st v 0 segs_dr len τ_dr
      (by simpa [segs_dr, segs_z2, segs_z1] using hs)
      (by simpa [segs_dr, segs_z2, segs_z1] using ht)
      (by omega)
      (by dsimp only [segs_dr]; rw [getD_set_ne_seg _ h_st.symm, getD_set_ne_seg _ h_ds, getD_set_self_seg _ (by simpa [segs_z2, segs_z1] using hs)])
      (by dsimp only [segs_dr]; rw [getD_set_self_seg _ (by simpa [segs_z2, segs_z1] using ht)])
      htw_dr
    with ⟨τ_end, htw_end, hout_end, he_res⟩
  rw [hM_dr] at hout_end he_res
  simp only [Nat.zero_add] at htw_end
  have hsegs_final : ((segs_dr.set tmp (natToBitsLE w 0)).set src (natToBitsLE w v)) =
      ((segs.set dst (natToBitsLE w v)).set tmp (natToBitsLE w 0)) := by
    apply List.ext_getElem (by simp [segs_dr, segs_z2, segs_z1])
    intro k hk1 hk2
    simp only [segs_dr, segs_z2, segs_z1, List.getElem_set]
    by_cases hkt : tmp = k
    · subst hkt; simp [h_st]
    · by_cases hkd : dst = k
      · subst hkd; simp [hkt, h_ds.symm]
      · by_cases hks : src = k
        · subst hks; simp [hkt, hkd]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, Option.getD_some] at hseg_s
          exact hseg_s.symm
        · simp [hkt, hkd, hks]
  rw [hsegs_final] at htw_end
  have he_34 := seq0_spec (f := fun _ => Sum.inl (wsDecJzEntry MaxSeg tr.2.2)) hlen_pos he_dr he_res
  have he_234 := seq0_spec (f := fun _ => Sum.inl (Sum.inl (wsDecJzEntry MaxSeg tr.2.1))) hlen_pos he_z2 he_34
  have he_1234 := seq0_spec (f := fun _ => Sum.inl (wsZeroEntry MaxSeg tr.2.2)) hlen_pos he_z1 he_234
  let M := (encodeWorkspace segs).length
  have he_w := he_1234.weaken ((v + 2) * (150 * M + 50)) (by
      have hmul1 : (v + 1) * (147 * M + 45) ≤ (v + 1) * (150 * M + 50) :=
        Nat.mul_le_mul_left (v + 1) (by omega)
      have hring1 : (v + 1) * (84 * M + 25) + 1 + (v + 1) * (63 * M + 20) =
          1 + (v + 1) * (147 * M + 45) := by ring
      have hring2 : (v + 2) * (150 * M + 50) = (150 * M + 50) + (v + 1) * (150 * M + 50) := by ring
      dsimp only [M] at *
      omega)
  exact ⟨_, τ_end, htw_end, fun p hp =>
    (hout_end p hp).trans ((hout_dr p hp).trans ((hout_z2 p hp).trans (hout_z1 p hp))), he_w⟩

theorem wsCopy_spec (MaxSeg B : ℕ) (segs : List (List Bool)) {dst src tmp w v : ℕ}
    (hd : dst < segs.length) (hs : src < segs.length) (ht : tmp < segs.length)
    (hd_m : dst ≤ MaxSeg) (hs_m : src ≤ MaxSeg) (ht_m : tmp ≤ MaxSeg)
    (h_ds : dst ≠ src) (h_dt : dst ≠ tmp) (h_st : src ≠ tmp)
    (hlen_d : (segs.getD dst []).length = w)
    (hseg_s : segs.getD src [] = natToBitsLE w v)
    (hlen_t : (segs.getD tmp []).length = w)
    (hv : v < 2 ^ w)
    {len : ℕ} {τ₁ : ℕ → Bool} (htw : TapeWS τ₁ len B segs) :
    let tr : SegTriple MaxSeg := (⟨dst, by omega⟩, ⟨src, by omega⟩, ⟨tmp, by omega⟩)
    ∃ q_end, ∃ τ₂ : ℕ → Bool,
      TapeWS τ₂ len B ((segs.set dst (natToBitsLE w v)).set tmp (natToBitsLE w 0)) ∧
      (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (wsCopy MaxSeg) B (wsCopyEntry MaxSeg tr) len τ₁ 0
        q_end len τ₂ 0 ((v + 2) * (150 * (encodeWorkspace segs).length + 50)) := by
  intro tr
  rcases wsCopyFor_spec MaxSeg B segs hd hs ht hd_m hs_m ht_m h_ds h_dt h_st hlen_d hseg_s hlen_t hv htw
    with ⟨q_in, τ₂, htw₂, hout₂, he_in⟩
  exact ⟨(tr, q_in), τ₂, htw₂, hout₂, familyStep_spec (wsCopyFor MaxSeg) tr he_in⟩

/-!
### Random-Access Segment Bit Read (`wsReadBit`)
-/

def reMark (S : ℕ → Bool) (σ : ℕ → BlkSym) : ℕ → BlkSym :=
  fun j => if S j && !(σ j).1 then blkData true (σ j).2.2 else σ j

theorem reMark_of_false {S : ℕ → Bool} (σ : ℕ → BlkSym) {j : ℕ} (hj : S j = false) :
    reMark S σ j = σ j := by
  simp [reMark, hj]

theorem reMark_of_ctrl (S : ℕ → Bool) (σ : ℕ → BlkSym) {j : ℕ} (hj : (σ j).1 = true) :
    reMark S σ j = σ j := by
  simp [reMark, hj]

theorem reMark_home_iff {S : ℕ → Bool} {σ : ℕ → BlkSym} {j : ℕ} :
    reMark S σ j = blkHome ↔ σ j = blkHome := by
  unfold reMark
  by_cases h : (S j && !(σ j).1) = true
  · simp only [h, ↓reduceIte]
    constructor
    · intro h0; simp [blkData, blkHome] at h0
    · intro h0; rw [h0] at h; simp [blkHome] at h
  · simp [h]

theorem reMark_sep_iff {S : ℕ → Bool} {σ : ℕ → BlkSym} {j : ℕ} :
    reMark S σ j = blkSep ↔ σ j = blkSep := by
  unfold reMark
  by_cases h : (S j && !(σ j).1) = true
  · simp only [h, ↓reduceIte]
    constructor
    · intro h0; simp [blkData, blkSep] at h0
    · intro h0; rw [h0] at h; simp [blkSep] at h
  · simp [h]

theorem reMark_fst (S : ℕ → Bool) (σ : ℕ → BlkSym) (j : ℕ) :
    (reMark S σ j).1 = (σ j).1 := by
  unfold reMark
  by_cases h : (S j && !(σ j).1) = true
  · rw [Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [h.1, h.2, blkData]
  · simp [h]

theorem reMark_thd (S : ℕ → Bool) (σ : ℕ → BlkSym) (j : ℕ) :
    (reMark S σ j).2.2 = (σ j).2.2 := by
  unfold reMark
  split_ifs <;> rfl

theorem reMark_update_false {S : ℕ → Bool} (σ : ℕ → BlkSym) {j : ℕ} (hj : S j = false) (sym : BlkSym) :
    Function.update (reMark S σ) j sym = reMark S (Function.update σ j sym) := by
  funext i
  by_cases hij : i = j
  · subst hij; simp [reMark, hj]
  · simp [Function.update_of_ne hij, reMark]

def segMarkRange (segs : List (List Bool)) (arrSeg lo hi : ℕ) (j : ℕ) : Bool :=
  decide (segStart segs arrSeg + lo ≤ j ∧ j < segStart segs arrSeg + hi)

def segMarkPred (segs : List (List Bool)) (arrSeg k : ℕ) (j : ℕ) : Bool :=
  segMarkRange segs arrSeg 0 (min k (segs.getD arrSeg []).length) j

def TapeMarkedWS (τ : ℕ → Bool) (len B : ℕ) (segs : List (List Bool)) (arrSeg k : ℕ) : Prop :=
  segs ≠ [] ∧ 3 * (encodeWorkspace segs).length ≤ len ∧ len ≤ B ∧
  ∃ σ₀ : ℕ → BlkSym, MatchesWS σ₀ segs ∧ readBlk τ = reMark (segMarkPred segs arrSeg k) σ₀

theorem TapeMarkedWS_zero_iff {τ : ℕ → Bool} {len B : ℕ} {segs : List (List Bool)} {arrSeg : ℕ} :
    TapeMarkedWS τ len B segs arrSeg 0 ↔ TapeWS τ len B segs := by
  have hzero : segMarkPred segs arrSeg 0 = fun _ => false := by
    funext j; simp [segMarkPred, segMarkRange]
  have hrm : ∀ σ₀, reMark (fun _ => false) σ₀ = σ₀ := by
    intro σ₀; funext j; simp [reMark]
  constructor
  · rintro ⟨h1, h2, h3, σ₀, hws, heq⟩
    rw [hzero, hrm] at heq
    exact ⟨h1, h2, h3, heq.symm ▸ hws⟩
  · rintro ⟨h1, h2, h3, hws⟩
    exact ⟨h1, h2, h3, readBlk τ, hws, by rw [hzero, hrm]⟩

theorem blkCheckZeroSeg_reMark (MaxSeg : ℕ) (S : ℕ → Bool) (q : Fin (MaxSeg + 1) × Bool × Bool)
    (σ : ℕ → BlkSym) (j : ℕ) :
    blkCheckZeroSeg MaxSeg q (reMark S σ j) =
      (blkCheckZeroSeg MaxSeg q (σ j)).map (fun (q', _, d) => (q', reMark S σ j, d)) := by
  rcases q with ⟨rem, rew, res⟩
  unfold blkCheckZeroSeg
  simp only [reMark_home_iff, reMark_sep_iff, reMark_fst, reMark_thd]
  by_cases hrw : rew = true
  · simp only [hrw, ↓reduceIte]; split_ifs <;> rfl
  · simp only [hrw, Bool.false_eq_true, ↓reduceIte]
    by_cases hh : σ j = blkHome
    · have hc : (σ j).1 = true := by rw [hh]; rfl
      simp [hh, reMark_of_ctrl S σ hc]
    · simp only [hh, ↓reduceIte]
      by_cases hrem : 0 < rem.val
      · simp only [hrem, ↓reduceDIte]
        by_cases hsep : σ j = blkSep
        · have hc : (σ j).1 = true := by rw [hsep]; rfl
          simp [hsep, reMark_of_ctrl S σ hc]
        · simp [hsep]
      · simp only [hrem, ↓reduceDIte]
        split_ifs <;> rfl

theorem blkCheckZeroSeg_sym_eq (MaxSeg : ℕ) (q q' : Fin (MaxSeg + 1) × Bool × Bool)
    (sym sym' : BlkSym) (dir : QCSD_HeadDir)
    (h : blkCheckZeroSeg MaxSeg q sym = some (q', sym', dir)) : sym' = sym := by
  rcases q with ⟨rem, rew, res⟩
  unfold blkCheckZeroSeg at h
  by_cases hrw : rew = true
  · simp only [hrw, ↓reduceIte] at h
    split_ifs at h with hh
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.1.symm
  · simp only [hrw, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hh : sym = blkHome
    · simp only [hh, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.1.symm.trans hh.symm
    · simp only [hh, ↓reduceIte] at h
      by_cases hrem : 0 < rem.val
      · simp only [hrem, ↓reduceDIte] at h
        split_ifs at h with hsep
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.2.1.symm.trans hsep.symm
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.2.1.symm
      · simp only [hrem, ↓reduceDIte] at h
        split_ifs at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.1.symm)

theorem blkIter_checkZero_reMark (MaxSeg : ℕ) (S : ℕ → Bool) :
    ∀ i q (σ : ℕ → BlkSym) j,
      blkIter (blkCheckZeroSeg MaxSeg) (q, reMark S σ, j) i =
        (blkIter (blkCheckZeroSeg MaxSeg) (q, σ, j) i).map
          (fun (q', σ', j') => (q', reMark S σ', j')) := by
  intro i
  induction i with
  | zero => intros; rfl
  | succ i ih =>
    intro q σ j
    simp only [blkIter, blkOnce, blkCheckZeroSeg_reMark]
    cases h : blkCheckZeroSeg MaxSeg q (σ j) with
    | none => rfl
    | some val =>
      rcases val with ⟨q', sym', dir⟩
      obtain rfl : sym' = σ j := blkCheckZeroSeg_sym_eq MaxSeg q q' (σ j) sym' dir h
      simp only [Option.map_some, Function.update_eq_self]
      exact ih q' σ (moveHead j dir)

theorem blkGoToSeg_reMark_aux {Q : Type} (bs : BlkStepFn Q) (segs : List (List Bool))
    (S : ℕ → Bool) (σ₀ : ℕ → BlkSym) (hws : MatchesWS σ₀ segs)
    (go : ℕ → Q) {s : ℕ} (hs : s < segs.length)
    (h_home : bs (go s) blkHome = some (go s, blkHome, QCSD_HeadDir.right))
    (h_data : ∀ r < s, ∀ m b, bs (go (r + 1)) (blkData m b) =
      some (go (r + 1), blkData m b, QCSD_HeadDir.right))
    (h_sep : ∀ r < s, bs (go (r + 1)) blkSep = some (go r, blkSep, QCSD_HeadDir.right)) :
    let M_blk := (encodeWorkspace segs).length
    let σ := reMark S σ₀
    blkIter bs (go s, σ, 0) (segStart segs s) = some (go 0, σ, segStart segs s) ∧
    (∀ i ≤ segStart segs s, ∀ q' σ' j',
      blkIter bs (go s, σ, 0) i = some (q', σ', j') → j' < M_blk) ∧
    (∀ i < segStart segs s, ∀ q' σ' j' q'' sym' dir,
      blkIter bs (go s, σ, 0) i = some (q', σ', j') →
      bs q' (σ' j') = some (q'', sym', dir) →
      (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
  intro M_blk σ
  have hsb := segStart_bound segs s hs
  have hs1 := segStart_pos segs s
  have h0_at : σ 0 = blkHome := reMark_home_iff.mpr ((hws 0 (by omega)).trans (encodeWorkspace_getD_zero segs))
  have hbs0 : bs (go s) (σ 0) = some (go s, σ 0, QCSD_HeadDir.right) := by rw [h0_at]; exact h_home
  have hstep0 : blkIter bs (go s, σ, 0) 1 = some (go s, σ, 1) := by
    simp [blkIter, blkOnce, hbs0, moveHead]
  have hfrom1 : ∀ k s₀, k ≤ s → k + s₀ < segs.length →
      blkIter bs (go k, σ, segStart segs s₀) (segStart segs (s₀ + k) - segStart segs s₀) =
        some (go 0, σ, segStart segs (s₀ + k)) ∧
      (∀ i ≤ segStart segs (s₀ + k) - segStart segs s₀, ∀ q' σ' j',
        blkIter bs (go k, σ, segStart segs s₀) i = some (q', σ', j') → j' < M_blk) ∧
      (∀ i < segStart segs (s₀ + k) - segStart segs s₀, ∀ q' σ' j' q'' sym' dir,
        blkIter bs (go k, σ, segStart segs s₀) i = some (q', σ', j') →
        bs q' (σ' j') = some (q'', sym', dir) →
        (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
    intro k
    induction k with
    | zero =>
      intro s₀ _ hs₀
      have hsb₀ := segStart_bound segs s₀ (by omega)
      simp only [Nat.add_zero, Nat.sub_self]
      refine ⟨rfl, ?_, fun i hi => by omega⟩
      intro i hi _ _ j' hi_eq
      obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
      cases hi_eq; omega
    | succ k ih =>
      intro s₀ hkS hs₀
      have hk_lt : k < s := by omega
      have hs₀_lt : s₀ < segs.length := by omega
      have hs1_lt : s₀ + 1 < segs.length := by omega
      have hsb₀ := segStart_bound segs s₀ hs₀_lt
      have hsucc := segStart_succ_eq segs hs1_lt
      let L₀ := (segs.getD s₀ []).length
      have hdat₀ : ∀ i < L₀, ∃ m b, σ (segStart segs s₀ + i) = blkData m b := by
        intro i hi
        have hbase : σ₀ (segStart segs s₀ + i) = blkData false ((segs.getD s₀ []).getD i false) :=
          (hws _ (by omega)).trans (encodeWorkspace_seg_data segs hs₀_lt hi)
        dsimp only [σ, reMark]
        rw [hbase]
        by_cases hS : S (segStart segs s₀ + i) = true
        · exact ⟨true, (segs.getD s₀ []).getD i false, by simp [hS, blkData]⟩
        · exact ⟨false, (segs.getD s₀ []).getD i false, by simp [hS, blkData]⟩
      rcases blkSkipData_aux bs M_blk (go (k + 1)) (h_data k hk_lt) L₀ (segStart segs s₀) σ hsb₀ hdat₀
        with ⟨hiter_d, hbnd_d, hdir_d⟩
      have hsep_at : σ (segStart segs s₀ + L₀) = blkSep := by
        apply reMark_sep_iff.mpr
        rw [hws _ hsb₀]
        simpa [L₀, hs1_lt] using encodeWorkspace_seg_end segs hs₀_lt
      have hbs_sep : bs (go (k + 1)) (σ (segStart segs s₀ + L₀)) =
          some (go k, σ (segStart segs s₀ + L₀), QCSD_HeadDir.right) := by
        rw [hsep_at]; exact h_sep k hk_lt
      have hsep_step : blkIter bs (go (k + 1), σ, segStart segs s₀ + L₀) 1 =
          some (go k, σ, segStart segs (s₀ + 1)) := by
        have hsucc' : segStart segs s₀ + L₀ + 1 = segStart segs (s₀ + 1) := by dsimp only [L₀]; omega
        simp [blkIter, blkOnce, hbs_sep, moveHead, hsucc']
      have hsk_eq : s₀ + (k + 1) = (s₀ + 1) + k := by omega
      rcases ih (s₀ + 1) (by omega) (by omega) with ⟨hiter_rest, hbnd_rest, hdir_rest⟩
      rw [← hsk_eq] at hiter_rest hbnd_rest hdir_rest
      have hsk_mono : segStart segs (s₀ + 1) ≤ segStart segs (s₀ + (k + 1)) :=
        segStart_mono segs (by omega) (by omega)
      have htot_len : segStart segs (s₀ + (k + 1)) - segStart segs s₀ =
          L₀ + 1 + (segStart segs (s₀ + (k + 1)) - segStart segs (s₀ + 1)) := by omega
      rw [htot_len]
      refine ⟨?_, ?_, ?_⟩
      · rw [blkIter_add, blkIter_add, hiter_d, Option.bind_some, hsep_step, Option.bind_some, hiter_rest]
      · intro i hi q' σ' j' hi_eq
        by_cases hi1 : i ≤ L₀
        · rcases blkIter_le_some hi1 hiter_d with ⟨⟨qi, σi, ji⟩, hsub⟩
          rw [hsub] at hi_eq; cases hi_eq
          exact hbnd_d i hi1 q' σ' j' hsub
        · have heq : i = L₀ + 1 + (i - (L₀ + 1)) := by omega
          rw [heq, blkIter_add, blkIter_add, hiter_d, Option.bind_some, hsep_step, Option.bind_some] at hi_eq
          exact hbnd_rest (i - (L₀ + 1)) (by omega) q' σ' j' hi_eq
      · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
        by_cases hi1 : i < L₀
        · exact hdir_d i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
        · by_cases hi2 : i = L₀
          · subst hi2; rw [hiter_d] at hi_eq; cases hi_eq; rw [hbs_sep] at hbs'; cases hbs'
            have hsb1 := segStart_bound segs (s₀ + 1) hs1_lt
            exact ⟨by simp, fun _ => by omega⟩
          · have heq : i = L₀ + 1 + (i - (L₀ + 1)) := by omega
            rw [heq, blkIter_add, blkIter_add, hiter_d, Option.bind_some, hsep_step, Option.bind_some] at hi_eq
            exact hdir_rest (i - (L₀ + 1)) (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
  rcases hfrom1 s 0 (Nat.le_refl s) (by omega) with ⟨hiter_r, hbnd_r, hdir_r⟩
  simp only [Nat.zero_add, segStart] at hiter_r hbnd_r hdir_r
  have hlen : segStart segs s = 1 + (segStart segs s - 1) := by omega
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [hlen]
    rw [blkIter_add, hstep0, Option.bind_some, hiter_r]
  · intro i hi q' σ' j' hi_eq
    cases i with
    | zero => cases hi_eq; omega
    | succ i' =>
      rw [Nat.add_comm i' 1, blkIter_add, hstep0, Option.bind_some] at hi_eq
      exact hbnd_r i' (by omega) q' σ' j' hi_eq
  · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
    cases i with
    | zero =>
      cases hi_eq; rw [hbs0] at hbs'; cases hbs'
      exact ⟨by simp, fun _ => by omega⟩
    | succ i' =>
      rw [Nat.add_comm i' 1, blkIter_add, hstep0, Option.bind_some] at hi_eq
      exact hdir_r i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

theorem blkIter_transform_reMark_scan (MaxSeg : ℕ) (stepBit : Bool → Bool × Bool)
    (S : ℕ → Bool) (start : ℕ) (hS_after : ∀ j, start ≤ j → S j = false) :
    ∀ i (rew : Bool) (σ : ℕ → BlkSym) j,
      (rew = false → start ≤ j) →
      blkIter (blkTransformSeg MaxSeg stepBit) ((0, rew), reMark S σ, j) i =
        (blkIter (blkTransformSeg MaxSeg stepBit) ((0, rew), σ, j) i).map
          (fun (q', σ', j') => (q', reMark S σ', j')) ∧
      (∀ q' σ' j', blkIter (blkTransformSeg MaxSeg stepBit) ((0, rew), σ, j) i = some (q', σ', j') →
        q'.1 = 0 ∧ (q'.2 = false → start ≤ j')) := by
  intro i
  induction i with
  | zero =>
    intro rew σ j hge
    refine ⟨rfl, ?_⟩
    intro q' σ' j' h0; cases h0; exact ⟨rfl, hge⟩
  | succ i ih =>
    intro rew σ j hge
    cases rew with
    | false =>
      have hj_ge : start ≤ j := hge rfl
      have hSj : S j = false := hS_after j hj_ge
      simp only [blkIter, blkOnce, reMark_of_false σ hSj]
      cases h : blkTransformSeg MaxSeg stepBit (0, false) (σ j) with
      | none => exact ⟨rfl, fun _ _ _ h0 => by simp at h0⟩
      | some val =>
        rcases val with ⟨⟨rem', rew'⟩, sym', dir⟩
        have hrem0 : rem' = 0 ∧ (rew' = false → dir = QCSD_HeadDir.right) := by
          unfold blkTransformSeg at h
          by_cases hh : σ j = blkHome
          · simp only [hh, ↓reduceIte, Bool.false_eq_true, Option.some.injEq, Prod.mk.injEq] at h
            exact ⟨h.1.1.symm, fun _ => h.2.2.symm⟩
          · simp only [hh, Bool.false_eq_true, ↓reduceIte, Fin.val_zero, Nat.lt_irrefl, ↓reduceDIte] at h
            by_cases hc0 : (σ j).1 = true
            · simp only [hc0, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              exact ⟨h.1.1.symm, fun hrf => absurd (h.1.2.trans hrf) (by decide)⟩
            · have hc0f : (σ j).1 = false := Bool.eq_false_iff.mpr hc0
              simp only [hc0f, Bool.not_false, ↓reduceIte] at h
              rcases hsb : stepBit (σ j).2.2 with ⟨b', stop⟩
              simp only [hsb] at h
              cases stop
              · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                exact ⟨h.1.1.symm, fun _ => h.2.2.symm⟩
              · simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                exact ⟨h.1.1.symm, fun hrf => absurd (h.1.2.trans hrf) (by decide)⟩
        rcases hrem0 with ⟨rfl, hdir_r⟩
        dsimp only
        rw [reMark_update_false σ hSj sym']
        exact ih rew' (Function.update σ j sym') (moveHead j dir) (fun hrf => by
          rw [hdir_r hrf, moveHead]; omega)
    | true =>
      simp only [blkIter, blkOnce]
      by_cases hhome : σ j = blkHome
      · have hh' : reMark S σ j = blkHome := reMark_home_iff.mpr hhome
        simp [blkTransformSeg, hhome, hh']
      · have hh' : reMark S σ j ≠ blkHome := fun h => hhome (reMark_home_iff.mp h)
        simp only [blkTransformSeg, ↓reduceIte, hhome, hh', Function.update_eq_self]
        exact ih true σ (moveHead j QCSD_HeadDir.left) (by simp)

theorem wsDecJz_marked_spec (MaxSeg B : ℕ) (segs : List (List Bool)) {arrSeg k s w v : ℕ}
    (harr_s : arrSeg < s) (hs : s < segs.length) (hs_max : s ≤ MaxSeg)
    (hseg : segs.getD s [] = natToBitsLE w v) (hv : v < 2 ^ w)
    {len : ℕ} {τ₁ : ℕ → Bool} (htw : TapeMarkedWS τ₁ len B segs arrSeg k) :
    ∃ q_out : WsDecJzQ MaxSeg, ∃ τ₂ : ℕ → Bool,
      wsDecJzWasZero q_out = decide (v = 0) ∧
      TapeMarkedWS τ₂ len B (if v = 0 then segs else segs.set s (natToBitsLE w (v - 1))) arrSeg k ∧
      (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (wsDecJz MaxSeg) B (wsDecJzEntry MaxSeg ⟨s, by omega⟩) len τ₁ 0
        q_out len τ₂ 0 (42 * (encodeWorkspace segs).length + 10) := by
  rcases htw with ⟨hsegs, hW_le, hlen_B, σ₀, hws₀, hread₁⟩
  have hlen_pos : 1 ≤ len := by
    have : 1 ≤ (encodeWorkspace segs).length := by simp [encodeWorkspace]
    omega
  let M_blk := (encodeWorkspace segs).length
  let S := segMarkPred segs arrSeg k
  -- Step 1: CheckZero commutes with reMark S
  rcases blkCheckZeroSeg_spec MaxSeg segs hs hs_max σ₀ hws₀
    with ⟨k_cz, hk_cz, hiter_cz₀, hnone_cz₀, hbnd_cz₀, hdir_cz₀⟩
  have hexec_cz : BlkExec (blkCheckZeroSeg MaxSeg) M_blk
      (⟨s, by omega⟩, false, true) (readBlk τ₁) 0
      (0, true, isAllFalse (segs.getD s [])) (readBlk τ₁) 0 (3 * M_blk) := by
    rw [hread₁]
    refine ⟨k_cz, hk_cz, ?_, ?_, ?_, ?_⟩
    · rw [blkIter_checkZero_reMark, hiter_cz₀]; rfl
    · rw [blkCheckZeroSeg_reMark, hnone_cz₀]; rfl
    · intro i hi q' σ' j' hi_eq
      rw [blkIter_checkZero_reMark] at hi_eq
      rcases hsub : blkIter (blkCheckZeroSeg MaxSeg) ((⟨s, by omega⟩, false, true), σ₀, 0) i with _ | ⟨qi, σi, ji⟩
      · rw [hsub] at hi_eq; simp at hi_eq
      · rw [hsub] at hi_eq; cases hi_eq; exact hbnd_cz₀ i hi q' σi j' hsub
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      rw [blkIter_checkZero_reMark] at hi_eq
      rcases hsub : blkIter (blkCheckZeroSeg MaxSeg) ((⟨s, by omega⟩, false, true), σ₀, 0) i with _ | ⟨qi, σi, ji⟩
      · rw [hsub] at hi_eq; simp at hi_eq
      · rw [hsub] at hi_eq; cases hi_eq
        rw [blkCheckZeroSeg_reMark] at hbs'
        rcases hsub2 : blkCheckZeroSeg MaxSeg q' (σi j') with _ | ⟨q2, s2, d2⟩
        · rw [hsub2] at hbs'; simp at hbs'
        · rw [hsub2] at hbs'; cases hbs'
          exact hdir_cz₀ i hi q' σi j' q'' s2 dir hsub hsub2
  rcases liftBlockStep_spec (blkCheckZeroSeg MaxSeg) B M_blk len τ₁
      (⟨s, by omega⟩, false, true) (0, true, isAllFalse (segs.getD s [])) (readBlk τ₁) 0 0
      (3 * M_blk) hW_le hlen_B hexec_cz
    with ⟨τ_mid, hread_mid, hout_mid, k₁, hk₁, hiter₁, hexit₁, hbnd₁⟩
  have he₁ := familyStep_spec (fun (_ : Fin (MaxSeg + 1)) => liftBlockStep (blkCheckZeroSeg MaxSeg))
    ⟨s, by omega⟩ ⟨k₁, hk₁, hiter₁, hexit₁, hbnd₁⟩
  have hz_eq : isAllFalse (segs.getD s []) = decide (v = 0) := by
    rw [hseg]
    by_cases hv0 : v = 0
    · subst hv0; simp only [decide_true]
      exact (isAllFalse_iff _).mpr ((all_false_natToBitsLE_iff hv).mpr rfl)
    · simp only [decide_eq_false hv0]
      apply Bool.eq_false_iff.mpr; intro htrue
      exact hv0 ((all_false_natToBitsLE_iff hv).mp ((isAllFalse_iff _).mp htrue))
  by_cases hv0 : v = 0
  · subst hv0
    have hz_t : isAllFalse (segs.getD s []) = true := by simpa using hz_eq
    have hf_eq : wsDecJzF MaxSeg (⟨s, by omega⟩, liftBlkExit (0, true, isAllFalse (segs.getD s []))) =
        Sum.inl true := by dsimp only [wsDecJzF, liftBlkExit]; rw [hz_t]; rfl
    have he₂_raw := sumStep_inl_spec (nopStep Bool)
      (liftBlockStep (blkTransformSeg MaxSeg stepBitDec))
      (nopStep_spec true len τ_mid 0 hlen_B (by omega))
    have hcomb := (seq0_spec (f := wsDecJzF MaxSeg) hlen_pos he₁ (by rw [hf_eq]; exact he₂_raw)).weaken
      (42 * M_blk + 10) (by omega)
    exact ⟨Sum.inr (Sum.inl true), τ_mid, rfl,
      ⟨hsegs, hW_le, hlen_B, σ₀, hws₀, hread_mid.trans hread₁⟩, hout_mid, hcomb⟩
  · have hz_f : isAllFalse (segs.getD s []) = false := by simpa [hv0] using hz_eq
    have hf_eq : wsDecJzF MaxSeg (⟨s, by omega⟩, liftBlkExit (0, true, isAllFalse (segs.getD s []))) =
        Sum.inr (liftBlkEntry (⟨s, by omega⟩, false)) := by
      dsimp only [wsDecJzF, liftBlkExit]; rw [hz_f]; rfl
    have hv_pos : 1 ≤ v := by omega
    -- Step 2: TransformSeg (dec) commutes with reMark S
    let go : ℕ → Fin (MaxSeg + 1) × Bool := fun r =>
      (⟨if h : r ≤ MaxSeg then r else 0, by split_ifs <;> omega⟩, false)
    have hgo_s : go s = (⟨s, by omega⟩, false) := by simp [go, hs_max]
    have hgo_0 : go 0 = (0, false) := by ext <;> simp [go]
    rcases blkGoToSeg_reMark_aux (blkTransformSeg MaxSeg stepBitDec) segs S σ₀ hws₀ go hs
        (by simp [go, hs_max, blkTransformSeg])
        (fun r hr m b => by
          have hr1 : r + 1 ≤ MaxSeg := by omega
          simp [go, hr1, blkTransformSeg, blkHome, blkData, blkSep])
        (fun r hr => by
          have hr1 : r + 1 ≤ MaxSeg := by omega
          have hr0 : r ≤ MaxSeg := by omega
          have hpos : 0 < (if h : r + 1 ≤ MaxSeg then r + 1 else 0) := by simp [hr1]
          simp only [go, blkTransformSeg, Bool.false_eq_true, ↓reduceIte,
            show blkSep ≠ blkHome by decide, dite_true, hpos]
          congr 1; ext <;> simp [hr1, hr0])
      with ⟨hiter_go, hbnd_go, hdir_go⟩
    rw [hgo_s, hgo_0] at hiter_go
    rw [hgo_s] at hbnd_go hdir_go
    have hset_self : segs.set s ([] ++ segs.getD s []) = segs := by
      apply List.ext_getElem (by simp)
      intro idx hk1 hk2
      rw [List.getElem_set]
      split_ifs with hsk
      · subst hsk; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2]
      · rfl
    have hws0_unm : MatchesWS σ₀ (segs.set s ([] ++ segs.getD s [])) := by rwa [hset_self]
    rcases blkTransformSeg_scan_aux MaxSeg stepBitDec segs hs (segs.getD s []) [] σ₀ (by simp) hws0_unm
      with ⟨σ_end₀, hws_end₀, k_sc, hk_sc, hiter_sc₀, hnone_sc₀, hbnd_sc₀, hdir_sc₀⟩
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at hws_end₀ hiter_sc₀ hbnd_sc₀ hdir_sc₀
    rw [hseg, applyTransform_dec, decBits_natToBitsLE hv_pos hv] at hws_end₀
    have hS_after : ∀ j, segStart segs s ≤ j → S j = false := by
      intro j hj
      have harr1 : arrSeg + 1 ≤ s := harr_s
      have hmono := segStart_mono segs harr1 hs
      have hsucc_arr := segStart_succ_eq segs (show arrSeg + 1 < segs.length by omega)
      simp only [S, segMarkPred, segMarkRange, decide_eq_false_iff_not]
      omega
    have hscan_map := blkIter_transform_reMark_scan MaxSeg stepBitDec S (segStart segs s) hS_after
    have hsb := segStart_bound segs s hs
    have hexec_dec : BlkExec (blkTransformSeg MaxSeg stepBitDec) M_blk
        (⟨s, by omega⟩, false) (readBlk τ_mid) 0 (0, true) (reMark S σ_end₀) 0 (3 * M_blk) := by
      rw [hread_mid, hread₁]
      refine ⟨segStart segs s + k_sc, by omega, ?_, ?_, ?_, ?_⟩
      · rw [blkIter_add, hiter_go, Option.bind_some,
            (hscan_map k_sc false σ₀ (segStart segs s) (fun _ => Nat.le_refl _)).1, hiter_sc₀]
        rfl
      · have h0_end : σ_end₀ 0 = blkHome := (hws_end₀ 0 (by
          rw [length_encodeWorkspace_set hs (by rw [hseg, length_natToBitsLE, length_natToBitsLE])]
          have : 1 ≤ M_blk := by simp [M_blk, encodeWorkspace]
          omega)).trans (encodeWorkspace_getD_zero _)
        simp [blkTransformSeg, reMark_home_iff.mpr h0_end]
      · intro i hi q' σ' j' hi_eq
        by_cases hi1 : i ≤ segStart segs s
        · rcases blkIter_le_some hi1 hiter_go with ⟨⟨qi, σi, ji⟩, hsub⟩
          rw [hsub] at hi_eq; cases hi_eq; exact hbnd_go i hi1 q' σ' j' hsub
        · have heq : i = segStart segs s + (i - segStart segs s) := by omega
          rw [heq, blkIter_add, hiter_go, Option.bind_some,
              (hscan_map _ false σ₀ (segStart segs s) (fun _ => Nat.le_refl _)).1] at hi_eq
          rcases hsub : blkIter (blkTransformSeg MaxSeg stepBitDec) ((0, false), σ₀, segStart segs s)
              (i - segStart segs s) with _ | ⟨qi, σi, ji⟩
          · rw [hsub] at hi_eq; simp at hi_eq
          · rw [hsub] at hi_eq; cases hi_eq
            exact hbnd_sc₀ (i - segStart segs s) (by omega) q' σi j' hsub
      · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
        by_cases hi1 : i < segStart segs s
        · exact hdir_go i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
        · have heq : i = segStart segs s + (i - segStart segs s) := by omega
          rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
          rcases hscan_map (i - segStart segs s) false σ₀ (segStart segs s) (fun _ => Nat.le_refl _)
            with ⟨hsub_map, hsub_inv⟩
          rw [hsub_map] at hi_eq
          rcases hsub : blkIter (blkTransformSeg MaxSeg stepBitDec) ((0, false), σ₀, segStart segs s)
              (i - segStart segs s) with _ | ⟨⟨rem_i, rew_i⟩, σi, ji⟩
          · rw [hsub] at hi_eq; simp at hi_eq
          · rw [hsub] at hi_eq; cases hi_eq
            rcases hsub_inv (rem_i, rew_i) σi j' hsub with ⟨_, hge_j'⟩
            cases rew_i with
            | false =>
              have hSj' : S j' = false := hS_after j' (hge_j' rfl)
              rw [reMark_of_false σi hSj'] at hbs'
              exact hdir_sc₀ (i - segStart segs s) (by omega) (rem_i, false) σi j' q'' sym' dir hsub hbs'
            | true =>
              by_cases hhome : σi j' = blkHome
              · simp [blkTransformSeg, reMark_home_iff.mpr hhome] at hbs'
              · have hh' : reMark S σi j' ≠ blkHome := fun h => hhome (reMark_home_iff.mp h)
                simp only [blkTransformSeg, ↓reduceIte, hh', Option.some.injEq, Prod.mk.injEq] at hbs'
                have hbs0 : blkTransformSeg MaxSeg stepBitDec (rem_i, true) (σi j') =
                    some ((rem_i, true), σi j', QCSD_HeadDir.left) := by simp [blkTransformSeg, hhome]
                rw [← hbs'.2.2]
                exact hdir_sc₀ (i - segStart segs s) (by omega) (rem_i, true) σi j' _ _ _ hsub hbs0
    rcases liftBlockStep_spec (blkTransformSeg MaxSeg stepBitDec) B M_blk len τ_mid
        (⟨s, by omega⟩, false) (0, true) (reMark S σ_end₀) 0 0
        (3 * M_blk) hW_le hlen_B hexec_dec
      with ⟨τ₂, hread₂, hout₂, k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
    have he₂_raw := sumStep_inr_spec (nopStep Bool)
      (liftBlockStep (blkTransformSeg MaxSeg stepBitDec))
      ⟨k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
    rw [← hf_eq] at he₂_raw
    have hcomb := (seq0_spec hlen_pos he₁ he₂_raw).weaken (42 * M_blk + 10) (by omega)
    let segs' := segs.set s (natToBitsLE w (v - 1))
    have hlen_s' : (natToBitsLE w (v - 1)).length = (segs.getD s []).length := by
      rw [hseg, length_natToBitsLE, length_natToBitsLE]
    have hM' : (encodeWorkspace segs').length = M_blk := length_encodeWorkspace_set hs hlen_s'
    have hS_eq : segMarkPred segs' arrSeg k = S := by
      funext j
      simp only [S, segs', segMarkPred, segMarkRange,
        segStart_set_eq segs s arrSeg _ hs hlen_s',
        getD_set_ne_seg segs (by omega : s ≠ arrSeg)]
    have hne_set : segs' ≠ [] := by simp [segs', hsegs]
    have htm₂ : TapeMarkedWS τ₂ len B (if v = 0 then segs else segs') arrSeg k := by
      simp only [hv0, ↓reduceIte]
      exact ⟨hne_set, by rw [hM']; exact hW_le, hlen_B, σ_end₀, hws_end₀, by rw [hread₂, hS_eq]⟩
    exact ⟨Sum.inr (Sum.inr (liftBlkExit (0, true))), τ₂, by simp [wsDecJzWasZero, hv0],
      htm₂, fun p hp => (hout₂ p hp).trans (hout_mid p hp), hcomb⟩

def blkMarkNext (MaxSeg : ℕ) : BlkStepFn (Fin (MaxSeg + 1) × Bool) :=
  fun (rem, rewinding) sym =>
    if rewinding then
      if sym = blkHome then none
      else some ((rem, true), sym, QCSD_HeadDir.left)
    else if sym = blkHome then
      some ((rem, false), blkHome, QCSD_HeadDir.right)
    else if hrem : 0 < rem.val then
      let prev : Fin (MaxSeg + 1) := ⟨rem.val - 1, by omega⟩
      if sym = blkSep then some ((prev, false), blkSep, QCSD_HeadDir.right)
      else some ((rem, false), sym, QCSD_HeadDir.right)
    else
      if !sym.1 then
        if sym.2.1 then some ((0, false), sym, QCSD_HeadDir.right)
        else some ((0, true), blkData true sym.2.2, QCSD_HeadDir.left)
      else
        some ((0, true), sym, QCSD_HeadDir.left)

theorem blkMarkNext_spec (MaxSeg : ℕ) (segs : List (List Bool)) {arrSeg k : ℕ}
    (harr : arrSeg < segs.length) (harr_m : arrSeg ≤ MaxSeg)
    (σ₀ : ℕ → BlkSym) (hws₀ : MatchesWS σ₀ segs) :
    let M_blk := (encodeWorkspace segs).length
    let σ_in := reMark (segMarkPred segs arrSeg k) σ₀
    let σ_out := reMark (segMarkPred segs arrSeg (k + 1)) σ₀
    BlkExec (blkMarkNext MaxSeg) M_blk (⟨arrSeg, by omega⟩, false) σ_in 0 (0, true) σ_out 0 (3 * M_blk) := by
  intro M_blk σ_in σ_out
  let go : ℕ → Fin (MaxSeg + 1) × Bool := fun r =>
    (⟨if h : r ≤ MaxSeg then r else 0, by split_ifs <;> omega⟩, false)
  have hgo_a : go arrSeg = (⟨arrSeg, by omega⟩, false) := by simp [go, harr_m]
  have hgo_0 : go 0 = (0, false) := by ext <;> simp [go]
  rcases blkGoToSeg_reMark_aux (blkMarkNext MaxSeg) segs (segMarkPred segs arrSeg k) σ₀ hws₀ go harr
      (by simp [go, harr_m, blkMarkNext])
      (fun r hr m b => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        simp [go, hr1, blkMarkNext, blkHome, blkData, blkSep])
      (fun r hr => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        have hr0 : r ≤ MaxSeg := by omega
        have hpos : 0 < (if h : r + 1 ≤ MaxSeg then r + 1 else 0) := by simp [hr1]
        simp only [go, blkMarkNext, Bool.false_eq_true, ↓reduceIte,
          show blkSep ≠ blkHome by decide, dite_true, hpos]
        congr 1; ext <;> simp [hr1, hr0])
    with ⟨hiter_go, hbnd_go, hdir_go⟩
  rw [hgo_a, hgo_0] at hiter_go
  rw [hgo_a] at hbnd_go hdir_go
  let L := (segs.getD arrSeg []).length
  let m := min k L
  have hsb := segStart_bound segs arrSeg harr
  have hs1 := segStart_pos segs arrSeg
  -- Skip `m` already-marked blocks from `segStart segs arrSeg` to `segStart segs arrSeg + m`
  have hskip_m : blkIter (blkMarkNext MaxSeg) ((0, false), σ_in, segStart segs arrSeg) m =
      some ((0, false), σ_in, segStart segs arrSeg + m) ∧
    (∀ i ≤ m, ∀ q' σ' j',
      blkIter (blkMarkNext MaxSeg) ((0, false), σ_in, segStart segs arrSeg) i = some (q', σ', j') → j' < M_blk) ∧
    (∀ i < m, ∀ q' σ' j' q'' sym' dir,
      blkIter (blkMarkNext MaxSeg) ((0, false), σ_in, segStart segs arrSeg) i = some (q', σ', j') →
      blkMarkNext MaxSeg q' (σ' j') = some (q'', sym', dir) →
      (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
    have haux : ∀ rem off, off + rem = m →
        blkIter (blkMarkNext MaxSeg) ((0, false), σ_in, segStart segs arrSeg + off) rem =
          some ((0, false), σ_in, segStart segs arrSeg + m) ∧
        (∀ i ≤ rem, ∀ q' σ' j',
          blkIter (blkMarkNext MaxSeg) ((0, false), σ_in, segStart segs arrSeg + off) i = some (q', σ', j') → j' < M_blk) ∧
        (∀ i < rem, ∀ q' σ' j' q'' sym' dir,
          blkIter (blkMarkNext MaxSeg) ((0, false), σ_in, segStart segs arrSeg + off) i = some (q', σ', j') →
          blkMarkNext MaxSeg q' (σ' j') = some (q'', sym', dir) →
          (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
      intro rem
      induction rem with
      | zero =>
        intro off hoff
        have : off = m := by omega
        subst this
        refine ⟨rfl, ?_, fun i hi => by omega⟩
        intro i hi _ _ j' hi_eq
        obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
        cases hi_eq; omega
      | succ rem ih =>
        intro off hoff
        have hoff_m : off < m := by omega
        have hoff_L : off < L := by omega
        have hbase : σ₀ (segStart segs arrSeg + off) = blkData false ((segs.getD arrSeg []).getD off false) :=
          (hws₀ _ (by omega)).trans (encodeWorkspace_seg_data segs harr hoff_L)
        have hS_t : segMarkPred segs arrSeg k (segStart segs arrSeg + off) = true := by
          simp only [segMarkPred, segMarkRange, decide_eq_true_eq]; omega
        have hsym : σ_in (segStart segs arrSeg + off) = blkData true ((segs.getD arrSeg []).getD off false) := by
          dsimp only [σ_in, reMark]; rw [hbase, hS_t]; rfl
        have hbs : blkMarkNext MaxSeg (0, false) (σ_in (segStart segs arrSeg + off)) =
            some ((0, false), σ_in (segStart segs arrSeg + off), QCSD_HeadDir.right) := by
          rw [hsym]; simp [blkMarkNext, blkHome, blkData]
        rcases ih (off + 1) (by omega) with ⟨hit, hbd, hdr⟩
        have hadd : segStart segs arrSeg + off + 1 = segStart segs arrSeg + (off + 1) := by omega
        refine ⟨?_, ?_, ?_⟩
        · simp [blkIter, blkOnce, hbs, moveHead, hadd, hit]
        · intro i hi q' σ' j' hi_eq
          cases i with
          | zero => cases hi_eq; omega
          | succ i' =>
            simp only [blkIter, blkOnce, hbs, moveHead, Function.update_eq_self, hadd] at hi_eq
            exact hbd i' (by omega) q' σ' j' hi_eq
        · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
          cases i with
          | zero => cases hi_eq; rw [hbs] at hbs'; cases hbs'; exact ⟨by simp, fun _ => by omega⟩
          | succ i' =>
            simp only [blkIter, blkOnce, hbs, moveHead, Function.update_eq_self, hadd] at hi_eq
            exact hdr i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
    simpa using haux m 0 (by omega)
  rcases hskip_m with ⟨hiter_sk, hbnd_sk, hdir_sk⟩
  -- At `segStart segs arrSeg + m`: either `k < L` (mark block `k`) or `L ≤ k` (at separator/wall)
  have hturn : blkIter (blkMarkNext MaxSeg) ((0, false), σ_in, segStart segs arrSeg + m) 1 =
      some ((0, true), σ_out, segStart segs arrSeg + m - 1) ∧
    (∀ q'' sym' dir, blkMarkNext MaxSeg (0, false) (σ_in (segStart segs arrSeg + m)) = some (q'', sym', dir) →
      (dir = QCSD_HeadDir.left → 1 ≤ segStart segs arrSeg + m) ∧
      (dir = QCSD_HeadDir.right → segStart segs arrSeg + m + 1 < M_blk)) := by
    by_cases hkL : k < L
    · have hm_eq : m = k := Nat.min_eq_left (Nat.le_of_lt hkL)
      have hm1_eq : min (k + 1) L = k + 1 := Nat.min_eq_left hkL
      have hbase : σ₀ (segStart segs arrSeg + m) = blkData false ((segs.getD arrSeg []).getD m false) :=
        (hws₀ _ (by omega)).trans (encodeWorkspace_seg_data segs harr (by omega))
      have hS_f : segMarkPred segs arrSeg k (segStart segs arrSeg + m) = false := by
        simp only [segMarkPred, segMarkRange, decide_eq_false_iff_not]; omega
      have hsym : σ_in (segStart segs arrSeg + m) = blkData false ((segs.getD arrSeg []).getD m false) := by
        dsimp only [σ_in]; rw [reMark_of_false _ hS_f, hbase]
      have hbs : blkMarkNext MaxSeg (0, false) (σ_in (segStart segs arrSeg + m)) =
          some ((0, true), blkData true ((segs.getD arrSeg []).getD m false), QCSD_HeadDir.left) := by
        rw [hsym]; simp [blkMarkNext, blkHome, blkData]
      have hupd : Function.update σ_in (segStart segs arrSeg + m)
          (blkData true ((segs.getD arrSeg []).getD m false)) = σ_out := by
        funext j
        by_cases hj : j = segStart segs arrSeg + m
        · subst hj
          have hS_t : segMarkPred segs arrSeg (k + 1) (segStart segs arrSeg + m) = true := by
            simp only [segMarkPred, segMarkRange, decide_eq_true_eq]; omega
          simp [σ_out, reMark, hbase, hS_t, blkData]
        · rw [Function.update_of_ne hj]
          have hpred_eq : segMarkPred segs arrSeg k j = segMarkPred segs arrSeg (k + 1) j := by
            have hj' : j ≠ segStart segs arrSeg + k := by dsimp only [m, L] at hj hm_eq; omega
            have hmin1 : min k (segs.getD arrSeg []).length = k := hm_eq
            have hmin2 : min (k + 1) (segs.getD arrSeg []).length = k + 1 := hm1_eq
            simp only [segMarkPred, segMarkRange, hmin1, hmin2, Nat.add_zero]
            by_cases h1 : segStart segs arrSeg ≤ j ∧ j < segStart segs arrSeg + k
            · have h2 : segStart segs arrSeg ≤ j ∧ j < segStart segs arrSeg + (k + 1) := by omega
              simp [h1, h2]
            · have h2 : ¬(segStart segs arrSeg ≤ j ∧ j < segStart segs arrSeg + (k + 1)) := by omega
              simp [h1, h2]
          simp [σ_in, σ_out, reMark, hpred_eq]
      refine ⟨by simp only [blkIter, blkOnce, hbs, moveHead]; rw [hupd], ?_⟩
      intro q'' sym' dir hbs'; rw [hbs] at hbs'; cases hbs'
      exact ⟨fun _ => by omega, by simp⟩
    · have hm_eq : m = L := Nat.min_eq_right (by omega)
      have hm1_eq : min (k + 1) (segs.getD arrSeg []).length = L := Nat.min_eq_right (by omega)
      have hend : σ₀ (segStart segs arrSeg + m) = (if arrSeg + 1 < segs.length then blkSep else blkWall) := by
        rw [hm_eq, hws₀ _ hsb]; exact encodeWorkspace_seg_end segs harr
      have hfst : (σ_in (segStart segs arrSeg + m)).1 = true := by
        rw [reMark_fst, hend]; split_ifs <;> rfl
      have hnhome : σ_in (segStart segs arrSeg + m) ≠ blkHome := by
        intro hh
        have hh0 := reMark_home_iff.mp hh
        rw [hend] at hh0; split_ifs at hh0 <;> simp [blkSep, blkWall, blkHome] at hh0
      have hbs : blkMarkNext MaxSeg (0, false) (σ_in (segStart segs arrSeg + m)) =
          some ((0, true), σ_in (segStart segs arrSeg + m), QCSD_HeadDir.left) := by
        simp [blkMarkNext, hnhome, hfst]
      have hout_eq : σ_in = σ_out := by
        have hmin1 : min k (segs.getD arrSeg []).length = (segs.getD arrSeg []).length := hm_eq
        have hmin2 : min (k + 1) (segs.getD arrSeg []).length = (segs.getD arrSeg []).length := hm1_eq
        funext j
        dsimp only [σ_in, σ_out]
        unfold segMarkPred
        rw [hmin1, hmin2]
      refine ⟨by simp only [blkIter, blkOnce, hbs, moveHead]; rw [Function.update_eq_self, hout_eq], ?_⟩
      intro q'' sym' dir hbs'; rw [hbs] at hbs'; cases hbs'
      exact ⟨fun _ => by omega, by simp⟩
  rcases hturn with ⟨hiter_t, hdir_t⟩
  let j_rw := segStart segs arrSeg + m - 1
  have h0_out : σ_out 0 = blkHome :=
    reMark_home_iff.mpr ((hws₀ 0 (by omega)).trans (encodeWorkspace_getD_zero segs))
  have hne_out : ∀ i, 1 ≤ i → i ≤ j_rw → σ_out i ≠ blkHome := by
    intro i hi1 hi2 hh
    exact encodeWorkspace_ne_home segs hi1 (by omega) ((hws₀ i (by omega)).symm.trans (reMark_home_iff.mp hh))
  rcases blkRewind_aux (blkMarkNext MaxSeg) M_blk (0, true)
      (by simp [blkMarkNext]) (fun sym hne => by simp [blkMarkNext, hne])
      j_rw σ_out (by omega) h0_out hne_out
    with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
  refine ⟨segStart segs arrSeg + m + 1 + j_rw, by omega, ?_, hnone_rw, ?_, ?_⟩
  · rw [blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
        hiter_sk, Option.bind_some, hiter_t, Option.bind_some, hiter_rw]
  · intro i hi q' σ' j' hi_eq
    by_cases hi1 : i ≤ segStart segs arrSeg
    · rcases blkIter_le_some hi1 hiter_go with ⟨⟨qi, σi, ji⟩, hsub⟩
      rw [hsub] at hi_eq; cases hi_eq; exact hbnd_go i hi1 q' σ' j' hsub
    · by_cases hi2 : i ≤ segStart segs arrSeg + m
      · have heq : i = segStart segs arrSeg + (i - segStart segs arrSeg) := by omega
        rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
        exact hbnd_sk (i - segStart segs arrSeg) (by omega) q' σ' j' hi_eq
      · have heq : i = segStart segs arrSeg + m + 1 + (i - (segStart segs arrSeg + m + 1)) := by omega
        rw [heq, blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
            hiter_sk, Option.bind_some, hiter_t, Option.bind_some] at hi_eq
        exact hbnd_rw (i - (segStart segs arrSeg + m + 1)) (by omega) q' σ' j' hi_eq
  · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
    by_cases hi1 : i < segStart segs arrSeg
    · exact hdir_go i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
    · by_cases hi2 : i < segStart segs arrSeg + m
      · have heq : i = segStart segs arrSeg + (i - segStart segs arrSeg) := by omega
        rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
        exact hdir_sk (i - segStart segs arrSeg) (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
      · by_cases hi3 : i = segStart segs arrSeg + m
        · subst hi3
          rw [blkIter_add, hiter_go, Option.bind_some, hiter_sk] at hi_eq
          cases hi_eq; exact hdir_t q'' sym' dir hbs'
        · have heq : i = segStart segs arrSeg + m + 1 + (i - (segStart segs arrSeg + m + 1)) := by omega
          rw [heq, blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
              hiter_sk, Option.bind_some, hiter_t, Option.bind_some] at hi_eq
          exact hdir_rw (i - (segStart segs arrSeg + m + 1)) (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

def blkReadAndClear (MaxSeg : ℕ) : BlkStepFn (Fin (MaxSeg + 1) × Bool × Bool) :=
  fun (rem, rewinding, res) sym =>
    if rewinding then
      if sym = blkHome then none
      else some ((rem, true, res), sym, QCSD_HeadDir.left)
    else if sym = blkHome then
      some ((rem, false, res), blkHome, QCSD_HeadDir.right)
    else if hrem : 0 < rem.val then
      let prev : Fin (MaxSeg + 1) := ⟨rem.val - 1, by omega⟩
      if sym = blkSep then some ((prev, false, res), blkSep, QCSD_HeadDir.right)
      else some ((rem, false, res), sym, QCSD_HeadDir.right)
    else
      if !sym.1 then
        if sym.2.1 then some ((0, false, res), blkData false sym.2.2, QCSD_HeadDir.right)
        else some ((0, true, sym.2.2), sym, QCSD_HeadDir.left)
      else
        some ((0, true, false), sym, QCSD_HeadDir.left)

theorem blkReadAndClear_spec (MaxSeg : ℕ) (segs : List (List Bool)) {arrSeg v : ℕ}
    (harr : arrSeg < segs.length) (harr_m : arrSeg ≤ MaxSeg)
    (σ₀ : ℕ → BlkSym) (hws₀ : MatchesWS σ₀ segs) :
    let M_blk := (encodeWorkspace segs).length
    let σ_in := reMark (segMarkPred segs arrSeg v) σ₀
    let res := (segs.getD arrSeg []).getD v false
    BlkExec (blkReadAndClear MaxSeg) M_blk (⟨arrSeg, by omega⟩, false, false) σ_in 0
      (0, true, res) σ₀ 0 (3 * M_blk) := by
  intro M_blk σ_in res
  let go : ℕ → Fin (MaxSeg + 1) × Bool × Bool := fun r =>
    (⟨if h : r ≤ MaxSeg then r else 0, by split_ifs <;> omega⟩, false, false)
  have hgo_a : go arrSeg = (⟨arrSeg, by omega⟩, false, false) := by simp [go, harr_m]
  have hgo_0 : go 0 = (0, false, false) := by ext <;> simp [go]
  rcases blkGoToSeg_reMark_aux (blkReadAndClear MaxSeg) segs (segMarkPred segs arrSeg v) σ₀ hws₀ go harr
      (by simp [go, harr_m, blkReadAndClear])
      (fun r hr m b => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        simp [go, hr1, blkReadAndClear, blkHome, blkData, blkSep])
      (fun r hr => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        have hr0 : r ≤ MaxSeg := by omega
        have hpos : 0 < (if h : r + 1 ≤ MaxSeg then r + 1 else 0) := by simp [hr1]
        simp only [go, blkReadAndClear, Bool.false_eq_true, ↓reduceIte,
          show blkSep ≠ blkHome by decide, dite_true, hpos]
        congr 1; ext <;> simp [hr1, hr0])
    with ⟨hiter_go, hbnd_go, hdir_go⟩
  rw [hgo_a, hgo_0] at hiter_go
  rw [hgo_a] at hbnd_go hdir_go
  let L := (segs.getD arrSeg []).length
  let m := min v L
  have hsb := segStart_bound segs arrSeg harr
  have hs1 := segStart_pos segs arrSeg
  -- Clear `m` marked blocks from `segStart segs arrSeg` to `segStart segs arrSeg + m`
  have hclr_m : blkIter (blkReadAndClear MaxSeg) ((0, false, false), σ_in, segStart segs arrSeg) m =
      some ((0, false, false), σ₀, segStart segs arrSeg + m) ∧
    (∀ i ≤ m, ∀ q' σ' j',
      blkIter (blkReadAndClear MaxSeg) ((0, false, false), σ_in, segStart segs arrSeg) i = some (q', σ', j') → j' < M_blk) ∧
    (∀ i < m, ∀ q' σ' j' q'' sym' dir,
      blkIter (blkReadAndClear MaxSeg) ((0, false, false), σ_in, segStart segs arrSeg) i = some (q', σ', j') →
      blkReadAndClear MaxSeg q' (σ' j') = some (q'', sym', dir) →
      (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
    have haux : ∀ rem off, off + rem = m →
        let σ_cur := reMark (segMarkRange segs arrSeg off m) σ₀
        blkIter (blkReadAndClear MaxSeg) ((0, false, false), σ_cur, segStart segs arrSeg + off) rem =
          some ((0, false, false), σ₀, segStart segs arrSeg + m) ∧
        (∀ i ≤ rem, ∀ q' σ' j',
          blkIter (blkReadAndClear MaxSeg) ((0, false, false), σ_cur, segStart segs arrSeg + off) i = some (q', σ', j') → j' < M_blk) ∧
        (∀ i < rem, ∀ q' σ' j' q'' sym' dir,
          blkIter (blkReadAndClear MaxSeg) ((0, false, false), σ_cur, segStart segs arrSeg + off) i = some (q', σ', j') →
          blkReadAndClear MaxSeg q' (σ' j') = some (q'', sym', dir) →
          (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
      intro rem
      induction rem with
      | zero =>
        intro off hoff
        have hoff_eq : off = m := by omega
        subst hoff_eq
        have hcur : reMark (segMarkRange segs arrSeg m m) σ₀ = σ₀ := by
          funext j
          have hfalse : segMarkRange segs arrSeg m m j = false := by
            simp [segMarkRange]
          exact reMark_of_false σ₀ hfalse
        dsimp only
        rw [hcur]
        refine ⟨rfl, ?_, fun i hi => by omega⟩
        intro i hi _ _ j' hi_eq
        obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
        cases hi_eq; omega
      | succ rem ih =>
        intro off hoff
        have hoff_m : off < m := by omega
        have hoff_L : off < L := by omega
        have hbase : σ₀ (segStart segs arrSeg + off) = blkData false ((segs.getD arrSeg []).getD off false) :=
          (hws₀ _ (by omega)).trans (encodeWorkspace_seg_data segs harr hoff_L)
        have hS_t : segMarkRange segs arrSeg off m (segStart segs arrSeg + off) = true := by
          simp only [segMarkRange, decide_eq_true_eq]; omega
        have hsym : reMark (segMarkRange segs arrSeg off m) σ₀ (segStart segs arrSeg + off) =
            blkData true ((segs.getD arrSeg []).getD off false) := by
          simp only [reMark, hbase, hS_t, blkData, Bool.not_false, Bool.and_self, ↓reduceIte]
        have hbs : blkReadAndClear MaxSeg (0, false, false)
            (reMark (segMarkRange segs arrSeg off m) σ₀ (segStart segs arrSeg + off)) =
            some ((0, false, false), blkData false ((segs.getD arrSeg []).getD off false), QCSD_HeadDir.right) := by
          rw [hsym]; simp [blkReadAndClear, blkHome, blkData]
        have hupd : Function.update (reMark (segMarkRange segs arrSeg off m) σ₀) (segStart segs arrSeg + off)
            (blkData false ((segs.getD arrSeg []).getD off false)) =
            reMark (segMarkRange segs arrSeg (off + 1) m) σ₀ := by
          funext j
          by_cases hj : j = segStart segs arrSeg + off
          · subst hj
            have hS_f : segMarkRange segs arrSeg (off + 1) m (segStart segs arrSeg + off) = false := by
              simp only [segMarkRange, decide_eq_false_iff_not]; omega
            simp [reMark_of_false _ hS_f, hbase]
          · rw [Function.update_of_ne hj]
            have hpred_eq : segMarkRange segs arrSeg off m j = segMarkRange segs arrSeg (off + 1) m j := by
              simp only [segMarkRange]
              by_cases h1 : segStart segs arrSeg + off ≤ j ∧ j < segStart segs arrSeg + m
              · have h2 : segStart segs arrSeg + (off + 1) ≤ j ∧ j < segStart segs arrSeg + m := by omega
                simp [h1, h2]
              · have h2 : ¬(segStart segs arrSeg + (off + 1) ≤ j ∧ j < segStart segs arrSeg + m) := by omega
                simp [h1, h2]
            simp [reMark, hpred_eq]
        rcases ih (off + 1) (by omega) with ⟨hit, hbd, hdr⟩
        have hadd : segStart segs arrSeg + off + 1 = segStart segs arrSeg + (off + 1) := by omega
        refine ⟨?_, ?_, ?_⟩
        · simp only [blkIter, blkOnce, hbs, moveHead, hadd, hupd]
          exact hit
        · intro i hi q' σ' j' hi_eq
          cases i with
          | zero => cases hi_eq; omega
          | succ i' =>
            simp only [blkIter, blkOnce, hbs, moveHead, hupd, hadd] at hi_eq
            exact hbd i' (by omega) q' σ' j' hi_eq
        · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
          cases i with
          | zero => cases hi_eq; rw [hbs] at hbs'; cases hbs'; exact ⟨by simp, fun _ => by omega⟩
          | succ i' =>
            simp only [blkIter, blkOnce, hbs, moveHead, hupd, hadd] at hi_eq
            exact hdr i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
    rcases haux m 0 (by omega) with ⟨ha1, ha2, ha3⟩
    dsimp only [σ_in, segMarkPred, m, L] at ha1 ha2 ha3 ⊢
    simp only [Nat.add_zero] at ha1 ha2 ha3
    exact ⟨ha1, ha2, ha3⟩
  rcases hclr_m with ⟨hiter_cl, hbnd_cl, hdir_cl⟩
  -- Read target bit at `segStart segs arrSeg + m` on `σ₀`
  have hturn : blkIter (blkReadAndClear MaxSeg) ((0, false, false), σ₀, segStart segs arrSeg + m) 1 =
      some ((0, true, res), σ₀, segStart segs arrSeg + m - 1) ∧
    (∀ q'' sym' dir, blkReadAndClear MaxSeg (0, false, false) (σ₀ (segStart segs arrSeg + m)) = some (q'', sym', dir) →
      (dir = QCSD_HeadDir.left → 1 ≤ segStart segs arrSeg + m) ∧
      (dir = QCSD_HeadDir.right → segStart segs arrSeg + m + 1 < M_blk)) := by
    by_cases hvL : v < L
    · have hm_eq : m = v := Nat.min_eq_left (Nat.le_of_lt hvL)
      have hbase : σ₀ (segStart segs arrSeg + m) = blkData false res := by
        rw [hm_eq]; exact (hws₀ _ (by omega)).trans (encodeWorkspace_seg_data segs harr hvL)
      have hbs : blkReadAndClear MaxSeg (0, false, false) (σ₀ (segStart segs arrSeg + m)) =
          some ((0, true, res), σ₀ (segStart segs arrSeg + m), QCSD_HeadDir.left) := by
        rw [hbase]; simp [blkReadAndClear, blkHome, blkData]
      refine ⟨by simp [blkIter, blkOnce, hbs, moveHead], ?_⟩
      intro q'' sym' dir hbs'; rw [hbs] at hbs'; cases hbs'
      exact ⟨fun _ => by omega, by simp⟩
    · have hm_eq : m = L := Nat.min_eq_right (by omega)
      have hres_f : res = false := by
        dsimp only [res]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      have hend : σ₀ (segStart segs arrSeg + m) = (if arrSeg + 1 < segs.length then blkSep else blkWall) := by
        rw [hm_eq, hws₀ _ hsb]; exact encodeWorkspace_seg_end segs harr
      have hbs : blkReadAndClear MaxSeg (0, false, false) (σ₀ (segStart segs arrSeg + m)) =
          some ((0, true, res), σ₀ (segStart segs arrSeg + m), QCSD_HeadDir.left) := by
        rw [hend, hres_f]; split_ifs <;> simp [blkReadAndClear, blkSep, blkWall, blkHome]
      refine ⟨by simp [blkIter, blkOnce, hbs, moveHead], ?_⟩
      intro q'' sym' dir hbs'; rw [hbs] at hbs'; cases hbs'
      exact ⟨fun _ => by omega, by simp⟩
  rcases hturn with ⟨hiter_t, hdir_t⟩
  let j_rw := segStart segs arrSeg + m - 1
  have h0_0 : σ₀ 0 = blkHome := (hws₀ 0 (by omega)).trans (encodeWorkspace_getD_zero segs)
  have hne_0 : ∀ i, 1 ≤ i → i ≤ j_rw → σ₀ i ≠ blkHome := by
    intro i hi1 hi2; rw [hws₀ i (by omega)]; exact encodeWorkspace_ne_home segs hi1 (by omega)
  rcases blkRewind_aux (blkReadAndClear MaxSeg) M_blk (0, true, res)
      (by simp [blkReadAndClear]) (fun sym hne => by simp [blkReadAndClear, hne])
      j_rw σ₀ (by omega) h0_0 hne_0
    with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
  refine ⟨segStart segs arrSeg + m + 1 + j_rw, by omega, ?_, hnone_rw, ?_, ?_⟩
  · rw [blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
        hiter_cl, Option.bind_some, hiter_t, Option.bind_some, hiter_rw]
  · intro i hi q' σ' j' hi_eq
    by_cases hi1 : i ≤ segStart segs arrSeg
    · rcases blkIter_le_some hi1 hiter_go with ⟨⟨qi, σi, ji⟩, hsub⟩
      rw [hsub] at hi_eq; cases hi_eq; exact hbnd_go i hi1 q' σ' j' hsub
    · by_cases hi2 : i ≤ segStart segs arrSeg + m
      · have heq : i = segStart segs arrSeg + (i - segStart segs arrSeg) := by omega
        rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
        exact hbnd_cl (i - segStart segs arrSeg) (by omega) q' σ' j' hi_eq
      · have heq : i = segStart segs arrSeg + m + 1 + (i - (segStart segs arrSeg + m + 1)) := by omega
        rw [heq, blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
            hiter_cl, Option.bind_some, hiter_t, Option.bind_some] at hi_eq
        exact hbnd_rw (i - (segStart segs arrSeg + m + 1)) (by omega) q' σ' j' hi_eq
  · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
    by_cases hi1 : i < segStart segs arrSeg
    · exact hdir_go i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
    · by_cases hi2 : i < segStart segs arrSeg + m
      · have heq : i = segStart segs arrSeg + (i - segStart segs arrSeg) := by omega
        rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
        exact hdir_cl (i - segStart segs arrSeg) (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
      · by_cases hi3 : i = segStart segs arrSeg + m
        · subst hi3
          rw [blkIter_add, hiter_go, Option.bind_some, hiter_cl] at hi_eq
          cases hi_eq; exact hdir_t q'' sym' dir hbs'
        · have heq : i = segStart segs arrSeg + m + 1 + (i - (segStart segs arrSeg + m + 1)) := by omega
          rw [heq, blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
              hiter_cl, Option.bind_some, hiter_t, Option.bind_some] at hi_eq
          exact hdir_rw (i - (segStart segs arrSeg + m + 1)) (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

abbrev SegQuad (MaxSeg : ℕ) : Type :=
  Fin (MaxSeg + 1) × Fin (MaxSeg + 1) × Fin (MaxSeg + 1) × Fin (MaxSeg + 1)

abbrev WsReadLoopQ (MaxSeg : ℕ) : Type :=
  WsDecJzQ MaxSeg ⊕
  (LiftBlkQ (Fin (MaxSeg + 1) × Bool × Bool) ⊕ LiftBlkQ (Fin (MaxSeg + 1) × Bool))

def wsReadBody (MaxSeg : ℕ) (arrSeg : Fin (MaxSeg + 1)) : StepFn (WsReadLoopQ MaxSeg) :=
  seq0 (wsDecJz MaxSeg)
    (sumStep (liftBlockStep (blkReadAndClear MaxSeg)) (liftBlockStep (blkMarkNext MaxSeg)))
    (fun q => if wsDecJzWasZero q
      then Sum.inl (liftBlkEntry (arrSeg, false, false))
      else Sum.inr (liftBlkEntry (arrSeg, false)))

def wsReadNext (MaxSeg : ℕ) (tmpSeg : Fin (MaxSeg + 1)) : WsReadLoopQ MaxSeg → Option (WsReadLoopQ MaxSeg)
  | Sum.inr (Sum.inr _) => some (Sum.inl (wsDecJzEntry MaxSeg tmpSeg))
  | _ => none

def wsReadLoop (MaxSeg : ℕ) (arrSeg tmpSeg : Fin (MaxSeg + 1)) : StepFn (WsReadLoopQ MaxSeg) :=
  loop0 (wsReadBody MaxSeg arrSeg) (wsReadNext MaxSeg tmpSeg)

abbrev WsReadBitInnerQ (MaxSeg : ℕ) : Type :=
  WsCopyInnerQ MaxSeg ⊕ WsReadLoopQ MaxSeg

def wsReadBitFor (MaxSeg : ℕ) (qd : SegQuad MaxSeg) : StepFn (WsReadBitInnerQ MaxSeg) :=
  seq0 (wsCopyFor MaxSeg (qd.2.2.1, qd.2.1, qd.2.2.2))
    (wsReadLoop MaxSeg qd.1 qd.2.2.1)
    (fun _ => Sum.inl (wsDecJzEntry MaxSeg qd.2.2.1))

def wsReadBit (MaxSeg : ℕ) : StepFn (SegQuad MaxSeg × WsReadBitInnerQ MaxSeg) :=
  familyStep (wsReadBitFor MaxSeg)

def wsReadBitEntry (MaxSeg : ℕ) (qd : SegQuad MaxSeg) : SegQuad MaxSeg × WsReadBitInnerQ MaxSeg :=
  (qd, Sum.inl (Sum.inl (wsZeroEntry MaxSeg qd.2.2.1)))

def wsReadBitResult {MaxSeg : ℕ} : SegQuad MaxSeg × WsReadBitInnerQ MaxSeg → Bool
  | (_, Sum.inr (Sum.inr (Sum.inl q_rc))) => q_rc.1.2.2
  | _ => false

theorem wsReadLoop_spec (MaxSeg B w : ℕ) (arrSeg tmpSeg : Fin (MaxSeg + 1))
    (h_at : arrSeg.val < tmpSeg.val) :
    ∀ rem k (segs : List (List Bool)) len (τ₁ : ℕ → Bool),
      arrSeg.val < segs.length → tmpSeg.val < segs.length →
      rem < 2 ^ w →
      segs.getD tmpSeg.val [] = natToBitsLE w rem →
      TapeMarkedWS τ₁ len B segs arrSeg.val k →
      ∃ τ₂ : ℕ → Bool,
        TapeWS τ₂ len B (segs.set tmpSeg.val (natToBitsLE w 0)) ∧
        (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
        StepExec (wsReadLoop MaxSeg arrSeg tmpSeg) B
          (Sum.inl (wsDecJzEntry MaxSeg tmpSeg)) len τ₁ 0
          (Sum.inr (Sum.inl (liftBlkExit (0, true, (segs.getD arrSeg.val []).getD (k + rem) false)))) len τ₂ 0
          ((rem + 1) * (63 * (encodeWorkspace segs).length + 20)) := by
  intro rem
  induction rem with
  | zero =>
    intro k segs len τ₁ ha ht hrem hseg_t htm
    have hlen_pos : 1 ≤ len := by
      rcases htm with ⟨_, hW_le, _, _⟩
      have : 1 ≤ (encodeWorkspace segs).length := by simp [encodeWorkspace]
      omega
    rcases wsDecJz_marked_spec MaxSeg B segs h_at ht (Nat.le_of_lt_succ tmpSeg.isLt) hseg_t hrem htm
      with ⟨q_dec, τ_mid, hz_out, htm_mid, hout_mid, he_dec⟩
    simp only [decide_true, ↓reduceIte, Nat.add_zero] at hz_out htm_mid ⊢
    rcases htm_mid with ⟨hsegs, hW_le, hlen_B, σ₀, hws₀, hread_mid⟩
    have hexec_rc := blkReadAndClear_spec MaxSeg segs (v := k) ha (Nat.le_of_lt_succ arrSeg.isLt) σ₀ hws₀
    rw [← hread_mid] at hexec_rc
    rcases liftBlockStep_spec (blkReadAndClear MaxSeg) B (encodeWorkspace segs).length len τ_mid
        (arrSeg, false, false) (0, true, (segs.getD arrSeg.val []).getD k false) σ₀ 0 0
        (3 * (encodeWorkspace segs).length) hW_le hlen_B hexec_rc
      with ⟨τ₂, hread₂, hout₂, k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
    have he_rc := sumStep_inl_spec (liftBlockStep (blkReadAndClear MaxSeg))
      (liftBlockStep (blkMarkNext MaxSeg)) ⟨k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
    have hbody := seq0_spec (f := fun q => if wsDecJzWasZero q
      then Sum.inl (liftBlkEntry (arrSeg, false, false))
      else Sum.inr (liftBlkEntry (arrSeg, false))) hlen_pos he_dec (by simpa [hz_out] using he_rc)
    have hdone := (loop0_done (next := wsReadNext MaxSeg tmpSeg) hbody rfl).weaken
      ((0 + 1) * (63 * (encodeWorkspace segs).length + 20)) (by omega)
    have hset_noop : segs.set tmpSeg.val (natToBitsLE w 0) = segs := by
      apply List.ext_getElem (by simp)
      intro idx hk1 hk2
      rw [List.getElem_set]
      split_ifs with h1
      · subst h1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2, Option.getD_some] at hseg_t
        exact hseg_t.symm
      · rfl
    rw [hset_noop]
    exact ⟨τ₂, ⟨hsegs, hW_le, hlen_B, hread₂.symm ▸ hws₀⟩,
      fun p hp => (hout₂ p hp).trans (hout_mid p hp), hdone⟩
  | succ rem ih =>
    intro k segs len τ₁ ha ht hrem hseg_t htm
    have hlen_pos : 1 ≤ len := by
      rcases htm with ⟨_, hW_le, _, _⟩
      have : 1 ≤ (encodeWorkspace segs).length := by simp [encodeWorkspace]
      omega
    rcases wsDecJz_marked_spec MaxSeg B segs h_at ht (Nat.le_of_lt_succ tmpSeg.isLt) hseg_t hrem htm
      with ⟨q_dec, τ₁', hz_out, htm₁, hout₁, he_dec⟩
    simp only [Nat.add_one_ne_zero, decide_false, ↓reduceIte, Nat.add_sub_cancel] at hz_out htm₁
    let segs₁ := segs.set tmpSeg.val (natToBitsLE w rem)
    have hM₁ : (encodeWorkspace segs₁).length = (encodeWorkspace segs).length :=
      length_encodeWorkspace_set ht (by rw [hseg_t, length_natToBitsLE, length_natToBitsLE])
    rcases htm₁ with ⟨hsegs₁, hW_le₁, hlen_B₁, σ₀, hws₀, hread₁'⟩
    have ha₁ : arrSeg.val < segs₁.length := by simpa [segs₁] using ha
    have hexec_mk := blkMarkNext_spec MaxSeg segs₁ (k := k) ha₁ (Nat.le_of_lt_succ arrSeg.isLt) σ₀ hws₀
    rw [← hread₁'] at hexec_mk
    rcases liftBlockStep_spec (blkMarkNext MaxSeg) B (encodeWorkspace segs₁).length len τ₁'
        (arrSeg, false) (0, true) (reMark (segMarkPred segs₁ arrSeg.val (k + 1)) σ₀) 0 0
        (3 * (encodeWorkspace segs₁).length) hW_le₁ hlen_B₁ hexec_mk
      with ⟨τ₂', hread₂', hout₂', k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
    rw [hM₁] at hout₂' hk₂
    have he_mk := sumStep_inr_spec (liftBlockStep (blkReadAndClear MaxSeg))
      (liftBlockStep (blkMarkNext MaxSeg))
      ⟨k₂, by omega, hiter₂, hexit₂, hbnd₂⟩
    have hbody := seq0_spec (f := fun q => if wsDecJzWasZero q
      then Sum.inl (liftBlkEntry (arrSeg, false, false))
      else Sum.inr (liftBlkEntry (arrSeg, false))) hlen_pos he_dec (by simpa [hz_out] using he_mk)
    have htm₂ : TapeMarkedWS τ₂' len B segs₁ arrSeg.val (k + 1) :=
      ⟨hsegs₁, hW_le₁, hlen_B₁, σ₀, hws₀, hread₂'⟩
    rcases ih (k + 1) segs₁ len τ₂' ha₁ (by simpa [segs₁] using ht) (by omega)
        (getD_set_self_seg segs ht _) htm₂
      with ⟨τ_end, htw_end, hout_end, he_rest⟩
    rw [hM₁] at hout_end he_rest
    have hget_arr : segs₁.getD arrSeg.val [] = segs.getD arrSeg.val [] :=
      getD_set_ne_seg segs (by omega : tmpSeg.val ≠ arrSeg.val) _
    have hidx_eq : k + 1 + rem = k + (rem + 1) := by omega
    rw [hget_arr, hidx_eq] at he_rest
    have hsegs_eq : segs₁.set tmpSeg.val (natToBitsLE w 0) = segs.set tmpSeg.val (natToBitsLE w 0) := by
      simp [segs₁]
    rw [hsegs_eq] at htw_end
    let M := (encodeWorkspace segs).length
    have hstep := (loop0_step (next := wsReadNext MaxSeg tmpSeg) hlen_pos hbody rfl he_rest).weaken
      ((rem + 1 + 1) * (63 * M + 20)) (by
        have : (rem + 1 + 1) * (63 * M + 20) = (63 * M + 20) + (rem + 1) * (63 * M + 20) := by ring
        dsimp only [M] at *; omega)
    exact ⟨τ_end, htw_end, fun p hp => (hout_end p hp).trans ((hout₂' p hp).trans (hout₁ p hp)), hstep⟩

theorem wsReadBit_spec (MaxSeg B : ℕ) (segs : List (List Bool)) {arr idx tmp tmp2 w v : ℕ}
    (ha : arr < segs.length) (hi : idx < segs.length) (ht : tmp < segs.length) (ht2 : tmp2 < segs.length)
    (ha_m : arr ≤ MaxSeg) (hi_m : idx ≤ MaxSeg) (ht_m : tmp ≤ MaxSeg) (ht2_m : tmp2 ≤ MaxSeg)
    (h_at : arr < tmp) (h_ti : tmp ≠ idx) (h_tt2 : tmp ≠ tmp2) (h_it2 : idx ≠ tmp2) (h_at2 : arr ≠ tmp2)
    (hseg_i : segs.getD idx [] = natToBitsLE w v)
    (hlen_t : (segs.getD tmp []).length = w)
    (hlen_t2 : (segs.getD tmp2 []).length = w)
    (hv : v < 2 ^ w)
    {len : ℕ} {τ₁ : ℕ → Bool} (htw : TapeWS τ₁ len B segs) :
    let qd : SegQuad MaxSeg := (⟨arr, by omega⟩, ⟨idx, by omega⟩, ⟨tmp, by omega⟩, ⟨tmp2, by omega⟩)
    ∃ q_end, ∃ τ₂ : ℕ → Bool,
      wsReadBitResult q_end = (segs.getD arr []).getD v false ∧
      TapeWS τ₂ len B ((segs.set tmp (natToBitsLE w 0)).set tmp2 (natToBitsLE w 0)) ∧
      (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (wsReadBit MaxSeg) B (wsReadBitEntry MaxSeg qd) len τ₁ 0
        q_end len τ₂ 0 ((v + 2) * (220 * (encodeWorkspace segs).length + 80)) := by
  intro qd
  have hlen_pos := TapeWS_pos htw
  rcases wsCopyFor_spec MaxSeg B segs ht hi ht2 ht_m hi_m ht2_m h_ti h_tt2 h_it2 hlen_t hseg_i hlen_t2 hv htw
    with ⟨q_cp, τ_cp, htw_cp, hout_cp, he_cp_inner⟩
  let segs_cp := (segs.set tmp (natToBitsLE w v)).set tmp2 (natToBitsLE w 0)
  have hM_cp : (encodeWorkspace segs_cp).length = (encodeWorkspace segs).length := by
    have h1 := length_encodeWorkspace_set ht
      (newSeg := natToBitsLE w v) (by rw [hlen_t, length_natToBitsLE])
    have h2 := length_encodeWorkspace_set (segs := segs.set tmp (natToBitsLE w v)) (s := tmp2)
      (newSeg := natToBitsLE w 0) (by simpa using ht2)
      (by rw [getD_set_ne_seg segs h_tt2, hlen_t2, length_natToBitsLE])
    exact h2.trans h1
  have htm_cp : TapeMarkedWS τ_cp len B segs_cp arr 0 := TapeMarkedWS_zero_iff.mpr htw_cp
  rcases wsReadLoop_spec MaxSeg B w qd.1 qd.2.2.1 h_at v 0 segs_cp len τ_cp
      (by simpa [segs_cp] using ha) (by simpa [segs_cp] using ht) hv
      (by dsimp only [segs_cp, qd]; rw [getD_set_ne_seg _ h_tt2.symm, getD_set_self_seg _ ht])
      htm_cp
    with ⟨τ_end, htw_end, hout_end, he_rl⟩
  rw [hM_cp] at hout_end he_rl
  simp only [Nat.zero_add] at he_rl
  have hget_arr : segs_cp.getD qd.1.val [] = segs.getD arr [] := by
    dsimp only [segs_cp, qd]
    rw [getD_set_ne_seg _ h_at2.symm, getD_set_ne_seg _ (by omega : tmp ≠ arr)]
  rw [hget_arr] at he_rl
  have hsegs_final : segs_cp.set qd.2.2.1.val (natToBitsLE w 0) =
      (segs.set tmp (natToBitsLE w 0)).set tmp2 (natToBitsLE w 0) := by
    apply List.ext_getElem (by simp [segs_cp])
    intro k hk1 hk2
    simp only [segs_cp, qd, List.getElem_set]
    by_cases h1 : tmp = k
    · subst h1; simp [h_tt2.symm]
    · by_cases h2 : tmp2 = k
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [hsegs_final] at htw_end
  have he_seq := seq0_spec (f := fun _ => Sum.inl (wsDecJzEntry MaxSeg qd.2.2.1)) hlen_pos he_cp_inner he_rl
  let M := (encodeWorkspace segs).length
  have htime : (v + 2) * (150 * M + 50) + 1 + (v + 1) * (63 * M + 20) ≤ (v + 2) * (220 * M + 80) := by
    calc (v + 2) * (150 * M + 50) + 1 + (v + 1) * (63 * M + 20)
        ≤ (v + 2) * (150 * M + 50) + 1 + (v + 2) * (63 * M + 20) := by
          have := Nat.mul_le_mul_right (63 * M + 20) (show v + 1 ≤ v + 2 by omega)
          omega
      _ = 1 + (v + 2) * (213 * M + 70) := by ring
      _ ≤ (v + 2) * (220 * M + 80) := by
          have : (v + 2) * (220 * M + 80) = (v + 2) * (213 * M + 70) + (v + 2) * (7 * M + 10) := by ring
          have : 1 ≤ (v + 2) * (7 * M + 10) := Nat.mul_pos (by omega) (by omega)
          omega
  have he_fam := (familyStep_spec (wsReadBitFor MaxSeg) qd he_seq).weaken ((v + 2) * (220 * M + 80)) htime
  exact ⟨(qd, Sum.inr (Sum.inr (Sum.inl (liftBlkExit (0, true, (segs.getD arr []).getD v false))))),
    τ_end, rfl, htw_end, fun p hp => (hout_end p hp).trans (hout_cp p hp), he_fam⟩

/-!
### Right-to-Left In-Bounds Output Writer (`shuttleWrite`)
-/

abbrev CursorMode : Type := Unit ⊕ (Unit ⊕ Bool)

def cursorOp (mode : CursorMode) : StepFn (Fin 14) :=
  fun q b =>
    if q.val = 0 then some (if b then 1 else 2, b, QCSD_HeadDir.right)
    else if q.val = 1 then some (if !b then 3 else 4, b, QCSD_HeadDir.right)
    else if q.val = 2 then some (4, b, QCSD_HeadDir.right)
    else if q.val = 3 then some (if b then 5 else 0, b, QCSD_HeadDir.right)
    else if q.val = 4 then some (0, b, QCSD_HeadDir.right)
    else if q.val = 5 then
      match mode with
      | Sum.inl () => some (8, true, QCSD_HeadDir.left)
      | Sum.inr (Sum.inl ()) =>
          if !b then some (5, false, QCSD_HeadDir.right)
          else some (6, false, QCSD_HeadDir.right)
      | Sum.inr (Sum.inr b_out) =>
          if !b then some (5, false, QCSD_HeadDir.right)
          else some (7, b_out, QCSD_HeadDir.left)
    else if q.val = 6 then some (7, true, QCSD_HeadDir.left)
    else if q.val = 7 then
      if !b then some (7, false, QCSD_HeadDir.left)
      else some (9, true, QCSD_HeadDir.left)
    else if q.val = 8 then some (if b then 9 else 10, b, QCSD_HeadDir.left)
    else if q.val = 9 then some (if b then 11 else 12, b, QCSD_HeadDir.left)
    else if q.val = 10 then some (12, b, QCSD_HeadDir.left)
    else if q.val = 11 then some (if b then 13 else 8, b, QCSD_HeadDir.left)
    else if q.val = 12 then some (8, b, QCSD_HeadDir.left)
    else none

theorem update_eq_self_of_eq {α : Type} {p : ℕ} {τ : ℕ → α} {v : α} (h : τ p = v) :
    Function.update τ p v = τ := by
  rw [← h]; simp

theorem cursorOp_goWall_blk (mode : CursorMode) {len B : ℕ} {τ : ℕ → Bool} {j : ℕ}
    (hlen : 3 * (j + 1) ≤ len) (hB : len ≤ B) :
    let q_end : Fin 14 := if readBlk τ j = blkWall then 5 else 0
    stepFnIter (cursorOp mode) (0, len, τ, 3 * j) 3 = some (q_end, len, τ, 3 * (j + 1)) ∧
    (∀ i ≤ 3, ∀ q' l' τ' h',
      stepFnIter (cursorOp mode) (0, len, τ, 3 * j) i = some (q', l', τ', h') →
      l' ≤ B ∧ h' ≤ 3 * (j + 1)) := by
  have hm0 : max len (3 * j + 1) = len := by omega
  have hm1 : max len (3 * j + 1 + 1) = len := by omega
  have ha1 : 3 * j + 1 + 1 = 3 * j + 2 := by omega
  have ha2 : 3 * j + 2 + 1 = 3 * (j + 1) := by omega
  have hiter3 : stepFnIter (cursorOp mode) (0, len, τ, 3 * j) 3 =
      some (if readBlk τ j = blkWall then 5 else 0, len, τ, 3 * (j + 1)) := by
    dsimp only [readBlk, blkWall]
    rcases Bool.eq_false_or_eq_true (τ (3 * j)) with hc0 | hc0 <;>
      rcases Bool.eq_false_or_eq_true (τ (3 * j + 1)) with hc1 | hc1 <;>
      rcases Bool.eq_false_or_eq_true (τ (3 * j + 2)) with hc2 | hc2 <;>
      simp [stepFnIter, stepFnOnce, cursorOp, moveHead, hc0, hc1, hc2,
        update_eq_self_of_eq hc0, update_eq_self_of_eq hc1, update_eq_self_of_eq hc2,
        hm0, hm1, hlen, ha1, ha2]
  refine ⟨hiter3, ?_⟩
  intro i hi q' l' τ' h' hi_eq
  match i with
  | 0 => cases hi_eq; exact ⟨hB, by omega⟩
  | 1 =>
    rcases Bool.eq_false_or_eq_true (τ (3 * j)) with hc0 | hc0 <;>
      simp [stepFnIter, stepFnOnce, cursorOp, moveHead, hc0, hm0] at hi_eq <;>
      rcases hi_eq with ⟨_, rfl, _, rfl⟩ <;> exact ⟨hB, by omega⟩
  | 2 =>
    rcases Bool.eq_false_or_eq_true (τ (3 * j)) with hc0 | hc0 <;>
      rcases Bool.eq_false_or_eq_true (τ (3 * j + 1)) with hc1 | hc1 <;>
      simp [stepFnIter, stepFnOnce, cursorOp, moveHead, hc0, hc1,
        update_eq_self_of_eq hc0, hm0, hm1, ha1] at hi_eq <;>
      rcases hi_eq with ⟨_, rfl, _, rfl⟩ <;> exact ⟨hB, by omega⟩
  | 3 =>
    rw [hiter3] at hi_eq; cases hi_eq; exact ⟨hB, Nat.le_refl _⟩
  | n + 4 => omega

theorem cursorOp_goWall_aux (mode : CursorMode) {M_blk len B : ℕ} {τ : ℕ → Bool}
    (hM_pos : 1 ≤ M_blk) (hW_le : 3 * M_blk ≤ len) (hlen_B : len ≤ B) (hW_lt : 3 * M_blk < B)
    (hwall : ∀ j < M_blk, (readBlk τ j = blkWall ↔ j = M_blk - 1)) :
    stepFnIter (cursorOp mode) (0, len, τ, 0) (3 * M_blk) = some (5, len, τ, 3 * M_blk) ∧
    (∀ i ≤ 3 * M_blk, ∀ q' l' τ' h',
      stepFnIter (cursorOp mode) (0, len, τ, 0) i = some (q', l', τ', h') →
      l' ≤ B ∧ h' + 1 ≤ B) := by
  have haux : ∀ d j, j + (d + 1) = M_blk →
      stepFnIter (cursorOp mode) (0, len, τ, 3 * j) (3 * (d + 1)) = some (5, len, τ, 3 * M_blk) ∧
      (∀ i ≤ 3 * (d + 1), ∀ q' l' τ' h',
        stepFnIter (cursorOp mode) (0, len, τ, 3 * j) i = some (q', l', τ', h') →
        l' ≤ B ∧ h' + 1 ≤ B) := by
    intro d
    induction d with
    | zero =>
      intro j hjr
      rcases cursorOp_goWall_blk mode (j := j) (len := len) (B := B) (τ := τ) (by omega) hlen_B
        with ⟨h3, hb3⟩
      have hj_eq : j = M_blk - 1 := by omega
      have hw_t : readBlk τ j = blkWall := (hwall j (by omega)).mpr hj_eq
      simp only [hw_t, ↓reduceIte] at h3
      have h3M : 3 * (j + 1) = 3 * M_blk := by omega
      rw [h3M] at h3
      refine ⟨by simpa using h3, ?_⟩
      intro i hi q' l' τ' h' hi_eq
      rcases hb3 i (by omega) q' l' τ' h' hi_eq with ⟨hl, hh⟩
      exact ⟨hl, by omega⟩
    | succ d ih =>
      intro j hjr
      rcases cursorOp_goWall_blk mode (j := j) (len := len) (B := B) (τ := τ) (by omega) hlen_B
        with ⟨h3, hb3⟩
      have hj_ne : j ≠ M_blk - 1 := by omega
      have hw_f : readBlk τ j ≠ blkWall := fun h => hj_ne ((hwall j (by omega)).mp h)
      simp only [hw_f, ↓reduceIte] at h3
      rcases ih (j + 1) (by omega) with ⟨hrest, hbrest⟩
      have hmul : 3 * (d + 1 + 1) = 3 + 3 * (d + 1) := by ring
      refine ⟨?_, ?_⟩
      · rw [hmul, stepFnIter_add, h3, Option.bind_some, hrest]
      · intro i hi q' l' τ' h' hi_eq
        by_cases hi3 : i ≤ 3
        · rcases hb3 i hi3 q' l' τ' h' hi_eq with ⟨hl, hh⟩
          exact ⟨hl, by omega⟩
        · have heq : i = 3 + (i - 3) := by omega
          rw [heq, stepFnIter_add, h3, Option.bind_some] at hi_eq
          exact hbrest (i - 3) (by omega) q' l' τ' h' hi_eq
  have hM_eq : 3 * (M_blk - 1 + 1) = 3 * M_blk := by omega
  rcases haux (M_blk - 1) 0 (by omega) with ⟨hit, hbd⟩
  rw [hM_eq] at hit hbd
  exact ⟨hit, hbd⟩

theorem cursorOp_backHome_blk (mode : CursorMode) {len B : ℕ} {τ : ℕ → Bool} {j : ℕ}
    (hlen : 3 * (j + 1) ≤ len) (hB : len ≤ B) :
    let q_end : Fin 14 := if readBlk τ j = blkHome then 13 else 8
    stepFnIter (cursorOp mode) (8, len, τ, 3 * j + 2) 3 =
      some (q_end, len, τ, moveHead (3 * j) QCSD_HeadDir.left) ∧
    (∀ i ≤ 3, ∀ q' l' τ' h',
      stepFnIter (cursorOp mode) (8, len, τ, 3 * j + 2) i = some (q', l', τ', h') →
      l' ≤ B ∧ h' + 1 ≤ B) := by
  have hm2 : max len (3 * j + 2 + 1) = len := by omega
  have hm1 : max len (3 * j + 1 + 1) = len := by omega
  have hm0 : max len (3 * j + 1) = len := by omega
  have hs2 : moveHead (3 * j + 2) QCSD_HeadDir.left = 3 * j + 1 := by simp [moveHead]
  have hs1 : moveHead (3 * j + 1) QCSD_HeadDir.left = 3 * j := by simp [moveHead]
  have hiter3 : stepFnIter (cursorOp mode) (8, len, τ, 3 * j + 2) 3 =
      some (if readBlk τ j = blkHome then 13 else 8, len, τ, moveHead (3 * j) QCSD_HeadDir.left) := by
    dsimp only [readBlk, blkHome]
    rcases Bool.eq_false_or_eq_true (τ (3 * j + 2)) with hc2 | hc2 <;>
      rcases Bool.eq_false_or_eq_true (τ (3 * j + 1)) with hc1 | hc1 <;>
      rcases Bool.eq_false_or_eq_true (τ (3 * j)) with hc0 | hc0 <;>
      simp [stepFnIter, stepFnOnce, cursorOp, hs2, hs1, hc2, hc1, hc0,
        update_eq_self_of_eq hc2, update_eq_self_of_eq hc1, update_eq_self_of_eq hc0,
        hm2, hm1, hm0]
  refine ⟨hiter3, ?_⟩
  intro i hi q' l' τ' h' hi_eq
  match i with
  | 0 => cases hi_eq; exact ⟨hB, by omega⟩
  | 1 =>
    rcases Bool.eq_false_or_eq_true (τ (3 * j + 2)) with hc2 | hc2 <;>
      simp [stepFnIter, stepFnOnce, cursorOp, hs2, hc2, hm2] at hi_eq <;>
      rcases hi_eq with ⟨_, rfl, _, rfl⟩ <;> exact ⟨hB, by omega⟩
  | 2 =>
    rcases Bool.eq_false_or_eq_true (τ (3 * j + 2)) with hc2 | hc2 <;>
      rcases Bool.eq_false_or_eq_true (τ (3 * j + 1)) with hc1 | hc1 <;>
      simp [stepFnIter, stepFnOnce, cursorOp, hs2, hs1, hc2, hc1,
        update_eq_self_of_eq hc2, hm2, hm1] at hi_eq <;>
      rcases hi_eq with ⟨_, rfl, _, rfl⟩ <;> exact ⟨hB, by omega⟩
  | 3 =>
    rw [hiter3] at hi_eq; cases hi_eq
    simp only [moveHead]
    exact ⟨hB, by omega⟩
  | n + 4 => omega

theorem cursorOp_backHome_aux (mode : CursorMode) {M_blk len B : ℕ} {τ : ℕ → Bool}
    (hW_le : 3 * M_blk ≤ len) (hlen_B : len ≤ B)
    (h0 : readBlk τ 0 = blkHome)
    (hne : ∀ j, 1 ≤ j → j < M_blk → readBlk τ j ≠ blkHome) :
    ∀ j < M_blk,
      stepFnIter (cursorOp mode) (8, len, τ, 3 * j + 2) (3 * (j + 1)) = some (13, len, τ, 0) ∧
      (∀ i ≤ 3 * (j + 1), ∀ q' l' τ' h',
        stepFnIter (cursorOp mode) (8, len, τ, 3 * j + 2) i = some (q', l', τ', h') →
        l' ≤ B ∧ h' + 1 ≤ B) := by
  intro j
  induction j with
  | zero =>
    intro hj
    rcases cursorOp_backHome_blk mode (j := 0) (len := len) (B := B) (τ := τ) (by omega) hlen_B
      with ⟨h3, hb3⟩
    simp only [h0, ↓reduceIte, Nat.mul_zero, moveHead, Nat.zero_sub] at h3
    exact ⟨h3, hb3⟩
  | succ j ih =>
    intro hj
    rcases cursorOp_backHome_blk mode (j := j + 1) (len := len) (B := B) (τ := τ) (by omega) hlen_B
      with ⟨h3, hb3⟩
    have hnh : readBlk τ (j + 1) ≠ blkHome := hne (j + 1) (by omega) hj
    have hprev : moveHead (3 * (j + 1)) QCSD_HeadDir.left = 3 * j + 2 := by simp [moveHead]; omega
    simp only [hnh, ↓reduceIte, hprev] at h3
    rcases ih (by omega) with ⟨hrest, hbrest⟩
    have hmul : 3 * (j + 1 + 1) = 3 + 3 * (j + 1) := by ring
    refine ⟨?_, ?_⟩
    · rw [hmul, stepFnIter_add, h3, Option.bind_some, hrest]
    · intro i hi q' l' τ' h' hi_eq
      by_cases hi3 : i ≤ 3
      · exact hb3 i hi3 q' l' τ' h' hi_eq
      · have heq : i = 3 + (i - 3) := by omega
        rw [heq, stepFnIter_add, h3, Option.bind_some] at hi_eq
        exact hbrest (i - 3) (by omega) q' l' τ' h' hi_eq

theorem cursorOp_backHome_from9 (mode : CursorMode) {M_blk len B : ℕ} {τ : ℕ → Bool}
    (hM_ge2 : 2 ≤ M_blk) (hW_le : 3 * M_blk ≤ len) (hlen_B : len ≤ B)
    (h0 : readBlk τ 0 = blkHome)
    (hne : ∀ j, 1 ≤ j → j < M_blk → readBlk τ j ≠ blkHome)
    (hw : readBlk τ (M_blk - 1) = blkWall) :
    stepFnIter (cursorOp mode) (9, len, τ, 3 * M_blk - 2) (3 * M_blk - 1) = some (13, len, τ, 0) ∧
    (∀ i ≤ 3 * M_blk - 1, ∀ q' l' τ' h',
      stepFnIter (cursorOp mode) (9, len, τ, 3 * M_blk - 2) i = some (q', l', τ', h') →
      l' ≤ B ∧ h' + 1 ≤ B) := by
  have hw0 : τ (3 * (M_blk - 1)) = true := by
    have := congrArg Prod.fst hw; simpa [readBlk, blkWall] using this
  have hw1 : τ (3 * (M_blk - 1) + 1) = false := by
    have := congrArg (fun x => x.2.1) hw; simpa [readBlk, blkWall] using this
  have hp1 : 3 * M_blk - 2 = 3 * (M_blk - 1) + 1 := by omega
  have hm1 : max len (3 * (M_blk - 1) + 1 + 1) = len := by omega
  have hm0 : max len (3 * (M_blk - 1) + 1) = len := by omega
  have hs1 : moveHead (3 * (M_blk - 1) + 1) QCSD_HeadDir.left = 3 * (M_blk - 1) := by simp [moveHead]
  have hs0 : moveHead (3 * (M_blk - 1)) QCSD_HeadDir.left = 3 * (M_blk - 2) + 2 := by simp [moveHead]; omega
  have hstep2 : stepFnIter (cursorOp mode) (9, len, τ, 3 * M_blk - 2) 2 =
      some (8, len, τ, 3 * (M_blk - 2) + 2) := by
    have hu1 : Function.update τ (3 * (M_blk - 1) + 1) false = τ := by rw [← hw1]; simp
    have hu0 : Function.update τ (3 * (M_blk - 1)) true = τ := by rw [← hw0]; simp
    rw [hp1]
    simp [stepFnIter, stepFnOnce, cursorOp, hw1, hw0, hm1, hm0, hs1, hs0, hu1, hu0]
  rcases cursorOp_backHome_aux mode hW_le hlen_B h0 hne (M_blk - 2) (by omega)
    with ⟨hrest, hbrest⟩
  have hcnt : 3 * M_blk - 1 = 2 + 3 * (M_blk - 2 + 1) := by omega
  refine ⟨?_, ?_⟩
  · rw [hcnt, stepFnIter_add, hstep2, Option.bind_some, hrest]
  · intro i hi q' l' τ' h' hi_eq
    match i with
    | 0 => cases hi_eq; exact ⟨hlen_B, by omega⟩
    | 1 =>
      rw [hp1] at hi_eq
      simp [stepFnIter, stepFnOnce, cursorOp, hw1, hm1, hs1] at hi_eq
      rcases hi_eq with ⟨_, rfl, _, rfl⟩
      exact ⟨hlen_B, by omega⟩
    | i' + 2 =>
      rw [Nat.add_comm i' 2, stepFnIter_add, hstep2, Option.bind_some] at hi_eq
      exact hbrest i' (by omega) q' l' τ' h' hi_eq

def scanLen (len pos rem : ℕ) : ℕ :=
  if rem = 0 then len else max len (pos + rem)

theorem cursorOp_scanRight_aux (sub : Unit ⊕ Bool) {B : ℕ} :
    ∀ rem pos len (τ : ℕ → Bool),
      len ≤ B → pos + rem < B →
      (∀ i < rem, τ (pos + i) = false) →
      stepFnIter (cursorOp (Sum.inr sub)) (5, len, τ, pos) rem =
        some (5, scanLen len pos rem, τ, pos + rem) ∧
      (∀ i ≤ rem, ∀ q' l' τ' h',
        stepFnIter (cursorOp (Sum.inr sub)) (5, len, τ, pos) i = some (q', l', τ', h') →
        l' ≤ B ∧ h' + 1 ≤ B) := by
  intro rem
  induction rem with
  | zero =>
    intro pos len τ hlen hpos _
    simp only [Nat.add_zero, scanLen, ↓reduceIte]
    refine ⟨rfl, ?_⟩
    intro i hi _ l' _ h' hi_eq
    obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
    cases hi_eq; exact ⟨hlen, by omega⟩
  | succ rem ih =>
    intro pos len τ hlen hpos hfalse
    have hf0 : τ pos = false := by simpa using hfalse 0 (Nat.zero_lt_succ rem)
    have hstep1 : stepFnIter (cursorOp (Sum.inr sub)) (5, len, τ, pos) 1 =
        some (5, max len (pos + 1), τ, pos + 1) := by
      have hupd : Function.update τ pos false = τ := by rw [← hf0]; simp
      cases sub <;> simp [stepFnIter, stepFnOnce, cursorOp, hf0, moveHead, hupd]
    rcases ih (pos + 1) (max len (pos + 1)) τ (by omega) (by omega)
        (fun i hi => by
          have := hfalse (i + 1) (Nat.succ_lt_succ hi)
          rwa [Nat.add_assoc, Nat.add_comm 1 i])
      with ⟨hrest, hbrest⟩
    have hsl : scanLen (max len (pos + 1)) (pos + 1) rem = scanLen len pos (rem + 1) := by
      simp only [scanLen, Nat.add_one_ne_zero, ↓reduceIte]
      split_ifs <;> omega
    have hadd : pos + 1 + rem = pos + (rem + 1) := by omega
    rw [hsl, hadd] at hrest
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [Nat.add_comm rem 1]
      rw [stepFnIter_add, hstep1, Option.bind_some, hrest]
    · intro i hi q' l' τ' h' hi_eq
      cases i with
      | zero => cases hi_eq; exact ⟨hlen, by omega⟩
      | succ i' =>
        rw [Nat.add_comm i' 1, stepFnIter_add, hstep1, Option.bind_some] at hi_eq
        exact hbrest i' (by omega) q' l' τ' h' hi_eq

theorem cursorOp_scanLeft_aux (mode : CursorMode) {W len B : ℕ} {τ : ℕ → Bool}
    (hW_ge2 : 2 ≤ W) (hlen_B : len ≤ B) (hw_true : τ (W - 1) = true) :
    ∀ m, W + m ≤ len →
      (∀ i < m, τ (W + i) = false) →
      stepFnIter (cursorOp mode) (7, len, τ, W - 1 + m) (m + 1) =
        some (9, len, τ, W - 2) ∧
      (∀ i ≤ m + 1, ∀ q' l' τ' h',
        stepFnIter (cursorOp mode) (7, len, τ, W - 1 + m) i = some (q', l', τ', h') →
        l' ≤ B ∧ h' + 1 ≤ B) := by
  intro m
  induction m with
  | zero =>
    intro hWm _
    simp only [Nat.add_zero]
    have hm : max len (W - 1 + 1) = len := by omega
    have hs : moveHead (W - 1) QCSD_HeadDir.left = W - 2 := by simp [moveHead]; omega
    have hupd : Function.update τ (W - 1) true = τ := by rw [← hw_true]; simp
    have h1 : stepFnIter (cursorOp mode) (7, len, τ, W - 1) 1 = some (9, len, τ, W - 2) := by
      simp [stepFnIter, stepFnOnce, cursorOp, hw_true, hm, hs, hupd]
    refine ⟨h1, ?_⟩
    intro i hi q' l' τ' h' hi_eq
    match i with
    | 0 => cases hi_eq; exact ⟨hlen_B, by omega⟩
    | 1 => rw [h1] at hi_eq; cases hi_eq; exact ⟨hlen_B, by omega⟩
    | n + 2 => omega
  | succ m ih =>
    intro hWm hfalse
    have hp_eq : W - 1 + (m + 1) = W + m := by omega
    have hfm : τ (W + m) = false := hfalse m (Nat.lt_succ_self m)
    have hm : max len (W + m + 1) = len := by omega
    have hs : moveHead (W + m) QCSD_HeadDir.left = W - 1 + m := by simp [moveHead]; omega
    have hupd : Function.update τ (W + m) false = τ := by rw [← hfm]; simp
    have hstep1 : stepFnIter (cursorOp mode) (7, len, τ, W - 1 + (m + 1)) 1 =
        some (7, len, τ, W - 1 + m) := by
      rw [hp_eq]
      simp [stepFnIter, stepFnOnce, cursorOp, hfm, hm, hs, hupd]
    rcases ih (by omega) (fun i hi => hfalse i (by omega)) with ⟨hrest, hbrest⟩
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm (m + 1) 1, stepFnIter_add, hstep1, Option.bind_some, hrest]
    · intro i hi q' l' τ' h' hi_eq
      cases i with
      | zero => cases hi_eq; exact ⟨hlen_B, by omega⟩
      | succ i' =>
        rw [Nat.add_comm i' 1, stepFnIter_add, hstep1, Option.bind_some] at hi_eq
        exact hbrest i' (by omega) q' l' τ' h' hi_eq

theorem TapeWS_M_ge2 {τ : ℕ → Bool} {len B : ℕ} {segs : List (List Bool)}
    (htw : TapeWS τ len B segs) : 2 ≤ (encodeWorkspace segs).length := by
  rcases htw with ⟨hsegs, _, _, _⟩
  have := length_encodeSegmentsAux segs hsegs
  cases segs with
  | nil => contradiction
  | cons s l =>
    simp only [encodeWorkspace, List.length_cons, this, List.map_cons, List.sum_cons]
    omega

theorem TapeWS_update_ge_W {τ : ℕ → Bool} {len len' B : ℕ} {segs : List (List Bool)}
    (htw : TapeWS τ len B segs) (hW' : 3 * (encodeWorkspace segs).length ≤ len') (hB' : len' ≤ B)
    {p : ℕ} (hp : 3 * (encodeWorkspace segs).length ≤ p) (b : Bool) :
    TapeWS (Function.update τ p b) len' B segs := by
  rcases htw with ⟨hsegs, _, _, hws⟩
  refine ⟨hsegs, hW', hB', ?_⟩
  intro j hj
  have hr : readBlk (Function.update τ p b) j = readBlk τ j := by
    simp only [readBlk, Function.update_of_ne (by omega : 3 * j ≠ p),
      Function.update_of_ne (by omega : 3 * j + 1 ≠ p),
      Function.update_of_ne (by omega : 3 * j + 2 ≠ p)]
  rw [hr]
  exact hws j hj

theorem cursorOp_place_spec {B len : ℕ} {segs : List (List Bool)} {τ₁ : ℕ → Bool}
    (htw : TapeWS τ₁ len B segs) (hW_lt : 3 * (encodeWorkspace segs).length < B) :
    let W := 3 * (encodeWorkspace segs).length
    let τ₂ := Function.update τ₁ W true
    let len₂ := max len (W + 1)
    TapeWS τ₂ len₂ B segs ∧
    StepExec (cursorOp (Sum.inl ())) B 0 len τ₁ 0 13 len₂ τ₂ 0 (2 * W + 2) := by
  intro W τ₂ len₂
  have hM_ge2 := TapeWS_M_ge2 htw
  rcases htw with ⟨hsegs, hW_le, hlen_B, hws⟩
  let M_blk := (encodeWorkspace segs).length
  have hwall : ∀ j < M_blk, (readBlk τ₁ j = blkWall ↔ j = M_blk - 1) := by
    intro j hj; rw [hws j hj]; exact encodeWorkspace_wall_iff segs hsegs hj
  rcases cursorOp_goWall_aux (Sum.inl ()) (by omega) hW_le hlen_B hW_lt hwall with ⟨hgw, hbgw⟩
  have htw₂ : TapeWS τ₂ len₂ B segs :=
    TapeWS_update_ge_W ⟨hsegs, hW_le, hlen_B, hws⟩ (by omega) (by omega) (Nat.le_refl W) true
  have hsW : moveHead (3 * M_blk) QCSD_HeadDir.left = 3 * (M_blk - 1) + 2 := by simp [moveHead]; omega
  have hstepW : stepFnIter (cursorOp (Sum.inl ())) (5, len, τ₁, 3 * M_blk) 1 =
      some (8, len₂, τ₂, 3 * (M_blk - 1) + 2) := by
    dsimp only [len₂, τ₂, W, M_blk] at hsW ⊢
    simp [stepFnIter, stepFnOnce, cursorOp, hsW]
  have hws₂ := htw₂.2.2.2
  have h0₂ : readBlk τ₂ 0 = blkHome := (hws₂ 0 (by omega)).trans (encodeWorkspace_getD_zero segs)
  have hne₂ : ∀ j, 1 ≤ j → j < M_blk → readBlk τ₂ j ≠ blkHome := by
    intro j hj1 hj2; rw [hws₂ j hj2]; exact encodeWorkspace_ne_home segs hj1 hj2
  rcases cursorOp_backHome_aux (Sum.inl ()) htw₂.2.1 htw₂.2.2.1 h0₂ hne₂ (M_blk - 1) (by omega)
    with ⟨hbh, hbbh⟩
  have h3M : 3 * (M_blk - 1 + 1) = 3 * M_blk := by omega
  rw [h3M] at hbh hbbh
  refine ⟨htw₂, 3 * M_blk + 1 + 3 * M_blk, by dsimp only [W, M_blk]; omega, ?_, fun _ => rfl, ?_⟩
  · rw [stepFnIter_add, stepFnIter_add, hgw, Option.bind_some, hstepW, Option.bind_some, hbh]
  · intro i hi q' l' τ' h' hi_eq
    by_cases hi1 : i ≤ 3 * M_blk
    · exact hbgw i hi1 q' l' τ' h' hi_eq
    · have heq : i = 3 * M_blk + 1 + (i - (3 * M_blk + 1)) := by omega
      rw [heq, stepFnIter_add, stepFnIter_add, hgw, Option.bind_some, hstepW, Option.bind_some] at hi_eq
      exact hbbh (i - (3 * M_blk + 1)) (by omega) q' l' τ' h' hi_eq

theorem cursorOp_step_spec {B len k : ℕ} {segs : List (List Bool)} {τ₁ : ℕ → Bool}
    (htw : TapeWS τ₁ len B segs)
    (hWk_lt : 3 * (encodeWorkspace segs).length + k + 1 < B)
    (hfalse_pre : ∀ i < k, τ₁ (3 * (encodeWorkspace segs).length + i) = false)
    (hcur : τ₁ (3 * (encodeWorkspace segs).length + k) = true) :
    let W := 3 * (encodeWorkspace segs).length
    let τ₂ := Function.update (Function.update τ₁ (W + k) false) (W + k + 1) true
    let len₂ := max len (W + k + 2)
    TapeWS τ₂ len₂ B segs ∧
    StepExec (cursorOp (Sum.inr (Sum.inl ()))) B 0 len τ₁ 0 13 len₂ τ₂ 0 (2 * (W + k) + 10) := by
  intro W τ₂ len₂
  have hM_ge2 := TapeWS_M_ge2 htw
  rcases htw with ⟨hsegs, hW_le, hlen_B, hws⟩
  let M_blk := (encodeWorkspace segs).length
  have hwall : ∀ j < M_blk, (readBlk τ₁ j = blkWall ↔ j = M_blk - 1) := by
    intro j hj; rw [hws j hj]; exact encodeWorkspace_wall_iff segs hsegs hj
  rcases cursorOp_goWall_aux (Sum.inr (Sum.inl ())) (by omega) hW_le hlen_B (by omega) hwall
    with ⟨hgw, hbgw⟩
  rcases cursorOp_scanRight_aux (Sum.inl ()) k (3 * M_blk) len τ₁ hlen_B (by omega) hfalse_pre
    with ⟨hsr, hbsr⟩
  let l_mid := max (scanLen len (3 * M_blk) k) (3 * M_blk + k + 1)
  have hl_mid_eq : l_mid = max len (3 * M_blk + k + 1) := by
    dsimp only [l_mid, scanLen]; split_ifs <;> omega
  have hl2_eq : max l_mid (3 * M_blk + k + 1 + 1) = len₂ := by
    rw [hl_mid_eq]; dsimp only [len₂, W, M_blk]; omega
  have hstep1a : stepFnIter (cursorOp (Sum.inr (Sum.inl ())))
      (5, scanLen len (3 * M_blk) k, τ₁, 3 * M_blk + k) 1 =
      some (6, l_mid, Function.update τ₁ (3 * M_blk + k) false, 3 * M_blk + k + 1) := by
    dsimp only [l_mid, M_blk] at hcur ⊢
    simp [stepFnIter, stepFnOnce, cursorOp, hcur, moveHead]
  have hstep2 : stepFnIter (cursorOp (Sum.inr (Sum.inl ())))
      (5, scanLen len (3 * M_blk) k, τ₁, 3 * M_blk + k) 2 =
      some (7, len₂, τ₂, 3 * M_blk - 1 + (k + 1)) := by
    have hs_back : moveHead (3 * M_blk + k + 1) QCSD_HeadDir.left = 3 * M_blk - 1 + (k + 1) := by
      simp [moveHead]; omega
    rw [show (2 : ℕ) = 1 + 1 from rfl, stepFnIter_add, hstep1a, Option.bind_some]
    dsimp only [τ₂, W, M_blk] at hl2_eq hs_back ⊢
    simp [stepFnIter, stepFnOnce, cursorOp, hl2_eq, hs_back]
  have htw₂ : TapeWS τ₂ len₂ B segs := by
    have htw_m := TapeWS_update_ge_W ⟨hsegs, hW_le, hlen_B, hws⟩ hW_le hlen_B (by omega : W ≤ W + k) false
    exact TapeWS_update_ge_W htw_m (by omega) (by omega) (by omega : W ≤ W + k + 1) true
  have hws₂ := htw₂.2.2.2
  have hw2_at : readBlk τ₂ (M_blk - 1) = blkWall := by
    rw [hws₂ (M_blk - 1) (by omega)]
    exact (encodeWorkspace_wall_iff segs hsegs (by omega)).mpr rfl
  have hw2_true : τ₂ (3 * M_blk - 1) = true := by
    have h2 := congrArg (fun x => x.2.2) hw2_at
    have hp : 3 * (M_blk - 1) + 2 = 3 * M_blk - 1 := by omega
    simpa [readBlk, blkWall, hp] using h2
  have hfalse₂ : ∀ i < k + 1, τ₂ (3 * M_blk + i) = false := by
    intro i hi
    dsimp only [τ₂, W, M_blk]
    rw [Function.update_of_ne (by omega : 3 * (encodeWorkspace segs).length + i ≠
        3 * (encodeWorkspace segs).length + k + 1)]
    by_cases hik : i = k
    · subst hik; simp
    · rw [Function.update_of_ne (by omega : 3 * (encodeWorkspace segs).length + i ≠
          3 * (encodeWorkspace segs).length + k)]
      exact hfalse_pre i (by omega)
  rcases cursorOp_scanLeft_aux (Sum.inr (Sum.inl ())) (W := 3 * M_blk) (len := len₂) (B := B) (τ := τ₂)
      (by omega) (by omega) hw2_true (k + 1) (by dsimp only [len₂, W, M_blk]; omega) hfalse₂
    with ⟨hsl, hbsl⟩
  have h0₂ : readBlk τ₂ 0 = blkHome := (hws₂ 0 (by omega)).trans (encodeWorkspace_getD_zero segs)
  have hne₂ : ∀ j, 1 ≤ j → j < M_blk → readBlk τ₂ j ≠ blkHome := by
    intro j hj1 hj2; rw [hws₂ j hj2]; exact encodeWorkspace_ne_home segs hj1 hj2
  rcases cursorOp_backHome_from9 (Sum.inr (Sum.inl ())) hM_ge2 htw₂.2.1 htw₂.2.2.1 h0₂ hne₂ hw2_at
    with ⟨hbh, hbbh⟩
  let K_tot := 3 * M_blk + k + 2 + (k + 2) + (3 * M_blk - 1)
  refine ⟨htw₂, K_tot, by dsimp only [K_tot, W, M_blk]; omega, ?_, fun _ => rfl, ?_⟩
  · rw [stepFnIter_add, stepFnIter_add, stepFnIter_add, stepFnIter_add,
        hgw, Option.bind_some, hsr, Option.bind_some, hstep2, Option.bind_some,
        hsl, Option.bind_some, hbh]
  · intro i hi q' l' τ' h' hi_eq
    by_cases hi1 : i ≤ 3 * M_blk
    · exact hbgw i hi1 q' l' τ' h' hi_eq
    · by_cases hi2 : i ≤ 3 * M_blk + k
      · have heq : i = 3 * M_blk + (i - 3 * M_blk) := by omega
        rw [heq, stepFnIter_add, hgw, Option.bind_some] at hi_eq
        exact hbsr (i - 3 * M_blk) (by omega) q' l' τ' h' hi_eq
      · by_cases hi3 : i = 3 * M_blk + k + 1
        · subst hi3
          rw [Nat.add_assoc (3 * M_blk) k 1, stepFnIter_add, hgw, Option.bind_some,
              stepFnIter_add, hsr, Option.bind_some, hstep1a] at hi_eq
          cases hi_eq
          rw [hl_mid_eq]
          exact ⟨by omega, by omega⟩
        · by_cases hi4 : i ≤ 3 * M_blk + k + 2 + (k + 2)
          · have heq : i = 3 * M_blk + k + 2 + (i - (3 * M_blk + k + 2)) := by omega
            rw [heq, stepFnIter_add, stepFnIter_add, stepFnIter_add,
                hgw, Option.bind_some, hsr, Option.bind_some, hstep2, Option.bind_some] at hi_eq
            exact hbsl (i - (3 * M_blk + k + 2)) (by omega) q' l' τ' h' hi_eq
          · have heq : i = 3 * M_blk + k + 2 + (k + 2) + (i - (3 * M_blk + k + 2 + (k + 2))) := by omega
            rw [heq, stepFnIter_add, stepFnIter_add, stepFnIter_add, stepFnIter_add,
                hgw, Option.bind_some, hsr, Option.bind_some, hstep2, Option.bind_some,
                hsl, Option.bind_some] at hi_eq
            exact hbbh (i - (3 * M_blk + k + 2 + (k + 2))) (by omega) q' l' τ' h' hi_eq

theorem cursorOp_finish_spec (b_out : Bool) {B len offset : ℕ} {segs : List (List Bool)} {τ₁ : ℕ → Bool}
    (htw : TapeWS τ₁ len B segs)
    (hWo_lt : 3 * (encodeWorkspace segs).length + offset < B)
    (hfalse_pre : ∀ i < offset, τ₁ (3 * (encodeWorkspace segs).length + i) = false)
    (hcur : τ₁ (3 * (encodeWorkspace segs).length + offset) = true) :
    let W := 3 * (encodeWorkspace segs).length
    let τ₂ := Function.update τ₁ (W + offset) b_out
    let len₂ := max len (W + offset + 1)
    TapeWS τ₂ len₂ B segs ∧
    StepExec (cursorOp (Sum.inr (Sum.inr b_out))) B 0 len τ₁ 0 13 len₂ τ₂ 0 (2 * (W + offset) + 10) := by
  intro W τ₂ len₂
  have hM_ge2 := TapeWS_M_ge2 htw
  rcases htw with ⟨hsegs, hW_le, hlen_B, hws⟩
  let M_blk := (encodeWorkspace segs).length
  have hwall : ∀ j < M_blk, (readBlk τ₁ j = blkWall ↔ j = M_blk - 1) := by
    intro j hj; rw [hws j hj]; exact encodeWorkspace_wall_iff segs hsegs hj
  rcases cursorOp_goWall_aux (Sum.inr (Sum.inr b_out)) (by omega) hW_le hlen_B (by omega) hwall
    with ⟨hgw, hbgw⟩
  rcases cursorOp_scanRight_aux (Sum.inr b_out) offset (3 * M_blk) len τ₁ hlen_B hWo_lt hfalse_pre
    with ⟨hsr, hbsr⟩
  have hl2_eq : max (scanLen len (3 * M_blk) offset) (3 * M_blk + offset + 1) = len₂ := by
    dsimp only [len₂, W, M_blk, scanLen]; split_ifs <;> omega
  have hstep1 : stepFnIter (cursorOp (Sum.inr (Sum.inr b_out)))
      (5, scanLen len (3 * M_blk) offset, τ₁, 3 * M_blk + offset) 1 =
      some (7, len₂, τ₂, 3 * M_blk - 1 + offset) := by
    have hs_back : moveHead (3 * M_blk + offset) QCSD_HeadDir.left = 3 * M_blk - 1 + offset := by
      simp [moveHead]; omega
    dsimp only [τ₂, W, M_blk] at hcur hl2_eq hs_back ⊢
    simp [stepFnIter, stepFnOnce, cursorOp, hcur, hl2_eq, hs_back]
  have htw₂ : TapeWS τ₂ len₂ B segs :=
    TapeWS_update_ge_W ⟨hsegs, hW_le, hlen_B, hws⟩ (by omega) (by omega) (by omega : W ≤ W + offset) b_out
  have hws₂ := htw₂.2.2.2
  have hw2_at : readBlk τ₂ (M_blk - 1) = blkWall := by
    rw [hws₂ (M_blk - 1) (by omega)]
    exact (encodeWorkspace_wall_iff segs hsegs (by omega)).mpr rfl
  have hw2_true : τ₂ (3 * M_blk - 1) = true := by
    have h2 := congrArg (fun x => x.2.2) hw2_at
    have hp : 3 * (M_blk - 1) + 2 = 3 * M_blk - 1 := by omega
    simpa [readBlk, blkWall, hp] using h2
  have hfalse₂ : ∀ i < offset, τ₂ (3 * M_blk + i) = false := by
    intro i hi
    dsimp only [τ₂, W, M_blk]
    rw [Function.update_of_ne (by omega : 3 * (encodeWorkspace segs).length + i ≠
        3 * (encodeWorkspace segs).length + offset)]
    exact hfalse_pre i hi
  rcases cursorOp_scanLeft_aux (Sum.inr (Sum.inr b_out)) (W := 3 * M_blk) (len := len₂) (B := B) (τ := τ₂)
      (by omega) (by omega) hw2_true offset (by dsimp only [len₂, W, M_blk]; omega) hfalse₂
    with ⟨hsl, hbsl⟩
  have h0₂ : readBlk τ₂ 0 = blkHome := (hws₂ 0 (by omega)).trans (encodeWorkspace_getD_zero segs)
  have hne₂ : ∀ j, 1 ≤ j → j < M_blk → readBlk τ₂ j ≠ blkHome := by
    intro j hj1 hj2; rw [hws₂ j hj2]; exact encodeWorkspace_ne_home segs hj1 hj2
  rcases cursorOp_backHome_from9 (Sum.inr (Sum.inr b_out)) hM_ge2 htw₂.2.1 htw₂.2.2.1 h0₂ hne₂ hw2_at
    with ⟨hbh, hbbh⟩
  let K_tot := 3 * M_blk + offset + 1 + (offset + 1) + (3 * M_blk - 1)
  refine ⟨htw₂, K_tot, by dsimp only [K_tot, W, M_blk]; omega, ?_, fun _ => rfl, ?_⟩
  · rw [stepFnIter_add, stepFnIter_add, stepFnIter_add, stepFnIter_add,
        hgw, Option.bind_some, hsr, Option.bind_some, hstep1, Option.bind_some,
        hsl, Option.bind_some, hbh]
  · intro i hi q' l' τ' h' hi_eq
    by_cases hi1 : i ≤ 3 * M_blk
    · exact hbgw i hi1 q' l' τ' h' hi_eq
    · by_cases hi2 : i ≤ 3 * M_blk + offset
      · have heq : i = 3 * M_blk + (i - 3 * M_blk) := by omega
        rw [heq, stepFnIter_add, hgw, Option.bind_some] at hi_eq
        exact hbsr (i - 3 * M_blk) (by omega) q' l' τ' h' hi_eq
      · by_cases hi3 : i ≤ 3 * M_blk + offset + 1 + (offset + 1)
        · have heq : i = 3 * M_blk + offset + 1 + (i - (3 * M_blk + offset + 1)) := by omega
          rw [heq, stepFnIter_add, stepFnIter_add, stepFnIter_add,
              hgw, Option.bind_some, hsr, Option.bind_some, hstep1, Option.bind_some] at hi_eq
          exact hbsl (i - (3 * M_blk + offset + 1)) (by omega) q' l' τ' h' hi_eq
        · have heq : i = 3 * M_blk + offset + 1 + (offset + 1) + (i - (3 * M_blk + offset + 1 + (offset + 1))) := by omega
          rw [heq, stepFnIter_add, stepFnIter_add, stepFnIter_add, stepFnIter_add,
              hgw, Option.bind_some, hsr, Option.bind_some, hstep1, Option.bind_some,
              hsl, Option.bind_some] at hi_eq
          exact hbbh (i - (3 * M_blk + offset + 1 + (offset + 1))) (by omega) q' l' τ' h' hi_eq

abbrev ShuttleLoopQ (MaxSeg : ℕ) : Type :=
  WsDecJzQ MaxSeg ⊕ (Fin 14 ⊕ Fin 14)

def shuttleBody (MaxSeg : ℕ) (b_out : Bool) : StepFn (ShuttleLoopQ MaxSeg) :=
  seq0 (wsDecJz MaxSeg)
    (sumStep (cursorOp (Sum.inr (Sum.inr b_out))) (cursorOp (Sum.inr (Sum.inl ()))))
    (fun q => if wsDecJzWasZero q then Sum.inl 0 else Sum.inr 0)

def shuttleNext (MaxSeg : ℕ) (s_off : Fin (MaxSeg + 1)) : ShuttleLoopQ MaxSeg → Option (ShuttleLoopQ MaxSeg)
  | Sum.inr (Sum.inr _) => some (Sum.inl (wsDecJzEntry MaxSeg s_off))
  | _ => none

def shuttleLoop (MaxSeg : ℕ) (s_off : Fin (MaxSeg + 1)) (b_out : Bool) : StepFn (ShuttleLoopQ MaxSeg) :=
  loop0 (shuttleBody MaxSeg b_out) (shuttleNext MaxSeg s_off)

abbrev ShuttleWriteInnerQ (MaxSeg : ℕ) : Type :=
  Fin 14 ⊕ ShuttleLoopQ MaxSeg

def shuttleWriteFor (MaxSeg : ℕ) (p : Fin (MaxSeg + 1) × Bool) : StepFn (ShuttleWriteInnerQ MaxSeg) :=
  seq0 (cursorOp (Sum.inl ())) (shuttleLoop MaxSeg p.1 p.2)
    (fun _ => Sum.inl (wsDecJzEntry MaxSeg p.1))

def shuttleWrite (MaxSeg : ℕ) : StepFn ((Fin (MaxSeg + 1) × Bool) × ShuttleWriteInnerQ MaxSeg) :=
  familyStep (shuttleWriteFor MaxSeg)

def shuttleWriteEntry (MaxSeg : ℕ) (s_off : Fin (MaxSeg + 1)) (b_out : Bool) :
    (Fin (MaxSeg + 1) × Bool) × ShuttleWriteInnerQ MaxSeg :=
  ((s_off, b_out), Sum.inl 0)

theorem shuttleLoop_spec (MaxSeg B w : ℕ) (s_off : Fin (MaxSeg + 1)) (b_out : Bool) :
    ∀ rem k (segs : List (List Bool)) len (τ₁ : ℕ → Bool),
      s_off.val < segs.length →
      rem < 2 ^ w →
      3 * (encodeWorkspace segs).length + k + rem < B →
      segs.getD s_off.val [] = natToBitsLE w rem →
      TapeWS τ₁ len B segs →
      (∀ i < k, τ₁ (3 * (encodeWorkspace segs).length + i) = false) →
      τ₁ (3 * (encodeWorkspace segs).length + k) = true →
      (∀ p, 3 * (encodeWorkspace segs).length + k < p → p ≤ 3 * (encodeWorkspace segs).length + k + rem →
        τ₁ p = false) →
      let W := 3 * (encodeWorkspace segs).length
      ∃ τ₂ : ℕ → Bool,
        TapeWS τ₂ (max len (W + k + rem + 1)) B (segs.set s_off.val (natToBitsLE w 0)) ∧
        (∀ p, W ≤ p → p < W + k + rem → τ₂ p = false) ∧
        τ₂ (W + k + rem) = b_out ∧
        (∀ p, W + k + rem < p → τ₂ p = τ₁ p) ∧
        StepExec (shuttleLoop MaxSeg s_off b_out) B
          (Sum.inl (wsDecJzEntry MaxSeg s_off)) len τ₁ 0
          (Sum.inr (Sum.inl 13)) (max len (W + k + rem + 1)) τ₂ 0
          ((rem + 1) * (16 * W + 2 * (k + rem) + 30)) := by
  intro rem
  induction rem with
  | zero =>
    intro k segs len τ₁ hs hrem hB hseg htw hpre hcur _ W
    have hlen_pos := TapeWS_pos htw
    rcases wsDecJz_spec MaxSeg B segs hs (Nat.le_of_lt_succ s_off.isLt) hseg hrem htw
      with ⟨q_dec, τ_mid, hz_out, htw_mid, hout_mid, he_dec⟩
    simp only [decide_true, ↓reduceIte, Nat.add_zero] at hz_out htw_mid ⊢
    have hpre_mid : ∀ i < k, τ_mid (3 * (encodeWorkspace segs).length + i) = false := by
      intro i hi; rw [hout_mid _ (by omega)]; exact hpre i hi
    have hcur_mid : τ_mid (3 * (encodeWorkspace segs).length + k) = true := by
      rw [hout_mid _ (by omega)]; exact hcur
    rcases cursorOp_finish_spec b_out htw_mid (by omega) hpre_mid hcur_mid
      with ⟨htw_fin, he_fin⟩
    have he_left := sumStep_inl_spec (cursorOp (Sum.inr (Sum.inr b_out)))
      (cursorOp (Sum.inr (Sum.inl ()))) he_fin
    have hbody := seq0_spec (f := fun q => if wsDecJzWasZero q then (Sum.inl 0 : Fin 14 ⊕ Fin 14) else Sum.inr 0)
      hlen_pos he_dec (by rw [hz_out]; exact he_left)
    have hdone := (loop0_done (next := shuttleNext MaxSeg s_off) hbody rfl).weaken
      ((0 + 1) * (16 * W + 2 * (k + 0) + 30)) (by dsimp only [W]; omega)
    have hset_noop : segs.set s_off.val (natToBitsLE w 0) = segs := by
      apply List.ext_getElem (by simp)
      intro idx hk1 hk2
      rw [List.getElem_set]
      split_ifs with h1
      · subst h1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, Option.getD_some] at hseg
        exact hseg.symm
      · rfl
    rw [hset_noop]
    refine ⟨Function.update τ_mid (W + k) b_out, htw_fin, ?_, by simp, ?_, hdone⟩
    · intro p hp1 hp2
      rw [Function.update_of_ne (by omega : p ≠ W + k)]
      simpa [W, Nat.add_sub_cancel' hp1] using hpre_mid (p - W) (by omega)
    · intro p hp
      rw [Function.update_of_ne (by omega : p ≠ W + k)]
      exact hout_mid p (by dsimp only [W] at hp; omega)
  | succ rem ih =>
    intro k segs len τ₁ hs hrem hB hseg htw hpre hcur hpost W
    have hlen_pos := TapeWS_pos htw
    rcases wsDecJz_spec MaxSeg B segs hs (Nat.le_of_lt_succ s_off.isLt) hseg hrem htw
      with ⟨q_dec, τ₁', hz_out, htw₁, hout₁, he_dec⟩
    simp only [Nat.add_one_ne_zero, decide_false, ↓reduceIte, Nat.add_sub_cancel] at hz_out htw₁
    let segs₁ := segs.set s_off.val (natToBitsLE w rem)
    have hM₁ : (encodeWorkspace segs₁).length = (encodeWorkspace segs).length :=
      length_encodeWorkspace_set hs (by rw [hseg, length_natToBitsLE, length_natToBitsLE])
    have hW₁ : 3 * (encodeWorkspace segs₁).length = W := by rw [hM₁]
    have hpre₁ : ∀ i < k, τ₁' (3 * (encodeWorkspace segs₁).length + i) = false := by
      intro i hi; rw [hW₁, hout₁ (W + i) (by dsimp only [W]; omega)]; exact hpre i hi
    have hcur₁ : τ₁' (3 * (encodeWorkspace segs₁).length + k) = true := by
      rw [hW₁, hout₁ (W + k) (by dsimp only [W]; omega)]; exact hcur
    rcases cursorOp_step_spec htw₁ (by rw [hW₁]; dsimp only [W]; omega) hpre₁ hcur₁
      with ⟨htw_st, he_st⟩
    rw [hW₁] at htw_st he_st
    let τ₂' := Function.update (Function.update τ₁' (W + k) false) (W + k + 1) true
    let len₂' := max len (W + k + 2)
    have he_right := sumStep_inr_spec (cursorOp (Sum.inr (Sum.inr b_out)))
      (cursorOp (Sum.inr (Sum.inl ()))) he_st
    have hbody := seq0_spec (f := fun q => if wsDecJzWasZero q then (Sum.inl 0 : Fin 14 ⊕ Fin 14) else Sum.inr 0)
      hlen_pos he_dec (by rw [hz_out]; exact he_right)
    have hpre₂ : ∀ i < k + 1, τ₂' (3 * (encodeWorkspace segs₁).length + i) = false := by
      intro i hi
      rw [hW₁]
      dsimp only [τ₂']
      rw [Function.update_of_ne (by omega : W + i ≠ W + k + 1)]
      by_cases hik : i = k
      · subst hik; simp
      · rw [Function.update_of_ne (by omega : W + i ≠ W + k), hout₁ (W + i) (by dsimp only [W]; omega)]
        exact hpre i (by omega)
    have hcur₂ : τ₂' (3 * (encodeWorkspace segs₁).length + (k + 1)) = true := by
      rw [hW₁]; dsimp only [τ₂']
      have : W + (k + 1) = W + k + 1 := by omega
      rw [this]; simp
    have hpost₂ : ∀ p, 3 * (encodeWorkspace segs₁).length + (k + 1) < p →
        p ≤ 3 * (encodeWorkspace segs₁).length + (k + 1) + rem → τ₂' p = false := by
      intro p hp1 hp2
      rw [hW₁] at hp1 hp2
      dsimp only [τ₂']
      rw [Function.update_of_ne (by omega : p ≠ W + k + 1),
          Function.update_of_ne (by omega : p ≠ W + k),
          hout₁ p (by dsimp only [W] at hp1; omega)]
      exact hpost p (by dsimp only [W] at hp1 ⊢; omega) (by dsimp only [W] at hp2 ⊢; omega)
    rcases ih (k + 1) segs₁ len₂' τ₂' (by simpa [segs₁] using hs) (by omega)
        (by rw [hW₁]; dsimp only [W]; omega) (getD_set_self_seg segs hs _) htw_st hpre₂ hcur₂ hpost₂
      with ⟨τ_end, htw_end, hpre_end, hcur_end, hout_end, he_rest⟩
    rw [hW₁] at htw_end hpre_end hcur_end hout_end he_rest
    have hlen_eq : max len₂' (W + (k + 1) + rem + 1) = max len (W + k + (rem + 1) + 1) := by
      dsimp only [len₂']; omega
    have hpos_eq : W + (k + 1) + rem = W + k + (rem + 1) := by omega
    have hsegs_eq : segs₁.set s_off.val (natToBitsLE w 0) = segs.set s_off.val (natToBitsLE w 0) := by
      simp [segs₁]
    rw [hlen_eq, hsegs_eq] at htw_end
    rw [hlen_eq] at he_rest
    rw [hpos_eq] at hpre_end hcur_end hout_end
    have hlen2_pos : 1 ≤ len₂' := TapeWS_pos htw_st
    have htime : 42 * (encodeWorkspace segs).length + 10 + 1 + (2 * (W + k) + 10) + 1 +
        (rem + 1) * (16 * W + 2 * (k + 1 + rem) + 30) ≤
        (rem + 1 + 1) * (16 * W + 2 * (k + (rem + 1)) + 30) := by
      have hk_eq : k + 1 + rem = k + (rem + 1) := by omega
      rw [hk_eq]
      have hexp : (rem + 1 + 1) * (16 * W + 2 * (k + (rem + 1)) + 30) =
          (16 * W + 2 * (k + (rem + 1)) + 30) + (rem + 1) * (16 * W + 2 * (k + (rem + 1)) + 30) := by ring
      rw [hexp]
      dsimp only [W]
      omega
    have hstep := (loop0_step (next := shuttleNext MaxSeg s_off) hlen2_pos hbody rfl he_rest).weaken
      ((rem + 1 + 1) * (16 * W + 2 * (k + (rem + 1)) + 30)) htime
    refine ⟨τ_end, htw_end, hpre_end, hcur_end, ?_, hstep⟩
    intro p hp
    rw [hout_end p hp]
    dsimp only [τ₂']
    rw [Function.update_of_ne (by omega : p ≠ W + k + 1),
        Function.update_of_ne (by omega : p ≠ W + k)]
    exact hout₁ p (by dsimp only [W] at hp; omega)

theorem shuttleWrite_spec (MaxSeg B : ℕ) (segs : List (List Bool)) {s_off w offset : ℕ} (b_out : Bool)
    (hs : s_off < segs.length) (hs_m : s_off ≤ MaxSeg)
    (hseg : segs.getD s_off [] = natToBitsLE w offset) (hoff : offset < 2 ^ w)
    (hWo_lt : 3 * (encodeWorkspace segs).length + offset < B)
    {len : ℕ} {τ₁ : ℕ → Bool} (htw : TapeWS τ₁ len B segs)
    (hclean : ∀ p, 3 * (encodeWorkspace segs).length ≤ p →
      p ≤ 3 * (encodeWorkspace segs).length + offset → τ₁ p = false) :
    let W := 3 * (encodeWorkspace segs).length
    let s_fin : Fin (MaxSeg + 1) := ⟨s_off, by omega⟩
    ∃ q_end, ∃ τ₂ : ℕ → Bool,
      TapeWS τ₂ (max len (W + offset + 1)) B (segs.set s_off (natToBitsLE w 0)) ∧
      (∀ p, W ≤ p → p < W + offset → τ₂ p = false) ∧
      τ₂ (W + offset) = b_out ∧
      (∀ p, W + offset < p → τ₂ p = τ₁ p) ∧
      StepExec (shuttleWrite MaxSeg) B (shuttleWriteEntry MaxSeg s_fin b_out) len τ₁ 0
        q_end (max len (W + offset + 1)) τ₂ 0
        ((offset + 2) * (16 * W + 2 * offset + 30)) := by
  intro W s_fin
  rcases cursorOp_place_spec htw (by omega) with ⟨htw_pl, he_pl⟩
  let τ_pl := Function.update τ₁ W true
  let len_pl := max len (W + 1)
  have hlen_pl_pos := TapeWS_pos htw_pl
  rcases shuttleLoop_spec MaxSeg B w s_fin b_out offset 0 segs len_pl τ_pl hs hoff
      (by omega) hseg htw_pl (fun i hi => by omega) (by dsimp only [τ_pl, W]; simp)
      (fun p hp1 hp2 => by
        dsimp only [τ_pl, W] at hp1 hp2 ⊢
        rw [Function.update_of_ne (by omega : p ≠ 3 * (encodeWorkspace segs).length)]
        exact hclean p (by omega) (by omega))
    with ⟨τ_end, htw_end, hpre_end, hcur_end, hout_end, he_lp⟩
  simp only [Nat.add_zero, Nat.zero_add] at htw_end hpre_end hcur_end hout_end he_lp
  have hlen_eq : max len_pl (W + offset + 1) = max len (W + offset + 1) := by
    dsimp only [len_pl]; omega
  rw [hlen_eq] at htw_end he_lp
  have he_seq := seq0_spec (f := fun _ => Sum.inl (wsDecJzEntry MaxSeg s_fin)) hlen_pl_pos he_pl he_lp
  have htime : 2 * (3 * (encodeWorkspace segs).length) + 2 + 1 +
      (offset + 1) * (16 * (3 * (encodeWorkspace segs).length) + 2 * offset + 30) ≤
      (offset + 2) * (16 * W + 2 * offset + 30) := by
    dsimp only [W]
    have : (offset + 2) * (16 * (3 * (encodeWorkspace segs).length) + 2 * offset + 30) =
        (16 * (3 * (encodeWorkspace segs).length) + 2 * offset + 30) +
        (offset + 1) * (16 * (3 * (encodeWorkspace segs).length) + 2 * offset + 30) := by ring
    omega
  have he_fam := (familyStep_spec (shuttleWriteFor MaxSeg) (s_fin, b_out) he_seq).weaken
    ((offset + 2) * (16 * W + 2 * offset + 30)) htime
  refine ⟨_, τ_end, htw_end, hpre_end, hcur_end, ?_, he_fam⟩
  intro p hp
  rw [hout_end p hp]
  exact Function.update_of_ne (by omega : p ≠ W) _ _

/-!
## Layer 3: Segment Bit Writer (`wsWriteBit`) and `RMProg`-to-`QCSD_DetTM` Output Compiler
-/

theorem MatchesWS_update_seg_set (segs : List (List Bool)) {s v : ℕ} (hs : s < segs.length)
    (hv : v < (segs.getD s []).length) (b_val : Bool)
    {σ : ℕ → BlkSym} (hws : MatchesWS σ segs) :
    MatchesWS (Function.update σ (segStart segs s + v) (blkData false b_val))
      (segs.set s ((segs.getD s []).set v b_val)) := by
  let newSeg := (segs.getD s []).set v b_val
  have hlen_new : newSeg.length = (segs.getD s []).length := by simp [newSeg]
  have hM := length_encodeWorkspace_set hs hlen_new
  have hs_set := segStart_set_eq segs s s newSeg hs hlen_new
  have hs' : s < (segs.set s newSeg).length := by simpa using hs
  have hget_new : (segs.set s newSeg).getD s [] = newSeg := getD_set_self_seg segs hs newSeg
  intro j hj
  rw [hM] at hj
  by_cases hjeq : j = segStart segs s + v
  · subst hjeq
    rw [Function.update_self]
    have hv' : v < ((segs.set s newSeg).getD s []).length := by rw [hget_new, hlen_new]; exact hv
    have hd := encodeWorkspace_seg_data (segs.set s newSeg) hs' hv'
    rw [hs_set, hget_new] at hd
    rw [hd]
    simp only [newSeg]
    rw [getD_set_eq _ _ _ _ _ hv]
    simp
  · rw [Function.update_of_ne hjeq, hws j hj]
    by_cases hin : segStart segs s ≤ j ∧ j < segStart segs s + (segs.getD s []).length
    · let idx := j - segStart segs s
      have hj_eq : j = segStart segs s + idx := by omega
      have hidx_ne : v ≠ idx := by omega
      have hidx_lt : idx < (segs.getD s []).length := by omega
      have hidx_lt' : idx < ((segs.set s newSeg).getD s []).length := by rw [hget_new, hlen_new]; exact hidx_lt
      have hd1 := encodeWorkspace_seg_data segs hs hidx_lt
      have hd2 := encodeWorkspace_seg_data (segs.set s newSeg) hs' hidx_lt'
      rw [hs_set, hget_new, ← hj_eq] at hd2
      rw [← hj_eq] at hd1
      rw [hd1, hd2]
      simp only [newSeg]
      rw [getD_set_eq _ _ _ _ _ hv]
      simp [hidx_ne.symm]
    · have hout : j < segStart segs s ∨ segStart segs s + (segs.getD s []).length ≤ j := by omega
      exact (encodeWorkspace_set_outside segs hs hlen_new hj hout).symm

def blkWriteAndClear (MaxSeg : ℕ) (b_val : Bool) : BlkStepFn (Fin (MaxSeg + 1) × Bool) :=
  fun (rem, rewinding) sym =>
    if rewinding then
      if sym = blkHome then none
      else some ((rem, true), sym, QCSD_HeadDir.left)
    else if sym = blkHome then
      some ((rem, false), blkHome, QCSD_HeadDir.right)
    else if hrem : 0 < rem.val then
      let prev : Fin (MaxSeg + 1) := ⟨rem.val - 1, by omega⟩
      if sym = blkSep then some ((prev, false), blkSep, QCSD_HeadDir.right)
      else some ((rem, false), sym, QCSD_HeadDir.right)
    else
      if !sym.1 then
        if sym.2.1 then some ((0, false), blkData false sym.2.2, QCSD_HeadDir.right)
        else some ((0, true), blkData false b_val, QCSD_HeadDir.left)
      else
        some ((0, true), sym, QCSD_HeadDir.left)

theorem blkWriteAndClear_spec (MaxSeg : ℕ) (b_val : Bool) (segs : List (List Bool)) {arrSeg v : ℕ}
    (harr : arrSeg < segs.length) (harr_m : arrSeg ≤ MaxSeg)
    (hv_lt : v < (segs.getD arrSeg []).length)
    (σ₀ : ℕ → BlkSym) (hws₀ : MatchesWS σ₀ segs) :
    let M_blk := (encodeWorkspace segs).length
    let σ_in := reMark (segMarkPred segs arrSeg v) σ₀
    let σ_out := Function.update σ₀ (segStart segs arrSeg + v) (blkData false b_val)
    MatchesWS σ_out (segs.set arrSeg ((segs.getD arrSeg []).set v b_val)) ∧
    BlkExec (blkWriteAndClear MaxSeg b_val) M_blk (⟨arrSeg, by omega⟩, false) σ_in 0
      (0, true) σ_out 0 (3 * M_blk) := by
  intro M_blk σ_in σ_out
  have hws_out : MatchesWS σ_out (segs.set arrSeg ((segs.getD arrSeg []).set v b_val)) :=
    MatchesWS_update_seg_set segs harr hv_lt b_val hws₀
  let go : ℕ → Fin (MaxSeg + 1) × Bool := fun r =>
    (⟨if h : r ≤ MaxSeg then r else 0, by split_ifs <;> omega⟩, false)
  have hgo_a : go arrSeg = (⟨arrSeg, by omega⟩, false) := by simp [go, harr_m]
  have hgo_0 : go 0 = (0, false) := by ext <;> simp [go]
  rcases blkGoToSeg_reMark_aux (blkWriteAndClear MaxSeg b_val) segs (segMarkPred segs arrSeg v) σ₀ hws₀ go harr
      (by simp [go, harr_m, blkWriteAndClear])
      (fun r hr m b => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        simp [go, hr1, blkWriteAndClear, blkHome, blkData, blkSep])
      (fun r hr => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        have hr0 : r ≤ MaxSeg := by omega
        have hpos : 0 < (if h : r + 1 ≤ MaxSeg then r + 1 else 0) := by simp [hr1]
        simp only [go, blkWriteAndClear, Bool.false_eq_true, ↓reduceIte,
          show blkSep ≠ blkHome by decide, dite_true, hpos]
        congr 1; ext <;> simp [hr1, hr0])
    with ⟨hiter_go, hbnd_go, hdir_go⟩
  rw [hgo_a, hgo_0] at hiter_go
  rw [hgo_a] at hbnd_go hdir_go
  have hsb := segStart_bound segs arrSeg harr
  have hs1 := segStart_pos segs arrSeg
  have hm_eq : min v (segs.getD arrSeg []).length = v := Nat.min_eq_left (Nat.le_of_lt hv_lt)
  have hclr_v : blkIter (blkWriteAndClear MaxSeg b_val) ((0, false), σ_in, segStart segs arrSeg) v =
      some ((0, false), σ₀, segStart segs arrSeg + v) ∧
    (∀ i ≤ v, ∀ q' σ' j',
      blkIter (blkWriteAndClear MaxSeg b_val) ((0, false), σ_in, segStart segs arrSeg) i = some (q', σ', j') → j' < M_blk) ∧
    (∀ i < v, ∀ q' σ' j' q'' sym' dir,
      blkIter (blkWriteAndClear MaxSeg b_val) ((0, false), σ_in, segStart segs arrSeg) i = some (q', σ', j') →
      blkWriteAndClear MaxSeg b_val q' (σ' j') = some (q'', sym', dir) →
      (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
    have haux : ∀ rem off, off + rem = v →
        blkIter (blkWriteAndClear MaxSeg b_val) ((0, false), reMark (segMarkRange segs arrSeg off v) σ₀, segStart segs arrSeg + off) rem =
          some ((0, false), σ₀, segStart segs arrSeg + v) ∧
        (∀ i ≤ rem, ∀ q' σ' j',
          blkIter (blkWriteAndClear MaxSeg b_val) ((0, false), reMark (segMarkRange segs arrSeg off v) σ₀, segStart segs arrSeg + off) i = some (q', σ', j') → j' < M_blk) ∧
        (∀ i < rem, ∀ q' σ' j' q'' sym' dir,
          blkIter (blkWriteAndClear MaxSeg b_val) ((0, false), reMark (segMarkRange segs arrSeg off v) σ₀, segStart segs arrSeg + off) i = some (q', σ', j') →
          blkWriteAndClear MaxSeg b_val q' (σ' j') = some (q'', sym', dir) →
          (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
      intro rem
      induction rem with
      | zero =>
        intro off hoff
        have hoff_eq : off = v := by omega
        subst off
        have hcur : reMark (segMarkRange segs arrSeg v v) σ₀ = σ₀ := by
          funext j; exact reMark_of_false σ₀ (by simp [segMarkRange])
        rw [hcur]
        refine ⟨rfl, ?_, fun i hi => by omega⟩
        intro i hi _ _ j' hi_eq
        obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi
        cases hi_eq; omega
      | succ rem ih =>
        intro off hoff
        have hoff_L : off < (segs.getD arrSeg []).length := by omega
        have hbase : σ₀ (segStart segs arrSeg + off) = blkData false ((segs.getD arrSeg []).getD off false) :=
          (hws₀ _ (by omega)).trans (encodeWorkspace_seg_data segs harr hoff_L)
        have hS_t : segMarkRange segs arrSeg off v (segStart segs arrSeg + off) = true := by
          simp only [segMarkRange, decide_eq_true_eq]; omega
        have hsym : reMark (segMarkRange segs arrSeg off v) σ₀ (segStart segs arrSeg + off) =
            blkData true ((segs.getD arrSeg []).getD off false) := by
          simp only [reMark, hbase, hS_t, blkData, Bool.not_false, Bool.and_self, ↓reduceIte]
        have hbs : blkWriteAndClear MaxSeg b_val (0, false)
            (reMark (segMarkRange segs arrSeg off v) σ₀ (segStart segs arrSeg + off)) =
            some ((0, false), blkData false ((segs.getD arrSeg []).getD off false), QCSD_HeadDir.right) := by
          rw [hsym]; simp [blkWriteAndClear, blkHome, blkData]
        have hupd : Function.update (reMark (segMarkRange segs arrSeg off v) σ₀) (segStart segs arrSeg + off)
            (blkData false ((segs.getD arrSeg []).getD off false)) =
            reMark (segMarkRange segs arrSeg (off + 1) v) σ₀ := by
          funext j
          by_cases hj : j = segStart segs arrSeg + off
          · subst hj
            have hS_f : segMarkRange segs arrSeg (off + 1) v (segStart segs arrSeg + off) = false := by
              simp only [segMarkRange, decide_eq_false_iff_not]; omega
            simp [reMark_of_false _ hS_f, hbase]
          · rw [Function.update_of_ne hj]
            have hpred_eq : segMarkRange segs arrSeg off v j = segMarkRange segs arrSeg (off + 1) v j := by
              simp only [segMarkRange]
              by_cases h1 : segStart segs arrSeg + off ≤ j ∧ j < segStart segs arrSeg + v
              · have h2 : segStart segs arrSeg + (off + 1) ≤ j ∧ j < segStart segs arrSeg + v := by omega
                simp [h1, h2]
              · have h2 : ¬(segStart segs arrSeg + (off + 1) ≤ j ∧ j < segStart segs arrSeg + v) := by omega
                simp [h1, h2]
            simp [reMark, hpred_eq]
        rcases ih (off + 1) (by omega) with ⟨hit, hbd, hdr⟩
        have hadd : segStart segs arrSeg + off + 1 = segStart segs arrSeg + (off + 1) := by omega
        refine ⟨?_, ?_, ?_⟩
        · simp only [blkIter, blkOnce, hbs, moveHead, hadd, hupd]; exact hit
        · intro i hi q' σ' j' hi_eq
          cases i with
          | zero => cases hi_eq; omega
          | succ i' =>
            simp only [blkIter, blkOnce, hbs, moveHead, hupd, hadd] at hi_eq
            exact hbd i' (by omega) q' σ' j' hi_eq
        · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
          cases i with
          | zero => cases hi_eq; rw [hbs] at hbs'; cases hbs'; exact ⟨by simp, fun _ => by omega⟩
          | succ i' =>
            simp only [blkIter, blkOnce, hbs, moveHead, hupd, hadd] at hi_eq
            exact hdr i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
    rcases haux v 0 (by omega) with ⟨ha1, ha2, ha3⟩
    have hpred_v : segMarkPred segs arrSeg v = segMarkRange segs arrSeg 0 v := by
      unfold segMarkPred; rw [hm_eq]
    dsimp only [σ_in]
    rw [hpred_v]
    simp only [Nat.add_zero] at ha1 ha2 ha3
    exact ⟨ha1, ha2, ha3⟩
  rcases hclr_v with ⟨hiter_cl, hbnd_cl, hdir_cl⟩
  have hbase_v : σ₀ (segStart segs arrSeg + v) = blkData false ((segs.getD arrSeg []).getD v false) :=
    (hws₀ _ (by omega)).trans (encodeWorkspace_seg_data segs harr hv_lt)
  have hbs_v : blkWriteAndClear MaxSeg b_val (0, false) (σ₀ (segStart segs arrSeg + v)) =
      some ((0, true), blkData false b_val, QCSD_HeadDir.left) := by
    rw [hbase_v]; simp [blkWriteAndClear, blkHome, blkData]
  have hturn : blkIter (blkWriteAndClear MaxSeg b_val) ((0, false), σ₀, segStart segs arrSeg + v) 1 =
      some ((0, true), σ_out, segStart segs arrSeg + v - 1) := by
    simp [blkIter, blkOnce, hbs_v, moveHead, σ_out]
  let j_rw := segStart segs arrSeg + v - 1
  have hM_out : (encodeWorkspace (segs.set arrSeg ((segs.getD arrSeg []).set v b_val))).length = M_blk :=
    length_encodeWorkspace_set harr (by simp)
  have h0_out : σ_out 0 = blkHome := (hws_out 0 (by omega)).trans (encodeWorkspace_getD_zero _)
  have hne_out : ∀ i, 1 ≤ i → i ≤ j_rw → σ_out i ≠ blkHome := by
    intro i hi1 hi2; rw [hws_out i (by omega)]; exact encodeWorkspace_ne_home _ hi1 (by omega)
  rcases blkRewind_aux (blkWriteAndClear MaxSeg b_val) M_blk (0, true)
      (by simp [blkWriteAndClear]) (fun sym hne => by simp [blkWriteAndClear, hne])
      j_rw σ_out (by omega) h0_out hne_out
    with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
  refine ⟨hws_out, segStart segs arrSeg + v + 1 + j_rw, by omega, ?_, hnone_rw, ?_, ?_⟩
  · rw [blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
        hiter_cl, Option.bind_some, hturn, Option.bind_some, hiter_rw]
  · intro i hi q' σ' j' hi_eq
    by_cases hi1 : i ≤ segStart segs arrSeg
    · rcases blkIter_le_some hi1 hiter_go with ⟨⟨qi, σi, ji⟩, hsub⟩
      rw [hsub] at hi_eq; cases hi_eq; exact hbnd_go i hi1 q' σ' j' hsub
    · by_cases hi2 : i ≤ segStart segs arrSeg + v
      · have heq : i = segStart segs arrSeg + (i - segStart segs arrSeg) := by omega
        rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
        exact hbnd_cl (i - segStart segs arrSeg) (by omega) q' σ' j' hi_eq
      · have heq : i = segStart segs arrSeg + v + 1 + (i - (segStart segs arrSeg + v + 1)) := by omega
        rw [heq, blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
            hiter_cl, Option.bind_some, hturn, Option.bind_some] at hi_eq
        exact hbnd_rw (i - (segStart segs arrSeg + v + 1)) (by omega) q' σ' j' hi_eq
  · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
    by_cases hi1 : i < segStart segs arrSeg
    · exact hdir_go i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
    · by_cases hi2 : i < segStart segs arrSeg + v
      · have heq : i = segStart segs arrSeg + (i - segStart segs arrSeg) := by omega
        rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
        exact hdir_cl (i - segStart segs arrSeg) (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
      · by_cases hi3 : i = segStart segs arrSeg + v
        · subst hi3
          rw [blkIter_add, hiter_go, Option.bind_some, hiter_cl] at hi_eq
          cases hi_eq; rw [hbs_v] at hbs'; cases hbs'
          exact ⟨fun _ => by omega, by simp⟩
        · have heq : i = segStart segs arrSeg + v + 1 + (i - (segStart segs arrSeg + v + 1)) := by omega
          rw [heq, blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
              hiter_cl, Option.bind_some, hturn, Option.bind_some] at hi_eq
          exact hdir_rw (i - (segStart segs arrSeg + v + 1)) (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

abbrev WsWriteLoopQ (MaxSeg : ℕ) : Type :=
  WsDecJzQ MaxSeg ⊕
  (LiftBlkQ (Fin (MaxSeg + 1) × Bool) ⊕ LiftBlkQ (Fin (MaxSeg + 1) × Bool))

def wsWriteBody (MaxSeg : ℕ) (arrSeg : Fin (MaxSeg + 1)) (b_val : Bool) : StepFn (WsWriteLoopQ MaxSeg) :=
  seq0 (wsDecJz MaxSeg)
    (sumStep (liftBlockStep (blkWriteAndClear MaxSeg b_val)) (liftBlockStep (blkMarkNext MaxSeg)))
    (fun q => if wsDecJzWasZero q
      then Sum.inl (liftBlkEntry (arrSeg, false))
      else Sum.inr (liftBlkEntry (arrSeg, false)))

def wsWriteNext (MaxSeg : ℕ) (tmpSeg : Fin (MaxSeg + 1)) : WsWriteLoopQ MaxSeg → Option (WsWriteLoopQ MaxSeg)
  | Sum.inr (Sum.inr _) => some (Sum.inl (wsDecJzEntry MaxSeg tmpSeg))
  | _ => none

def wsWriteLoop (MaxSeg : ℕ) (arrSeg tmpSeg : Fin (MaxSeg + 1)) (b_val : Bool) : StepFn (WsWriteLoopQ MaxSeg) :=
  loop0 (wsWriteBody MaxSeg arrSeg b_val) (wsWriteNext MaxSeg tmpSeg)

abbrev WsWriteBitInnerQ (MaxSeg : ℕ) : Type :=
  WsCopyInnerQ MaxSeg ⊕ WsWriteLoopQ MaxSeg

def wsWriteBitFor (MaxSeg : ℕ) (p : SegQuad MaxSeg × Bool) : StepFn (WsWriteBitInnerQ MaxSeg) :=
  seq0 (wsCopyFor MaxSeg (p.1.2.2.1, p.1.2.1, p.1.2.2.2))
    (wsWriteLoop MaxSeg p.1.1 p.1.2.2.1 p.2)
    (fun _ => Sum.inl (wsDecJzEntry MaxSeg p.1.2.2.1))

def wsWriteBit (MaxSeg : ℕ) : StepFn ((SegQuad MaxSeg × Bool) × WsWriteBitInnerQ MaxSeg) :=
  familyStep (wsWriteBitFor MaxSeg)

def wsWriteBitEntry (MaxSeg : ℕ) (qd : SegQuad MaxSeg) (b_val : Bool) :
    (SegQuad MaxSeg × Bool) × WsWriteBitInnerQ MaxSeg :=
  ((qd, b_val), Sum.inl (Sum.inl (wsZeroEntry MaxSeg qd.2.2.1)))

theorem wsWriteLoop_spec (MaxSeg B w : ℕ) (arrSeg tmpSeg : Fin (MaxSeg + 1)) (b_val : Bool)
    (h_at : arrSeg.val < tmpSeg.val) :
    ∀ rem k (segs : List (List Bool)) len (τ₁ : ℕ → Bool),
      arrSeg.val < segs.length → tmpSeg.val < segs.length →
      k + rem < (segs.getD arrSeg.val []).length →
      rem < 2 ^ w →
      segs.getD tmpSeg.val [] = natToBitsLE w rem →
      TapeMarkedWS τ₁ len B segs arrSeg.val k →
      ∃ τ₂ : ℕ → Bool,
        TapeWS τ₂ len B ((segs.set tmpSeg.val (natToBitsLE w 0)).set
          arrSeg.val ((segs.getD arrSeg.val []).set (k + rem) b_val)) ∧
        (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
        StepExec (wsWriteLoop MaxSeg arrSeg tmpSeg b_val) B
          (Sum.inl (wsDecJzEntry MaxSeg tmpSeg)) len τ₁ 0
          (Sum.inr (Sum.inl (liftBlkExit (0, true)))) len τ₂ 0
          ((rem + 1) * (63 * (encodeWorkspace segs).length + 20)) := by
  intro rem
  induction rem with
  | zero =>
    intro k segs len τ₁ ha ht hkL hrem hseg_t htm
    have hlen_pos : 1 ≤ len := by
      rcases htm with ⟨_, hW_le, _, _⟩
      have : 1 ≤ (encodeWorkspace segs).length := by simp [encodeWorkspace]
      omega
    rcases wsDecJz_marked_spec MaxSeg B segs h_at ht (Nat.le_of_lt_succ tmpSeg.isLt) hseg_t hrem htm
      with ⟨q_dec, τ_mid, hz_out, htm_mid, hout_mid, he_dec⟩
    simp only [decide_true, ↓reduceIte, Nat.add_zero] at hz_out htm_mid hkL ⊢
    rcases htm_mid with ⟨hsegs, hW_le, hlen_B, σ₀, hws₀, hread_mid⟩
    rcases blkWriteAndClear_spec MaxSeg b_val segs ha (Nat.le_of_lt_succ arrSeg.isLt) hkL σ₀ hws₀
      with ⟨hws_out, hexec_wc⟩
    rw [← hread_mid] at hexec_wc
    rcases liftBlockStep_spec (blkWriteAndClear MaxSeg b_val) B (encodeWorkspace segs).length len τ_mid
        (arrSeg, false) (0, true) _ 0 0
        (3 * (encodeWorkspace segs).length) hW_le hlen_B hexec_wc
      with ⟨τ₂, hread₂, hout₂, k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
    have he_wc := sumStep_inl_spec (liftBlockStep (blkWriteAndClear MaxSeg b_val))
      (liftBlockStep (blkMarkNext MaxSeg)) ⟨k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
    have hbody := seq0_spec (f := fun q => if wsDecJzWasZero q
      then Sum.inl (liftBlkEntry (arrSeg, false))
      else Sum.inr (liftBlkEntry (arrSeg, false))) hlen_pos he_dec (by rw [hz_out]; exact he_wc)
    have hdone := (loop0_done (next := wsWriteNext MaxSeg tmpSeg) hbody rfl).weaken
      ((0 + 1) * (63 * (encodeWorkspace segs).length + 20)) (by omega)
    have hset_noop : segs.set tmpSeg.val (natToBitsLE w 0) = segs := by
      apply List.ext_getElem (by simp)
      intro idx hk1 hk2
      rw [List.getElem_set]
      split_ifs with h1
      · subst h1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some] at hseg_t
        exact hseg_t.symm
      · rfl
    rw [hset_noop]
    have hM_out : (encodeWorkspace (segs.set arrSeg.val ((segs.getD arrSeg.val []).set k b_val))).length =
        (encodeWorkspace segs).length := length_encodeWorkspace_set ha (by simp)
    exact ⟨τ₂, ⟨by simp [hsegs], by rw [hM_out]; exact hW_le, hlen_B, hread₂.symm ▸ hws_out⟩,
      fun p hp => (hout₂ p hp).trans (hout_mid p hp), hdone⟩
  | succ rem ih =>
    intro k segs len τ₁ ha ht hkL hrem hseg_t htm
    have hlen_pos : 1 ≤ len := by
      rcases htm with ⟨_, hW_le, _, _⟩
      have : 1 ≤ (encodeWorkspace segs).length := by simp [encodeWorkspace]
      omega
    rcases wsDecJz_marked_spec MaxSeg B segs h_at ht (Nat.le_of_lt_succ tmpSeg.isLt) hseg_t hrem htm
      with ⟨q_dec, τ₁', hz_out, htm₁, hout₁, he_dec⟩
    simp only [Nat.add_one_ne_zero, decide_false, ↓reduceIte, Nat.add_sub_cancel] at hz_out htm₁
    let segs₁ := segs.set tmpSeg.val (natToBitsLE w rem)
    have hM₁ : (encodeWorkspace segs₁).length = (encodeWorkspace segs).length :=
      length_encodeWorkspace_set ht (by rw [hseg_t, length_natToBitsLE, length_natToBitsLE])
    rcases htm₁ with ⟨hsegs₁, hW_le₁, hlen_B₁, σ₀, hws₀, hread₁'⟩
    have ha₁ : arrSeg.val < segs₁.length := by simpa [segs₁] using ha
    have hexec_mk := blkMarkNext_spec MaxSeg segs₁ (k := k) ha₁ (Nat.le_of_lt_succ arrSeg.isLt) σ₀ hws₀
    rw [← hread₁'] at hexec_mk
    rcases liftBlockStep_spec (blkMarkNext MaxSeg) B (encodeWorkspace segs₁).length len τ₁'
        (arrSeg, false) (0, true) (reMark (segMarkPred segs₁ arrSeg.val (k + 1)) σ₀) 0 0
        (3 * (encodeWorkspace segs₁).length) hW_le₁ hlen_B₁ hexec_mk
      with ⟨τ₂', hread₂', hout₂', k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
    rw [hM₁] at hout₂' hk₂
    have he_mk := sumStep_inr_spec (liftBlockStep (blkWriteAndClear MaxSeg b_val))
      (liftBlockStep (blkMarkNext MaxSeg)) ⟨k₂, by omega, hiter₂, hexit₂, hbnd₂⟩
    have hbody := seq0_spec (f := fun q => if wsDecJzWasZero q
      then Sum.inl (liftBlkEntry (arrSeg, false))
      else Sum.inr (liftBlkEntry (arrSeg, false))) hlen_pos he_dec (by rw [hz_out]; exact he_mk)
    have htm₂ : TapeMarkedWS τ₂' len B segs₁ arrSeg.val (k + 1) :=
      ⟨hsegs₁, hW_le₁, hlen_B₁, σ₀, hws₀, hread₂'⟩
    have hget_arr : segs₁.getD arrSeg.val [] = segs.getD arrSeg.val [] :=
      getD_set_ne_seg segs (by omega : tmpSeg.val ≠ arrSeg.val) _
    rcases ih (k + 1) segs₁ len τ₂' ha₁ (by simpa [segs₁] using ht)
        (by rw [hget_arr]; omega) (by omega) (getD_set_self_seg segs ht _) htm₂
      with ⟨τ_end, htw_end, hout_end, he_rest⟩
    rw [hM₁] at hout_end he_rest
    have hidx_eq : k + 1 + rem = k + (rem + 1) := by omega
    have hsegs_eq : (segs₁.set tmpSeg.val (natToBitsLE w 0)).set arrSeg.val
        ((segs₁.getD arrSeg.val []).set (k + 1 + rem) b_val) =
      (segs.set tmpSeg.val (natToBitsLE w 0)).set arrSeg.val
        ((segs.getD arrSeg.val []).set (k + (rem + 1)) b_val) := by
      rw [hget_arr, hidx_eq]; simp [segs₁]
    rw [hsegs_eq] at htw_end
    let M := (encodeWorkspace segs).length
    have hstep := (loop0_step (next := wsWriteNext MaxSeg tmpSeg) hlen_pos hbody rfl he_rest).weaken
      ((rem + 1 + 1) * (63 * M + 20)) (by
        have : (rem + 1 + 1) * (63 * M + 20) = (63 * M + 20) + (rem + 1) * (63 * M + 20) := by ring
        dsimp only [M] at *; omega)
    exact ⟨τ_end, htw_end, fun p hp => (hout_end p hp).trans ((hout₂' p hp).trans (hout₁ p hp)), hstep⟩

theorem wsWriteBit_spec (MaxSeg B : ℕ) (segs : List (List Bool)) {arr idx tmp tmp2 w v : ℕ} (b_val : Bool)
    (ha : arr < segs.length) (hi : idx < segs.length) (ht : tmp < segs.length) (ht2 : tmp2 < segs.length)
    (ha_m : arr ≤ MaxSeg) (hi_m : idx ≤ MaxSeg) (ht_m : tmp ≤ MaxSeg) (ht2_m : tmp2 ≤ MaxSeg)
    (h_at : arr < tmp) (h_ti : tmp ≠ idx) (h_tt2 : tmp ≠ tmp2) (h_it2 : idx ≠ tmp2) (h_at2 : arr ≠ tmp2)
    (hv_len : v < (segs.getD arr []).length)
    (hseg_i : segs.getD idx [] = natToBitsLE w v)
    (hlen_t : (segs.getD tmp []).length = w)
    (hlen_t2 : (segs.getD tmp2 []).length = w)
    (hv : v < 2 ^ w)
    {len : ℕ} {τ₁ : ℕ → Bool} (htw : TapeWS τ₁ len B segs) :
    let qd : SegQuad MaxSeg := (⟨arr, by omega⟩, ⟨idx, by omega⟩, ⟨tmp, by omega⟩, ⟨tmp2, by omega⟩)
    ∃ q_end, ∃ τ₂ : ℕ → Bool,
      TapeWS τ₂ len B (((segs.set arr ((segs.getD arr []).set v b_val)).set
        tmp (natToBitsLE w 0)).set tmp2 (natToBitsLE w 0)) ∧
      (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (wsWriteBit MaxSeg) B (wsWriteBitEntry MaxSeg qd b_val) len τ₁ 0
        q_end len τ₂ 0 ((v + 2) * (220 * (encodeWorkspace segs).length + 80)) := by
  intro qd
  have hlen_pos := TapeWS_pos htw
  rcases wsCopyFor_spec MaxSeg B segs ht hi ht2 ht_m hi_m ht2_m h_ti h_tt2 h_it2 hlen_t hseg_i hlen_t2 hv htw
    with ⟨q_cp, τ_cp, htw_cp, hout_cp, he_cp_inner⟩
  let segs_cp := (segs.set tmp (natToBitsLE w v)).set tmp2 (natToBitsLE w 0)
  have hM_cp : (encodeWorkspace segs_cp).length = (encodeWorkspace segs).length := by
    have h1 := length_encodeWorkspace_set ht (newSeg := natToBitsLE w v) (by rw [hlen_t, length_natToBitsLE])
    have h2 := length_encodeWorkspace_set (segs := segs.set tmp (natToBitsLE w v)) (s := tmp2)
      (newSeg := natToBitsLE w 0) (by simpa using ht2)
      (by rw [getD_set_ne_seg segs h_tt2, hlen_t2, length_natToBitsLE])
    exact h2.trans h1
  have hget_arr : segs_cp.getD qd.1.val [] = segs.getD arr [] := by
    dsimp only [segs_cp, qd]
    rw [getD_set_ne_seg _ h_at2.symm, getD_set_ne_seg _ (by omega : tmp ≠ arr)]
  have htm_cp : TapeMarkedWS τ_cp len B segs_cp arr 0 := TapeMarkedWS_zero_iff.mpr htw_cp
  rcases wsWriteLoop_spec MaxSeg B w qd.1 qd.2.2.1 b_val h_at v 0 segs_cp len τ_cp
      (by simpa [segs_cp] using ha) (by simpa [segs_cp] using ht)
      (by rw [hget_arr]; simpa using hv_len) hv
      (by dsimp only [segs_cp, qd]; rw [getD_set_ne_seg _ h_tt2.symm, getD_set_self_seg _ ht])
      htm_cp
    with ⟨τ_end, htw_end, hout_end, he_wl⟩
  rw [hM_cp] at hout_end he_wl
  have hsegs_final : (segs_cp.set qd.2.2.1.val (natToBitsLE w 0)).set qd.1.val
      ((segs_cp.getD qd.1.val []).set (0 + v) b_val) =
    ((segs.set arr ((segs.getD arr []).set v b_val)).set tmp (natToBitsLE w 0)).set tmp2 (natToBitsLE w 0) := by
    rw [hget_arr, Nat.zero_add]
    apply List.ext_getElem (by simp [segs_cp])
    intro k hk1 hk2
    simp only [segs_cp, qd, List.getElem_set]
    by_cases h1 : arr = k
    · subst k; simp [show tmp ≠ arr by omega, show tmp2 ≠ arr by omega]
    · by_cases h2 : tmp = k
      · subst k; simp [h1, h_tt2.symm]
      · by_cases h3 : tmp2 = k
        · subst k; simp [h1, h2]
        · simp [h1, h2, h3]
  rw [hsegs_final] at htw_end
  have he_seq := seq0_spec (f := fun _ => Sum.inl (wsDecJzEntry MaxSeg qd.2.2.1)) hlen_pos he_cp_inner he_wl
  let M := (encodeWorkspace segs).length
  have htime : (v + 2) * (150 * M + 50) + 1 + (v + 1) * (63 * M + 20) ≤ (v + 2) * (220 * M + 80) := by
    calc (v + 2) * (150 * M + 50) + 1 + (v + 1) * (63 * M + 20)
        ≤ (v + 2) * (150 * M + 50) + 1 + (v + 2) * (63 * M + 20) := by
          have := Nat.mul_le_mul_right (63 * M + 20) (show v + 1 ≤ v + 2 by omega)
          omega
      _ = 1 + (v + 2) * (213 * M + 70) := by ring
      _ ≤ (v + 2) * (220 * M + 80) := by
          have : (v + 2) * (220 * M + 80) = (v + 2) * (213 * M + 70) + (v + 2) * (7 * M + 10) := by ring
          have : 1 ≤ (v + 2) * (7 * M + 10) := Nat.mul_pos (by omega) (by omega)
          omega
  have he_fam := (familyStep_spec (wsWriteBitFor MaxSeg) (qd, b_val) he_seq).weaken
    ((v + 2) * (220 * M + 80)) htime
  exact ⟨_, τ_end, htw_end, fun p hp => (hout_end p hp).trans (hout_cp p hp), he_fam⟩

/-!
### Phase 2: Compiling `Branch6Encoder.RMProg` to `StepFn` and `QCSD_DetTM`
-/

def WSRMInv (base R w L_buf M_blk B : ℕ) (seg_inp : ℕ) (inp : List Bool)
    (τ : ℕ → Bool) (len : ℕ) (reg : RegState R) (emitted : List Bool) (sys1Val : ℕ) : Prop :=
  ∃ segs : List (List Bool),
    segs.length = base + R + 6 ∧
    (encodeWorkspace segs).length = M_blk ∧
    TapeWS τ len B segs ∧
    (∀ i, (segs.getD seg_inp []).getD i false = inp.getD i false) ∧
    (∀ r : Fin R, segs.getD (base + r.val) [] = natToBitsLE w (reg r)) ∧
    segs.getD (base + R) [] = natToBitsLE w emitted.length ∧
    segs.getD (base + R + 1) [] = natToBitsLE w sys1Val ∧
    segs.getD (base + R + 2) [] = emitted ++ List.replicate (L_buf - emitted.length) false ∧
    emitted.length ≤ L_buf ∧
    (segs.getD (base + R + 3) []).length = w ∧
    (segs.getD (base + R + 4) []).length = w ∧
    segs.getD (base + R + 5) [] = natToBitsLE w (3 * M_blk)

abbrev WsEmitBitInnerQ (MaxSeg : ℕ) : Type :=
  ((SegQuad MaxSeg × Bool) × WsWriteBitInnerQ MaxSeg) ⊕ LiftBlkQ (Fin (MaxSeg + 1) × Bool)

def wsEmitBitFor (base R : ℕ) (_b : Bool) : StepFn (WsEmitBitInnerQ (base + R + 5)) :=
  let MaxSeg := base + R + 5
  seq0 (wsWriteBit MaxSeg) (wsInc MaxSeg)
    (fun _ => wsIncEntry MaxSeg ⟨base + R, by omega⟩)

def wsEmitBit (base R : ℕ) : StepFn (Bool × WsEmitBitInnerQ (base + R + 5)) :=
  familyStep (wsEmitBitFor base R)

def wsEmitBitEntry (base R : ℕ) (b : Bool) : Bool × WsEmitBitInnerQ (base + R + 5) :=
  let MaxSeg := base + R + 5
  let qd : SegQuad MaxSeg :=
    (⟨base + R + 2, by omega⟩, ⟨base + R, by omega⟩, ⟨base + R + 3, by omega⟩, ⟨base + R + 4, by omega⟩)
  (b, Sum.inl (wsWriteBitEntry MaxSeg qd b))

theorem append_replicate_set_end (emitted : List Bool) (L_buf : ℕ) (b : Bool)
    (hlt : emitted.length < L_buf) :
    (emitted ++ List.replicate (L_buf - emitted.length) false).set emitted.length b =
      (emitted ++ [b]) ++ List.replicate (L_buf - (emitted ++ [b]).length) false := by
  induction emitted generalizing L_buf with
  | nil =>
    cases L_buf with
    | zero => simp at hlt
    | succ m => simp [List.replicate_succ]
  | cons x xs ih =>
    cases L_buf with
    | zero => simp at hlt
    | succ m =>
      have hlt' : xs.length < m := by simp at hlt; omega
      simpa [Nat.succ_sub_succ_eq_sub] using congrArg (x :: ·) (ih m hlt')

theorem wsEmitBit_spec (base R w L_buf M_blk B seg_inp : ℕ) (_h_inp : seg_inp < base)
    (inp : List Bool) (b : Bool) {len sys1Val : ℕ} {τ₁ : ℕ → Bool} {reg : RegState R} {emitted : List Bool}
    (hinv : WSRMInv base R w L_buf M_blk B seg_inp inp τ₁ len reg emitted sys1Val)
    (hemit_lt : emitted.length < L_buf)
    (hL_pow : L_buf < 2 ^ w) :
    ∃ q_end, ∃ τ₂ : ℕ → Bool,
      WSRMInv base R w L_buf M_blk B seg_inp inp τ₂ len reg (emitted ++ [b]) sys1Val ∧
      (∀ p, 3 * M_blk ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (wsEmitBit base R) B (wsEmitBitEntry base R b) len τ₁ 0
        q_end len τ₂ 0 ((L_buf + 2) * (250 * M_blk + 100)) := by
  rcases hinv with ⟨segs, hlen_s, hM, htw, hinp_eq, hregs, houtL, hsys1, houtB, _, htmp1, htmp2, hW⟩
  have hlen_pos := TapeWS_pos htw
  let MaxSeg := base + R + 5
  have hv_len : emitted.length < (segs.getD (base + R + 2) []).length := by
    rw [houtB, List.length_append, List.length_replicate]; omega
  rcases wsWriteBit_spec MaxSeg B segs (arr := base + R + 2) (idx := base + R)
      (tmp := base + R + 3) (tmp2 := base + R + 4) (w := w) (v := emitted.length) b
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      hv_len houtL htmp1 htmp2 (by omega) htw
    with ⟨q_wb, τ_wb, htw_wb, hout_wb, he_wb⟩
  rw [hM] at hout_wb he_wb
  let segs_wb0 := segs.set (base + R + 2) ((segs.getD (base + R + 2) []).set emitted.length b)
  let segs_wb1 := segs_wb0.set (base + R + 3) (natToBitsLE w 0)
  let segs₁ := segs_wb1.set (base + R + 4) (natToBitsLE w 0)
  have hM₁ : (encodeWorkspace segs₁).length = M_blk := by
    have h1 := length_encodeWorkspace_set (segs := segs) (s := base + R + 2)
      (newSeg := (segs.getD (base + R + 2) []).set emitted.length b) (by omega) (by simp)
    have h2 := length_encodeWorkspace_set (segs := segs_wb0) (s := base + R + 3)
      (newSeg := natToBitsLE w 0) (by simp [segs_wb0]; omega)
      (by dsimp only [segs_wb0]; rw [getD_set_ne_seg _ (by omega), htmp1, length_natToBitsLE])
    have h3 := length_encodeWorkspace_set (segs := segs_wb1)
      (s := base + R + 4) (newSeg := natToBitsLE w 0) (by simp [segs_wb1, segs_wb0]; omega)
      (by dsimp only [segs_wb1, segs_wb0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), htmp2, length_natToBitsLE])
    exact h3.trans (h2.trans (h1.trans hM))
  have houtL₁ : segs₁.getD (base + R) [] = natToBitsLE w emitted.length := by
    dsimp only [segs₁, segs_wb1, segs_wb0]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), houtL]
  rcases wsInc_spec MaxSeg B segs₁ (s := base + R) (w := w) (v := emitted.length)
      (by simp [segs₁, segs_wb1, segs_wb0]; omega) (by omega) houtL₁ (by omega) htw_wb
    with ⟨τ₂, htw₂, hout₂, he_inc⟩
  rw [hM₁] at hout₂ he_inc
  let segs₂ := segs₁.set (base + R) (natToBitsLE w (emitted.length + 1))
  have hM₂ : (encodeWorkspace segs₂).length = M_blk :=
    (length_encodeWorkspace_set (by simp [segs₁, segs_wb1, segs_wb0]; omega)
      (by rw [houtL₁, length_natToBitsLE, length_natToBitsLE])).trans hM₁
  have he_seq := seq0_spec (f := fun _ => wsIncEntry MaxSeg ⟨base + R, by omega⟩) hlen_pos he_wb he_inc
  have htime : (emitted.length + 2) * (220 * M_blk + 80) + 1 + (21 * M_blk + 4) ≤
      (L_buf + 2) * (250 * M_blk + 100) := by
    calc (emitted.length + 2) * (220 * M_blk + 80) + 1 + (21 * M_blk + 4)
        ≤ (L_buf + 2) * (220 * M_blk + 80) + (21 * M_blk + 5) := by
          have := Nat.mul_le_mul_right (220 * M_blk + 80) (show emitted.length + 2 ≤ L_buf + 2 by omega)
          omega
      _ ≤ (L_buf + 2) * (250 * M_blk + 100) := by
          have : (L_buf + 2) * (250 * M_blk + 100) =
              (L_buf + 2) * (220 * M_blk + 80) + (L_buf + 2) * (30 * M_blk + 20) := by ring
          have : 21 * M_blk + 5 ≤ (L_buf + 2) * (30 * M_blk + 20) := by
            have := Nat.le_mul_of_pos_left (30 * M_blk + 20) (show 0 < L_buf + 2 by omega)
            omega
          omega
  have he_fam := (familyStep_spec (wsEmitBitFor base R) b he_seq).weaken _ htime
  refine ⟨_, τ₂, ⟨segs₂, by simp [segs₂, segs₁, segs_wb1, segs_wb0, hlen_s], hM₂, htw₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun p hp => (hout₂ p hp).trans (hout_wb p hp), he_fam⟩
  · intro i
    dsimp only [segs₂, segs₁, segs_wb1, segs_wb0]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
        getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]
    exact hinp_eq i
  · intro r
    dsimp only [segs₂, segs₁, segs_wb1, segs_wb0]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
        getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]
    exact hregs r
  · dsimp only [segs₂]
    rw [getD_set_self_seg _ (by simp [segs₁, segs_wb1, segs_wb0]; omega)]
    simp
  · dsimp only [segs₂, segs₁, segs_wb1, segs_wb0]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
        getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]
    exact hsys1
  · dsimp only [segs₂, segs₁, segs_wb1, segs_wb0]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
        getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by omega), houtB]
    exact append_replicate_set_end emitted L_buf b hemit_lt
  · simp; omega
  · dsimp only [segs₂, segs₁, segs_wb1, segs_wb0]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
        getD_set_self_seg _ (by simp; omega), length_natToBitsLE]
  · dsimp only [segs₂, segs₁, segs_wb1, segs_wb0]
    rw [getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by simp; omega), length_natToBitsLE]
  · dsimp only [segs₂, segs₁, segs_wb1, segs_wb0]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
        getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), hW]

abbrev RMSubQ (base R : ℕ) : Type :=
  Unit ⊕
  (LiftBlkQ (Fin (base + R + 5 + 1) × Bool) ⊕
  (LiftBlkQ (Fin (base + R + 5 + 1) × Bool) ⊕
  (WsDecJzQ (base + R + 5) ⊕
  ((SegTriple (base + R + 5) × WsCopyInnerQ (base + R + 5)) ⊕
  ((SegQuad (base + R + 5) × WsReadBitInnerQ (base + R + 5)) ⊕
  (Bool × WsEmitBitInnerQ (base + R + 5)))))))

def rmSubStep (base R : ℕ) : StepFn (RMSubQ base R) :=
  let MaxSeg := base + R + 5
  sumStep (nopStep Unit)
    (sumStep (wsZero MaxSeg)
      (sumStep (wsInc MaxSeg)
        (sumStep (wsDecJz MaxSeg)
          (sumStep (wsCopy MaxSeg)
            (sumStep (wsReadBit MaxSeg) (wsEmitBit base R))))))

def rmSubEntry (base R seg_inp : ℕ) {Q : Type} (M : RMProg R Q) (q : Q) : RMSubQ base R :=
  let MaxSeg := base + R + 5
  let s_in : Fin (MaxSeg + 1) := ⟨if seg_inp ≤ MaxSeg then seg_inp else 0, by split_ifs <;> omega⟩
  match M q with
  | none => Sum.inl ()
  | some (Sum.inl (r, _)) =>
      Sum.inr (Sum.inl (wsZeroEntry MaxSeg ⟨base + r.val, by omega⟩))
  | some (Sum.inr (Sum.inl (r, _))) =>
      Sum.inr (Sum.inr (Sum.inl (wsIncEntry MaxSeg ⟨base + r.val, by omega⟩)))
  | some (Sum.inr (Sum.inr (Sum.inl (r, _, _)))) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inl (wsDecJzEntry MaxSeg ⟨base + r.val, by omega⟩))))
  | some (Sum.inr (Sum.inr (Sum.inr (Sum.inl (dst, src, _))))) =>
      if dst = src then Sum.inl ()
      else Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
        (wsCopyEntry MaxSeg (⟨base + dst.val, by omega⟩, ⟨base + src.val, by omega⟩, ⟨base + R + 3, by omega⟩))))))
  | some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (rIdx, _, _)))))) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
        (wsReadBitEntry MaxSeg (s_in, ⟨base + rIdx.val, by omega⟩, ⟨base + R + 3, by omega⟩, ⟨base + R + 4, by omega⟩)))))))
  | some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (b, _)))))) =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (wsEmitBitEntry base R b))))))

def rmSubWasZero {base R : ℕ} : RMSubQ base R → Bool
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl q_dz))) => wsDecJzWasZero q_dz
  | _ => false

def rmSubReadRes {base R : ℕ} : RMSubQ base R → Bool
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q_rb))))) => wsReadBitResult q_rb
  | _ => false

def simRMNext (base R seg_inp : ℕ) {Q : Type} (M : RMProg R Q) :
    Q × RMSubQ base R → Option (Q × RMSubQ base R) :=
  fun (q, sub) =>
    match M q with
    | none => none
    | some (Sum.inl (_, next)) => some (next, rmSubEntry base R seg_inp M next)
    | some (Sum.inr (Sum.inl (_, next))) => some (next, rmSubEntry base R seg_inp M next)
    | some (Sum.inr (Sum.inr (Sum.inl (_, qz, qnz)))) =>
        let next := if rmSubWasZero sub then qz else qnz
        some (next, rmSubEntry base R seg_inp M next)
    | some (Sum.inr (Sum.inr (Sum.inr (Sum.inl (_, _, next))))) =>
        some (next, rmSubEntry base R seg_inp M next)
    | some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (_, qf, qt)))))) =>
        let next := if rmSubReadRes sub then qt else qf
        some (next, rmSubEntry base R seg_inp M next)
    | some (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (_, next)))))) =>
        some (next, rmSubEntry base R seg_inp M next)

def simRMLoop (base R seg_inp : ℕ) {Q : Type} (M : RMProg R Q) : StepFn (Q × RMSubQ base R) :=
  loop0 (familyStep (fun (_ : Q) => rmSubStep base R)) (simRMNext base R seg_inp M)

theorem simRMOneStep_spec (base R w L_buf M_blk B seg_inp Vmax : ℕ)
    (h_inp : seg_inp < base) (hV_pow : Vmax < 2 ^ w) (hL_pow : L_buf < 2 ^ w)
    {Q : Type} (M : RMProg R Q) (inp : List Bool)
    {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {bit emitted : List Bool}
    (hstep : rmStep M inp q₀ reg₀ = some (q₁, reg₁, bit))
    (hreg₀ : ∀ r, reg₀ r ≤ Vmax)
    (hreg₁ : ∀ r, reg₁ r ≤ Vmax)
    (hem_len : (emitted ++ bit).length ≤ L_buf)
    {len sys1Val : ℕ} {τ₁ : ℕ → Bool}
    (hinv : WSRMInv base R w L_buf M_blk B seg_inp inp τ₁ len reg₀ emitted sys1Val) :
    ∃ sub_end : RMSubQ base R, ∃ τ₂ : ℕ → Bool,
      simRMNext base R seg_inp M (q₀, sub_end) = some (q₁, rmSubEntry base R seg_inp M q₁) ∧
      WSRMInv base R w L_buf M_blk B seg_inp inp τ₂ len reg₁ (emitted ++ bit) sys1Val ∧
      (∀ p, 3 * M_blk ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (familyStep (fun (_ : Q) => rmSubStep base R)) B
        (q₀, rmSubEntry base R seg_inp M q₀) len τ₁ 0
        (q₀, sub_end) len τ₂ 0 ((max Vmax L_buf + 2) * (250 * M_blk + 100)) := by
  let MaxSeg := base + R + 5
  let T_step := (max Vmax L_buf + 2) * (250 * M_blk + 100)
  unfold rmStep at hstep
  cases hMq : M q₀ with
  | none => rw [hMq] at hstep; cases hstep
  | some op =>
    rw [hMq] at hstep
    rcases op with ⟨r, next⟩ | ⟨r, next⟩ | ⟨r, qz, qnz⟩ | ⟨dst, src, next⟩ | ⟨rIdx, qf, qt⟩ | ⟨b, next⟩
    · -- opZero
      cases hstep
      simp only [List.append_nil]
      rcases hinv with ⟨segs, hlen_s, hM, htw, hinp_eq, hregs, houtL, hsys1, houtB, hem_le, htmp1, htmp2, hW⟩
      rcases wsZero_spec MaxSeg B segs (s := base + r.val) (w := w)
          (by omega) (by omega) (by rw [hregs r, length_natToBitsLE]) htw
        with ⟨τ₂, htw₂, hout₂, he_z⟩
      rw [hM] at hout₂ he_z
      let segs₂ := segs.set (base + r.val) (natToBitsLE w 0)
      have hM₂ : (encodeWorkspace segs₂).length = M_blk :=
        (length_encodeWorkspace_set (by omega) (by rw [hregs r, length_natToBitsLE, length_natToBitsLE])).trans hM
      have he_sub : StepExec (rmSubStep base R) B
          (Sum.inr (Sum.inl (wsZeroEntry MaxSeg ⟨base + r.val, by omega⟩))) len τ₁ 0
          (Sum.inr (Sum.inl (liftBlkExit (0, true)))) len τ₂ 0 (21 * M_blk + 4) :=
        sumStep_inr_spec (nopStep Unit) _
          (sumStep_inl_spec (wsZero MaxSeg) _ he_z)
      have he_fam := (familyStep_spec (fun (_ : Q) => rmSubStep base R) q₀ he_sub).weaken T_step (by
        have := Nat.le_mul_of_pos_left (250 * M_blk + 100) (show 0 < max Vmax L_buf + 2 by omega)
        dsimp only [T_step]; omega)
      refine ⟨Sum.inr (Sum.inl (liftBlkExit (0, true))), τ₂,
        by simp [simRMNext, hMq],
        ⟨segs₂, by simp [segs₂, hlen_s], hM₂, htw₂, ?_, ?_, ?_, ?_, ?_, hem_le, ?_, ?_, ?_⟩,
        hout₂, by simpa [rmSubEntry, hMq] using he_fam⟩
      · intro i; rw [getD_set_ne_seg segs (by omega)]; exact hinp_eq i
      · intro i
        by_cases hir : i = r
        · subst hir; dsimp only [segs₂]; rw [regUpd_self, getD_set_self_seg segs (by omega)]
        · have hne : base + r.val ≠ base + i.val := by intro he; exact hir (Fin.ext (by omega))
          rw [getD_set_ne_seg segs hne, regUpd_ne _ hir]; exact hregs i
      · rw [getD_set_ne_seg segs (by omega)]; exact houtL
      · rw [getD_set_ne_seg segs (by omega)]; exact hsys1
      · rw [getD_set_ne_seg segs (by omega)]; exact houtB
      · rw [getD_set_ne_seg segs (by omega)]; exact htmp1
      · rw [getD_set_ne_seg segs (by omega)]; exact htmp2
      · rw [getD_set_ne_seg segs (by omega)]; exact hW
    · -- opInc
      cases hstep
      simp only [List.append_nil]
      rcases hinv with ⟨segs, hlen_s, hM, htw, hinp_eq, hregs, houtL, hsys1, houtB, hem_le, htmp1, htmp2, hW⟩
      have hr1_le : reg₀ r + 1 ≤ Vmax := by simpa [regUpd_self] using hreg₁ r
      rcases wsInc_spec MaxSeg B segs (s := base + r.val) (w := w) (v := reg₀ r)
          (by omega) (by omega) (hregs r) (by omega) htw
        with ⟨τ₂, htw₂, hout₂, he_inc⟩
      rw [hM] at hout₂ he_inc
      let segs₂ := segs.set (base + r.val) (natToBitsLE w (reg₀ r + 1))
      have hM₂ : (encodeWorkspace segs₂).length = M_blk :=
        (length_encodeWorkspace_set (by omega) (by rw [hregs r, length_natToBitsLE, length_natToBitsLE])).trans hM
      have he_sub : StepExec (rmSubStep base R) B
          (Sum.inr (Sum.inr (Sum.inl (wsIncEntry MaxSeg ⟨base + r.val, by omega⟩)))) len τ₁ 0
          (Sum.inr (Sum.inr (Sum.inl (liftBlkExit (0, true))))) len τ₂ 0 (21 * M_blk + 4) :=
        sumStep_inr_spec (nopStep Unit) _
          (sumStep_inr_spec (wsZero MaxSeg) _ (sumStep_inl_spec (wsInc MaxSeg) _ he_inc))
      have he_fam := (familyStep_spec (fun (_ : Q) => rmSubStep base R) q₀ he_sub).weaken T_step (by
        have := Nat.le_mul_of_pos_left (250 * M_blk + 100) (show 0 < max Vmax L_buf + 2 by omega)
        dsimp only [T_step]; omega)
      refine ⟨Sum.inr (Sum.inr (Sum.inl (liftBlkExit (0, true)))), τ₂,
        by simp [simRMNext, hMq],
        ⟨segs₂, by simp [segs₂, hlen_s], hM₂, htw₂, ?_, ?_, ?_, ?_, ?_, hem_le, ?_, ?_, ?_⟩,
        hout₂, by simpa [rmSubEntry, hMq] using he_fam⟩
      · intro i; rw [getD_set_ne_seg segs (by omega)]; exact hinp_eq i
      · intro i
        by_cases hir : i = r
        · subst hir; dsimp only [segs₂]; rw [regUpd_self, getD_set_self_seg segs (by omega)]
        · have hne : base + r.val ≠ base + i.val := by intro he; exact hir (Fin.ext (by omega))
          rw [getD_set_ne_seg segs hne, regUpd_ne _ hir]; exact hregs i
      · rw [getD_set_ne_seg segs (by omega)]; exact houtL
      · rw [getD_set_ne_seg segs (by omega)]; exact hsys1
      · rw [getD_set_ne_seg segs (by omega)]; exact houtB
      · rw [getD_set_ne_seg segs (by omega)]; exact htmp1
      · rw [getD_set_ne_seg segs (by omega)]; exact htmp2
      · rw [getD_set_ne_seg segs (by omega)]; exact hW
    · -- opDecJz
      rcases hinv with ⟨segs, hlen_s, hM, htw, hinp_eq, hregs, houtL, hsys1, houtB, hem_le, htmp1, htmp2, hW⟩
      have hr0_le := hreg₀ r
      rcases wsDecJz_spec MaxSeg B segs (s := base + r.val) (w := w) (v := reg₀ r)
          (by omega) (by omega) (hregs r) (by omega) htw
        with ⟨q_dz, τ₂, hz_out, htw₂, hout₂, he_dz⟩
      rw [hM] at hout₂ he_dz
      have he_sub : StepExec (rmSubStep base R) B
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl (wsDecJzEntry MaxSeg ⟨base + r.val, by omega⟩))))) len τ₁ 0
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl q_dz)))) len τ₂ 0 (42 * M_blk + 10) :=
        sumStep_inr_spec (nopStep Unit) _
          (sumStep_inr_spec (wsZero MaxSeg) _
            (sumStep_inr_spec (wsInc MaxSeg) _ (sumStep_inl_spec (wsDecJz MaxSeg) _ he_dz)))
      have he_fam := (familyStep_spec (fun (_ : Q) => rmSubStep base R) q₀ he_sub).weaken T_step (by
        have := Nat.le_mul_of_pos_left (250 * M_blk + 100) (show 0 < max Vmax L_buf + 2 by omega)
        dsimp only [T_step]; omega)
      by_cases hv0 : reg₀ r = 0
      · simp only [hv0, ↓reduceIte, decide_true] at hstep hz_out htw₂
        cases hstep
        simp only [List.append_nil]
        exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl q_dz))), τ₂,
          by simp [simRMNext, hMq, rmSubWasZero, hz_out],
          ⟨segs, hlen_s, hM, htw₂, hinp_eq, hregs, houtL, hsys1, houtB, hem_le, htmp1, htmp2, hW⟩,
          hout₂, by simpa [rmSubEntry, hMq] using he_fam⟩
      · simp only [hv0, ↓reduceIte, decide_false] at hstep hz_out htw₂
        cases hstep
        simp only [List.append_nil]
        let segs₂ := segs.set (base + r.val) (natToBitsLE w (reg₀ r - 1))
        have hM₂ : (encodeWorkspace segs₂).length = M_blk :=
          (length_encodeWorkspace_set (by omega) (by rw [hregs r, length_natToBitsLE, length_natToBitsLE])).trans hM
        refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl q_dz))), τ₂,
          by simp [simRMNext, hMq, rmSubWasZero, hz_out],
          ⟨segs₂, by simp [segs₂, hlen_s], hM₂, htw₂, ?_, ?_, ?_, ?_, ?_, hem_le, ?_, ?_, ?_⟩,
          hout₂, by simpa [rmSubEntry, hMq] using he_fam⟩
        · intro i; rw [getD_set_ne_seg segs (by omega)]; exact hinp_eq i
        · intro i
          by_cases hir : i = r
          · subst hir; dsimp only [segs₂]; rw [regUpd_self, getD_set_self_seg segs (by omega)]
          · have hne : base + r.val ≠ base + i.val := by intro he; exact hir (Fin.ext (by omega))
            rw [getD_set_ne_seg segs hne, regUpd_ne _ hir]; exact hregs i
        · rw [getD_set_ne_seg segs (by omega)]; exact houtL
        · rw [getD_set_ne_seg segs (by omega)]; exact hsys1
        · rw [getD_set_ne_seg segs (by omega)]; exact houtB
        · rw [getD_set_ne_seg segs (by omega)]; exact htmp1
        · rw [getD_set_ne_seg segs (by omega)]; exact htmp2
        · rw [getD_set_ne_seg segs (by omega)]; exact hW
    · -- opCopy
      cases hstep
      simp only [List.append_nil]
      by_cases hds : dst = src
      · subst hds
        rw [regUpd_eq_self]
        rcases hinv with ⟨segs, hlen_s, hM, htw, hinp_eq, hregs, houtL, hsys1, houtB, hem_le, htmp1, htmp2, hW⟩
        have hlen_pos := TapeWS_pos htw
        have hlen_B := htw.2.2.1
        have he_nop : StepExec (rmSubStep base R) B (Sum.inl ()) len τ₁ 0 (Sum.inl ()) len τ₁ 0 0 :=
          sumStep_inl_spec (nopStep Unit) _ (nopStep_spec () len τ₁ 0 hlen_B (by omega))
        have he_fam := (familyStep_spec (fun (_ : Q) => rmSubStep base R) q₀ he_nop).weaken T_step (by omega)
        exact ⟨Sum.inl (), τ₁, by simp [simRMNext, hMq],
          ⟨segs, hlen_s, hM, htw, hinp_eq, hregs, houtL, hsys1, houtB, hem_le, htmp1, htmp2, hW⟩,
          fun _ _ => rfl, by simpa [rmSubEntry, hMq] using he_fam⟩
      · rcases hinv with ⟨segs, hlen_s, hM, htw, hinp_eq, hregs, houtL, hsys1, houtB, hem_le, htmp1, htmp2, hW⟩
        have h_ds_ne : base + dst.val ≠ base + src.val := by
          intro he; exact hds (Fin.ext (by omega))
        have hs_le := hreg₀ src
        rcases wsCopy_spec MaxSeg B segs (dst := base + dst.val) (src := base + src.val) (tmp := base + R + 3)
            (w := w) (v := reg₀ src)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            h_ds_ne (by omega) (by omega)
            (by rw [hregs dst, length_natToBitsLE]) (hregs src) htmp1 (by omega) htw
          with ⟨q_cp, τ₂, htw₂, hout₂, he_cp⟩
        rw [hM] at hout₂ he_cp
        let segs_c0 := segs.set (base + dst.val) (natToBitsLE w (reg₀ src))
        let segs₂ := segs_c0.set (base + R + 3) (natToBitsLE w 0)
        have hM₂ : (encodeWorkspace segs₂).length = M_blk := by
          have h1 := length_encodeWorkspace_set (segs := segs) (s := base + dst.val)
            (newSeg := natToBitsLE w (reg₀ src)) (by omega)
            (by rw [hregs dst, length_natToBitsLE, length_natToBitsLE])
          have h2 := length_encodeWorkspace_set (segs := segs_c0) (s := base + R + 3)
            (newSeg := natToBitsLE w 0) (by simp [segs_c0]; omega)
            (by dsimp only [segs_c0]; rw [getD_set_ne_seg _ (by omega), htmp1, length_natToBitsLE])
          exact h2.trans (h1.trans hM)
        have he_sub : StepExec (rmSubStep base R) B
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
              (wsCopyEntry MaxSeg (⟨base + dst.val, by omega⟩, ⟨base + src.val, by omega⟩, ⟨base + R + 3, by omega⟩)))))))
            len τ₁ 0
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q_cp)))))
            len τ₂ 0 ((reg₀ src + 2) * (150 * M_blk + 50)) :=
          sumStep_inr_spec (nopStep Unit) _
            (sumStep_inr_spec (wsZero MaxSeg) _
              (sumStep_inr_spec (wsInc MaxSeg) _
                (sumStep_inr_spec (wsDecJz MaxSeg) _
                  (sumStep_inl_spec (wsCopy MaxSeg) _ he_cp))))
        have he_fam := (familyStep_spec (fun (_ : Q) => rmSubStep base R) q₀ he_sub).weaken T_step (by
          calc (reg₀ src + 2) * (150 * M_blk + 50)
              ≤ (max Vmax L_buf + 2) * (150 * M_blk + 50) :=
                Nat.mul_le_mul_right _ (by omega)
            _ ≤ (max Vmax L_buf + 2) * (250 * M_blk + 100) :=
                Nat.mul_le_mul_left _ (by omega))
        refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q_cp)))), τ₂,
          by simp [simRMNext, hMq],
          ⟨segs₂, by simp [segs₂, segs_c0, hlen_s], hM₂, htw₂, ?_, ?_, ?_, ?_, ?_, hem_le, ?_, ?_, ?_⟩,
          hout₂, by simpa [rmSubEntry, hMq, hds] using he_fam⟩
        · intro i; dsimp only [segs₂, segs_c0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hinp_eq i
        · intro i
          dsimp only [segs₂, segs_c0]
          rw [getD_set_ne_seg _ (by omega)]
          by_cases hid : i = dst
          · subst hid; rw [regUpd_self, getD_set_self_seg segs (by omega)]
          · have hne : base + dst.val ≠ base + i.val := by intro he; exact hid (Fin.ext (by omega))
            rw [getD_set_ne_seg segs hne, regUpd_ne _ hid]; exact hregs i
        · dsimp only [segs₂, segs_c0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact houtL
        · dsimp only [segs₂, segs_c0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hsys1
        · dsimp only [segs₂, segs_c0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact houtB
        · dsimp only [segs₂, segs_c0]; rw [getD_set_self_seg _ (by simp; omega), length_natToBitsLE]
        · dsimp only [segs₂, segs_c0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact htmp2
        · dsimp only [segs₂, segs_c0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hW
    · -- opReadIn
      rcases hinv with ⟨segs, hlen_s, hM, htw, hinp_eq, hregs, houtL, hsys1, houtB, hem_le, htmp1, htmp2, hW⟩
      have hi_le := hreg₀ rIdx
      have hin_le : seg_inp ≤ MaxSeg := by omega
      rcases wsReadBit_spec MaxSeg B segs (arr := seg_inp) (idx := base + rIdx.val)
          (tmp := base + R + 3) (tmp2 := base + R + 4) (w := w) (v := reg₀ rIdx)
          (by omega) (by omega) (by omega) (by omega)
          hin_le (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (hregs rIdx) htmp1 htmp2 (by omega) htw
        with ⟨q_rb, τ₂, hres_rb, htw₂, hout₂, he_rb⟩
      rw [hM] at hout₂ he_rb
      rw [hinp_eq (reg₀ rIdx)] at hres_rb
      let segs_r0 := segs.set (base + R + 3) (natToBitsLE w 0)
      let segs₂ := segs_r0.set (base + R + 4) (natToBitsLE w 0)
      have hM₂ : (encodeWorkspace segs₂).length = M_blk := by
        have h1 := length_encodeWorkspace_set (segs := segs) (s := base + R + 3)
          (newSeg := natToBitsLE w 0) (by omega) (by rw [htmp1, length_natToBitsLE])
        have h2 := length_encodeWorkspace_set (segs := segs_r0) (s := base + R + 4)
          (newSeg := natToBitsLE w 0) (by simp [segs_r0]; omega)
          (by dsimp only [segs_r0]; rw [getD_set_ne_seg _ (by omega), htmp2, length_natToBitsLE])
        exact h2.trans (h1.trans hM)
      have he_sub : StepExec (rmSubStep base R) B
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
            (wsReadBitEntry MaxSeg (⟨seg_inp, by omega⟩, ⟨base + rIdx.val, by omega⟩,
              ⟨base + R + 3, by omega⟩, ⟨base + R + 4, by omega⟩))))))))
          len τ₁ 0
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q_rb))))))
          len τ₂ 0 ((reg₀ rIdx + 2) * (220 * M_blk + 80)) :=
        sumStep_inr_spec (nopStep Unit) _
          (sumStep_inr_spec (wsZero MaxSeg) _
            (sumStep_inr_spec (wsInc MaxSeg) _
              (sumStep_inr_spec (wsDecJz MaxSeg) _
                (sumStep_inr_spec (wsCopy MaxSeg) _
                  (sumStep_inl_spec (wsReadBit MaxSeg) _ he_rb)))))
      have he_fam := (familyStep_spec (fun (_ : Q) => rmSubStep base R) q₀ he_sub).weaken T_step (by
        calc (reg₀ rIdx + 2) * (220 * M_blk + 80)
            ≤ (max Vmax L_buf + 2) * (220 * M_blk + 80) := Nat.mul_le_mul_right _ (by omega)
          _ ≤ (max Vmax L_buf + 2) * (250 * M_blk + 100) := Nat.mul_le_mul_left _ (by omega))
      have hentry_eq : (rmSubEntry base R seg_inp M q₀) =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
            (wsReadBitEntry MaxSeg (⟨seg_inp, by omega⟩, ⟨base + rIdx.val, by omega⟩,
              ⟨base + R + 3, by omega⟩, ⟨base + R + 4, by omega⟩))))))) := by
        dsimp only [MaxSeg] at hin_le ⊢
        simp [rmSubEntry, hMq, hin_le]
      rw [← hentry_eq] at he_fam
      cases hb_in : inp.getD (reg₀ rIdx) false
      · simp only [hb_in, Bool.false_eq_true, ↓reduceIte] at hstep hres_rb
        cases hstep
        simp only [List.append_nil]
        refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q_rb))))), τ₂,
          by simp [simRMNext, hMq, rmSubReadRes, hres_rb],
          ⟨segs₂, by simp [segs₂, segs_r0, hlen_s], hM₂, htw₂, ?_, ?_, ?_, ?_, ?_, hem_le, ?_, ?_, ?_⟩,
          hout₂, he_fam⟩
        · intro i; dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hinp_eq i
        · intro i; dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hregs i
        · dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact houtL
        · dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hsys1
        · dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact houtB
        · dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by omega), length_natToBitsLE]
        · dsimp only [segs₂, segs_r0]; rw [getD_set_self_seg _ (by simp; omega), length_natToBitsLE]
        · dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hW
      · simp only [hb_in, ↓reduceIte] at hstep hres_rb
        cases hstep
        simp only [List.append_nil]
        refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl q_rb))))), τ₂,
          by simp [simRMNext, hMq, rmSubReadRes, hres_rb],
          ⟨segs₂, by simp [segs₂, segs_r0, hlen_s], hM₂, htw₂, ?_, ?_, ?_, ?_, ?_, hem_le, ?_, ?_, ?_⟩,
          hout₂, he_fam⟩
        · intro i; dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hinp_eq i
        · intro i; dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hregs i
        · dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact houtL
        · dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hsys1
        · dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact houtB
        · dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by omega), length_natToBitsLE]
        · dsimp only [segs₂, segs_r0]; rw [getD_set_self_seg _ (by simp; omega), length_natToBitsLE]
        · dsimp only [segs₂, segs_r0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hW
    · -- opEmit
      cases hstep
      have hemit_lt : emitted.length < L_buf := by simp at hem_len; omega
      rcases wsEmitBit_spec base R w L_buf M_blk B seg_inp h_inp inp b hinv hemit_lt hL_pow
        with ⟨q_eb, τ₂, hinv₂, hout₂, he_eb⟩
      have he_sub : StepExec (rmSubStep base R) B
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (wsEmitBitEntry base R b)))))))
          len τ₁ 0
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr q_eb))))))
          len τ₂ 0 ((L_buf + 2) * (250 * M_blk + 100)) :=
        sumStep_inr_spec (nopStep Unit) _
          (sumStep_inr_spec (wsZero MaxSeg) _
            (sumStep_inr_spec (wsInc MaxSeg) _
              (sumStep_inr_spec (wsDecJz MaxSeg) _
                (sumStep_inr_spec (wsCopy MaxSeg) _
                  (sumStep_inr_spec (wsReadBit MaxSeg) _ he_eb)))))
      have he_fam := (familyStep_spec (fun (_ : Q) => rmSubStep base R) q₀ he_sub).weaken T_step (by
        calc (L_buf + 2) * (250 * M_blk + 100)
            ≤ (max Vmax L_buf + 2) * (250 * M_blk + 100) := Nat.mul_le_mul_right _ (by omega))
      exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr q_eb))))), τ₂,
        by simp [simRMNext, hMq], hinv₂, hout₂, by simpa [rmSubEntry, hMq] using he_fam⟩

theorem simRMLoop_spec (base R w L_buf M_blk B seg_inp Vmax : ℕ)
    (h_inp : seg_inp < base) (hV_pow : Vmax < 2 ^ w) (hL_pow : L_buf < 2 ^ w)
    {Q : Type} (M : RMProg R Q) (inp : List Bool)
    {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {emitted : List Bool} {steps : ℕ}
    (hexec : RMExec M Vmax inp q₀ reg₀ q₁ reg₁ emitted steps)
    (hem_le : emitted.length ≤ L_buf)
    {len sys1Val : ℕ} {τ₁ : ℕ → Bool}
    (hinv : WSRMInv base R w L_buf M_blk B seg_inp inp τ₁ len reg₀ [] sys1Val) :
    ∃ τ₂ : ℕ → Bool,
      WSRMInv base R w L_buf M_blk B seg_inp inp τ₂ len reg₁ emitted sys1Val ∧
      (∀ p, 3 * M_blk ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (simRMLoop base R seg_inp M) B
        (q₀, rmSubEntry base R seg_inp M q₀) len τ₁ 0
        (q₁, Sum.inl ()) len τ₂ 0
        ((steps + 1) * ((max Vmax L_buf + 2) * (250 * M_blk + 100) + 2)) := by
  rcases hexec with ⟨k, hk_steps, hiter_k, hhalt, hbnd_k⟩
  let S := (max Vmax L_buf + 2) * (250 * M_blk + 100)
  have haux : ∀ rem (qa : Q) (rega : RegState R) (pre out_rem : List Bool) (τa : ℕ → Bool),
      rmIter M inp rem qa rega = some (q₁, reg₁, out_rem) →
      (pre ++ out_rem).length ≤ L_buf →
      (∀ j ≤ rem, ∀ q' reg' out', rmIter M inp j qa rega = some (q', reg', out') → ∀ r, reg' r ≤ Vmax) →
      WSRMInv base R w L_buf M_blk B seg_inp inp τa len rega pre sys1Val →
      ∃ τ₂ : ℕ → Bool,
        WSRMInv base R w L_buf M_blk B seg_inp inp τ₂ len reg₁ (pre ++ out_rem) sys1Val ∧
        (∀ p, 3 * M_blk ≤ p → τ₂ p = τa p) ∧
        StepExec (simRMLoop base R seg_inp M) B
          (qa, rmSubEntry base R seg_inp M qa) len τa 0
          (q₁, Sum.inl ()) len τ₂ 0 ((rem + 1) * (S + 2)) := by
    intro rem
    induction rem with
    | zero =>
      intro qa rega pre out_rem τa hit hpre_le _ hinv_a
      simp only [rmIter, Option.some.injEq, Prod.mk.injEq] at hit
      rcases hit with ⟨rfl, rfl, rfl⟩
      simp only [List.append_nil]
      rcases hinv_a with ⟨segs, hlen_s, hM, htw, hinp_eq, hregs, houtL, hsys1, houtB, hem_le', htmp1, htmp2, hW⟩
      have hlen_pos := TapeWS_pos htw
      have hlen_B := htw.2.2.1
      have he_nop : StepExec (rmSubStep base R) B (Sum.inl ()) len τa 0 (Sum.inl ()) len τa 0 0 :=
        sumStep_inl_spec (nopStep Unit) _ (nopStep_spec () len τa 0 hlen_B (by omega))
      have he_fam := familyStep_spec (fun (_ : Q) => rmSubStep base R) qa he_nop
      have hentry_q1 : rmSubEntry base R seg_inp M qa = Sum.inl () := by simp [rmSubEntry, hhalt]
      have hdone := (loop0_done (next := simRMNext base R seg_inp M) he_fam (by simp [simRMNext, hhalt])).weaken
        ((0 + 1) * (S + 2)) (by omega)
      refine ⟨τa, ⟨segs, hlen_s, hM, htw, hinp_eq, hregs, houtL, hsys1, houtB, hem_le', htmp1, htmp2, hW⟩,
        fun _ _ => rfl, ?_⟩
      rw [hentry_q1]
      exact hdone
    | succ rem ih =>
      intro qa rega pre out_rem τa hit hpre_le hbnd_a hinv_a
      simp only [rmIter] at hit
      cases hs1 : rmStep M inp qa rega with
      | none => rw [hs1] at hit; cases hit
      | some val =>
        rcases val with ⟨qb, regb, bit⟩
        simp only [hs1] at hit
        cases hr_rest : rmIter M inp rem qb regb with
        | none => rw [hr_rest] at hit; cases hit
        | some val2 =>
          rcases val2 with ⟨qc, regc, out'⟩
          simp only [hr_rest, Option.some.injEq, Prod.mk.injEq] at hit
          rcases hit with ⟨rfl, rfl, rfl⟩
          have hrega_le : ∀ r, rega r ≤ Vmax := hbnd_a 0 (Nat.zero_le _) qa rega [] rfl
          have hregb_le : ∀ r, regb r ≤ Vmax :=
            hbnd_a 1 (by omega) qb regb (bit ++ []) (by simp [rmIter, hs1])
          have hpre_bit_le : (pre ++ bit).length ≤ L_buf := by simp at hpre_le ⊢; omega
          rcases simRMOneStep_spec base R w L_buf M_blk B seg_inp Vmax h_inp hV_pow hL_pow
              M inp hs1 hrega_le hregb_le hpre_bit_le hinv_a
            with ⟨sub_end, τ_mid, hnext_eq, hinv_mid, hout_mid, he_one⟩
          have hlen_pos : 1 ≤ len := by rcases hinv_mid with ⟨_, _, _, htw_m, _⟩; exact TapeWS_pos htw_m
          have hbnd_b : ∀ j ≤ rem, ∀ q' reg' out1, rmIter M inp j qb regb = some (q', reg', out1) →
              ∀ r, reg' r ≤ Vmax := by
            intro j hj q' reg' out1 hj_eq
            exact hbnd_a (j + 1) (by omega) q' reg' (bit ++ out1) (by simp [rmIter, hs1, hj_eq])
          rcases ih qb regb (pre ++ bit) out' τ_mid hr_rest
              (by simpa [List.append_assoc] using hpre_le) hbnd_b hinv_mid
            with ⟨τ_end, hinv_end, hout_end, he_rest⟩
          rw [List.append_assoc] at hinv_end
          have hstep := (loop0_step (next := simRMNext base R seg_inp M) hlen_pos he_one hnext_eq he_rest).weaken
            ((rem + 1 + 1) * (S + 2)) (by
              have : (rem + 1 + 1) * (S + 2) = (S + 2) + (rem + 1) * (S + 2) := by ring
              omega)
          exact ⟨τ_end, hinv_end, fun p hp => (hout_end p hp).trans (hout_mid p hp), hstep⟩
  rcases haux k q₀ reg₀ [] emitted τ₁ hiter_k (by simpa using hem_le) hbnd_k hinv
    with ⟨τ₂, hinv₂, hout₂, he_k⟩
  simp only [List.nil_append] at hinv₂
  refine ⟨τ₂, hinv₂, hout₂, he_k.weaken ((steps + 1) * (S + 2)) ?_⟩
  exact Nat.mul_le_mul_right (S + 2) (by omega)

/-!
### Padding-Vertex Circuit Tail Emitter (`appendPadTail`), Unpacker (`unpackOutLoop`), and `blkSweepTrue`
-/

abbrev EmitOneQ (base R : ℕ) : Type := Bool × WsEmitBitInnerQ (base + R + 5)

abbrev Emit6Q (base R : ℕ) : Type :=
  EmitOneQ base R ⊕
  (EmitOneQ base R ⊕
  (EmitOneQ base R ⊕
  (EmitOneQ base R ⊕
  (EmitOneQ base R ⊕ EmitOneQ base R))))

def emitPadCircuit6 (base R : ℕ) : StepFn (Emit6Q base R) :=
  seq0 (wsEmitBit base R)
    (seq0 (wsEmitBit base R)
      (seq0 (wsEmitBit base R)
        (seq0 (wsEmitBit base R)
          (seq0 (wsEmitBit base R) (wsEmitBit base R)
            (fun _ => wsEmitBitEntry base R true))
          (fun _ => Sum.inl (wsEmitBitEntry base R false)))
        (fun _ => Sum.inl (wsEmitBitEntry base R false)))
      (fun _ => Sum.inl (wsEmitBitEntry base R false)))
    (fun _ => Sum.inl (wsEmitBitEntry base R true))

def emitPadCircuit6Entry (base R : ℕ) : Emit6Q base R :=
  Sum.inl (wsEmitBitEntry base R false)

theorem emitPadCircuit6_spec (base R w L_buf M_blk B seg_inp : ℕ) (h_inp : seg_inp < base)
    (inp : List Bool) {len sys1Val : ℕ} {τ₁ : ℕ → Bool} {reg : RegState R} {emitted : List Bool}
    (hinv : WSRMInv base R w L_buf M_blk B seg_inp inp τ₁ len reg emitted sys1Val)
    (hem6 : emitted.length + 6 ≤ L_buf) (hL_pow : L_buf < 2 ^ w) :
    ∃ q_end, ∃ τ₂ : ℕ → Bool,
      WSRMInv base R w L_buf M_blk B seg_inp inp τ₂ len reg
        (emitted ++ [false, true, false, false, false, true]) sys1Val ∧
      (∀ p, 3 * M_blk ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (emitPadCircuit6 base R) B (emitPadCircuit6Entry base R) len τ₁ 0
        q_end len τ₂ 0 (6 * ((L_buf + 2) * (250 * M_blk + 100)) + 10) := by
  have hlen_pos : 1 ≤ len := by rcases hinv with ⟨_, _, _, htw, _⟩; exact TapeWS_pos htw
  rcases wsEmitBit_spec base R w L_buf M_blk B seg_inp h_inp inp false hinv (by omega) hL_pow
    with ⟨_, τ1, hi1, ho1, he1⟩
  rcases wsEmitBit_spec base R w L_buf M_blk B seg_inp h_inp inp true hi1 (by simp; omega) hL_pow
    with ⟨_, τ2, hi2, ho2, he2⟩
  rcases wsEmitBit_spec base R w L_buf M_blk B seg_inp h_inp inp false hi2 (by simp; omega) hL_pow
    with ⟨_, τ3, hi3, ho3, he3⟩
  rcases wsEmitBit_spec base R w L_buf M_blk B seg_inp h_inp inp false hi3 (by simp; omega) hL_pow
    with ⟨_, τ4, hi4, ho4, he4⟩
  rcases wsEmitBit_spec base R w L_buf M_blk B seg_inp h_inp inp false hi4 (by simp; omega) hL_pow
    with ⟨_, τ5, hi5, ho5, he5⟩
  rcases wsEmitBit_spec base R w L_buf M_blk B seg_inp h_inp inp true hi5 (by simp; omega) hL_pow
    with ⟨_, τ6, hi6, ho6, he6⟩
  simp only [List.append_assoc, List.singleton_append] at hi6
  have hc56 := seq0_spec (f := fun _ => wsEmitBitEntry base R true) hlen_pos he5 he6
  have hc46 := seq0_spec (f := fun _ => Sum.inl (wsEmitBitEntry base R false)) hlen_pos he4 hc56
  have hc36 := seq0_spec (f := fun _ => Sum.inl (wsEmitBitEntry base R false)) hlen_pos he3 hc46
  have hc26 := seq0_spec (f := fun _ => Sum.inl (wsEmitBitEntry base R false)) hlen_pos he2 hc36
  have hc16 := (seq0_spec (f := fun _ => Sum.inl (wsEmitBitEntry base R true)) hlen_pos he1 hc26).weaken
    (6 * ((L_buf + 2) * (250 * M_blk + 100)) + 10) (by omega)
  refine ⟨_, τ6, hi6, fun p hp => ?_, hc16⟩
  exact (ho6 p hp).trans ((ho5 p hp).trans ((ho4 p hp).trans ((ho3 p hp).trans ((ho2 p hp).trans (ho1 p hp)))))

abbrev PadLoopQ (base R : ℕ) : Type :=
  WsDecJzQ (base + R + 5) ⊕ (Unit ⊕ Emit6Q base R)

def padLoopBody (base R : ℕ) : StepFn (PadLoopQ base R) :=
  seq0 (wsDecJz (base + R + 5))
    (sumStep (nopStep Unit) (emitPadCircuit6 base R))
    (fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (emitPadCircuit6Entry base R))

def padLoopNext (base R : ℕ) : PadLoopQ base R → Option (PadLoopQ base R)
  | Sum.inr (Sum.inr _) => some (Sum.inl (wsDecJzEntry (base + R + 5) ⟨base + R + 1, by omega⟩))
  | _ => none

def appendPadTail (base R : ℕ) :
    StepFn ((SegTriple (base + R + 5) × WsCopyInnerQ (base + R + 5)) ⊕ PadLoopQ base R) :=
  seq0 (wsCopy (base + R + 5))
    (loop0 (padLoopBody base R) (padLoopNext base R))
    (fun _ => Sum.inl (wsDecJzEntry (base + R + 5) ⟨base + R + 1, by omega⟩))

def appendPadTailEntry (base R : ℕ) :
    (SegTriple (base + R + 5) × WsCopyInnerQ (base + R + 5)) ⊕ PadLoopQ base R :=
  Sum.inl (wsCopyEntry (base + R + 5) (⟨base + R + 1, by omega⟩, ⟨base + R + 5, by omega⟩, ⟨base + R + 3, by omega⟩))

theorem range_flatMap_const (m : ℕ) (c : List Bool) :
    c ++ (List.range m).flatMap (fun _ => c) = (List.range (m + 1)).flatMap (fun _ => c) := by
  induction m with
  | zero => simp [List.range_succ]
  | succ m ih =>
    conv_lhs => rw [List.range_succ]
    rw [List.flatMap_append, ← List.append_assoc, ih]
    simp [List.range_succ]

theorem appendPadTail_spec (base R w L_buf M_blk B seg_inp : ℕ) (h_inp : seg_inp < base)
    (inp : List Bool) {len sys1Val : ℕ} {τ₁ : ℕ → Bool} {reg : RegState R} {emitted : List Bool}
    (hinv : WSRMInv base R w L_buf M_blk B seg_inp inp τ₁ len reg emitted sys1Val)
    (hem_pad : emitted.length + 6 * (3 * M_blk) ≤ L_buf)
    (hL_pow : L_buf < 2 ^ w) :
    let padBits := (List.range (3 * M_blk)).flatMap (fun _ => [false, true, false, false, false, true])
    ∃ q_end, ∃ τ₂ : ℕ → Bool,
      WSRMInv base R w L_buf M_blk B seg_inp inp τ₂ len reg (emitted ++ padBits) 0 ∧
      (∀ p, 3 * M_blk ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (appendPadTail base R) B (appendPadTailEntry base R) len τ₁ 0
        q_end len τ₂ 0
        ((3 * M_blk + 2) * (6 * ((L_buf + 2) * (250 * M_blk + 100)) + 210 * M_blk + 100)) := by
  intro padBits
  let MaxSeg := base + R + 5
  let c6 : List Bool := [false, true, false, false, false, true]
  have hW_pow : 3 * M_blk < 2 ^ w := by omega
  rcases hinv with ⟨segs, hlen_s, hM, htw, hinp_eq, hregs, houtL, hsys1, houtB, hem_le, htmp1, htmp2, hW⟩
  have hlen_pos := TapeWS_pos htw
  rcases wsCopy_spec MaxSeg B segs (dst := base + R + 1) (src := base + R + 5) (tmp := base + R + 3)
      (w := w) (v := 3 * M_blk)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
      (by rw [hsys1, length_natToBitsLE]) hW htmp1 hW_pow htw
    with ⟨q_cp, τ_cp, htw_cp, hout_cp, he_cp⟩
  rw [hM] at hout_cp he_cp
  let segs_cp0 := segs.set (base + R + 1) (natToBitsLE w (3 * M_blk))
  let segs_cp := segs_cp0.set (base + R + 3) (natToBitsLE w 0)
  have hM_cp : (encodeWorkspace segs_cp).length = M_blk := by
    have h1 := length_encodeWorkspace_set (segs := segs) (s := base + R + 1)
      (newSeg := natToBitsLE w (3 * M_blk)) (by omega)
      (by rw [hsys1, length_natToBitsLE, length_natToBitsLE])
    have h2 := length_encodeWorkspace_set (segs := segs_cp0) (s := base + R + 3)
      (newSeg := natToBitsLE w 0) (by simp [segs_cp0]; omega)
      (by dsimp only [segs_cp0]; rw [getD_set_ne_seg _ (by omega), htmp1, length_natToBitsLE])
    exact h2.trans (h1.trans hM)
  have hinv_cp : WSRMInv base R w L_buf M_blk B seg_inp inp τ_cp len reg emitted (3 * M_blk) := by
    refine ⟨segs_cp, by simp [segs_cp, segs_cp0, hlen_s], hM_cp, htw_cp, ?_, ?_, ?_, ?_, ?_, hem_le, ?_, ?_, ?_⟩
    · intro i; dsimp only [segs_cp, segs_cp0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hinp_eq i
    · intro r; dsimp only [segs_cp, segs_cp0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hregs r
    · dsimp only [segs_cp, segs_cp0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact houtL
    · dsimp only [segs_cp, segs_cp0]; rw [getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by omega)]
    · dsimp only [segs_cp, segs_cp0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact houtB
    · dsimp only [segs_cp, segs_cp0]; rw [getD_set_self_seg _ (by simp; omega), length_natToBitsLE]
    · dsimp only [segs_cp, segs_cp0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact htmp2
    · dsimp only [segs_cp, segs_cp0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]; exact hW
  let S_pad := 6 * ((L_buf + 2) * (250 * M_blk + 100)) + 50 * M_blk + 30
  have hloop : ∀ rem (pre : List Bool) (τa : ℕ → Bool),
      rem ≤ 3 * M_blk →
      pre.length + 6 * rem ≤ L_buf →
      WSRMInv base R w L_buf M_blk B seg_inp inp τa len reg pre rem →
      ∃ τ_end : ℕ → Bool,
        WSRMInv base R w L_buf M_blk B seg_inp inp τ_end len reg
          (pre ++ (List.range rem).flatMap (fun _ => c6)) 0 ∧
        (∀ p, 3 * M_blk ≤ p → τ_end p = τa p) ∧
        StepExec (loop0 (padLoopBody base R) (padLoopNext base R)) B
          (Sum.inl (wsDecJzEntry MaxSeg ⟨base + R + 1, by omega⟩)) len τa 0
          (Sum.inr (Sum.inl ())) len τ_end 0 ((rem + 1) * (S_pad + 2)) := by
    intro rem
    induction rem with
    | zero =>
      intro pre τa _ _ hinv_a
      simp only [List.range_zero, List.flatMap_nil, List.append_nil]
      rcases hinv_a with ⟨sa, hla, hMa, htwa, hinpa, hregsa, houtLa, hsys1a, houtBa, hem_a, htmp1a, htmp2a, hWa⟩
      have hlen_B := htwa.2.2.1
      rcases wsDecJz_spec MaxSeg B sa (s := base + R + 1) (w := w) (v := 0)
          (by omega) (by omega) hsys1a (by omega) htwa
        with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
      rw [hMa] at hout_dz he_dz
      simp only [decide_true, ↓reduceIte] at hz_dz htw_dz
      have he_nop := sumStep_inl_spec (nopStep Unit) (emitPadCircuit6 base R)
        (nopStep_spec () len τ_dz 0 hlen_B (by omega))
      have hbody := seq0_spec
        (f := fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (emitPadCircuit6Entry base R))
        hlen_pos he_dz (by rw [hz_dz]; exact he_nop)
      have hdone := (loop0_done (next := padLoopNext base R) hbody rfl).weaken
        ((0 + 1) * (S_pad + 2)) (by dsimp only [S_pad]; omega)
      exact ⟨τ_dz, ⟨sa, hla, hMa, htw_dz, hinpa, hregsa, houtLa, hsys1a, houtBa, hem_a, htmp1a, htmp2a, hWa⟩,
        hout_dz, hdone⟩
    | succ rem ih =>
      intro pre τa hrem_le hpre_pad hinv_a
      rcases hinv_a with ⟨sa, hla, hMa, htwa, hinpa, hregsa, houtLa, hsys1a, houtBa, hem_a, htmp1a, htmp2a, hWa⟩
      rcases wsDecJz_spec MaxSeg B sa (s := base + R + 1) (w := w) (v := rem + 1)
          (by omega) (by omega) hsys1a (by omega) htwa
        with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
      rw [hMa] at hout_dz he_dz
      simp only [Nat.succ_ne_zero, decide_false, ↓reduceIte, Nat.add_sub_cancel] at hz_dz htw_dz
      let sa' := sa.set (base + R + 1) (natToBitsLE w rem)
      have hMa' : (encodeWorkspace sa').length = M_blk :=
        (length_encodeWorkspace_set (by omega) (by rw [hsys1a, length_natToBitsLE, length_natToBitsLE])).trans hMa
      have hinv_dz : WSRMInv base R w L_buf M_blk B seg_inp inp τ_dz len reg pre rem := by
        refine ⟨sa', by simp [sa', hla], hMa', htw_dz, ?_, ?_, ?_, ?_, ?_, hem_a, ?_, ?_, ?_⟩
        · intro i; rw [getD_set_ne_seg sa (by omega)]; exact hinpa i
        · intro r; rw [getD_set_ne_seg sa (by omega)]; exact hregsa r
        · rw [getD_set_ne_seg sa (by omega)]; exact houtLa
        · rw [getD_set_self_seg sa (by omega)]
        · rw [getD_set_ne_seg sa (by omega)]; exact houtBa
        · rw [getD_set_ne_seg sa (by omega)]; exact htmp1a
        · rw [getD_set_ne_seg sa (by omega)]; exact htmp2a
        · rw [getD_set_ne_seg sa (by omega)]; exact hWa
      rcases emitPadCircuit6_spec base R w L_buf M_blk B seg_inp h_inp inp hinv_dz (by omega) hL_pow
        with ⟨q_c6, τ_c6, hinv_c6, hout_c6, he_c6⟩
      have he_right := sumStep_inr_spec (nopStep Unit) (emitPadCircuit6 base R) he_c6
      have hbody := (seq0_spec
        (f := fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (emitPadCircuit6Entry base R))
        hlen_pos he_dz (by rw [hz_dz]; exact he_right)).weaken S_pad (by dsimp only [S_pad]; omega)
      have hpre6_pad : (pre ++ c6).length + 6 * rem ≤ L_buf := by
        simp only [c6, List.length_append, List.length_cons, List.length_nil]; omega
      rcases ih (pre ++ c6) τ_c6 (by omega) hpre6_pad hinv_c6
        with ⟨τ_end, hinv_end, hout_end, he_rest⟩
      rw [List.append_assoc, range_flatMap_const rem c6] at hinv_end
      have hstep := (loop0_step (next := padLoopNext base R) hlen_pos hbody rfl he_rest).weaken
        ((rem + 1 + 1) * (S_pad + 2)) (by
          have : (rem + 1 + 1) * (S_pad + 2) = (S_pad + 2) + (rem + 1) * (S_pad + 2) := by ring
          omega)
      exact ⟨τ_end, hinv_end, fun p hp => (hout_end p hp).trans ((hout_c6 p hp).trans (hout_dz p hp)), hstep⟩
  rcases hloop (3 * M_blk) emitted τ_cp (Nat.le_refl _) hem_pad hinv_cp
    with ⟨τ_end, hinv_end, hout_end, he_lp⟩
  have he_tot := seq0_spec
    (f := fun _ => Sum.inl (wsDecJzEntry MaxSeg ⟨base + R + 1, by omega⟩))
    hlen_pos he_cp he_lp
  have htime : (3 * M_blk + 2) * (150 * M_blk + 50) + 1 + (3 * M_blk + 1) * (S_pad + 2) ≤
      (3 * M_blk + 2) * (6 * ((L_buf + 2) * (250 * M_blk + 100)) + 210 * M_blk + 100) := by
    calc (3 * M_blk + 2) * (150 * M_blk + 50) + 1 + (3 * M_blk + 1) * (S_pad + 2)
        ≤ (3 * M_blk + 2) * (150 * M_blk + 50) + 1 + (3 * M_blk + 2) * (S_pad + 2) := by
          have := Nat.mul_le_mul_right (S_pad + 2) (show 3 * M_blk + 1 ≤ 3 * M_blk + 2 by omega)
          omega
      _ = 1 + (3 * M_blk + 2) * (6 * ((L_buf + 2) * (250 * M_blk + 100)) + 200 * M_blk + 82) := by
          dsimp only [S_pad]; ring
      _ ≤ (3 * M_blk + 2) * (6 * ((L_buf + 2) * (250 * M_blk + 100)) + 210 * M_blk + 100) := by
          have : (3 * M_blk + 2) * (6 * ((L_buf + 2) * (250 * M_blk + 100)) + 210 * M_blk + 100) =
              (3 * M_blk + 2) * (6 * ((L_buf + 2) * (250 * M_blk + 100)) + 200 * M_blk + 82) +
              (3 * M_blk + 2) * (10 * M_blk + 18) := by ring
          have : 1 ≤ (3 * M_blk + 2) * (10 * M_blk + 18) := Nat.mul_pos (by omega) (by omega)
          omega
  exact ⟨_, τ_end, hinv_end, fun p hp => (hout_end p hp).trans (hout_cp p hp), he_tot.weaken _ htime⟩

/-!
### Right-to-Left Buffer Unpacker (`unpackOutLoop`), Workspace Sweep (`execRMToOutput`), and Polynomial Bridges
-/

def WSUnpackInv (base R w L_buf M_blk B : ℕ) (full_tail : List Bool)
    (τ : ℕ → Bool) (len rem : ℕ) : Prop :=
  ∃ segs : List (List Bool),
    segs.length = base + R + 6 ∧
    (encodeWorkspace segs).length = M_blk ∧
    TapeWS τ len B segs ∧
    segs.getD (base + R) [] = natToBitsLE w rem ∧
    (segs.getD (base + R + 1) []).length = w ∧
    segs.getD (base + R + 2) [] = full_tail ++ List.replicate (L_buf - full_tail.length) false ∧
    (segs.getD (base + R + 3) []).length = w ∧
    (segs.getD (base + R + 4) []).length = w

abbrev UnpackActiveQ (MaxSeg : ℕ) : Type :=
  (SegTriple MaxSeg × WsCopyInnerQ MaxSeg) ⊕
  ((SegQuad MaxSeg × WsReadBitInnerQ MaxSeg) ⊕
   ((Fin (MaxSeg + 1) × Bool) × ShuttleWriteInnerQ MaxSeg))

def unpackActive (base R : ℕ) : StepFn (UnpackActiveQ (base + R + 5)) :=
  let MaxSeg := base + R + 5
  let qd : SegQuad MaxSeg :=
    (⟨base + R + 2, by omega⟩, ⟨base + R, by omega⟩, ⟨base + R + 3, by omega⟩, ⟨base + R + 4, by omega⟩)
  seq0 (wsCopy MaxSeg)
    (seq0 (wsReadBit MaxSeg) (shuttleWrite MaxSeg)
      (fun q_rb => shuttleWriteEntry MaxSeg ⟨base + R + 1, by omega⟩ (wsReadBitResult q_rb)))
    (fun _ => Sum.inl (wsReadBitEntry MaxSeg qd))

def unpackActiveEntry (base R : ℕ) : UnpackActiveQ (base + R + 5) :=
  let MaxSeg := base + R + 5
  Sum.inl (wsCopyEntry MaxSeg (⟨base + R + 1, by omega⟩, ⟨base + R, by omega⟩, ⟨base + R + 3, by omega⟩))

abbrev UnpackLoopQ (base R : ℕ) : Type :=
  WsDecJzQ (base + R + 5) ⊕ (Unit ⊕ UnpackActiveQ (base + R + 5))

def unpackBody (base R : ℕ) : StepFn (UnpackLoopQ base R) :=
  seq0 (wsDecJz (base + R + 5))
    (sumStep (nopStep Unit) (unpackActive base R))
    (fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (unpackActiveEntry base R))

def unpackNext (base R : ℕ) : UnpackLoopQ base R → Option (UnpackLoopQ base R)
  | Sum.inr (Sum.inr _) => some (Sum.inl (wsDecJzEntry (base + R + 5) ⟨base + R, by omega⟩))
  | _ => none

def unpackOutLoop (base R : ℕ) : StepFn (UnpackLoopQ base R) :=
  loop0 (unpackBody base R) (unpackNext base R)

def unpackOutLoopEntry (base R : ℕ) : UnpackLoopQ base R :=
  Sum.inl (wsDecJzEntry (base + R + 5) ⟨base + R, by omega⟩)

theorem unpackOutLoop_spec (base R w L_buf M_blk B : ℕ) (full_tail : List Bool)
    (htail_le : full_tail.length ≤ L_buf)
    (hL_pow : L_buf < 2 ^ w)
    (hout_le_B : 3 * M_blk + full_tail.length ≤ B)
    {τ₁ : ℕ → Bool}
    (hinv : WSUnpackInv base R w L_buf M_blk B full_tail τ₁ (3 * M_blk) full_tail.length)
    (hclean : ∀ p, 3 * M_blk ≤ p → τ₁ p = false) :
    ∃ τ₂ : ℕ → Bool,
      WSUnpackInv base R w L_buf M_blk B full_tail τ₂ (3 * M_blk + full_tail.length) 0 ∧
      (∀ i < full_tail.length, τ₂ (3 * M_blk + i) = full_tail.getD i false) ∧
      StepExec (unpackOutLoop base R) B (unpackOutLoopEntry base R) (3 * M_blk) τ₁ 0
        (Sum.inr (Sum.inl ())) (3 * M_blk + full_tail.length) τ₂ 0
        ((L_buf + 1) * ((L_buf + 2) * (450 * M_blk + 2 * L_buf + 200) + 2)) := by
  let MaxSeg := base + R + 5
  let L_tail := full_tail.length
  let S_unp := (L_buf + 2) * (450 * M_blk + 2 * L_buf + 200)
  have haux : ∀ rem (τa : ℕ → Bool),
      rem ≤ L_tail →
      WSUnpackInv base R w L_buf M_blk B full_tail τa
        (if rem = L_tail then 3 * M_blk else 3 * M_blk + L_tail) rem →
      (∀ p, 3 * M_blk ≤ p → p < 3 * M_blk + rem → τa p = false) →
      (∀ i, rem ≤ i → i < L_tail → τa (3 * M_blk + i) = full_tail.getD i false) →
      ∃ τ₂ : ℕ → Bool,
        WSUnpackInv base R w L_buf M_blk B full_tail τ₂ (3 * M_blk + L_tail) 0 ∧
        (∀ i < L_tail, τ₂ (3 * M_blk + i) = full_tail.getD i false) ∧
        StepExec (unpackOutLoop base R) B (unpackOutLoopEntry base R)
          (if rem = L_tail then 3 * M_blk else 3 * M_blk + L_tail) τa 0
          (Sum.inr (Sum.inl ())) (3 * M_blk + L_tail) τ₂ 0
          ((rem + 1) * (S_unp + 2)) := by
    intro rem
    induction rem with
    | zero =>
      intro τa _ hinv_a _ hwritten
      have hlen_eq : (if 0 = L_tail then 3 * M_blk else 3 * M_blk + L_tail) = 3 * M_blk + L_tail := by
        split_ifs with h0 <;> omega
      rw [hlen_eq] at hinv_a ⊢
      rcases hinv_a with ⟨sa, hla, hMa, htwa, houtLa, hsys1a, houtBa, htmp1a, htmp2a⟩
      have hlen_pos := TapeWS_pos htwa
      have hlen_B := htwa.2.2.1
      rcases wsDecJz_spec MaxSeg B sa (s := base + R) (w := w) (v := 0)
          (by omega) (by omega) houtLa (by omega) htwa
        with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
      rw [hMa] at hout_dz he_dz
      simp only [decide_true, ↓reduceIte] at hz_dz htw_dz
      have he_nop := sumStep_inl_spec (nopStep Unit) (unpackActive base R)
        (nopStep_spec () (3 * M_blk + L_tail) τ_dz 0 hlen_B (by omega))
      have hbody := seq0_spec
        (f := fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (unpackActiveEntry base R))
        hlen_pos he_dz (by rw [hz_dz]; exact he_nop)
      have hdone := (loop0_done (next := unpackNext base R) hbody rfl).weaken
        ((0 + 1) * (S_unp + 2)) (by
          have : 2 * (450 * M_blk + 2 * L_buf + 200) ≤ S_unp := Nat.mul_le_mul_right _ (by omega)
          omega)
      refine ⟨τ_dz, ⟨sa, hla, hMa, htw_dz, houtLa, hsys1a, houtBa, htmp1a, htmp2a⟩, ?_, hdone⟩
      intro i hi
      rw [hout_dz _ (by omega)]
      exact hwritten i (Nat.zero_le i) hi
    | succ rem ih =>
      intro τa hrem_le hinv_a hpre_a hwritten_a
      let len_a := if rem + 1 = L_tail then 3 * M_blk else 3 * M_blk + L_tail
      change WSUnpackInv base R w L_buf M_blk B full_tail τa len_a (rem + 1) at hinv_a
      rcases hinv_a with ⟨sa, hla, hMa, htwa, houtLa, hsys1a, houtBa, htmp1a, htmp2a⟩
      have hlen_pos := TapeWS_pos htwa
      have hrem_lt_L : rem < L_tail := by omega
      have hrem1_pow : rem + 1 < 2 ^ w := by omega
      have hrem_pow : rem < 2 ^ w := by omega
      -- 1. wsDecJz on base + R (rem + 1 -> rem)
      rcases wsDecJz_spec MaxSeg B sa (s := base + R) (w := w) (v := rem + 1)
          (by omega) (by omega) houtLa hrem1_pow htwa
        with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
      rw [hMa] at hout_dz he_dz
      simp only [Nat.succ_ne_zero, decide_false, ↓reduceIte, Nat.add_sub_cancel] at hz_dz htw_dz
      let sa₁ := sa.set (base + R) (natToBitsLE w rem)
      have hMa₁ : (encodeWorkspace sa₁).length = M_blk :=
        (length_encodeWorkspace_set (by omega) (by rw [houtLa, length_natToBitsLE, length_natToBitsLE])).trans hMa
      -- 2. wsCopy from base + R (rem) into base + R + 1 (s_sys1) using tmp = base + R + 3
      rcases wsCopy_spec MaxSeg B sa₁ (dst := base + R + 1) (src := base + R) (tmp := base + R + 3)
          (w := w) (v := rem)
          (by simp [sa₁]; omega) (by simp [sa₁]; omega) (by simp [sa₁]; omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by dsimp only [sa₁]; rw [getD_set_ne_seg _ (by omega), hsys1a])
          (by dsimp only [sa₁]; rw [getD_set_self_seg _ (by omega)])
          (by dsimp only [sa₁]; rw [getD_set_ne_seg _ (by omega), htmp1a])
          hrem_pow htw_dz
        with ⟨q_cp, τ_cp, htw_cp, hout_cp, he_cp⟩
      rw [hMa₁] at hout_cp he_cp
      let sa₂_0 := sa₁.set (base + R + 1) (natToBitsLE w rem)
      let sa₂ := sa₂_0.set (base + R + 3) (natToBitsLE w 0)
      have hMa₂ : (encodeWorkspace sa₂).length = M_blk := by
        have h1 := length_encodeWorkspace_set (segs := sa₁) (s := base + R + 1)
          (newSeg := natToBitsLE w rem) (by simp [sa₁]; omega)
          (by dsimp only [sa₁]; rw [getD_set_ne_seg _ (by omega), hsys1a, length_natToBitsLE])
        have h2 := length_encodeWorkspace_set (segs := sa₂_0) (s := base + R + 3)
          (newSeg := natToBitsLE w 0) (by simp [sa₂_0, sa₁]; omega)
          (by dsimp only [sa₂_0, sa₁]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), htmp1a, length_natToBitsLE])
        exact h2.trans (h1.trans hMa₁)
      -- 3. wsReadBit on arr = base + R + 2, idx = base + R (rem), tmp = base + R + 3, tmp2 = base + R + 4
      rcases wsReadBit_spec MaxSeg B sa₂ (arr := base + R + 2) (idx := base + R)
          (tmp := base + R + 3) (tmp2 := base + R + 4) (w := w) (v := rem)
          (by simp [sa₂, sa₂_0, sa₁]; omega) (by simp [sa₂, sa₂_0, sa₁]; omega)
          (by simp [sa₂, sa₂_0, sa₁]; omega) (by simp [sa₂, sa₂_0, sa₁]; omega)
          (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by dsimp only [sa₂, sa₂_0, sa₁]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by omega)])
          (by dsimp only [sa₂, sa₂_0, sa₁]; rw [getD_set_self_seg _ (by simp; omega), length_natToBitsLE])
          (by dsimp only [sa₂, sa₂_0, sa₁]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), htmp2a])
          hrem_pow htw_cp
        with ⟨q_rb, τ_rb, hres_rb, htw_rb, hout_rb, he_rb⟩
      rw [hMa₂] at hout_rb he_rb
      have houtB₂ : sa₂.getD (base + R + 2) [] = full_tail ++ List.replicate (L_buf - full_tail.length) false := by
        dsimp only [sa₂, sa₂_0, sa₁]
        rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), houtBa]
      have hbit_eq : wsReadBitResult q_rb = full_tail.getD rem false := by
        rw [hres_rb, houtB₂, getD_append_left _ _ _ hrem_lt_L]
      let sa₃_0 := sa₂.set (base + R + 3) (natToBitsLE w 0)
      let sa₃ := sa₃_0.set (base + R + 4) (natToBitsLE w 0)
      have hMa₃ : (encodeWorkspace sa₃).length = M_blk := by
        have h1 := length_encodeWorkspace_set (segs := sa₂) (s := base + R + 3)
          (newSeg := natToBitsLE w 0) (by simp [sa₂, sa₂_0, sa₁]; omega)
          (by dsimp only [sa₂, sa₂_0, sa₁]; rw [getD_set_self_seg _ (by simp; omega)])
        have h2 := length_encodeWorkspace_set (segs := sa₃_0) (s := base + R + 4)
          (newSeg := natToBitsLE w 0) (by simp [sa₃_0, sa₂, sa₂_0, sa₁]; omega)
          (by dsimp only [sa₃_0, sa₂, sa₂_0, sa₁]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), htmp2a, length_natToBitsLE])
        exact h2.trans (h1.trans hMa₂)
      -- 4. shuttleWrite on s_off = base + R + 1 (rem) with bit wsReadBitResult q_rb
      have hsys1₃ : sa₃.getD (base + R + 1) [] = natToBitsLE w rem := by
        dsimp only [sa₃, sa₃_0, sa₂, sa₂_0, sa₁]
        rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
            getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by simp; omega)]
      have hclean_rb : ∀ p, 3 * (encodeWorkspace sa₃).length ≤ p →
          p ≤ 3 * (encodeWorkspace sa₃).length + rem → τ_rb p = false := by
        intro p hp1 hp2
        rw [hMa₃] at hp1 hp2
        rw [hout_rb p hp1, hout_cp p hp1, hout_dz p hp1]
        exact hpre_a p hp1 (by omega)
      rcases shuttleWrite_spec MaxSeg B sa₃ (s_off := base + R + 1) (w := w) (offset := rem)
          (wsReadBitResult q_rb)
          (by simp [sa₃, sa₃_0, sa₂, sa₂_0, sa₁]; omega) (by omega) hsys1₃ hrem_pow
          (by rw [hMa₃]; omega) htw_rb hclean_rb
        with ⟨q_sw, τ_sw, htw_sw, hpre_sw, hcur_sw, hout_sw, he_sw⟩
      rw [hMa₃] at htw_sw hpre_sw hcur_sw hout_sw he_sw
      let sa₄ := sa₃.set (base + R + 1) (natToBitsLE w 0)
      have hMa₄ : (encodeWorkspace sa₄).length = M_blk :=
        (length_encodeWorkspace_set (by simp [sa₃, sa₃_0, sa₂, sa₂_0, sa₁]; omega)
          (by rw [hsys1₃, length_natToBitsLE, length_natToBitsLE])).trans hMa₃
      have hlen_next : max len_a (3 * M_blk + rem + 1) =
          (if rem = L_tail then 3 * M_blk else 3 * M_blk + L_tail) := by
        dsimp only [len_a]
        split_ifs <;> omega
      rw [hlen_next] at htw_sw he_sw
      let qd : SegQuad MaxSeg :=
        (⟨base + R + 2, by omega⟩, ⟨base + R, by omega⟩, ⟨base + R + 3, by omega⟩, ⟨base + R + 4, by omega⟩)
      have he_rbsw := seq0_spec
        (f := fun q => shuttleWriteEntry MaxSeg ⟨base + R + 1, by omega⟩ (wsReadBitResult q))
        hlen_pos he_rb he_sw
      have he_act := seq0_spec (f := fun _ => Sum.inl (wsReadBitEntry MaxSeg qd)) hlen_pos he_cp he_rbsw
      have he_right := sumStep_inr_spec (nopStep Unit) (unpackActive base R) he_act
      have htime_body : 42 * M_blk + 10 + 1 +
          ((rem + 2) * (150 * M_blk + 50) + 1 +
           ((rem + 2) * (220 * M_blk + 80) + 1 + (rem + 2) * (16 * (3 * M_blk) + 2 * rem + 30))) ≤ S_unp := by
        have hrem_L : rem ≤ L_buf := by omega
        calc 42 * M_blk + 10 + 1 +
              ((rem + 2) * (150 * M_blk + 50) + 1 +
               ((rem + 2) * (220 * M_blk + 80) + 1 + (rem + 2) * (16 * (3 * M_blk) + 2 * rem + 30)))
            ≤ (42 * M_blk + 13) + (rem + 2) * (418 * M_blk + 2 * rem + 160) := by
              have : (rem + 2) * (150 * M_blk + 50) + (rem + 2) * (220 * M_blk + 80) +
                  (rem + 2) * (16 * (3 * M_blk) + 2 * rem + 30) =
                  (rem + 2) * (418 * M_blk + 2 * rem + 160) := by ring
              omega
          _ ≤ (42 * M_blk + 13) + (L_buf + 2) * (418 * M_blk + 2 * L_buf + 160) := by
              have := Nat.mul_le_mul (show rem + 2 ≤ L_buf + 2 by omega)
                (show 418 * M_blk + 2 * rem + 160 ≤ 418 * M_blk + 2 * L_buf + 160 by omega)
              omega
          _ ≤ (L_buf + 2) * (450 * M_blk + 2 * L_buf + 200) := by
              have : (L_buf + 2) * (450 * M_blk + 2 * L_buf + 200) =
                  (L_buf + 2) * (418 * M_blk + 2 * L_buf + 160) + (L_buf + 2) * (32 * M_blk + 40) := by ring
              have : 2 * (32 * M_blk + 40) ≤ (L_buf + 2) * (32 * M_blk + 40) :=
                Nat.mul_le_mul_right _ (by omega)
              omega
      have hbody := (seq0_spec
        (f := fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (unpackActiveEntry base R))
        hlen_pos he_dz (by rw [hz_dz]; exact he_right)).weaken S_unp htime_body
      have hinv_sw : WSUnpackInv base R w L_buf M_blk B full_tail τ_sw
          (if rem = L_tail then 3 * M_blk else 3 * M_blk + L_tail) rem := by
        refine ⟨sa₄, by simp [sa₄, sa₃, sa₃_0, sa₂, sa₂_0, sa₁, hla], hMa₄, htw_sw, ?_, ?_, ?_, ?_, ?_⟩
        · dsimp only [sa₄, sa₃, sa₃_0, sa₂, sa₂_0, sa₁]
          rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
              getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by omega)]
        · dsimp only [sa₄]; rw [getD_set_self_seg _ (by simp [sa₃, sa₃_0, sa₂, sa₂_0, sa₁]; omega), length_natToBitsLE]
        · dsimp only [sa₄, sa₃, sa₃_0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), houtB₂]
        · dsimp only [sa₄, sa₃, sa₃_0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by simp [sa₂, sa₂_0, sa₁]; omega), length_natToBitsLE]
        · dsimp only [sa₄, sa₃, sa₃_0]; rw [getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by simp [sa₂, sa₂_0, sa₁]; omega), length_natToBitsLE]
      have hwritten_sw : ∀ i, rem ≤ i → i < L_tail → τ_sw (3 * M_blk + i) = full_tail.getD i false := by
        intro i hi1 hi2
        by_cases hieq : i = rem
        · subst hieq; rw [hcur_sw, hbit_eq]
        · have hgt : 3 * M_blk + rem < 3 * M_blk + i := by omega
          rw [hout_sw _ hgt, hout_rb _ (by omega), hout_cp _ (by omega), hout_dz _ (by omega)]
          exact hwritten_a i (by omega) hi2
      have hlen_sw_pos := TapeWS_pos htw_sw
      rcases ih τ_sw (by omega) hinv_sw hpre_sw hwritten_sw with ⟨τ_end, hinv_end, hwr_end, he_rest⟩
      have hstep := (loop0_step (next := unpackNext base R) hlen_sw_pos hbody rfl he_rest).weaken
        ((rem + 1 + 1) * (S_unp + 2)) (by
          have : (rem + 1 + 1) * (S_unp + 2) = (S_unp + 2) + (rem + 1) * (S_unp + 2) := by ring
          omega)
      exact ⟨τ_end, hinv_end, hwr_end, hstep⟩
  rcases haux L_tail τ₁ (Nat.le_refl _) (by simpa [L_tail] using hinv)
      (fun p hp _ => hclean p hp) (fun i hi1 hi2 => by omega)
    with ⟨τ₂, hinv₂, hwr₂, he_tot⟩
  simp only [↓reduceIte] at he_tot
  refine ⟨τ₂, hinv₂, hwr₂, he_tot.weaken _ ?_⟩
  exact Nat.mul_le_mul_right (S_unp + 2) (by omega)

abbrev PadPhaseQ (base R : ℕ) : Type :=
  Unit ⊕ ((SegTriple (base + R + 5) × WsCopyInnerQ (base + R + 5)) ⊕ PadLoopQ base R)

def padPhase (base R : ℕ) : StepFn (PadPhaseQ base R) :=
  sumStep (nopStep Unit) (appendPadTail base R)

def padPhaseEntry (base R : ℕ) (appendPad : Bool) : PadPhaseQ base R :=
  if appendPad then Sum.inr (appendPadTailEntry base R) else Sum.inl ()

abbrev ExecRMOutQ (base R : ℕ) (Q : Type) : Type :=
  (Q × RMSubQ base R) ⊕
  (PadPhaseQ base R ⊕
   (UnpackLoopQ base R ⊕ LiftBlkQ Bool))

def execRMToOutput (base R seg_inp : ℕ) (appendPad : Bool) {Q : Type} (M : RMProg R Q) :
    StepFn (ExecRMOutQ base R Q) :=
  seq0 (simRMLoop base R seg_inp M)
    (seq0 (padPhase base R)
      (seq0 (unpackOutLoop base R) (liftBlockStep blkSweepTrue)
        (fun _ => liftBlkEntry false))
      (fun _ => Sum.inl (unpackOutLoopEntry base R)))
    (fun _ => Sum.inl (padPhaseEntry base R appendPad))

def execRMToOutputEntry (base R seg_inp : ℕ) {Q : Type} (M : RMProg R Q) (q₀ : Q) :
    ExecRMOutQ base R Q :=
  Sum.inl (q₀, rmSubEntry base R seg_inp M q₀)

def execRMTimeBound (steps Vmax L_buf M_blk : ℕ) : ℕ :=
  (steps + 1) * ((max Vmax L_buf + 2) * (250 * M_blk + 100) + 2) +
  (3 * M_blk + 2) * (6 * ((L_buf + 2) * (250 * M_blk + 100)) + 210 * M_blk + 100) +
  (L_buf + 1) * ((L_buf + 2) * (450 * M_blk + 2 * L_buf + 200) + 2) +
  14 * M_blk + 20

theorem execRMToOutput_spec (base R w L_buf M_blk B seg_inp Vmax : ℕ) (appendPad : Bool)
    (h_inp : seg_inp < base) (hV_pow : Vmax < 2 ^ w) (hL_pow : L_buf < 2 ^ w)
    {Q : Type} (M : RMProg R Q) (inp : List Bool)
    {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {emitted : List Bool} {steps sys1Val : ℕ}
    (hexec : RMExec M Vmax inp q₀ reg₀ q₁ reg₁ emitted steps)
    (hbuf : (if appendPad then
        emitted ++ (List.range (3 * M_blk)).flatMap (fun _ => [false, true, false, false, false, true])
      else emitted).length ≤ L_buf)
    (hout_B : 3 * M_blk + (if appendPad then
        emitted ++ (List.range (3 * M_blk)).flatMap (fun _ => [false, true, false, false, false, true])
      else emitted).length ≤ B)
    {τ₀ : ℕ → Bool}
    (hinv₀ : WSRMInv base R w L_buf M_blk B seg_inp inp τ₀ (3 * M_blk) reg₀ [] sys1Val)
    (hclean₀ : ∀ p, 3 * M_blk ≤ p → τ₀ p = false) :
    let full_tail := if appendPad then
        emitted ++ (List.range (3 * M_blk)).flatMap (fun _ => [false, true, false, false, false, true])
      else emitted
    let out := List.replicate (3 * M_blk) true ++ full_tail
    ∃ q_end, ∃ τ_final : ℕ → Bool,
      1 ≤ out.length ∧
      (∀ j < out.length, τ_final j = QCSD_tapeRead out j) ∧
      StepExec (execRMToOutput base R seg_inp appendPad M) B
        (execRMToOutputEntry base R seg_inp M q₀) (3 * M_blk) τ₀ 0
        q_end out.length τ_final 0 (execRMTimeBound steps Vmax L_buf M_blk) := by
  intro full_tail out
  have hlen0_pos : 1 ≤ 3 * M_blk := by rcases hinv₀ with ⟨_, _, _, htw₀, _⟩; exact TapeWS_pos htw₀
  have hem_le : emitted.length ≤ L_buf := by
    cases appendPad <;> simp at hbuf <;> omega
  -- Stage 1: simRMLoop
  rcases simRMLoop_spec base R w L_buf M_blk B seg_inp Vmax h_inp hV_pow hL_pow M inp hexec hem_le hinv₀
    with ⟨τ₁, hinv₁, hout₁, he_sim⟩
  have hclean₁ : ∀ p, 3 * M_blk ≤ p → τ₁ p = false := fun p hp => (hout₁ p hp).trans (hclean₀ p hp)
  -- Stage 2: padPhase
  have hstage2 : ∃ q_pad, ∃ τ₂ : ℕ → Bool,
      WSUnpackInv base R w L_buf M_blk B full_tail τ₂ (3 * M_blk) full_tail.length ∧
      (∀ p, 3 * M_blk ≤ p → τ₂ p = false) ∧
      StepExec (padPhase base R) B (padPhaseEntry base R appendPad) (3 * M_blk) τ₁ 0
        q_pad (3 * M_blk) τ₂ 0
        ((3 * M_blk + 2) * (6 * ((L_buf + 2) * (250 * M_blk + 100)) + 210 * M_blk + 100)) := by
    cases appendPad with
    | false =>
      dsimp only [full_tail, Bool.false_eq_true, ↓reduceIte, padPhaseEntry]
      rcases hinv₁ with ⟨s1, hl1, hM1, htw1, _, _, houtL1, hsys1_1, houtB1, _, htmp1_1, htmp2_1, _⟩
      have he_nop := (sumStep_inl_spec (nopStep Unit) (appendPadTail base R)
        (nopStep_spec () (3 * M_blk) τ₁ 0 htw1.2.2.1 (by omega))).weaken
        ((3 * M_blk + 2) * (6 * ((L_buf + 2) * (250 * M_blk + 100)) + 210 * M_blk + 100)) (by omega)
      exact ⟨Sum.inl (), τ₁,
        ⟨s1, hl1, hM1, htw1, houtL1, by rw [hsys1_1, length_natToBitsLE], houtB1, htmp1_1, htmp2_1⟩,
        hclean₁, he_nop⟩
    | true =>
      dsimp only [full_tail, padPhaseEntry]
      simp only [↓reduceIte] at hbuf ⊢
      have hem_pad : emitted.length + 6 * (3 * M_blk) ≤ L_buf := by
        have hpad_len : ((List.range (3 * M_blk)).flatMap
            (fun _ => [false, true, false, false, false, true])).length = 6 * (3 * M_blk) := by
          clear * -
          induction (3 * M_blk) with
          | zero => simp
          | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; omega
        rw [List.length_append, hpad_len] at hbuf
        exact hbuf
      rcases appendPadTail_spec base R w L_buf M_blk B seg_inp h_inp inp hinv₁ hem_pad hL_pow
        with ⟨q_ap, τ₂, hinv₂, hout₂, he_ap⟩
      rcases hinv₂ with ⟨s2, hl2, hM2, htw2, _, _, houtL2, hsys1_2, houtB2, _, htmp1_2, htmp2_2, _⟩
      exact ⟨Sum.inr q_ap, τ₂,
        ⟨s2, hl2, hM2, htw2, houtL2, by rw [hsys1_2, length_natToBitsLE], houtB2, htmp1_2, htmp2_2⟩,
        fun p hp => (hout₂ p hp).trans (hclean₁ p hp),
        sumStep_inr_spec (nopStep Unit) (appendPadTail base R) he_ap⟩
  rcases hstage2 with ⟨q_pad, τ₂, hunp₂, hclean₂, he_pad⟩
  -- Stage 3: unpackOutLoop
  rcases unpackOutLoop_spec base R w L_buf M_blk B full_tail hbuf hL_pow hout_B hunp₂ hclean₂
    with ⟨τ₃, hunp₃, hwr₃, he_unp⟩
  -- Stage 4: blkSweepTrue
  rcases hunp₃ with ⟨s3, hl3, hM3, htw3, _⟩
  rcases htw3 with ⟨hs3_ne, hW_le3, hlen_B3, hws3⟩
  rw [hM3] at hW_le3
  rcases blkSweepTrue_spec s3 hs3_ne (readBlk τ₃) hws3 with ⟨σ_end, hall_home, hblk_sw⟩
  rw [hM3] at hall_home hblk_sw
  rcases liftBlockStep_spec blkSweepTrue B M_blk (3 * M_blk + full_tail.length) τ₃
      false true σ_end 0 0 (2 * M_blk) hW_le3 hlen_B3 hblk_sw
    with ⟨τ_final, hread_fin, hout_fin, he_sw⟩
  simp only [Nat.mul_zero] at he_sw
  have hout_len : out.length = 3 * M_blk + full_tail.length := by
    simp [out]
  have hout_pos : 1 ≤ out.length := by omega
  have he34 := seq0_spec (f := fun _ => liftBlkEntry false) (by omega) he_unp he_sw
  have he24 := seq0_spec (f := fun _ => Sum.inl (unpackOutLoopEntry base R)) hlen0_pos he_pad he34
  have he14 := (seq0_spec (f := fun _ => Sum.inl (padPhaseEntry base R appendPad)) hlen0_pos he_sim he24).weaken
    (execRMTimeBound steps Vmax L_buf M_blk) (by dsimp only [execRMTimeBound]; omega)
  rw [← hout_len] at he14
  refine ⟨_, τ_final, hout_pos, ?_, he14⟩
  intro j hj
  rw [hout_len] at hj
  simp only [QCSD_tapeRead, out]
  by_cases hjW : j < 3 * M_blk
  · rw [getD_append_left _ _ _ (by simpa using hjW)]
    have hrep : (List.replicate (3 * M_blk) true).getD j false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      simp [hjW]
    rw [hrep]
    have hdiv : j / 3 < M_blk := by omega
    have hblk := (congrFun hread_fin (j / 3)).trans (hall_home (j / 3) hdiv)
    dsimp only [readBlk, blkHome] at hblk
    have h0 : τ_final (3 * (j / 3)) = true := (Prod.mk.inj hblk).1
    have h1 : τ_final (3 * (j / 3) + 1) = true := (Prod.mk.inj (Prod.mk.inj hblk).2).1
    have h2 : τ_final (3 * (j / 3) + 2) = true := (Prod.mk.inj (Prod.mk.inj hblk).2).2
    have hmod : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hmod with hm | hm | hm
    · have : j = 3 * (j / 3) := by omega
      rw [this, h0]
    · have : j = 3 * (j / 3) + 1 := by omega
      rw [this, h1]
    · have : j = 3 * (j / 3) + 2 := by omega
      rw [this, h2]
  · rw [getD_append_right _ _ _ (by simp; omega)]
    simp only [List.length_replicate]
    have heq : j = 3 * M_blk + (j - 3 * M_blk) := by omega
    conv_lhs => rw [heq]
    rw [hout_fin _ (by omega), hwr₃ (j - 3 * M_blk) (by omega)]

instance instFintypeLiftBlkQ {Q : Type} [Fintype Q] : Fintype (LiftBlkQ Q) := by
  unfold LiftBlkQ; infer_instance
instance instDecEqLiftBlkQ {Q : Type} [DecidableEq Q] : DecidableEq (LiftBlkQ Q) := by
  unfold LiftBlkQ; infer_instance

instance instFintypeWsDecJzQ (MaxSeg : ℕ) : Fintype (WsDecJzQ MaxSeg) := by
  unfold WsDecJzQ; infer_instance
instance instDecEqWsDecJzQ (MaxSeg : ℕ) : DecidableEq (WsDecJzQ MaxSeg) := by
  unfold WsDecJzQ; infer_instance

instance instDecEqWsDrainQ (MaxSeg : ℕ) : DecidableEq (WsDrainQ MaxSeg) := by
  unfold WsDrainQ; infer_instance
instance instDecEqWsRestoreQ (MaxSeg : ℕ) : DecidableEq (WsRestoreQ MaxSeg) := by
  unfold WsRestoreQ; infer_instance
instance instFintypeWsCopyInnerQ (MaxSeg : ℕ) : Fintype (WsCopyInnerQ MaxSeg) := by
  unfold WsCopyInnerQ WsDrainQ WsRestoreQ; infer_instance
instance instDecEqWsCopyInnerQ (MaxSeg : ℕ) : DecidableEq (WsCopyInnerQ MaxSeg) := by
  unfold WsCopyInnerQ; infer_instance

instance instFintypeWsReadBitInnerQ (MaxSeg : ℕ) : Fintype (WsReadBitInnerQ MaxSeg) := by
  unfold WsReadBitInnerQ WsReadLoopQ; infer_instance
instance instDecEqWsReadBitInnerQ (MaxSeg : ℕ) : DecidableEq (WsReadBitInnerQ MaxSeg) := by
  unfold WsReadBitInnerQ WsReadLoopQ; infer_instance

instance instFintypeWsWriteBitInnerQ (MaxSeg : ℕ) : Fintype (WsWriteBitInnerQ MaxSeg) := by
  unfold WsWriteBitInnerQ WsWriteLoopQ; infer_instance
instance instDecEqWsWriteBitInnerQ (MaxSeg : ℕ) : DecidableEq (WsWriteBitInnerQ MaxSeg) := by
  unfold WsWriteBitInnerQ WsWriteLoopQ; infer_instance

instance instFintypeWsEmitBitInnerQ (MaxSeg : ℕ) : Fintype (WsEmitBitInnerQ MaxSeg) := by
  unfold WsEmitBitInnerQ; infer_instance
instance instDecEqWsEmitBitInnerQ (MaxSeg : ℕ) : DecidableEq (WsEmitBitInnerQ MaxSeg) := by
  unfold WsEmitBitInnerQ; infer_instance

instance instFintypeShuttleWriteInnerQ (MaxSeg : ℕ) : Fintype (ShuttleWriteInnerQ MaxSeg) := by
  unfold ShuttleWriteInnerQ ShuttleLoopQ; infer_instance
instance instDecEqShuttleWriteInnerQ (MaxSeg : ℕ) : DecidableEq (ShuttleWriteInnerQ MaxSeg) := by
  unfold ShuttleWriteInnerQ ShuttleLoopQ; infer_instance

instance instFintypeRMSubQ (base R : ℕ) : Fintype (RMSubQ base R) := by
  unfold RMSubQ; infer_instance
instance instDecEqRMSubQ (base R : ℕ) : DecidableEq (RMSubQ base R) := by
  unfold RMSubQ; infer_instance

instance instFintypeEmit6Q (base R : ℕ) : Fintype (Emit6Q base R) := by
  unfold Emit6Q EmitOneQ; infer_instance
instance instDecEqEmit6Q (base R : ℕ) : DecidableEq (Emit6Q base R) := by
  unfold Emit6Q EmitOneQ; infer_instance

instance instFintypePadPhaseQ (base R : ℕ) : Fintype (PadPhaseQ base R) := by
  unfold PadPhaseQ PadLoopQ; infer_instance
instance instDecEqPadPhaseQ (base R : ℕ) : DecidableEq (PadPhaseQ base R) := by
  unfold PadPhaseQ PadLoopQ; infer_instance

instance instFintypeUnpackLoopQ (base R : ℕ) : Fintype (UnpackLoopQ base R) := by
  unfold UnpackLoopQ UnpackActiveQ; infer_instance
instance instDecEqUnpackLoopQ (base R : ℕ) : DecidableEq (UnpackLoopQ base R) := by
  unfold UnpackLoopQ UnpackActiveQ; infer_instance

instance instFintypeExecRMOutQ (base R : ℕ) (Q : Type) [Fintype Q] : Fintype (ExecRMOutQ base R Q) := by
  unfold ExecRMOutQ; infer_instance
instance instDecEqExecRMOutQ (base R : ℕ) (Q : Type) [DecidableEq Q] : DecidableEq (ExecRMOutQ base R Q) := by
  unfold ExecRMOutQ; infer_instance

/-- Compile any workspace initializer `s_init` + register-machine program `M : RMProg R Q`
into a single deterministic Turing machine `QCSD_DetTM`. -/
def compileRMProgWithInit (base R seg_inp : ℕ) (appendPad : Bool)
    {Q_init Q : Type} [Fintype Q_init] [DecidableEq Q_init] [Fintype Q] [DecidableEq Q]
    (q_init : Q_init) (s_init : StepFn Q_init)
    (M : RMProg R Q) (q₀ : Q) : QCSD_DetTM :=
  toDetTM (Sum.inl q_init)
    (seq0 s_init (execRMToOutput base R seg_inp appendPad M)
      (fun _ => execRMToOutputEntry base R seg_inp M q₀))

theorem compileRMProgWithInit_spec (base R w L_buf M_blk B seg_inp Vmax T_init : ℕ)
    (appendPad : Bool) (h_inp : seg_inp < base) (hV_pow : Vmax < 2 ^ w) (hL_pow : L_buf < 2 ^ w)
    {Q_init Q : Type} [Fintype Q_init] [DecidableEq Q_init] [Fintype Q] [DecidableEq Q]
    (q_init : Q_init) (s_init : StepFn Q_init)
    (M : RMProg R Q) (inp : List Bool)
    {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {emitted : List Bool} {steps sys1Val : ℕ}
    {q_init_end : Q_init} {τ₀ : ℕ → Bool}
    (hinit : StepExec s_init B q_init inp.length (fun i => QCSD_tapeRead inp i) 0
      q_init_end (3 * M_blk) τ₀ 0 T_init)
    (hinv₀ : WSRMInv base R w L_buf M_blk B seg_inp inp τ₀ (3 * M_blk) reg₀ [] sys1Val)
    (hclean₀ : ∀ p, 3 * M_blk ≤ p → τ₀ p = false)
    (hexec : RMExec M Vmax inp q₀ reg₀ q₁ reg₁ emitted steps)
    (hbuf : (if appendPad then
        emitted ++ (List.range (3 * M_blk)).flatMap (fun _ => [false, true, false, false, false, true])
      else emitted).length ≤ L_buf)
    (hout_B : 3 * M_blk + (if appendPad then
        emitted ++ (List.range (3 * M_blk)).flatMap (fun _ => [false, true, false, false, false, true])
      else emitted).length ≤ B) :
    let M_tm := compileRMProgWithInit base R seg_inp appendPad q_init s_init M q₀
    let full_tail := if appendPad then
        emitted ++ (List.range (3 * M_blk)).flatMap (fun _ => [false, true, false, false, false, true])
      else emitted
    let out := List.replicate (3 * M_blk) true ++ full_tail
    ∃ k ≤ T_init + execRMTimeBound steps Vmax L_buf M_blk + 2,
      QCSD_configAt2 M_tm inp k = ⟨M_tm.qhalt, out, 0⟩ ∧
      (∀ j ≤ k, QCSD_spaceUse2 (QCSD_configAt2 M_tm inp j) ≤ B) := by
  intro M_tm full_tail out
  have hlen0_pos : 1 ≤ 3 * M_blk := by rcases hinv₀ with ⟨_, _, _, htw₀, _⟩; exact TapeWS_pos htw₀
  rcases execRMToOutput_spec base R w L_buf M_blk B seg_inp Vmax appendPad
      h_inp hV_pow hL_pow M inp hexec hbuf hout_B hinv₀ hclean₀
    with ⟨q_end, τ_final, hout_pos, hmatch, he_exec⟩
  have he_tot := seq0_spec (f := fun _ => execRMToOutputEntry base R seg_inp M q₀) hlen0_pos hinit he_exec
  have hout_le_B : out.length ≤ B := by simp only [out, List.length_append, List.length_replicate]; exact hout_B
  rcases toDetTM_spec (Sum.inl q_init) _ inp out B _ hout_pos hout_le_B he_tot hmatch
    with ⟨k, hk, hcfg, hsp⟩
  exact ⟨k, by omega, hcfg, hsp⟩

/-!
### Polynomial Register-Width & Subexponential `QCSD_timeBound` Bridge Lemmas
-/

theorem nat_lt_two_pow_self (m : ℕ) : m < 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [Nat.pow_succ]
    omega

theorem poly_lt_two_pow_regWidth (K d n : ℕ) :
    K * (n + 2) ^ d < 2 ^ (d * n + (K + 2 * d)) := by
  have hn_pow : (n + 2) ^ d ≤ 2 ^ ((n + 2) * d) := by
    calc (n + 2) ^ d ≤ (2 ^ (n + 2)) ^ d :=
          Nat.pow_le_pow_left (Nat.le_of_lt (nat_lt_two_pow_self (n + 2))) d
      _ = 2 ^ ((n + 2) * d) := (Nat.pow_mul 2 (n + 2) d).symm
  have hpos : 0 < 2 ^ ((n + 2) * d) := Nat.pos_of_ne_zero (by positivity)
  calc K * (n + 2) ^ d
      ≤ K * 2 ^ ((n + 2) * d) := Nat.mul_le_mul_left K hn_pow
    _ < 2 ^ K * 2 ^ ((n + 2) * d) := Nat.mul_lt_mul_of_pos_right (nat_lt_two_pow_self K) hpos
    _ = 2 ^ (K + (n + 2) * d) := (Nat.pow_add 2 K ((n + 2) * d)).symm
    _ = 2 ^ (d * n + (K + 2 * d)) := by congr 1; ring

theorem exists_Ctm_poly_le_timeBound (K d : ℕ) :
    ∃ Ctm : ℝ, 1 ≤ Ctm ∧ ∀ n : ℕ, 2 ≤ n → K * (n + 2) ^ d ≤ QCSD_timeBound Ctm n := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  let s := Real.sqrt (Real.log 2)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hlog2_pos
  have hs_sq : s * s = Real.log 2 := Real.mul_self_sqrt (le_of_lt hlog2_pos)
  have hs3_pos : 0 < s ^ 3 := pow_pos hs_pos 3
  let M : ℝ := ((K + 1 + 2 * d : ℕ) : ℝ)
  let Ctm : ℝ := max 1 (M / s ^ 3)
  refine ⟨Ctm, le_max_left _ _, ?_⟩
  intro n hn2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn_gt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  let t := Real.sqrt (n : ℝ)
  have ht_pos : 0 < t := Real.sqrt_pos.mpr hn_pos
  have ht_sq : t * t = (n : ℝ) := Real.mul_self_sqrt (le_of_lt hn_pos)
  have ht_ge1 : 1 ≤ t := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt1
  have hlogn_le : Real.log (n : ℝ) ≤ (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos hn_pos
    linarith
  have hqlog_pos : 0 < QCSD_log2 (n : ℝ) := div_pos hlogn_pos hlog2_pos
  have hqlog_le : QCSD_log2 (n : ℝ) ≤ (n : ℝ) / Real.log 2 :=
    div_le_div_of_nonneg_right hlogn_le (le_of_lt hlog2_pos)
  have hsqrt_pos : 0 < Real.sqrt (QCSD_log2 (n : ℝ)) := Real.sqrt_pos.mpr hqlog_pos
  have hsqrt_le : Real.sqrt (QCSD_log2 (n : ℝ)) ≤ t / s := by
    calc Real.sqrt (QCSD_log2 (n : ℝ))
        ≤ Real.sqrt ((n : ℝ) / Real.log 2) := Real.sqrt_le_sqrt hqlog_le
      _ = t / s := Real.sqrt_div (le_of_lt hn_pos) (Real.log 2)
  have hdiv_ge : s * t ≤ (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ)) := by
    have h1 : (n : ℝ) / (t / s) ≤ (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ)) :=
      div_le_div_of_nonneg_left (le_of_lt hn_pos) hsqrt_pos hsqrt_le
    have h2 : (n : ℝ) / (t / s) = s * t := by
      have ht_ne : t ≠ 0 := ne_of_gt ht_pos
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      rw [← ht_sq]
      field_simp
    linarith
  have hCtm_pos : 0 ≤ Ctm := le_trans zero_le_one (le_max_left _ _)
  have hM_le : M ≤ Ctm * s ^ 3 := by
    have : M / s ^ 3 ≤ Ctm := le_max_right _ _
    exact (div_le_iff₀ hs3_pos).mp this
  let E := Ctm * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ))
  have hlog2_E : M * t ≤ Real.log 2 * E := by
    have hCE : Ctm * (s * t) ≤ E := by
      have : Ctm * (s * t) ≤ Ctm * ((n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hdiv_ge hCtm_pos
      simpa [E, mul_div_assoc] using this
    calc M * t ≤ (Ctm * s ^ 3) * t := mul_le_mul_of_nonneg_right hM_le (le_of_lt ht_pos)
      _ = (s * s) * (Ctm * (s * t)) := by ring
      _ = Real.log 2 * (Ctm * (s * t)) := by rw [hs_sq]
      _ ≤ Real.log 2 * E := mul_le_mul_of_nonneg_left hCE (le_of_lt hlog2_pos)
  have hn2_le_exp : ((n + 2 : ℕ) : ℝ) ^ d ≤ Real.exp (((2 * d : ℕ) : ℝ) * t) := by
    have hn2_sq : ((n + 2 : ℕ) : ℝ) ≤ (t + 1) ^ 2 := by
      push_cast
      have : (t + 1) ^ 2 = t * t + 2 * t + 1 := by ring
      rw [this, ht_sq]
      linarith
    have hpow1 : ((n + 2 : ℕ) : ℝ) ^ d ≤ ((t + 1) ^ 2) ^ d :=
      pow_le_pow_left₀ (by positivity) hn2_sq d
    have hpow2 : ((t + 1) ^ 2) ^ d = (t + 1) ^ (2 * d) := (pow_mul (t + 1) 2 d).symm
    have hpow3 : (t + 1) ^ (2 * d) ≤ (Real.exp t) ^ (2 * d) :=
      pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp t) (2 * d)
    have hpow4 : (Real.exp t) ^ (2 * d) = Real.exp (((2 * d : ℕ) : ℝ) * t) :=
      (Real.exp_nat_mul t (2 * d)).symm
    linarith
  have hK_le_exp : (K : ℝ) ≤ Real.exp (((K + 1 : ℕ) : ℝ) * t) := by
    have h1 : (K : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * t := by
      push_cast
      nlinarith
    have h2 := Real.add_one_le_exp (((K + 1 : ℕ) : ℝ) * t)
    linarith
  have hpoly_le : ((K * (n + 2) ^ d : ℕ) : ℝ) ≤ (2 : ℝ) ^ E := by
    push_cast
    calc (K : ℝ) * ((n : ℝ) + 2) ^ d
        = (K : ℝ) * (((n + 2 : ℕ) : ℝ) ^ d) := by push_cast; rfl
      _ ≤ Real.exp (((K + 1 : ℕ) : ℝ) * t) * Real.exp (((2 * d : ℕ) : ℝ) * t) :=
          mul_le_mul hK_le_exp hn2_le_exp (by positivity) (le_of_lt (Real.exp_pos _))
      _ = Real.exp ((((K + 1 : ℕ) : ℝ) * t) + (((2 * d : ℕ) : ℝ) * t)) := (Real.exp_add _ _).symm
      _ = Real.exp (M * t) := by congr 1; dsimp only [M]; push_cast; ring
      _ ≤ Real.exp (Real.log 2 * E) := Real.exp_le_exp.mpr hlog2_E
      _ = (2 : ℝ) ^ E := (Real.rpow_def_of_pos two_pos E).symm
  exact_mod_cast le_trans hpoly_le (Nat.le_ceil ((2 : ℝ) ^ E))

end Branch4



