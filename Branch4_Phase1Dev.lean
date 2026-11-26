import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Branch4_TMCompiler

namespace Branch4Phase1Dev

open QCSD.Defs
open Branch6Encoder
open Branch4

/-! ### Head-Preserving Combinators (`seqAt`, `loopAt`) and `StepExecB` Calculus -/

def seqAt {Q₁ Q₂ : Type} (s₁ : StepFn Q₁) (s₂ : StepFn Q₂) (f : Q₁ → Q₂) :
    StepFn (Q₁ ⊕ (Bool × Q₂))
  | Sum.inl q₁, b =>
      match s₁ q₁ b with
      | some (q₁', b', d) => some (Sum.inl q₁', b', d)
      | none => some (Sum.inr (false, f q₁), b, QCSD_HeadDir.right)
  | Sum.inr (false, q₂), b =>
      some (Sum.inr (true, q₂), b, QCSD_HeadDir.left)
  | Sum.inr (true, q₂), b =>
      match s₂ q₂ b with
      | some (q₂', b', d) => some (Sum.inr (true, q₂'), b', d)
      | none => none

theorem stepFnIter_seqAt_left {Q₁ Q₂ : Type} (s₁ : StepFn Q₁) (s₂ : StepFn Q₂) (f : Q₁ → Q₂) :
    ∀ k (q₁ : Q₁) len₁ τ₁ h₁ (q₂ : Q₁) len₂ τ₂ h₂,
      stepFnIter s₁ (q₁, len₁, τ₁, h₁) k = some (q₂, len₂, τ₂, h₂) →
      stepFnIter (seqAt s₁ s₂ f) (Sum.inl q₁, len₁, τ₁, h₁) k =
        some (Sum.inl q₂, len₂, τ₂, h₂) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ h; cases h; rfl
  | succ k ih =>
    intro q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ h
    simp only [stepFnIter, stepFnOnce] at h ⊢
    cases hs : s₁ q₁ (τ₁ h₁) with
    | none => rw [hs] at h; simp at h
    | some val =>
      rcases val with ⟨q₁', b', d⟩
      rw [hs] at h
      simp only [seqAt, hs]
      exact ih q₁' _ _ _ q₂ len₂ τ₂ h₂ h

theorem stepFnIter_seqAt_right {Q₁ Q₂ : Type} (s₁ : StepFn Q₁) (s₂ : StepFn Q₂) (f : Q₁ → Q₂) :
    ∀ k (q₂ : Q₂) len₁ τ₁ h₁,
      stepFnIter (seqAt s₁ s₂ f) (Sum.inr (true, q₂), len₁, τ₁, h₁) k =
        (stepFnIter s₂ (q₂, len₁, τ₁, h₁) k).map
          (fun (q', l', τ', h') => (Sum.inr (true, q'), l', τ', h')) := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro q₂ len₁ τ₁ h₁
    simp only [stepFnIter, stepFnOnce, seqAt]
    cases s₂ q₂ (τ₁ h₁) with
    | none => rfl
    | some val => rcases val with ⟨q', b', d⟩; exact ih q' _ _ _

theorem seqAt_spec {Q₁ Q₂ : Type} {s₁ : StepFn Q₁} {s₂ : StepFn Q₂} {f : Q₁ → Q₂} {B : ℕ}
    {q₁ : Q₁} {len₁ : ℕ} {τ₁ : ℕ → Bool} {h₁ : ℕ}
    {q_mid : Q₁} {len₂ : ℕ} {τ₂ : ℕ → Bool} {h₂ : ℕ}
    {q₃ : Q₂} {len₃ : ℕ} {τ₃ : ℕ → Bool} {h₃ : ℕ}
    {T₁ T₂ : ℕ}
    (hh₂_B : h₂ + 2 ≤ B)
    (he₁ : StepExec s₁ B q₁ len₁ τ₁ h₁ q_mid len₂ τ₂ h₂ T₁)
    (he₂ : StepExec s₂ B (f q_mid) (max len₂ (h₂ + 2)) τ₂ h₂ q₃ len₃ τ₃ h₃ T₂) :
    StepExec (seqAt s₁ s₂ f) B (Sum.inl q₁) len₁ τ₁ h₁ (Sum.inr (true, q₃)) len₃ τ₃ h₃
      (T₁ + 2 + T₂) := by
  rcases he₁ with ⟨k₁, hk₁, hiter₁, hexit₁, hbnd₁⟩
  rcases he₂ with ⟨k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
  have hleft := stepFnIter_seqAt_left s₁ s₂ f k₁ q₁ len₁ τ₁ h₁ q_mid len₂ τ₂ h₂ hiter₁
  have hlen₂_B : len₂ ≤ B := (hbnd₁ k₁ (Nat.le_refl _) _ _ _ _ hiter₁).1
  have hmid1 : stepFnOnce (seqAt s₁ s₂ f) (Sum.inl q_mid, len₂, τ₂, h₂) =
      some (Sum.inr (false, f q_mid), max len₂ (h₂ + 1), τ₂, h₂ + 1) := by
    simp [stepFnOnce, seqAt, hexit₁, moveHead]
  have hmid2 : stepFnOnce (seqAt s₁ s₂ f) (Sum.inr (false, f q_mid), max len₂ (h₂ + 1), τ₂, h₂ + 1) =
      some (Sum.inr (true, f q_mid), max len₂ (h₂ + 2), τ₂, h₂) := by
    have hm : max (max len₂ (h₂ + 1)) (h₂ + 1 + 1) = max len₂ (h₂ + 2) := by omega
    simp [stepFnOnce, seqAt, moveHead, hm]
  have hmid12 : stepFnIter (seqAt s₁ s₂ f) (Sum.inl q_mid, len₂, τ₂, h₂) 2 =
      some (Sum.inr (true, f q_mid), max len₂ (h₂ + 2), τ₂, h₂) := by
    simp [stepFnIter, hmid1, hmid2]
  have hright : stepFnIter (seqAt s₁ s₂ f) (Sum.inr (true, f q_mid), max len₂ (h₂ + 2), τ₂, h₂) k₂ =
      some (Sum.inr (true, q₃), len₃, τ₃, h₃) := by
    rw [stepFnIter_seqAt_right, hiter₂]; rfl
  refine ⟨k₁ + 2 + k₂, by omega, ?_, fun b => by simp [seqAt, hexit₂ b], ?_⟩
  · rw [stepFnIter_add, stepFnIter_add, hleft, Option.bind_some, hmid12, Option.bind_some, hright]
  · intro j hj q' l' τ' h' hj_eq
    by_cases hj1 : j ≤ k₁
    · rcases stepFnIter_le_some hj1 hiter₁ with ⟨⟨qj, lj, τj, hj_p⟩, hsub⟩
      rw [stepFnIter_seqAt_left s₁ s₂ f j _ _ _ _ _ _ _ _ hsub] at hj_eq
      cases hj_eq
      exact hbnd₁ j hj1 qj l' τ' h' hsub
    · by_cases hj2 : j = k₁ + 1
      · subst hj2
        rw [stepFnIter_add, hleft, Option.bind_some] at hj_eq
        simp only [stepFnIter, hmid1, Option.some.injEq, Prod.mk.injEq] at hj_eq
        rcases hj_eq with ⟨_, rfl, _, rfl⟩
        omega
      · have heq : j = k₁ + 2 + (j - (k₁ + 2)) := by omega
        rw [heq, stepFnIter_add, stepFnIter_add, hleft, Option.bind_some, hmid12,
          Option.bind_some, stepFnIter_seqAt_right] at hj_eq
        cases hsub : stepFnIter s₂ (f q_mid, max len₂ (h₂ + 2), τ₂, h₂) (j - (k₁ + 2)) with
        | none => rw [hsub] at hj_eq; simp at hj_eq
        | some cfg =>
          rcases cfg with ⟨qj, lj, τj, hj_p⟩
          rw [hsub] at hj_eq; cases hj_eq
          exact hbnd₂ (j - (k₁ + 2)) (by omega) qj l' τ' h' hsub

def loopAt {Q : Type} (body : StepFn Q) (next : Q → Option Q) : StepFn (Bool × Q)
  | (true, q), b =>
      match body q b with
      | some (q', b', d) => some ((true, q'), b', d)
      | none =>
          match next q with
          | none => none
          | some q_next => some ((false, q_next), b, QCSD_HeadDir.right)
  | (false, q_next), b =>
      some ((true, q_next), b, QCSD_HeadDir.left)

theorem stepFnIter_loopAt_body {Q : Type} (body : StepFn Q) (next : Q → Option Q) :
    ∀ k (q₁ : Q) len₁ τ₁ h₁ (q₂ : Q) len₂ τ₂ h₂,
      stepFnIter body (q₁, len₁, τ₁, h₁) k = some (q₂, len₂, τ₂, h₂) →
      stepFnIter (loopAt body next) ((true, q₁), len₁, τ₁, h₁) k =
        some ((true, q₂), len₂, τ₂, h₂) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ h; cases h; rfl
  | succ k ih =>
    intro q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ h
    simp only [stepFnIter, stepFnOnce] at h ⊢
    cases hs : body q₁ (τ₁ h₁) with
    | none => rw [hs] at h; simp at h
    | some val =>
      rcases val with ⟨q₁', b', d⟩
      rw [hs] at h
      simp only [loopAt, hs]
      exact ih q₁' _ _ _ q₂ len₂ τ₂ h₂ h

theorem loopAt_done_raw {Q : Type} {body : StepFn Q} (next : Q → Option Q) {B : ℕ}
    {q₁ q₂ : Q} {len₁ len₂ h₁ h₂ T : ℕ} {τ₁ τ₂ : ℕ → Bool}
    (he : StepExec body B q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ T)
    (hnext : next q₂ = none) :
    StepExec (loopAt body next) B (true, q₁) len₁ τ₁ h₁ (true, q₂) len₂ τ₂ h₂ T := by
  rcases he with ⟨k, hk, hiter, hexit, hbnd⟩
  have hbody := stepFnIter_loopAt_body body next k q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ hiter
  refine ⟨k, hk, hbody, fun b => by simp [loopAt, hexit b, hnext], ?_⟩
  intro j hj q' l' τ' h' hj_eq
  rcases stepFnIter_le_some hj hiter with ⟨⟨qj, lj, τj, hj_p⟩, hsub⟩
  rw [stepFnIter_loopAt_body body next j _ _ _ _ _ _ _ _ hsub] at hj_eq
  cases hj_eq
  exact hbnd j hj qj l' τ' h' hsub

theorem loopAt_step_raw {Q : Type} {body : StepFn Q} (next : Q → Option Q) {B : ℕ}
    {q₁ q_mid q_next q₃ : Q} {len₁ len₂ len₃ h₁ h₂ h₃ T₁ T₂ : ℕ} {τ₁ τ₂ τ₃ : ℕ → Bool}
    (hh₂_B : h₂ + 2 ≤ B)
    (he₁ : StepExec body B q₁ len₁ τ₁ h₁ q_mid len₂ τ₂ h₂ T₁)
    (hnext : next q_mid = some q_next)
    (he₂ : StepExec (loopAt body next) B (true, q_next) (max len₂ (h₂ + 2)) τ₂ h₂
      (true, q₃) len₃ τ₃ h₃ T₂) :
    StepExec (loopAt body next) B (true, q₁) len₁ τ₁ h₁ (true, q₃) len₃ τ₃ h₃
      (T₁ + 2 + T₂) := by
  rcases he₁ with ⟨k₁, hk₁, hiter₁, hexit₁, hbnd₁⟩
  rcases he₂ with ⟨k₂, hk₂, hiter₂, hexit₂, hbnd₂⟩
  have hbody := stepFnIter_loopAt_body body next k₁ q₁ len₁ τ₁ h₁ q_mid len₂ τ₂ h₂ hiter₁
  have hlen₂_B : len₂ ≤ B := (hbnd₁ k₁ (Nat.le_refl _) _ _ _ _ hiter₁).1
  have hm1 : stepFnOnce (loopAt body next) ((true, q_mid), len₂, τ₂, h₂) =
      some ((false, q_next), max len₂ (h₂ + 1), τ₂, h₂ + 1) := by
    simp [stepFnOnce, loopAt, hexit₁, hnext, moveHead]
  have hm2 : stepFnOnce (loopAt body next) ((false, q_next), max len₂ (h₂ + 1), τ₂, h₂ + 1) =
      some ((true, q_next), max len₂ (h₂ + 2), τ₂, h₂) := by
    have hm : max (max len₂ (h₂ + 1)) (h₂ + 1 + 1) = max len₂ (h₂ + 2) := by omega
    simp [stepFnOnce, loopAt, moveHead, hm]
  have hm12 : stepFnIter (loopAt body next) ((true, q_mid), len₂, τ₂, h₂) 2 =
      some ((true, q_next), max len₂ (h₂ + 2), τ₂, h₂) := by
    simp [stepFnIter, hm1, hm2]
  refine ⟨k₁ + 2 + k₂, by omega, ?_, hexit₂, ?_⟩
  · rw [stepFnIter_add, stepFnIter_add, hbody, Option.bind_some, hm12, Option.bind_some, hiter₂]
  · intro j hj q' l' τ' h' hj_eq
    by_cases hj1 : j ≤ k₁
    · rcases stepFnIter_le_some hj1 hiter₁ with ⟨⟨qj, lj, τj, hj_p⟩, hsub⟩
      rw [stepFnIter_loopAt_body body next j _ _ _ _ _ _ _ _ hsub] at hj_eq
      cases hj_eq
      exact hbnd₁ j hj1 qj l' τ' h' hsub
    · by_cases hj2 : j = k₁ + 1
      · subst hj2
        rw [stepFnIter_add, hbody, Option.bind_some] at hj_eq
        simp only [stepFnIter, hm1, Option.some.injEq, Prod.mk.injEq] at hj_eq
        rcases hj_eq with ⟨_, rfl, _, rfl⟩
        omega
      · have heq : j = k₁ + 2 + (j - (k₁ + 2)) := by omega
        rw [heq, stepFnIter_add, stepFnIter_add, hbody, Option.bind_some, hm12, Option.bind_some] at hj_eq
        exact hbnd₂ (j - (k₁ + 2)) (by omega) q' l' τ' h' hj_eq

def StepExecB {Q : Type} (s : StepFn Q) (B L_bnd : ℕ)
    (q₁ : Q) (τ₁ : ℕ → Bool) (h₁ : ℕ)
    (q₂ : Q) (τ₂ : ℕ → Bool) (h₂ : ℕ) (T : ℕ) : Prop :=
  L_bnd ≤ B ∧ ∀ len₁ ≤ L_bnd, ∃ len₂ ≤ L_bnd, StepExec s B q₁ len₁ τ₁ h₁ q₂ len₂ τ₂ h₂ T

theorem StepExecB.done {Q : Type} {s : StepFn Q} {B L_bnd : ℕ}
    {q : Q} {τ : ℕ → Bool} {h : ℕ}
    (hLB : L_bnd ≤ B) (hh : h + 1 ≤ L_bnd) (hexit : ∀ b, s q b = none) :
    StepExecB s B L_bnd q τ h q τ h 0 := by
  refine ⟨hLB, fun len₁ hlen₁ => ⟨len₁, hlen₁, ⟨0, Nat.le_refl 0, rfl, hexit, ?_⟩⟩⟩
  intro j hj _ l' _ h' hj_eq
  obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
  cases hj_eq
  exact ⟨by omega, by omega⟩

theorem StepExecB.step {Q : Type} {s : StepFn Q} {B L_bnd : ℕ}
    {q₁ : Q} {τ₁ : ℕ → Bool} {h₁ : ℕ}
    (q' : Q) (b' : Bool) (d : QCSD_HeadDir) (τ' : ℕ → Bool) (h' : ℕ)
    {q₂ : Q} {τ₂ : ℕ → Bool} {h₂ T' : ℕ}
    (hs : s q₁ (τ₁ h₁) = some (q', b', d))
    (hh₁ : h₁ + 1 ≤ L_bnd)
    (hτ' : Function.update τ₁ h₁ b' = τ')
    (hh' : moveHead h₁ d = h')
    (hrest : StepExecB s B L_bnd q' τ' h' q₂ τ₂ h₂ T') :
    StepExecB s B L_bnd q₁ τ₁ h₁ q₂ τ₂ h₂ (T' + 1) := by
  rcases hrest with ⟨hLB, hfn⟩
  refine ⟨hLB, fun len₁ hlen₁ => ?_⟩
  rcases hfn (max len₁ (h₁ + 1)) (by omega) with ⟨len₂, hlen₂, k, hk, hiter, hexit, hbnd⟩
  subst hτ'; subst hh'
  refine ⟨len₂, hlen₂, k + 1, by omega, by simp [stepFnIter, stepFnOnce, hs, hiter], hexit, ?_⟩
  intro j hj qm lm τm hm hj_eq
  cases j with
  | zero => cases hj_eq; exact ⟨by omega, by omega⟩
  | succ j' =>
    simp only [stepFnIter, stepFnOnce, hs] at hj_eq
    exact hbnd j' (Nat.le_of_succ_le_succ hj) qm lm τm hm hj_eq

theorem StepExecB.weaken {Q : Type} {s : StepFn Q} {B L_bnd : ℕ}
    {q₁ q₂ : Q} {τ₁ τ₂ : ℕ → Bool} {h₁ h₂ T₁ : ℕ}
    (T₂ : ℕ) (he : StepExecB s B L_bnd q₁ τ₁ h₁ q₂ τ₂ h₂ T₁) (hT : T₁ ≤ T₂) :
    StepExecB s B L_bnd q₁ τ₁ h₁ q₂ τ₂ h₂ T₂ :=
  ⟨he.1, fun len₁ hlen₁ =>
    let ⟨len₂, hlen₂, hex⟩ := he.2 len₁ hlen₁
    ⟨len₂, hlen₂, hex.weaken T₂ hT⟩⟩

theorem StepExecB.seqAt {Q₁ Q₂ : Type} {s₁ : StepFn Q₁} {s₂ : StepFn Q₂} {f : Q₁ → Q₂}
    {B L_bnd : ℕ} {q₁ q_mid : Q₁} {q₃ : Q₂} {τ₁ τ₂ τ₃ : ℕ → Bool} {h₁ h₂ h₃ T₁ T₂ : ℕ}
    (hh₂ : h₂ + 2 ≤ L_bnd)
    (he₁ : StepExecB s₁ B L_bnd q₁ τ₁ h₁ q_mid τ₂ h₂ T₁)
    (he₂ : StepExecB s₂ B L_bnd (f q_mid) τ₂ h₂ q₃ τ₃ h₃ T₂) :
    StepExecB (seqAt s₁ s₂ f) B L_bnd (Sum.inl q₁) τ₁ h₁ (Sum.inr (true, q₃)) τ₃ h₃ (T₁ + 2 + T₂) := by
  refine ⟨he₁.1, fun len₁ hlen₁ => ?_⟩
  rcases he₁.2 len₁ hlen₁ with ⟨len₃_m, hlen₂, hex₁⟩
  rcases he₂.2 (max len₃_m (h₂ + 2)) (by omega) with ⟨len₃, hlen₃, hex₂⟩
  have hLB := he₁.1
  exact ⟨len₃, hlen₃, seqAt_spec (by omega) hex₁ hex₂⟩

theorem StepExecB.loopAt_done {Q : Type} {body : StepFn Q} (next : Q → Option Q)
    {B L_bnd : ℕ} {q₁ q₂ : Q} {τ₁ τ₂ : ℕ → Bool} {h₁ h₂ T : ℕ}
    (he : StepExecB body B L_bnd q₁ τ₁ h₁ q₂ τ₂ h₂ T)
    (hnext : next q₂ = none) :
    StepExecB (loopAt body next) B L_bnd (true, q₁) τ₁ h₁ (true, q₂) τ₂ h₂ T :=
  ⟨he.1, fun len₁ hlen₁ =>
    let ⟨len₂, hlen₂, hex⟩ := he.2 len₁ hlen₁
    ⟨len₂, hlen₂, loopAt_done_raw next hex hnext⟩⟩

theorem StepExecB.loopAt_step {Q : Type} {body : StepFn Q} (next : Q → Option Q)
    {B L_bnd : ℕ} {q₁ q_mid q_next q₃ : Q} {τ₁ τ₂ τ₃ : ℕ → Bool} {h₁ h₂ h₃ T₁ T₂ : ℕ}
    (hh₂ : h₂ + 2 ≤ L_bnd)
    (he₁ : StepExecB body B L_bnd q₁ τ₁ h₁ q_mid τ₂ h₂ T₁)
    (hnext : next q_mid = some q_next)
    (he₂ : StepExecB (loopAt body next) B L_bnd (true, q_next) τ₂ h₂ (true, q₃) τ₃ h₃ T₂) :
    StepExecB (loopAt body next) B L_bnd (true, q₁) τ₁ h₁ (true, q₃) τ₃ h₃ (T₁ + 2 + T₂) := by
  refine ⟨he₁.1, fun len₁ hlen₁ => ?_⟩
  rcases he₁.2 len₁ hlen₁ with ⟨len₂, hlen₂, hex₁⟩
  rcases he₂.2 (max len₂ (h₂ + 2)) (by omega) with ⟨len₃, hlen₃, hex₂⟩
  have hLB := he₁.1
  exact ⟨len₃, hlen₃, loopAt_step_raw next (by omega) hex₁ hnext hex₂⟩

theorem StepExecB.family {P Q : Type} (s : P → StepFn Q) (p : P) {B L_bnd : ℕ}
    {q₁ q₂ : Q} {τ₁ τ₂ : ℕ → Bool} {h₁ h₂ T : ℕ}
    (he : StepExecB (s p) B L_bnd q₁ τ₁ h₁ q₂ τ₂ h₂ T) :
    StepExecB (familyStep s) B L_bnd (p, q₁) τ₁ h₁ (p, q₂) τ₂ h₂ T :=
  ⟨he.1, fun len₁ hlen₁ =>
    let ⟨len₂, hlen₂, hex⟩ := he.2 len₁ hlen₁
    ⟨len₂, hlen₂, familyStep_spec s p hex⟩⟩

theorem StepExecB.inl {Q₁ Q₂ : Type} (s₁ : StepFn Q₁) (s₂ : StepFn Q₂) {B L_bnd : ℕ}
    {q₁ q₂ : Q₁} {τ₁ τ₂ : ℕ → Bool} {h₁ h₂ T : ℕ}
    (he : StepExecB s₁ B L_bnd q₁ τ₁ h₁ q₂ τ₂ h₂ T) :
    StepExecB (sumStep s₁ s₂) B L_bnd (Sum.inl q₁) τ₁ h₁ (Sum.inl q₂) τ₂ h₂ T :=
  ⟨he.1, fun len₁ hlen₁ =>
    let ⟨len₂, hlen₂, hex⟩ := he.2 len₁ hlen₁
    ⟨len₂, hlen₂, sumStep_inl_spec s₁ s₂ hex⟩⟩

theorem StepExecB.inr {Q₁ Q₂ : Type} (s₁ : StepFn Q₁) (s₂ : StepFn Q₂) {B L_bnd : ℕ}
    {q₁ q₂ : Q₂} {τ₁ τ₂ : ℕ → Bool} {h₁ h₂ T : ℕ}
    (he : StepExecB s₂ B L_bnd q₁ τ₁ h₁ q₂ τ₂ h₂ T) :
    StepExecB (sumStep s₁ s₂) B L_bnd (Sum.inr q₁) τ₁ h₁ (Sum.inr q₂) τ₂ h₂ T :=
  ⟨he.1, fun len₁ hlen₁ =>
    let ⟨len₂, hlen₂, hex⟩ := he.2 len₁ hlen₁
    ⟨len₂, hlen₂, sumStep_inr_spec s₁ s₂ hex⟩⟩

/-! ### Piece 1B: `rawExpandToWS` using `StepExecB` -/

def seedExpand : StepFn (Fin 11) :=
  fun st b =>
    if st = 0 then some (1, true, QCSD_HeadDir.right)
    else if st = 1 then some (2, true, QCSD_HeadDir.right)
    else if st = 2 then some (3, true, QCSD_HeadDir.right)
    else if st = 3 then some (4, true, QCSD_HeadDir.right)
    else if st = 4 then some (5, false, QCSD_HeadDir.right)
    else if st = 5 then some (6, true, QCSD_HeadDir.left)
    else if st = 6 then some (7, b, QCSD_HeadDir.left)
    else if st = 7 then some (8, b, QCSD_HeadDir.left)
    else if st = 8 then some (9, b, QCSD_HeadDir.left)
    else if st = 9 then some (10, b, QCSD_HeadDir.left)
    else none

def expandTapeVal (S : List Bool) (k p : ℕ) : Bool :=
  if p < k then S.getD p false
  else if p < k + 3 then true
  else if p < k + 3 + 3 * (S.length - k) then
    if (p - (k + 3)) % 3 = 2 then S.getD (k + (p - (k + 3)) / 3) false else false
  else if p < k + 6 + 3 * (S.length - k) then
    decide (p - (k + 3 + 3 * (S.length - k)) = 0 ∨ p - (k + 3 + 3 * (S.length - k)) = 2)
  else false

theorem expandTapeVal_lt (S : List Bool) {k p : ℕ} (hp : p < k) :
    expandTapeVal S k p = S.getD p false := by
  unfold expandTapeVal; simp [hp]

theorem expandTapeVal_home (S : List Bool) {k p : ℕ} (hp1 : k ≤ p) (hp2 : p < k + 3) :
    expandTapeVal S k p = true := by
  unfold expandTapeVal
  have h1 : ¬ (p < k) := by omega
  simp [h1, hp2]

theorem expandTapeVal_mid (S : List Bool) {k p : ℕ}
    (hp1 : k + 3 ≤ p) (hp2 : p < k + 3 + 3 * (S.length - k)) :
    expandTapeVal S k p =
      (if (p - (k + 3)) % 3 = 2 then S.getD (k + (p - (k + 3)) / 3) false else false) := by
  unfold expandTapeVal
  have h1 : ¬ (p < k) := by omega
  have h2 : ¬ (p < k + 3) := by omega
  simp only [h1, h2, hp2, ↓reduceIte]

theorem expandTapeVal_wall (S : List Bool) {k p : ℕ}
    (hp1 : k + 3 + 3 * (S.length - k) ≤ p) (hp2 : p < k + 6 + 3 * (S.length - k)) :
    expandTapeVal S k p =
      decide (p - (k + 3 + 3 * (S.length - k)) = 0 ∨ p - (k + 3 + 3 * (S.length - k)) = 2) := by
  unfold expandTapeVal
  have h1 : ¬ (p < k) := by omega
  have h2 : ¬ (p < k + 3) := by omega
  have h3 : ¬ (p < k + 3 + 3 * (S.length - k)) := by omega
  simp only [h1, h2, h3, hp2, ↓reduceIte]

theorem expandTapeVal_out (S : List Bool) {k p : ℕ}
    (hp : k + 6 + 3 * (S.length - k) ≤ p) :
    expandTapeVal S k p = false := by
  unfold expandTapeVal
  have h1 : ¬ (p < k) := by omega
  have h2 : ¬ (p < k + 3) := by omega
  have h3 : ¬ (p < k + 3 + 3 * (S.length - k)) := by omega
  have h4 : ¬ (p < k + 6 + 3 * (S.length - k)) := by omega
  simp only [h1, h2, h3, h4, ↓reduceIte]

theorem seedExpand_spec (B L_bnd : ℕ) (S : List Bool) {τ₁ : ℕ → Bool}
    (hLB : L_bnd ≤ B) (hL_bnd : S.length + 6 ≤ L_bnd)
    (hS : ∀ p, τ₁ p = if p < S.length then S.getD p false else false) :
    ∃ τ₂ : ℕ → Bool,
      (∀ p, τ₂ p = expandTapeVal S S.length p) ∧
      StepExecB seedExpand B L_bnd 0 τ₁ S.length 10 τ₂ S.length 10 := by
  let L := S.length
  let u0 := Function.update τ₁ L true
  let u1 := Function.update u0 (L + 1) true
  let u2 := Function.update u1 (L + 2) true
  let u3 := Function.update u2 (L + 3) true
  let u4 := Function.update u3 (L + 4) false
  let u5 := Function.update u4 (L + 5) true
  have he : StepExecB seedExpand B L_bnd 0 τ₁ L 10 u5 L 10 := by
    refine StepExecB.step 1 true .right u0 (L + 1) rfl (by omega) rfl rfl ?_
    refine StepExecB.step 2 true .right u1 (L + 2) rfl (by omega) rfl rfl ?_
    refine StepExecB.step 3 true .right u2 (L + 3) rfl (by omega) rfl rfl ?_
    refine StepExecB.step 4 true .right u3 (L + 4) rfl (by omega) rfl rfl ?_
    refine StepExecB.step 5 false .right u4 (L + 5) rfl (by omega) rfl rfl ?_
    refine StepExecB.step 6 true .left u5 (L + 4) rfl (by omega) rfl (by simp [moveHead]) ?_
    refine StepExecB.step 7 (u5 (L + 4)) .left u5 (L + 3) rfl (by omega) (by simp) (by simp [moveHead]) ?_
    refine StepExecB.step 8 (u5 (L + 3)) .left u5 (L + 2) rfl (by omega) (by simp) (by simp [moveHead]) ?_
    refine StepExecB.step 9 (u5 (L + 2)) .left u5 (L + 1) rfl (by omega) (by simp) (by simp [moveHead]) ?_
    refine StepExecB.step 10 (u5 (L + 1)) .left u5 L rfl (by omega) (by simp) (by simp [moveHead]) ?_
    exact StepExecB.done hLB (by omega) (fun _ => rfl)
  refine ⟨u5, ?_, he⟩
  intro p
  dsimp only [u5, u4, u3, u2, u1, u0, L]
  by_cases hp5 : p = S.length + 5
  · subst hp5
    rw [Function.update_self, expandTapeVal_wall S (by omega) (by omega)]
    have hsub : S.length + 5 - (S.length + 3 + 3 * (S.length - S.length)) = 2 := by omega
    rw [hsub]; rfl
  · rw [Function.update_of_ne hp5]
    by_cases hp4 : p = S.length + 4
    · subst hp4
      rw [Function.update_self, expandTapeVal_wall S (by omega) (by omega)]
      have hsub : S.length + 4 - (S.length + 3 + 3 * (S.length - S.length)) = 1 := by omega
      rw [hsub]; rfl
    · rw [Function.update_of_ne hp4]
      by_cases hp3 : p = S.length + 3
      · subst hp3
        rw [Function.update_self, expandTapeVal_wall S (by omega) (by omega)]
        have hsub : S.length + 3 - (S.length + 3 + 3 * (S.length - S.length)) = 0 := by omega
        rw [hsub]; rfl
      · rw [Function.update_of_ne hp3]
        by_cases hp2 : p = S.length + 2
        · subst hp2; rw [Function.update_self, expandTapeVal_home S (by omega) (by omega)]
        · rw [Function.update_of_ne hp2]
          by_cases hp1 : p = S.length + 1
          · subst hp1; rw [Function.update_self, expandTapeVal_home S (by omega) (by omega)]
          · rw [Function.update_of_ne hp1]
            by_cases hp0 : p = S.length
            · subst hp0; rw [Function.update_self, expandTapeVal_home S (by omega) (by omega)]
            · rw [Function.update_of_ne hp0, hS p]
              by_cases hpL : p < S.length
              · simp only [hpL, ↓reduceIte]; rw [expandTapeVal_lt S hpL]
              · simp only [hpL, ↓reduceIte]; rw [expandTapeVal_out S (by omega)]

def expandTestZero : StepFn (Fin 6 × Bool × Bool) :=
  fun (ph, done, bp) b =>
    if ph = 0 then some ((1, false, false), false, QCSD_HeadDir.left)
    else if ph = 1 then some ((2, false, b), b, QCSD_HeadDir.right)
    else if ph = 2 then
      if b then some ((3, true, false), true, QCSD_HeadDir.left)
      else some ((4, false, bp), false, QCSD_HeadDir.right)
    else if ph = 3 then some ((4, true, false), true, QCSD_HeadDir.right)
    else if ph = 4 then some ((5, done, bp), b, QCSD_HeadDir.left)
    else none

theorem expandTestZero_zero (B L_bnd : ℕ) {τ : ℕ → Bool}
    (hLB : L_bnd ≤ B) (h2 : 2 ≤ L_bnd)
    (h0 : τ 0 = true) (h1 : τ 1 = true) :
    StepExecB expandTestZero B L_bnd (0, false, false) τ 0 (5, true, false) τ 0 5 := by
  let τa := Function.update τ 0 false
  have ha0 : τa 0 = false := by simp [τa]
  have ha1 : τa 1 = true := by dsimp [τa]; rw [Function.update_of_ne (by omega)]; exact h1
  have hτ_back : Function.update τa 0 true = τ := by
    funext x; dsimp [τa]; by_cases hx : x = 0
    · subst hx; simp [h0]
    · simp [hx]
  refine StepExecB.step (1, false, false) false .left τa 0 rfl (by omega) rfl rfl ?_
  refine StepExecB.step (2, false, false) false .right τa 1 (by simp [expandTestZero, ha0]) (by omega) (update_eq_self_of_eq ha0) rfl ?_
  refine StepExecB.step (3, true, false) true .left τa 0 (by simp [expandTestZero, ha1]) (by omega) (update_eq_self_of_eq ha1) rfl ?_
  refine StepExecB.step (4, true, false) true .right τ 1 rfl (by omega) hτ_back rfl ?_
  refine StepExecB.step (5, true, false) (τ 1) .left τ 0 rfl (by omega) (by simp) rfl ?_
  exact StepExecB.done hLB (by omega) (fun _ => rfl)

theorem expandTestZero_succ (B L_bnd i : ℕ) {τ : ℕ → Bool}
    (hLB : L_bnd ≤ B) (hi : i + 3 ≤ L_bnd) :
    StepExecB expandTestZero B L_bnd (0, false, false) τ (i + 1)
      (5, false, τ i) (Function.update τ (i + 1) false) (i + 1) 5 := by
  let τa := Function.update τ (i + 1) false
  have hai : τa i = τ i := by dsimp [τa]; rw [Function.update_of_ne (by omega)]
  have hak : τa (i + 1) = false := by simp [τa]
  have he4 : StepExecB expandTestZero B L_bnd (0, false, false) τ (i + 1)
      (5, false, τ i) τa (i + 1) 4 := by
    refine StepExecB.step (1, false, false) false .left τa i rfl (by omega) rfl (by simp [moveHead]) ?_
    refine StepExecB.step (2, false, τ i) (τ i) .right τa (i + 1) (by simp [expandTestZero, hai]) (by omega) (update_eq_self_of_eq hai) rfl ?_
    refine StepExecB.step (4, false, τ i) false .right τa (i + 2) (by simp [expandTestZero, hak]) (by omega) (update_eq_self_of_eq hak) rfl ?_
    refine StepExecB.step (5, false, τ i) (τa (i + 2)) .left τa (i + 1) rfl (by omega) (by simp) (by simp [moveHead]) ?_
    exact StepExecB.done hLB (by omega) (fun _ => rfl)
  exact he4.weaken 5 (by omega)

def walkWallBlk : StepFn (Fin 5 × Bool × Bool) :=
  fun (ph, c0, c1) b =>
    if ph = 0 then some ((1, b, false), b, QCSD_HeadDir.right)
    else if ph = 1 then some ((2, c0, b), b, QCSD_HeadDir.right)
    else if ph = 2 then
      if c0 && (!c1) && b then some ((3, true, false), b, QCSD_HeadDir.left)
      else some ((4, false, false), b, QCSD_HeadDir.right)
    else if ph = 3 then some ((4, true, false), b, QCSD_HeadDir.left)
    else none

def walkWallNext : Fin 5 × Bool × Bool → Option (Fin 5 × Bool × Bool)
  | (_, false, _) => some (0, false, false)
  | _ => none

def walkToWall3 : StepFn (Bool × (Fin 5 × Bool × Bool)) :=
  loopAt walkWallBlk walkWallNext

theorem walkToWall3_spec (B L_bnd : ℕ) (hLB : L_bnd ≤ B) :
    ∀ m p {τ : ℕ → Bool},
      p + 3 * m + 5 ≤ L_bnd →
      (∀ t < m, (τ (p + 3 * t), τ (p + 3 * t + 1), τ (p + 3 * t + 2)) ≠ blkWall) →
      (τ (p + 3 * m), τ (p + 3 * m + 1), τ (p + 3 * m + 2)) = blkWall →
      StepExecB walkToWall3 B L_bnd (true, (0, false, false)) τ p
        (true, (4, true, false)) τ (p + 3 * m) (6 * m + 5) := by
  intro m
  induction m with
  | zero =>
    intro p τ hB _ hwall
    simp only [Nat.mul_zero, Nat.add_zero] at hwall hB ⊢
    have h0 : τ p = true := (Prod.mk.inj hwall).1
    have h1 : τ (p + 1) = false := (Prod.mk.inj (Prod.mk.inj hwall).2).1
    have h2 : τ (p + 2) = true := (Prod.mk.inj (Prod.mk.inj hwall).2).2
    have he4 : StepExecB walkWallBlk B L_bnd (0, false, false) τ p (4, true, false) τ p 4 := by
      refine StepExecB.step (1, true, false) true .right τ (p + 1) (by simp [walkWallBlk, h0]) (by omega) (update_eq_self_of_eq h0) rfl ?_
      refine StepExecB.step (2, true, false) false .right τ (p + 2) (by simp [walkWallBlk, h1]) (by omega) (update_eq_self_of_eq h1) rfl ?_
      refine StepExecB.step (3, true, false) true .left τ (p + 1) (by simp [walkWallBlk, h2]) (by omega) (update_eq_self_of_eq h2) (by simp [moveHead]) ?_
      refine StepExecB.step (4, true, false) (τ (p + 1)) .left τ p rfl (by omega) (by simp) (by simp [moveHead]) ?_
      exact StepExecB.done hLB (by omega) (fun _ => rfl)
    exact (StepExecB.loopAt_done walkWallNext he4 rfl).weaken 5 (by omega)
  | succ m ih =>
    intro p τ hB hnot hwall
    have hne0 := hnot 0 (Nat.zero_lt_succ m)
    simp only [Nat.mul_zero, Nat.add_zero] at hne0
    have hcond : (τ p && !(τ (p + 1)) && τ (p + 2)) = false := by
      cases hc0 : τ p <;> cases hc1 : τ (p + 1) <;> cases hc2 : τ (p + 2) <;> simp_all [blkWall]
    have he1 : StepExecB walkWallBlk B L_bnd (0, false, false) τ p (4, false, false) τ (p + 3) 3 := by
      refine StepExecB.step (1, τ p, false) (τ p) .right τ (p + 1) rfl (by omega) (by simp) rfl ?_
      refine StepExecB.step (2, τ p, τ (p + 1)) (τ (p + 1)) .right τ (p + 2) rfl (by omega) (by simp) rfl ?_
      refine StepExecB.step (4, false, false) (τ (p + 2)) .right τ (p + 3) (by simp [walkWallBlk, hcond]) (by omega) (by simp) rfl ?_
      exact StepExecB.done hLB (by omega) (fun _ => rfl)
    have he_rest := ih (p + 3) (by omega)
      (fun t ht => by simpa [show p + 3 + 3 * t = p + 3 * (t + 1) by ring] using hnot (t + 1) (by omega))
      (by simpa [show p + 3 + 3 * m = p + 3 * (m + 1) by ring] using hwall)
    have hpos : p + 3 + 3 * m = p + 3 * (m + 1) := by ring
    rw [hpos] at he_rest
    exact (StepExecB.loopAt_step walkWallNext (by omega) he1 rfl he_rest).weaken (6 * (m + 1) + 5) (by omega)

def shiftOneBlk (bp : Bool) : StepFn (Fin 20 × Bool × Bool) :=
  fun (ph, a1, a2) b =>
    if ph = 0 then some ((1, b, false), b, QCSD_HeadDir.right)
    else if ph = 1 then some ((2, a1, b), b, QCSD_HeadDir.right)
    else if ph = 2 then
      if (!a1) && a2 && b then
        some ((3, false, false), false, QCSD_HeadDir.right)
      else
        some ((11, a2, b), a1, QCSD_HeadDir.right)
    else if ph = 3 then some ((4, false, false), false, QCSD_HeadDir.right)
    else if ph = 4 then some ((5, false, false), bp, QCSD_HeadDir.left)
    else if ph = 5 then some ((6, false, false), b, QCSD_HeadDir.left)
    else if ph = 6 then some ((7, false, false), b, QCSD_HeadDir.left)
    else if ph = 7 then some ((8, false, false), true, QCSD_HeadDir.left)
    else if ph = 8 then some ((9, false, false), true, QCSD_HeadDir.left)
    else if ph = 9 then some ((10, false, false), true, QCSD_HeadDir.right)
    else if ph = 10 then some ((19, true, false), b, QCSD_HeadDir.left)
    else if ph = 11 then some ((12, false, a2), a1, QCSD_HeadDir.right)
    else if ph = 12 then some ((13, false, false), a2, QCSD_HeadDir.left)
    else if ph = 13 then some ((14, false, false), b, QCSD_HeadDir.left)
    else if ph = 14 then some ((15, false, false), b, QCSD_HeadDir.left)
    else if ph = 15 then some ((16, false, false), b, QCSD_HeadDir.left)
    else if ph = 16 then some ((17, false, false), b, QCSD_HeadDir.left)
    else if ph = 17 then some ((18, false, false), b, QCSD_HeadDir.left)
    else if ph = 18 then some ((19, false, false), b, QCSD_HeadDir.left)
    else none

def shiftBlkNext : Fin 20 × Bool × Bool → Option (Fin 20 × Bool × Bool)
  | (_, false, _) => some (0, false, false)
  | _ => none

def shiftSuffixFor (bp : Bool) : StepFn (Bool × (Fin 20 × Bool × Bool)) :=
  loopAt (shiftOneBlk bp) shiftBlkNext

theorem expandTapeVal_shift_eq (S : List Bool) (i p : ℕ) (hiL : i < S.length) (hp : i + 6 ≤ p) :
    expandTapeVal S (i + 1) (p - 2) = expandTapeVal S i p := by
  by_cases h5 : p < i + 3 + 3 * (S.length - i)
  · rw [expandTapeVal_mid S (by omega) (by omega), expandTapeVal_mid S (by omega) h5]
    have hsub : p - (i + 3) = (p - 2 - (i + 1 + 3)) + 3 := by omega
    have hmod : (p - (i + 3)) % 3 = (p - 2 - (i + 1 + 3)) % 3 := by rw [hsub, Nat.add_mod_right]
    have hdiv : i + (p - (i + 3)) / 3 = i + 1 + (p - 2 - (i + 1 + 3)) / 3 := by
      rw [hsub, Nat.add_div_right _ (by decide : 0 < 3)]; omega
    rw [hmod, hdiv]
  · by_cases h6 : p < i + 6 + 3 * (S.length - i)
    · rw [expandTapeVal_wall S (by omega) (by omega), expandTapeVal_wall S (by omega) h6]
      have hr : p - 2 - (i + 1 + 3 + 3 * (S.length - (i + 1))) = p - (i + 3 + 3 * (S.length - i)) := by omega
      rw [hr]
    · rw [expandTapeVal_out S (by omega), expandTapeVal_out S (by omega)]

theorem shiftSuffix_spec (B L_bnd : ℕ) (S : List Bool) (i : ℕ) (hiL : i < S.length)
    (hLB : L_bnd ≤ B) :
    ∀ m {τ : ℕ → Bool},
      m ≤ S.length - i →
      i + 6 + 3 * (S.length - i) ≤ L_bnd →
      (∀ p < i + 1, τ p = S.getD p false) →
      τ (i + 1) = false →
      τ (i + 2) = true →
      τ (i + 3) = true →
      (∀ p, i + 4 ≤ p → p < i + 4 + 3 * m → τ p = expandTapeVal S (i + 1) p) →
      (∀ p, i + 6 + 3 * m ≤ p → τ p = expandTapeVal S i p) →
      ∃ τ_end : ℕ → Bool,
        (∀ p, τ_end p = expandTapeVal S i p) ∧
        StepExecB (shiftSuffixFor (S.getD i false)) B L_bnd
          (true, (0, false, false)) τ (i + 1 + 3 * m)
          (true, (19, true, false)) τ_end i (13 * m + 12) := by
  intro m
  induction m with
  | zero =>
    intro τ _ hB hlow hk0 hk1 hk2 _ hhigh
    simp only [Nat.mul_zero, Nat.add_zero] at hhigh ⊢
    let bp := S.getD i false
    let u1 := Function.update τ (i + 3) false
    let u2 := Function.update u1 (i + 4) false
    let u3 := Function.update u2 (i + 5) bp
    let u4 := Function.update u3 (i + 2) true
    let u5 := Function.update u4 (i + 1) true
    let u6 := Function.update u5 i true
    have he11 : StepExecB (shiftOneBlk bp) B L_bnd (0, false, false) τ (i + 1)
        (19, true, false) u6 i 11 := by
      refine StepExecB.step (1, false, false) false .right τ (i + 2) (by simp [shiftOneBlk, hk0]) (by omega) (update_eq_self_of_eq hk0) rfl ?_
      refine StepExecB.step (2, false, true) true .right τ (i + 3) (by simp [shiftOneBlk, hk1]) (by omega) (update_eq_self_of_eq hk1) rfl ?_
      refine StepExecB.step (3, false, false) false .right u1 (i + 4) (by simp [shiftOneBlk, hk2]) (by omega) rfl rfl ?_
      refine StepExecB.step (4, false, false) false .right u2 (i + 5) rfl (by omega) rfl rfl ?_
      refine StepExecB.step (5, false, false) bp .left u3 (i + 4) rfl (by omega) rfl (by simp [moveHead]) ?_
      refine StepExecB.step (6, false, false) (u3 (i + 4)) .left u3 (i + 3) rfl (by omega) (by simp) (by simp [moveHead]) ?_
      refine StepExecB.step (7, false, false) (u3 (i + 3)) .left u3 (i + 2) rfl (by omega) (by simp) (by simp [moveHead]) ?_
      refine StepExecB.step (8, false, false) true .left u4 (i + 1) rfl (by omega) rfl (by simp [moveHead]) ?_
      refine StepExecB.step (9, false, false) true .left u5 i rfl (by omega) rfl (by simp [moveHead]) ?_
      refine StepExecB.step (10, false, false) true .right u6 (i + 1) rfl (by omega) rfl rfl ?_
      refine StepExecB.step (19, true, false) (u6 (i + 1)) .left u6 i rfl (by omega) (by simp) (by simp [moveHead]) ?_
      exact StepExecB.done hLB (by omega) (fun _ => rfl)
    refine ⟨u6, ?_, (StepExecB.loopAt_done shiftBlkNext he11 rfl).weaken 12 (by omega)⟩
    intro p
    dsimp only [u6, u5, u4, u3, u2, u1, bp]
    by_cases hp_i : p = i
    · subst hp_i; rw [Function.update_self, expandTapeVal_home S (by omega) (by omega)]
    · rw [Function.update_of_ne hp_i]
      by_cases hp1 : p = i + 1
      · subst hp1; rw [Function.update_self, expandTapeVal_home S (by omega) (by omega)]
      · rw [Function.update_of_ne hp1]
        by_cases hp2 : p = i + 2
        · subst hp2; rw [Function.update_self, expandTapeVal_home S (by omega) (by omega)]
        · rw [Function.update_of_ne hp2]
          by_cases hp5 : p = i + 5
          · subst hp5
            rw [Function.update_self, expandTapeVal_mid S (by omega) (by omega)]
            have hm5 : (i + 5 - (i + 3)) % 3 = 2 := by omega
            simp only [hm5, ↓reduceIte]
            congr 1; omega
          · rw [Function.update_of_ne hp5]
            by_cases hp4 : p = i + 4
            · subst hp4
              rw [Function.update_self, expandTapeVal_mid S (by omega) (by omega)]
              have hm4 : ¬ ((i + 4 - (i + 3)) % 3 = 2) := by omega
              simp only [hm4, ↓reduceIte]
            · rw [Function.update_of_ne hp4]
              by_cases hp3 : p = i + 3
              · subst hp3
                rw [Function.update_self, expandTapeVal_mid S (by omega) (by omega)]
                have hm3 : ¬ ((i + 3 - (i + 3)) % 3 = 2) := by omega
                simp only [hm3, ↓reduceIte]
              · rw [Function.update_of_ne hp3]
                by_cases hlt_i : p < i
                · rw [hlow p (by omega), expandTapeVal_lt S hlt_i]
                · exact hhigh p (by omega)
  | succ m ih =>
    intro τ hm_le hB hlow hk0 hk1 hk2 hmid hhigh
    let p0 := i + 1 + 3 * (m + 1)
    have hp0_eq : p0 = i + 4 + 3 * m := by dsimp [p0]; ring
    let c0 := τ p0
    let c1 := τ (p0 + 1)
    let c2 := τ (p0 + 2)
    have hc0_v : c0 = expandTapeVal S (i + 1) p0 := hmid p0 (by omega) (by omega)
    have hc1_v : c1 = expandTapeVal S (i + 1) (p0 + 1) := hmid (p0 + 1) (by omega) (by omega)
    have hc2_v : c2 = expandTapeVal S (i + 1) (p0 + 2) := hmid (p0 + 2) (by omega) (by omega)
    have hc1_false : c1 = false := by
      rw [hc1_v, hp0_eq]
      by_cases h3 : i + 4 + 3 * m + 1 < i + 1 + 3 + 3 * (S.length - (i + 1))
      · rw [expandTapeVal_mid S (by omega) h3]
        have hm1 : ¬ ((i + 4 + 3 * m + 1 - (i + 1 + 3)) % 3 = 2) := by omega
        simp only [hm1, ↓reduceIte]
      · rw [expandTapeVal_wall S (by omega) (by omega)]
        have hsub : i + 4 + 3 * m + 1 - (i + 1 + 3 + 3 * (S.length - (i + 1))) = 1 := by omega
        rw [hsub]; rfl
    have hcond : ((!c0) && c1 && c2) = false := by simp [hc1_false]
    let v1 := Function.update τ (p0 + 2) c0
    let v2 := Function.update v1 (p0 + 3) c1
    let v3 := Function.update v2 (p0 + 4) c2
    have he1 : StepExecB (shiftOneBlk (S.getD i false)) B L_bnd
        (0, false, false) τ p0 (19, false, false) v3 (i + 1 + 3 * m) 11 := by
      refine StepExecB.step (1, c0, false) c0 .right τ (p0 + 1) rfl (by omega) (by simp [c0]) rfl ?_
      refine StepExecB.step (2, c0, c1) c1 .right τ (p0 + 2) rfl (by omega) (by simp [c1]) rfl ?_
      refine StepExecB.step (11, c1, c2) c0 .right v1 (p0 + 3) (by simp [shiftOneBlk, c2, hcond]) (by omega) rfl rfl ?_
      refine StepExecB.step (12, false, c2) c1 .right v2 (p0 + 4) rfl (by omega) rfl rfl ?_
      refine StepExecB.step (13, false, false) c2 .left v3 (p0 + 3) rfl (by omega) rfl (by simp [moveHead]) ?_
      refine StepExecB.step (14, false, false) (v3 (p0 + 3)) .left v3 (p0 + 2) rfl (by omega) (by simp) (by simp [moveHead]) ?_
      refine StepExecB.step (15, false, false) (v3 (p0 + 2)) .left v3 (p0 + 1) rfl (by omega) (by simp) (by simp [moveHead]) ?_
      refine StepExecB.step (16, false, false) (v3 (p0 + 1)) .left v3 p0 rfl (by omega) (by simp) (by simp [moveHead]) ?_
      refine StepExecB.step (17, false, false) (v3 p0) .left v3 (p0 - 1) rfl (by omega) (by simp) (by simp [moveHead]) ?_
      refine StepExecB.step (18, false, false) (v3 (p0 - 1)) .left v3 (p0 - 2) rfl (by omega) (by simp) (by simp [moveHead]; omega) ?_
      refine StepExecB.step (19, false, false) (v3 (p0 - 2)) .left v3 (i + 1 + 3 * m) rfl (by omega) (by simp) (by simp [moveHead, p0]; omega) ?_
      exact StepExecB.done hLB (by omega) (fun _ => rfl)
    have hv3_lt : ∀ p < p0 + 2, v3 p = τ p := by
      intro p hp
      dsimp only [v3, v2, v1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hv3_high : ∀ p, i + 6 + 3 * m ≤ p → v3 p = expandTapeVal S i p := by
      intro p hp
      dsimp only [v3, v2, v1]
      by_cases h4 : p = p0 + 4
      · subst h4
        rw [Function.update_self, hc2_v, ← expandTapeVal_shift_eq S i (p0 + 4) hiL (by omega)]
        congr 1
      · rw [Function.update_of_ne h4]
        by_cases h3 : p = p0 + 3
        · subst h3
          rw [Function.update_self, hc1_v, ← expandTapeVal_shift_eq S i (p0 + 3) hiL (by omega)]
          congr 1
        · rw [Function.update_of_ne h3]
          by_cases h2 : p = p0 + 2
          · subst h2
            rw [Function.update_self, hc0_v, ← expandTapeVal_shift_eq S i (p0 + 2) hiL (by omega)]
            congr 1
          · rw [Function.update_of_ne h2]
            exact hhigh p (by omega)
    rcases ih (τ := v3) (by omega) hB
        (fun p hp => (hv3_lt p (by omega)).trans (hlow p hp))
        ((hv3_lt _ (by omega)).trans hk0)
        ((hv3_lt _ (by omega)).trans hk1)
        ((hv3_lt _ (by omega)).trans hk2)
        (fun p hp1 hp2 => (hv3_lt p (by omega)).trans (hmid p hp1 (by omega)))
        hv3_high
      with ⟨τ_end, hend_eq, he_rest⟩
    exact ⟨τ_end, hend_eq,
      (StepExecB.loopAt_step shiftBlkNext (by omega) he1 rfl he_rest).weaken (13 * (m + 1) + 12) (by omega)⟩

abbrev ExpandBodyQ : Type :=
  (Fin 6 × Bool × Bool) ⊕
  (Bool × (Unit ⊕ ((Bool × (Bool × (Fin 5 × Bool × Bool))) ⊕ (Bool × (Bool × (Bool × (Fin 20 × Bool × Bool)))))))

def expandIterBody : StepFn ExpandBodyQ :=
  seqAt expandTestZero
    (sumStep (nopStep Unit)
      (seqAt (familyStep (fun (_ : Bool) => walkToWall3))
        (familyStep shiftSuffixFor)
        (fun (bp, _) => (bp, (true, (0, false, false))))))
    (fun (_, done, bp) =>
      if done then Sum.inl ()
      else Sum.inr (Sum.inl (bp, (true, (0, false, false)))))

def expandIterNext : ExpandBodyQ → Option ExpandBodyQ
  | Sum.inr (true, Sum.inr _) => some (Sum.inl (0, false, false))
  | _ => none

def rawExpandToWS : StepFn (Fin 11 ⊕ (Bool × (Bool × ExpandBodyQ))) :=
  seqAt seedExpand (loopAt expandIterBody expandIterNext)
    (fun _ => (true, Sum.inl (0, false, false)))

theorem encodeSegmentsAux_singleton_getD (S : List Bool) (j : ℕ) (hj : j ≤ S.length) :
    (encodeSegmentsAux [S]).getD j blkHome =
      if j < S.length then blkData false (S.getD j false) else blkWall := by
  simp only [encodeSegmentsAux]
  by_cases hjS : j < S.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hjS]),
        List.getElem?_map, List.getElem?_eq_getElem hjS]
    simp [hjS, List.getD_eq_getElem?_getD]
  · have hjeq : j = S.length := by omega
    subst hjeq
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp

theorem expandTapeVal_zero_matchesWS (S : List Bool) {τ : ℕ → Bool}
    (hτ : ∀ p, τ p = expandTapeVal S 0 p) :
    MatchesWS (readBlk τ) [S] ∧ (∀ p, 3 * (S.length + 2) ≤ p → τ p = false) := by
  have hlen_ws : (encodeWorkspace [S]).length = S.length + 2 := by
    simp [encodeWorkspace, encodeSegmentsAux]
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [hlen_ws] at hj
    cases j with
    | zero =>
      dsimp only [readBlk, encodeWorkspace]
      rw [hτ 0, hτ 1, hτ 2,
          expandTapeVal_home S (by omega) (by omega),
          expandTapeVal_home S (by omega) (by omega),
          expandTapeVal_home S (by omega) (by omega)]
      rfl
    | succ j' =>
      have hj' : j' ≤ S.length := by omega
      simp only [encodeWorkspace, List.getD_cons_succ, encodeSegmentsAux_singleton_getD S j' hj']
      dsimp only [readBlk]
      rw [hτ (3 * (j' + 1)), hτ (3 * (j' + 1) + 1), hτ (3 * (j' + 1) + 2)]
      by_cases hjS : j' < S.length
      · simp only [hjS, ↓reduceIte]
        rw [expandTapeVal_mid S (by omega) (by omega),
            expandTapeVal_mid S (by omega) (by omega),
            expandTapeVal_mid S (by omega) (by omega)]
        have hm0 : ¬ ((3 * (j' + 1) - (0 + 3)) % 3 = 2) := by omega
        have hm1 : ¬ ((3 * (j' + 1) + 1 - (0 + 3)) % 3 = 2) := by omega
        have hm2 : (3 * (j' + 1) + 2 - (0 + 3)) % 3 = 2 := by omega
        simp only [hm0, hm1, hm2, ↓reduceIte]
        have hdiv : 0 + (3 * (j' + 1) + 2 - (0 + 3)) / 3 = j' := by omega
        rw [hdiv]; rfl
      · have hjeq : j' = S.length := by omega
        subst hjeq
        simp only [hjS, ↓reduceIte]
        rw [expandTapeVal_wall S (by omega) (by omega),
            expandTapeVal_wall S (by omega) (by omega),
            expandTapeVal_wall S (by omega) (by omega)]
        have s0 : 3 * (S.length + 1) - (0 + 3 + 3 * (S.length - 0)) = 0 := by omega
        have s1 : 3 * (S.length + 1) + 1 - (0 + 3 + 3 * (S.length - 0)) = 1 := by omega
        have s2 : 3 * (S.length + 1) + 2 - (0 + 3 + 3 * (S.length - 0)) = 2 := by omega
        rw [s0, s1, s2]; rfl
  · intro p hp
    rw [hτ p, expandTapeVal_out S (by omega)]

theorem rawExpandToWS_spec (B L_bnd : ℕ) (S : List Bool) {τ₁ : ℕ → Bool}
    (hLB : L_bnd ≤ B) (h3_bnd : 3 * (S.length + 2) ≤ L_bnd)
    (hS : ∀ p, τ₁ p = if p < S.length then S.getD p false else false) :
    ∃ q_end, ∃ τ₂ : ℕ → Bool,
      MatchesWS (readBlk τ₂) [S] ∧
      (∀ p, 3 * (S.length + 2) ≤ p → τ₂ p = false) ∧
      StepExecB rawExpandToWS B L_bnd (Sum.inl 0) τ₁ S.length
        q_end τ₂ 0 ((S.length + 2) * (20 * S.length + 40)) := by
  let L := S.length
  rcases seedExpand_spec B L_bnd S hLB (by omega) hS with ⟨τ_seed, hseed, he_seed⟩
  let S_step := 20 * L + 30
  have hloop : ∀ k {τa : ℕ → Bool},
      k ≤ L →
      (∀ p, τa p = expandTapeVal S k p) →
      ∃ τ_end : ℕ → Bool,
        (∀ p, τ_end p = expandTapeVal S 0 p) ∧
        StepExecB (loopAt expandIterBody expandIterNext) B L_bnd
          (true, Sum.inl (0, false, false)) τa k
          (true, Sum.inr (true, Sum.inl ())) τ_end 0 ((k + 1) * (S_step + 2)) := by
    intro k
    induction k with
    | zero =>
      intro τa _ hτa
      have h0 : τa 0 = true := by rw [hτa 0, expandTapeVal_home S (by omega) (by omega)]
      have h1 : τa 1 = true := by rw [hτa 1, expandTapeVal_home S (by omega) (by omega)]
      have he_tz := expandTestZero_zero B L_bnd hLB (by omega) h0 h1
      have he_nop : StepExecB (nopStep Unit) B L_bnd () τa 0 () τa 0 0 :=
        StepExecB.done hLB (by omega) (fun _ => rfl)
      have he_inl := StepExecB.inl (nopStep Unit)
        (seqAt (familyStep (fun (_ : Bool) => walkToWall3)) (familyStep shiftSuffixFor)
          (fun (bp, _) => (bp, (true, (0, false, false))))) he_nop
      have he_body_raw : StepExecB expandIterBody B L_bnd (Sum.inl (0, false, false)) τa 0
          (Sum.inr (true, Sum.inl ())) τa 0 (5 + 2 + 0) := by
        unfold expandIterBody
        exact StepExecB.seqAt (by omega) he_tz he_inl
      have he_body := he_body_raw.weaken S_step (by dsimp only [S_step]; omega)
      exact ⟨τa, hτa, (StepExecB.loopAt_done expandIterNext he_body rfl).weaken ((0 + 1) * (S_step + 2)) (by omega)⟩
    | succ i ih =>
      intro τa hi_le hτa
      have hiL : i < L := by omega
      have hτai : τa i = S.getD i false := by rw [hτa i, expandTapeVal_lt S (by omega)]
      have he_tz := expandTestZero_succ B L_bnd i (τ := τa) hLB (by omega)
      let τb := Function.update τa (i + 1) false
      let m_w := L - i
      have hnot_wall : ∀ t < m_w,
          (τb ((i + 1) + 3 * t), τb ((i + 1) + 3 * t + 1), τb ((i + 1) + 3 * t + 2)) ≠ blkWall := by
        intro t ht
        by_cases ht0 : t = 0
        · subst ht0
          have hb0 : τb (i + 1) = false := by simp [τb]
          rw [Nat.mul_zero, Nat.add_zero, hb0]; simp [blkWall]
        · have hc0 : τb ((i + 1) + 3 * t) = false := by
            dsimp [τb]
            rw [Function.update_of_ne (by omega), hτa _,
                expandTapeVal_mid S (by omega) (by dsimp [L, m_w] at ht; omega)]
            have hm0 : ¬ ((i + 1 + 3 * t - (i + 1 + 3)) % 3 = 2) := by omega
            simp only [hm0, ↓reduceIte]
          rw [hc0]; simp [blkWall]
      have h_at_wall : (τb ((i + 1) + 3 * m_w), τb ((i + 1) + 3 * m_w + 1), τb ((i + 1) + 3 * m_w + 2)) = blkWall := by
        have hw_pos : (i + 1) + 3 * m_w = i + 1 + 3 + 3 * (S.length - (i + 1)) := by dsimp [L, m_w]; omega
        dsimp [τb]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            hτa _, hτa _, hτa _, hw_pos,
            expandTapeVal_wall S (by omega) (by omega),
            expandTapeVal_wall S (by omega) (by omega),
            expandTapeVal_wall S (by omega) (by omega)]
        have s0 : i + 1 + 3 + 3 * (S.length - (i + 1)) - (i + 1 + 3 + 3 * (S.length - (i + 1))) = 0 := by omega
        have s1 : i + 1 + 3 + 3 * (S.length - (i + 1)) + 1 - (i + 1 + 3 + 3 * (S.length - (i + 1))) = 1 := by omega
        have s2 : i + 1 + 3 + 3 * (S.length - (i + 1)) + 2 - (i + 1 + 3 + 3 * (S.length - (i + 1))) = 2 := by omega
        rw [s0, s1, s2]; rfl
      have he_ww := StepExecB.family (fun (_ : Bool) => walkToWall3) (τa i)
        (walkToWall3_spec B L_bnd hLB m_w (i + 1) (by dsimp [m_w, L] at *; omega) hnot_wall h_at_wall)
      rcases shiftSuffix_spec B L_bnd S i hiL hLB m_w (τ := τb) (Nat.le_refl _) (by dsimp [L] at *; omega)
          (fun p hp => by dsimp [τb]; rw [Function.update_of_ne (by omega), hτa p, expandTapeVal_lt S hp])
          (by simp [τb])
          (by dsimp [τb]; rw [Function.update_of_ne (by omega), hτa (i + 2), expandTapeVal_home S (by omega) (by omega)])
          (by dsimp [τb]; rw [Function.update_of_ne (by omega), hτa (i + 3), expandTapeVal_home S (by omega) (by omega)])
          (fun p hp1 _ => by dsimp [τb]; rw [Function.update_of_ne (by omega), hτa p])
          (fun p hp => by
            dsimp [τb]
            rw [Function.update_of_ne (by omega), hτa p,
                expandTapeVal_out S (by dsimp [m_w, L] at hp; omega),
                expandTapeVal_out S (by dsimp [m_w, L] at hp; omega)])
        with ⟨τ_sh, hτ_sh, he_sh_raw⟩
      rw [← hτai] at he_sh_raw
      have he_sh := StepExecB.family shiftSuffixFor (τa i) he_sh_raw
      have he_ws := StepExecB.seqAt (s₂ := familyStep shiftSuffixFor)
        (f := fun (bp, _) => (bp, (true, (0, false, false))))
        (by dsimp [m_w, L] at *; omega) he_ww (by exact he_sh)
      have he_inr := StepExecB.inr (nopStep Unit) _ he_ws
      have he_body_raw : StepExecB expandIterBody B L_bnd (Sum.inl (0, false, false)) τa (i + 1)
          (Sum.inr (true, Sum.inr (Sum.inr (true, (τa i, (true, (19, true, false))))))) τ_sh i
          (5 + 2 + ((6 * m_w + 5) + 2 + (13 * m_w + 12))) := by
        unfold expandIterBody
        exact StepExecB.seqAt (by omega) he_tz he_inr
      have he_body := he_body_raw.weaken S_step (by
          have : m_w ≤ L := Nat.sub_le L i
          dsimp only [S_step]; omega)
      rcases ih (by omega) hτ_sh with ⟨τ_end, hend_eq, he_rest⟩
      refine ⟨τ_end, hend_eq, (StepExecB.loopAt_step expandIterNext (by omega) he_body rfl he_rest).weaken
        ((i + 1 + 1) * (S_step + 2)) ?_⟩
      linarith [show (i + 1 + 1) * (S_step + 2) = (S_step + 2) + (i + 1) * (S_step + 2) by ring]
  rcases hloop L (Nat.le_refl L) hseed with ⟨τ₂, hτ₂, he_lp⟩
  rcases expandTapeVal_zero_matchesWS S hτ₂ with ⟨hws, hout⟩
  have he_tot := (StepExecB.seqAt (f := fun _ => (true, Sum.inl (0, false, false)))
    (by omega) he_seed he_lp).weaken ((L + 2) * (20 * L + 40)) (by
      dsimp only [S_step]
      nlinarith)
  exact ⟨_, τ₂, hws, hout, he_tot⟩

/-! ### Pinning `len = 3 * M_blk` (`blkTouchWall`) and Growing Segments (`blkGrowLast`) -/

theorem writeBlk_readBlk_self (τ : ℕ → Bool) (j : ℕ) :
    writeBlk τ j (readBlk τ j) = τ := by
  funext k
  unfold writeBlk readBlk
  by_cases h0 : k = 3 * j
  · subst h0; simp
  · rw [Function.update_of_ne h0]
    by_cases h1 : k = 3 * j + 1
    · subst h1; simp
    · rw [Function.update_of_ne h1]
      by_cases h2 : k = 3 * j + 2
      · subst h2; simp
      · rw [Function.update_of_ne h2]

theorem encodeWorkspace_lt_wall_ne_wall (segs : List (List Bool)) (h : segs ≠ [])
    {j : ℕ} (hj : j < (encodeWorkspace segs).length - 1) :
    (encodeWorkspace segs).getD j blkHome ≠ blkWall := by
  intro heq
  have hiff := (encodeWorkspace_wall_iff segs h (by omega)).mp heq
  omega

theorem encodeWorkspace_last_wall (segs : List (List Bool)) (h : segs ≠ []) :
    (encodeWorkspace segs).getD ((encodeWorkspace segs).length - 1) blkHome = blkWall := by
  have hpos : 1 ≤ (encodeWorkspace segs).length := by simp [encodeWorkspace]
  exact (encodeWorkspace_wall_iff segs h (by omega)).mpr rfl

theorem encodeSegmentsAux_len_pos :
    ∀ (segs : List (List Bool)), segs ≠ [] → 1 ≤ (encodeSegmentsAux segs).length
  | [], h => absurd rfl h
  | [s], _ => by simp [encodeSegmentsAux]
  | s0 :: s1 :: rest, _ => by
      simp only [encodeSegmentsAux, List.length_append, List.length_singleton]
      omega

theorem encodeWorkspace_len_ge2 (segs : List (List Bool)) (h : segs ≠ []) :
    2 ≤ (encodeWorkspace segs).length := by
  have h1 := encodeSegmentsAux_len_pos segs h
  simp only [encodeWorkspace, List.length_cons]
  omega

/-- Walk right to `blkWall` at `M_cur - 1` (touching physical cell `3 * M_cur - 1` so ANY
`len ≤ 3 * M_cur` becomes EXACTLY `3 * M_cur`!) and rewind to `blkHome` at `0`. -/
def blkTouchWall : BlkStepFn Bool :=
  fun rew sym =>
    if rew then
      if sym = blkHome then none
      else some (true, sym, QCSD_HeadDir.left)
    else
      if sym = blkWall then some (true, sym, QCSD_HeadDir.left)
      else some (false, sym, QCSD_HeadDir.right)

theorem liftBlockStep_one_relaxed {Q : Type} (bs : BlkStepFn Q) (B M_blk len : ℕ)
    (τ : ℕ → Bool) (q q' : Q) (sym' : BlkSym) (d : QCSD_HeadDir) (j : ℕ)
    (hj : j < M_blk) (hlen_M : len ≤ 3 * M_blk) (hM_B : 3 * M_blk ≤ B)
    (hd_valid : (d = QCSD_HeadDir.left → 1 ≤ j) ∧ (d = QCSD_HeadDir.right → j + 1 < M_blk))
    (hsome : bs q (readBlk τ j) = some (q', sym', d)) :
    stepFnIter (liftBlockStep bs) (liftBlkEntry q, len, τ, 3 * j) 7 =
      some (liftBlkEntry q', max len (3 * j + 3), writeBlk τ j sym', 3 * moveHead j d) ∧
    (∀ m ≤ 7, ∀ q_m l_m τ_m h_m,
      stepFnIter (liftBlockStep bs) (liftBlkEntry q, len, τ, 3 * j) m =
        some (q_m, l_m, τ_m, h_m) → l_m ≤ B ∧ h_m + 1 ≤ B) := by
  rcases sym' with ⟨w0, w1, w2⟩
  let l0 := max len (3 * j + 1)
  let l1 := max l0 (3 * j + 2)
  let l2 := max len (3 * j + 3)
  have hl2_eq : max l1 (3 * j + 3) = l2 := by dsimp [l0, l1, l2]; omega
  have hm_r0 : max l2 (3 * j + 1) = l2 := by dsimp [l2]; omega
  have hm_r1 : max l2 (3 * j + 2) = l2 := by dsimp [l2]; omega
  have hm_r2 : max l2 (3 * (j + 1)) = l2 := by dsimp [l2]; omega
  have h3j2_sub : (3 * j + 2) - 1 = 3 * j + 1 := by omega
  have h3j1_sub : (3 * j + 1) - 1 = 3 * j := by omega
  have hread : (τ (3 * j), τ (3 * j + 1), τ (3 * j + 2)) = readBlk τ j := rfl
  let τ₁ := Function.update τ (3 * j + 2) w2
  let τ₂ := Function.update τ₁ (3 * j + 1) w1
  let τ₃ := writeBlk τ j (w0, w1, w2)
  have hτ₃_def : Function.update τ₂ (3 * j) w0 = τ₃ := rfl
  have hs0 : stepFnOnce (liftBlockStep bs) (liftBlkEntry q, len, τ, 3 * j) =
      some ((q, 1, τ (3 * j), false, false, QCSD_HeadDir.left), l0, τ, 3 * j + 1) := by
    simp [stepFnOnce, liftBlockStep, liftBlkEntry, moveHead, l0]
  have hs1 : stepFnOnce (liftBlockStep bs)
      ((q, 1, τ (3 * j), false, false, QCSD_HeadDir.left), l0, τ, 3 * j + 1) =
      some ((q, 2, τ (3 * j), τ (3 * j + 1), false, QCSD_HeadDir.left), l1, τ, 3 * j + 2) := by
    simp [stepFnOnce, liftBlockStep, moveHead, l1]
  have hs2 : stepFnOnce (liftBlockStep bs)
      ((q, 2, τ (3 * j), τ (3 * j + 1), false, QCSD_HeadDir.left), l1, τ, 3 * j + 2) =
      some ((q', 5, w0, w1, false, d), l2, τ₁, 3 * j + 1) := by
    simp [stepFnOnce, liftBlockStep, hread, hsome, moveHead, hl2_eq, h3j2_sub, τ₁]
  have hs3 : stepFnOnce (liftBlockStep bs)
      ((q', 5, w0, w1, false, d), l2, τ₁, 3 * j + 1) =
      some ((q', 6, w0, false, false, d), l2, τ₂, 3 * j) := by
    simp [stepFnOnce, liftBlockStep, moveHead, hm_r1, h3j1_sub, τ₂]
  cases d with
  | right =>
    have hj_next : j + 1 < M_blk := hd_valid.2 rfl
    have hs4 : stepFnOnce (liftBlockStep bs) ((q', 6, w0, false, false, QCSD_HeadDir.right), l2, τ₂, 3 * j) =
        some ((q', 7, false, false, false, QCSD_HeadDir.right), l2, τ₃, 3 * j + 1) := by
      simp [stepFnOnce, liftBlockStep, moveHead, hm_r0, hτ₃_def]
    have hs5 : stepFnOnce (liftBlockStep bs)
        ((q', 7, false, false, false, QCSD_HeadDir.right), l2, τ₃, 3 * j + 1) =
        some ((q', 8, false, false, false, QCSD_HeadDir.right), l2, τ₃, 3 * j + 2) := by
      simp [stepFnOnce, liftBlockStep, moveHead, hm_r1]
    have hs6 : stepFnOnce (liftBlockStep bs)
        ((q', 8, false, false, false, QCSD_HeadDir.right), l2, τ₃, 3 * j + 2) =
        some (liftBlkEntry q', l2, τ₃, 3 * (j + 1)) := by
      have h3j3 : 3 * j + 2 + 1 = 3 * (j + 1) := by omega
      simp [stepFnOnce, liftBlockStep, liftBlkEntry, moveHead, h3j3, hm_r2]
    refine ⟨by simp [stepFnIter, hs0, hs1, hs2, hs3, hs4, hs5, hs6, moveHead, τ₃, l2], ?_⟩
    intro m hm q_m l_m τ_m h_m hm_eq
    have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [stepFnIter] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
    · simp [stepFnIter, hs0] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l0]; omega
    · simp [stepFnIter, hs0, hs1] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l0, l1]; omega
    · simp [stepFnIter, hs0, hs1, hs2] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l2]; omega
    · simp [stepFnIter, hs0, hs1, hs2, hs3] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l2]; omega
    · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l2]; omega
    · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4, hs5] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l2]; omega
    · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l2]; omega
  | left =>
    have hj_pos : 1 ≤ j := hd_valid.1 rfl
    have hml1 : max l2 (3 * j - 1 + 1) = l2 := by dsimp [l2]; omega
    have hml2 : max l2 (3 * j - 2 + 1) = l2 := by dsimp [l2]; omega
    have hs4 : stepFnOnce (liftBlockStep bs) ((q', 6, w0, false, false, QCSD_HeadDir.left), l2, τ₂, 3 * j) =
        some ((q', 7, false, false, false, QCSD_HeadDir.left), l2, τ₃, 3 * j - 1) := by
      simp [stepFnOnce, liftBlockStep, moveHead, hm_r0, hτ₃_def]
    have hs5 : stepFnOnce (liftBlockStep bs)
        ((q', 7, false, false, false, QCSD_HeadDir.left), l2, τ₃, 3 * j - 1) =
        some ((q', 8, false, false, false, QCSD_HeadDir.left), l2, τ₃, 3 * j - 2) := by
      have hsub : 3 * j - 1 - 1 = 3 * j - 2 := by omega
      simp [stepFnOnce, liftBlockStep, moveHead, hml1, hsub]
    have hs6 : stepFnOnce (liftBlockStep bs)
        ((q', 8, false, false, false, QCSD_HeadDir.left), l2, τ₃, 3 * j - 2) =
        some (liftBlkEntry q', l2, τ₃, 3 * (j - 1)) := by
      have hsub : 3 * j - 2 - 1 = 3 * (j - 1) := by omega
      simp [stepFnOnce, liftBlockStep, liftBlkEntry, moveHead, hml2, hsub]
    refine ⟨by simp [stepFnIter, hs0, hs1, hs2, hs3, hs4, hs5, hs6, moveHead, τ₃, l2], ?_⟩
    intro m hm q_m l_m τ_m h_m hm_eq
    have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [stepFnIter] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; omega
    · simp [stepFnIter, hs0] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l0]; omega
    · simp [stepFnIter, hs0, hs1] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l0, l1]; omega
    · simp [stepFnIter, hs0, hs1, hs2] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l2]; omega
    · simp [stepFnIter, hs0, hs1, hs2, hs3] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l2]; omega
    · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l2]; omega
    · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4, hs5] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l2]; omega
    · simp [stepFnIter, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at hm_eq; rcases hm_eq with ⟨_, rfl, _, rfl⟩; dsimp [l2]; omega

theorem blkTouchWall_spec (B : ℕ) (segs : List (List Bool)) (hsegs : segs ≠ [])
    {len : ℕ} {τ : ℕ → Bool}
    (hlen : len ≤ 3 * (encodeWorkspace segs).length)
    (hB : 3 * (encodeWorkspace segs).length ≤ B)
    (hws : MatchesWS (readBlk τ) segs) :
    StepExec (liftBlockStep blkTouchWall) B (liftBlkEntry false) len τ 0
      (liftBlkExit true) (3 * (encodeWorkspace segs).length) τ 0
      (14 * (encodeWorkspace segs).length + 4) := by
  let M_blk := (encodeWorkspace segs).length
  have hM_ge2 : 2 ≤ M_blk := encodeWorkspace_len_ge2 segs hsegs
  -- Walk right `M_blk - 1` steps from `0` to `M_blk - 1`:
  have hwalk_right : ∀ d (l_cur : ℕ),
      d ≤ M_blk - 1 →
      l_cur ≤ 3 * M_blk →
      ∃ l_out ≤ 3 * M_blk,
        stepFnIter (liftBlockStep blkTouchWall) (liftBlkEntry false, l_cur, τ, 3 * (M_blk - 1 - d)) (7 * d) =
          some (liftBlkEntry false, l_out, τ, 3 * (M_blk - 1)) ∧
        (∀ m ≤ 7 * d, ∀ q_m l_m τ_m h_m,
          stepFnIter (liftBlockStep blkTouchWall) (liftBlkEntry false, l_cur, τ, 3 * (M_blk - 1 - d)) m =
            some (q_m, l_m, τ_m, h_m) → l_m ≤ B ∧ h_m + 1 ≤ B) := by
    intro d
    induction d with
    | zero =>
      intro l_cur _ hl
      simp only [Nat.sub_zero, Nat.mul_zero]
      exact ⟨l_cur, hl, rfl, fun m hm _ _ _ _ heq => by
        obtain rfl : m = 0 := by omega
        cases heq; exact ⟨by omega, by omega⟩⟩
    | succ d ih =>
      intro l_cur hd hl
      let j := M_blk - 1 - (d + 1)
      have hj_lt : j < M_blk - 1 := by omega
      have hne_wall : readBlk τ j ≠ blkWall := by
        rw [hws j (by omega)]
        exact encodeWorkspace_lt_wall_ne_wall segs hsegs hj_lt
      have hbs : blkTouchWall false (readBlk τ j) = some (false, readBlk τ j, QCSD_HeadDir.right) := by
        simp [blkTouchWall, hne_wall]
      have hone := liftBlockStep_one_relaxed blkTouchWall B M_blk l_cur τ false false
        (readBlk τ j) .right j (by omega) hl hB ⟨by simp, fun _ => by omega⟩ hbs
      have hw_self : writeBlk τ j (readBlk τ j) = τ := writeBlk_readBlk_self τ j
      have hnext_j : moveHead j .right = M_blk - 1 - d := by simp [moveHead]; omega
      rw [hw_self, hnext_j] at hone
      rcases ih (max l_cur (3 * j + 3)) (by omega) (by omega) with ⟨l_out, hl_out, hrest, hbnd_r⟩
      refine ⟨l_out, hl_out, ?_, ?_⟩
      · rw [show 7 * (d + 1) = 7 + 7 * d by ring, stepFnIter_add, hone.1, Option.bind_some, hrest]
      · intro m hm q_m l_m τ_m h_m hm_eq
        by_cases hm7 : m ≤ 7
        · rcases stepFnIter_le_some hm7 hone.1 with ⟨cfg, hsub⟩
          rw [hsub] at hm_eq; cases hm_eq
          exact hone.2 m hm7 q_m l_m τ_m h_m hsub
        · have heq : m = 7 + (m - 7) := by omega
          rw [heq, stepFnIter_add, hone.1, Option.bind_some] at hm_eq
          exact hbnd_r (m - 7) (by omega) q_m l_m τ_m h_m hm_eq
  rcases hwalk_right (M_blk - 1) len (Nat.le_refl _) hlen with ⟨l_mid, hl_mid, hwr, hbnd_wr⟩
  rw [Nat.sub_self, Nat.mul_zero] at hwr hbnd_wr
  -- Step at `M_blk - 1` (`blkWall`): sets `max l_mid (3 * (M_blk - 1) + 3) = 3 * M_blk`!
  have hwall_at : readBlk τ (M_blk - 1) = blkWall := by
    rw [hws (M_blk - 1) (by omega)]
    exact encodeWorkspace_last_wall segs hsegs
  have hbs_w : blkTouchWall false (readBlk τ (M_blk - 1)) = some (true, blkWall, QCSD_HeadDir.left) := by
    simp [blkTouchWall, hwall_at]
  have hone_w := liftBlockStep_one_relaxed blkTouchWall B M_blk l_mid τ false true
    blkWall .left (M_blk - 1) (by omega) hl_mid hB ⟨fun _ => by omega, by simp⟩ hbs_w
  have hw_w : writeBlk τ (M_blk - 1) blkWall = τ := by
    rw [← hwall_at]; exact writeBlk_readBlk_self τ (M_blk - 1)
  have hl_pin : max l_mid (3 * (M_blk - 1) + 3) = 3 * M_blk := by omega
  have hm_w : moveHead (M_blk - 1) .left = M_blk - 2 := by simp [moveHead]; omega
  rw [hw_w, hl_pin, hm_w] at hone_w
  -- Rewind from `M_blk - 2` to `0` using `blkRewind_aux` + `liftBlockStep_iter_aux`:
  have h0_at : readBlk τ 0 = blkHome := (hws 0 (by omega)).trans (encodeWorkspace_getD_zero _)
  have hne_at : ∀ i, 1 ≤ i → i ≤ M_blk - 2 → readBlk τ i ≠ blkHome := by
    intro i hi1 hi2; rw [hws i (by omega)]; exact encodeWorkspace_ne_home _ hi1 (by omega)
  rcases blkRewind_aux blkTouchWall M_blk true
      (by simp [blkTouchWall])
      (fun sym hne => by simp [blkTouchWall, hne])
      (M_blk - 2) (readBlk τ) (by omega) h0_at hne_at
    with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
  rcases liftBlockStep_iter_aux blkTouchWall B M_blk (3 * M_blk) (Nat.le_refl _) hB
      (M_blk - 2) true τ (M_blk - 2) true (readBlk τ) 0 hiter_rw hnone_rw hbnd_rw hdir_rw
    with ⟨τ_fin, hread_fin, hout_fin, k_rw, hk_rw, hiter_fin, hexit_fin, hbnd_fin⟩
  have hτ_eq : τ_fin = τ := by
    funext p
    by_cases hp : p < 3 * M_blk
    · have hblk := congrFun hread_fin (p / 3)
      dsimp only [readBlk] at hblk
      have hmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
      have hdiv : 3 * (p / 3) + p % 3 = p := Nat.div_add_mod p 3
      rcases hmod with hr | hr | hr
      · have hp0 : 3 * (p / 3) = p := by omega
        simpa [hp0] using (Prod.mk.inj hblk).1
      · have hp1 : 3 * (p / 3) + 1 = p := by omega
        simpa [hp1] using (Prod.mk.inj (Prod.mk.inj hblk).2).1
      · have hp2 : 3 * (p / 3) + 2 = p := by omega
        simpa [hp2] using (Prod.mk.inj (Prod.mk.inj hblk).2).2
    · exact hout_fin p (by omega)
  subst hτ_eq
  refine ⟨7 * (M_blk - 1) + 7 + k_rw, by omega, ?_, hexit_fin, ?_⟩
  · rw [stepFnIter_add, stepFnIter_add, hwr, Option.bind_some, hone_w.1, Option.bind_some, hiter_fin]
  · intro m hm q_m l_m τ_m h_m hm_eq
    by_cases hm1 : m ≤ 7 * (M_blk - 1)
    · exact hbnd_wr m hm1 q_m l_m τ_m h_m (by
        rcases stepFnIter_le_some hm1 hwr with ⟨cfg, hsub⟩
        rw [show 7 * (M_blk - 1) + 7 + k_rw = m + (7 * (M_blk - 1) + 7 + k_rw - m) by omega] at hm
        exact hm_eq)
    · by_cases hm2 : m ≤ 7 * (M_blk - 1) + 7
      · have heq : m = 7 * (M_blk - 1) + (m - 7 * (M_blk - 1)) := by omega
        rw [heq, stepFnIter_add, hwr, Option.bind_some] at hm_eq
        exact hone_w.2 _ (by omega) q_m l_m τ_m h_m hm_eq
      · have heq : m = 7 * (M_blk - 1) + 7 + (m - (7 * (M_blk - 1) + 7)) := by omega
        rw [heq, stepFnIter_add, stepFnIter_add, hwr, Option.bind_some, hone_w.1, Option.bind_some] at hm_eq
        exact hbnd_fin _ (by omega) q_m l_m τ_m h_m hm_eq

/-- Grow workspace by 1 block at `blkWall`: replace `blkWall` at `M_cur - 1` with `fillSym`,
write `blkWall` at `M_cur`, and rewind to `0`, updating `len` from `3 * M_cur` to `3 * (M_cur + 1)`. -/
def blkGrowLast (fillSym : BlkSym) : BlkStepFn (Fin 3) :=
  fun ph sym =>
    if ph = 0 then
      if sym = blkWall then some (1, fillSym, QCSD_HeadDir.right)
      else some (0, sym, QCSD_HeadDir.right)
    else if ph = 1 then
      some (2, blkWall, QCSD_HeadDir.left)
    else
      if sym = blkHome then none
      else some (2, sym, QCSD_HeadDir.left)

theorem encodeSegmentsAux_push_empty :
    ∀ (segs : List (List Bool)), segs ≠ [] →
      encodeSegmentsAux (segs ++ [[]]) =
        (encodeSegmentsAux segs).take ((encodeSegmentsAux segs).length - 1) ++ [blkSep, blkWall]
  | [], h => absurd rfl h
  | [lastSeg], _ => by
      simp [encodeSegmentsAux]
  | s0 :: s1 :: rest, _ => by
      have ih := encodeSegmentsAux_push_empty (s1 :: rest) (by simp)
      have hpos : 1 ≤ (encodeSegmentsAux (s1 :: rest)).length :=
        encodeSegmentsAux_len_pos (s1 :: rest) (by simp)
      have h1 : encodeSegmentsAux ((s0 :: s1 :: rest) ++ [[]]) =
          (s0.map (blkData false) ++ [blkSep]) ++ encodeSegmentsAux ((s1 :: rest) ++ [[]]) := by
        simp [encodeSegmentsAux]
      have h2 : encodeSegmentsAux (s0 :: s1 :: rest) =
          (s0.map (blkData false) ++ [blkSep]) ++ encodeSegmentsAux (s1 :: rest) := by
        simp [encodeSegmentsAux]
      rw [h1, ih, h2, List.length_append]
      let pfx := s0.map (blkData false) ++ [blkSep]
      have hsub : pfx.length + (encodeSegmentsAux (s1 :: rest)).length - 1 =
          pfx.length + ((encodeSegmentsAux (s1 :: rest)).length - 1) := by omega
      rw [hsub, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left]
      dsimp only [pfx]
      simp only [List.append_assoc]

theorem encodeSegmentsAux_extend_last_bit (b : Bool) :
    ∀ (segs : List (List Bool)), segs ≠ [] →
      encodeSegmentsAux (segs.set (segs.length - 1) (segs.getD (segs.length - 1) [] ++ [b])) =
        (encodeSegmentsAux segs).take ((encodeSegmentsAux segs).length - 1) ++
          [blkData false b, blkWall]
  | [], h => absurd rfl h
  | [lastSeg], _ => by
      simp [encodeSegmentsAux]
  | s0 :: s1 :: rest, _ => by
      have ih := encodeSegmentsAux_extend_last_bit b (s1 :: rest) (by simp)
      have hpos : 1 ≤ (encodeSegmentsAux (s1 :: rest)).length :=
        encodeSegmentsAux_len_pos (s1 :: rest) (by simp)
      have hlen_tail : (s0 :: s1 :: rest).length - 1 = (s1 :: rest).length - 1 + 1 := by simp
      have h1 : encodeSegmentsAux
          ((s0 :: s1 :: rest).set ((s0 :: s1 :: rest).length - 1)
            ((s0 :: s1 :: rest).getD ((s0 :: s1 :: rest).length - 1) [] ++ [b])) =
          (s0.map (blkData false) ++ [blkSep]) ++
            encodeSegmentsAux ((s1 :: rest).set ((s1 :: rest).length - 1)
              ((s1 :: rest).getD ((s1 :: rest).length - 1) [] ++ [b])) := by
        rw [hlen_tail, List.set_cons_succ, List.getD_cons_succ]
        cases hset : (s1 :: rest).set ((s1 :: rest).length - 1) ((s1 :: rest).getD ((s1 :: rest).length - 1) [] ++ [b]) with
        | nil =>
          have hlen := congrArg List.length hset
          simp at hlen
        | cons x xs =>
          simp [encodeSegmentsAux]
      have h2 : encodeSegmentsAux (s0 :: s1 :: rest) =
          (s0.map (blkData false) ++ [blkSep]) ++ encodeSegmentsAux (s1 :: rest) := by
        simp [encodeSegmentsAux]
      rw [h1, ih, h2, List.length_append]
      let pfx := s0.map (blkData false) ++ [blkSep]
      have hsub : pfx.length + (encodeSegmentsAux (s1 :: rest)).length - 1 =
          pfx.length + ((encodeSegmentsAux (s1 :: rest)).length - 1) := by omega
      rw [hsub, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left]
      dsimp only [pfx]
      simp only [List.append_assoc]

theorem encodeWorkspace_push_empty (segs : List (List Bool)) (h : segs ≠ []) :
    encodeWorkspace (segs ++ [[]]) =
      (encodeWorkspace segs).take ((encodeWorkspace segs).length - 1) ++ [blkSep, blkWall] := by
  have hpos := encodeSegmentsAux_len_pos segs h
  simp only [encodeWorkspace, encodeSegmentsAux_push_empty segs h, List.length_cons,
    Nat.add_sub_cancel]
  have hsub : (encodeSegmentsAux segs).length = ((encodeSegmentsAux segs).length - 1) + 1 := by omega
  rw [hsub, List.take_succ_cons]
  simp only [Nat.add_sub_cancel, List.cons_append]

theorem encodeWorkspace_extend_last_bit (b : Bool) (segs : List (List Bool)) (h : segs ≠ []) :
    encodeWorkspace (segs.set (segs.length - 1) (segs.getD (segs.length - 1) [] ++ [b])) =
      (encodeWorkspace segs).take ((encodeWorkspace segs).length - 1) ++
        [blkData false b, blkWall] := by
  have hpos := encodeSegmentsAux_len_pos segs h
  simp only [encodeWorkspace, encodeSegmentsAux_extend_last_bit b segs h, List.length_cons,
    Nat.add_sub_cancel]
  have hsub : (encodeSegmentsAux segs).length = ((encodeSegmentsAux segs).length - 1) + 1 := by omega
  rw [hsub, List.take_succ_cons]
  simp only [Nat.add_sub_cancel, List.cons_append]

theorem blkGrowLast_lift_spec (B : ℕ) (fillSym : BlkSym) (_hfill_nh : fillSym ≠ blkHome)
    (segs segs' : List (List Bool))
    (hws_eq : encodeWorkspace segs' =
      (encodeWorkspace segs).take ((encodeWorkspace segs).length - 1) ++ [fillSym, blkWall])
    (hne' : segs' ≠ [])
    {τ₁ : ℕ → Bool}
    (htw : TapeWS τ₁ (3 * (encodeWorkspace segs).length) B segs)
    (hB' : 3 * ((encodeWorkspace segs).length + 1) ≤ B) :
    let M_cur := (encodeWorkspace segs).length
    ∃ τ₂ : ℕ → Bool,
      TapeWS τ₂ (3 * (encodeWorkspace segs').length) B segs' ∧
      (encodeWorkspace segs').length = M_cur + 1 ∧
      (∀ p, 3 * (M_cur + 1) ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (liftBlockStep (blkGrowLast fillSym)) B (liftBlkEntry 0) (3 * M_cur) τ₁ 0
        (liftBlkExit 2) (3 * (encodeWorkspace segs').length) τ₂ 0 (14 * M_cur + 18) := by
  intro M_cur
  rcases htw with ⟨hsegs, _, _, hws⟩
  have hM_ge2 : 2 ≤ M_cur := encodeWorkspace_len_ge2 segs hsegs
  have hlen_ws' : (encodeWorkspace segs').length = M_cur + 1 := by
    rw [hws_eq, List.length_append, List.length_take]
    simp [M_cur]; omega
  -- 1) Walk right `M_cur - 1` blocks from `0` to `M_cur - 1` (`len = 3 * M_cur` stays fixed):
  have hwalk_right : ∀ d,
      d ≤ M_cur - 1 →
      stepFnIter (liftBlockStep (blkGrowLast fillSym))
        (liftBlkEntry 0, 3 * M_cur, τ₁, 3 * (M_cur - 1 - d)) (7 * d) =
        some (liftBlkEntry 0, 3 * M_cur, τ₁, 3 * (M_cur - 1)) ∧
      (∀ m ≤ 7 * d, ∀ q_m l_m τ_m h_m,
        stepFnIter (liftBlockStep (blkGrowLast fillSym))
          (liftBlkEntry 0, 3 * M_cur, τ₁, 3 * (M_cur - 1 - d)) m =
          some (q_m, l_m, τ_m, h_m) → l_m ≤ B ∧ h_m + 1 ≤ B) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [Nat.sub_zero, Nat.mul_zero]
      exact ⟨rfl, fun m hm _ _ _ _ heq => by
        obtain rfl : m = 0 := by omega
        cases heq; exact ⟨by omega, by omega⟩⟩
    | succ d ih =>
      intro hd
      let j := M_cur - 1 - (d + 1)
      have hj_lt : j < M_cur - 1 := by omega
      have hne_wall : readBlk τ₁ j ≠ blkWall := by
        rw [hws j (by omega)]
        exact encodeWorkspace_lt_wall_ne_wall segs hsegs hj_lt
      have hbs : blkGrowLast fillSym 0 (readBlk τ₁ j) = some (0, readBlk τ₁ j, QCSD_HeadDir.right) := by
        simp [blkGrowLast, hne_wall]
      have hone := liftBlockStep_one_relaxed (blkGrowLast fillSym) B (M_cur + 1) (3 * M_cur) τ₁ 0 0
        (readBlk τ₁ j) .right j (by omega) (by omega) hB' ⟨by simp, fun _ => by omega⟩ hbs
      have hw_self : writeBlk τ₁ j (readBlk τ₁ j) = τ₁ := writeBlk_readBlk_self τ₁ j
      have hmax_eq : max (3 * M_cur) (3 * j + 3) = 3 * M_cur := by omega
      have hnext_j : moveHead j .right = M_cur - 1 - d := by simp [moveHead]; omega
      rw [hw_self, hmax_eq, hnext_j] at hone
      rcases ih (by omega) with ⟨hrest, hbnd_r⟩
      refine ⟨?_, ?_⟩
      · rw [show 7 * (d + 1) = 7 + 7 * d by ring, stepFnIter_add, hone.1, Option.bind_some, hrest]
      · intro m hm q_m l_m τ_m h_m hm_eq
        by_cases hm7 : m ≤ 7
        · rcases stepFnIter_le_some hm7 hone.1 with ⟨cfg, hsub⟩
          rw [hsub] at hm_eq; cases hm_eq
          exact hone.2 m hm7 q_m l_m τ_m h_m hsub
        · have heq : m = 7 + (m - 7) := by omega
          rw [heq, stepFnIter_add, hone.1, Option.bind_some] at hm_eq
          exact hbnd_r (m - 7) (by omega) q_m l_m τ_m h_m hm_eq
  rcases hwalk_right (M_cur - 1) (Nat.le_refl _) with ⟨hwr, hbnd_wr⟩
  rw [Nat.sub_self, Nat.mul_zero] at hwr hbnd_wr
  -- 2) At `M_cur - 1` (`blkWall`): writes `fillSym` and moves right to `M_cur`:
  have hwall_at : readBlk τ₁ (M_cur - 1) = blkWall := by
    rw [hws (M_cur - 1) (by omega)]
    exact encodeWorkspace_last_wall segs hsegs
  have hbs_1 : blkGrowLast fillSym 0 (readBlk τ₁ (M_cur - 1)) = some (1, fillSym, QCSD_HeadDir.right) := by
    simp [blkGrowLast, hwall_at]
  have hone_1 := liftBlockStep_one_relaxed (blkGrowLast fillSym) B (M_cur + 1) (3 * M_cur) τ₁ 0 1
    fillSym .right (M_cur - 1) (by omega) (by omega) hB' ⟨by simp, fun _ => by omega⟩ hbs_1
  have hm1_l : max (3 * M_cur) (3 * (M_cur - 1) + 3) = 3 * M_cur := by omega
  have hm1_h : moveHead (M_cur - 1) .right = M_cur := by simp [moveHead]; omega
  rw [hm1_l, hm1_h] at hone_1
  let τ_a := writeBlk τ₁ (M_cur - 1) fillSym
  -- 3) At `M_cur` (`ph = 1`): writes `blkWall` and moves left to `M_cur - 1`, setting `len = 3 * (M_cur + 1)`!
  have hbs_2 : blkGrowLast fillSym 1 (readBlk τ_a M_cur) = some (2, blkWall, QCSD_HeadDir.left) := rfl
  have hone_2 := liftBlockStep_one_relaxed (blkGrowLast fillSym) B (M_cur + 1) (3 * M_cur) τ_a 1 2
    blkWall .left M_cur (by omega) (by omega) hB' ⟨fun _ => by omega, by simp⟩ hbs_2
  have hm2_l : max (3 * M_cur) (3 * M_cur + 3) = 3 * (M_cur + 1) := by omega
  have hm2_h : moveHead M_cur .left = M_cur - 1 := by simp [moveHead]
  rw [hm2_l, hm2_h] at hone_2
  let τ_b := writeBlk τ_a M_cur blkWall
  -- Verify `MatchesWS (readBlk τ_b) segs'`:
  have hws' : MatchesWS (readBlk τ_b) segs' := by
    intro j hj
    rw [hlen_ws'] at hj
    dsimp only [τ_b, τ_a]
    rw [readBlk_writeBlk, readBlk_writeBlk, hws_eq]
    by_cases hjM : j = M_cur
    · subst hjM
      simp only [↓reduceIte]
      have htl : ((encodeWorkspace segs).take ((encodeWorkspace segs).length - 1)).length =
          (encodeWorkspace segs).length - 1 := by
        rw [List.length_take]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [htl]; dsimp only [M_cur]; omega)]
      have hsub1 : M_cur - ((encodeWorkspace segs).take ((encodeWorkspace segs).length - 1)).length = 1 := by
        rw [htl]; dsimp only [M_cur]; omega
      rw [hsub1]; rfl
    · simp only [hjM, ↓reduceIte]
      by_cases hjM1 : j = M_cur - 1
      · subst hjM1
        simp only [↓reduceIte]
        have htl : ((encodeWorkspace segs).take ((encodeWorkspace segs).length - 1)).length =
            (encodeWorkspace segs).length - 1 := by
          rw [List.length_take]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [htl])]
        have hsub0 : M_cur - 1 - ((encodeWorkspace segs).take ((encodeWorkspace segs).length - 1)).length = 0 := by
          rw [htl]; dsimp only [M_cur]; omega
        rw [hsub0]; rfl
      · simp only [hjM1, ↓reduceIte]
        have hj_lt : j < (encodeWorkspace segs).length - 1 := by dsimp only [M_cur] at *; omega
        rw [hws j (by dsimp only [M_cur] at *; omega)]
        have htl : j < ((encodeWorkspace segs).take ((encodeWorkspace segs).length - 1)).length := by
          rw [List.length_take]; omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left htl, List.getElem?_take_of_lt hj_lt]
  -- 4) Rewind from `M_cur - 1` to `0` at `len = 3 * (M_cur + 1)`:
  have h0_at : readBlk τ_b 0 = blkHome := (hws' 0 (by omega)).trans (encodeWorkspace_getD_zero _)
  have hne_at : ∀ i, 1 ≤ i → i ≤ M_cur - 1 → readBlk τ_b i ≠ blkHome := by
    intro i hi1 hi2
    rw [hws' i (by omega)]
    exact encodeWorkspace_ne_home segs' hi1 (by omega)
  rcases blkRewind_aux (blkGrowLast fillSym) (M_cur + 1) 2
      (by simp [blkGrowLast])
      (fun sym hne => by simp [blkGrowLast, hne])
      (M_cur - 1) (readBlk τ_b) (by omega) h0_at hne_at
    with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
  rcases liftBlockStep_iter_aux (blkGrowLast fillSym) B (M_cur + 1) (3 * (M_cur + 1)) (Nat.le_refl _) hB'
      (M_cur - 1) 2 τ_b (M_cur - 1) 2 (readBlk τ_b) 0 hiter_rw hnone_rw hbnd_rw hdir_rw
    with ⟨τ₂, hread₂, hout₂, k_rw, hk_rw, hiter_fin, hexit_fin, hbnd_fin⟩
  rw [← hread₂] at hws'
  rw [hlen_ws']
  refine ⟨τ₂, ⟨hne', by rw [hlen_ws'], hB', hws'⟩, rfl, ?_,
    7 * (M_cur - 1) + 7 + 7 + k_rw, by omega, ?_, hexit_fin, ?_⟩
  · intro p hp
    rw [hout₂ p hp]
    dsimp only [τ_b, τ_a]
    rw [writeBlk_outside _ M_cur p blkWall (Or.inr (by omega)),
        writeBlk_outside _ (M_cur - 1) p fillSym (Or.inr (by omega))]
  · rw [stepFnIter_add, stepFnIter_add, stepFnIter_add, hwr, Option.bind_some,
        hone_1.1, Option.bind_some, hone_2.1, Option.bind_some, hiter_fin]
  · intro m hm q_m l_m τ_m h_m hm_eq
    by_cases hm1 : m ≤ 7 * (M_cur - 1)
    · exact hbnd_wr m hm1 q_m l_m τ_m h_m hm_eq
    · by_cases hm2 : m ≤ 7 * (M_cur - 1) + 7
      · have heq : m = 7 * (M_cur - 1) + (m - 7 * (M_cur - 1)) := by omega
        rw [heq, stepFnIter_add, hwr, Option.bind_some] at hm_eq
        exact hone_1.2 _ (by omega) q_m l_m τ_m h_m hm_eq
      · by_cases hm3 : m ≤ 7 * (M_cur - 1) + 7 + 7
        · have heq : m = 7 * (M_cur - 1) + 7 + (m - (7 * (M_cur - 1) + 7)) := by omega
          rw [heq, stepFnIter_add, stepFnIter_add, hwr, Option.bind_some, hone_1.1, Option.bind_some] at hm_eq
          exact hone_2.2 _ (by omega) q_m l_m τ_m h_m hm_eq
        · have heq : m = 7 * (M_cur - 1) + 7 + 7 + (m - (7 * (M_cur - 1) + 7 + 7)) := by omega
          rw [heq, stepFnIter_add, stepFnIter_add, stepFnIter_add, hwr, Option.bind_some,
              hone_1.1, Option.bind_some, hone_2.1, Option.bind_some] at hm_eq
          exact hbnd_fin _ (by omega) q_m l_m τ_m h_m hm_eq

/-! ### Reusable Constant-Count Repetition Combinators (`repeatAt` for `StepExecB`, `repeat0` for `StepExec`) -/

abbrev RepeatAtQ (N : ℕ) (Q : Type) : Type := Bool × (Fin (N + 1) × (Unit ⊕ Q))

def repeatAtBody (N : ℕ) {Q : Type} (body : StepFn Q) : StepFn (Fin (N + 1) × (Unit ⊕ Q)) :=
  familyStep (fun (_ : Fin (N + 1)) => sumStep (nopStep Unit) body)

def repeatAtNext (N : ℕ) {Q : Type} (q_entry : Q) :
    Fin (N + 1) × (Unit ⊕ Q) → Option (Fin (N + 1) × (Unit ⊕ Q))
  | (rem, Sum.inr _) =>
      if h : 1 < rem.val then some (⟨rem.val - 1, by omega⟩, Sum.inr q_entry)
      else some (⟨0, Nat.zero_lt_succ N⟩, Sum.inl ())
  | (_, Sum.inl _) => none

def repeatAt (N : ℕ) {Q : Type} (body : StepFn Q) (q_entry : Q) : StepFn (RepeatAtQ N Q) :=
  loopAt (repeatAtBody N body) (repeatAtNext N q_entry)

def repeatAtEntry (N : ℕ) {Q : Type} (q_entry : Q) : RepeatAtQ N Q :=
  (true, (⟨N, Nat.lt_succ_self N⟩, if N = 0 then Sum.inl () else Sum.inr q_entry))

def repeatAtExit (N : ℕ) {Q : Type} : RepeatAtQ N Q :=
  (true, (⟨0, Nat.zero_lt_succ N⟩, Sum.inl ()))

theorem repeatAt_spec (N : ℕ) {Q : Type} (body : StepFn Q) (q_entry : Q) (B L_bnd T_step : ℕ)
    (hLB : L_bnd ≤ B)
    (Inv : ℕ → (ℕ → Bool) → ℕ → Prop)
    (hstep : ∀ i < N, ∀ τ h, Inv i τ h →
      ∃ q_end τ' h', Inv (i + 1) τ' h' ∧ h' + 2 ≤ L_bnd ∧
        StepExecB body B L_bnd q_entry τ h q_end τ' h' T_step)
    {τ₀ : ℕ → Bool} {h₀ : ℕ} (hinv₀ : Inv 0 τ₀ h₀) (hh₀ : h₀ + 1 ≤ L_bnd) :
    ∃ τ_end h_end,
      Inv N τ_end h_end ∧
      StepExecB (repeatAt N body q_entry) B L_bnd
        (repeatAtEntry N q_entry) τ₀ h₀ (repeatAtExit N) τ_end h_end (N * (T_step + 2)) := by
  have haux : ∀ rem done, (_hdone : done + rem = N) → ∀ τ h, Inv done τ h → h + 1 ≤ L_bnd →
      ∃ τ_end h_end,
        Inv N τ_end h_end ∧
        StepExecB (repeatAt N body q_entry) B L_bnd
          (true, (⟨rem, by omega⟩, if rem = 0 then Sum.inl () else Sum.inr q_entry)) τ h
          (repeatAtExit N) τ_end h_end (rem * (T_step + 2)) := by
    intro rem
    induction rem with
    | zero =>
      intro done hdone τ h hinv hh
      have hdeq : done = N := by omega
      subst done
      simp only [↓reduceIte]
      have he_nop : StepExecB (nopStep Unit) B L_bnd () τ h () τ h 0 :=
        StepExecB.done hLB hh (fun _ => rfl)
      have he_inl := StepExecB.inl (nopStep Unit) body he_nop
      have he_fam := StepExecB.family (fun (_ : Fin (N + 1)) => sumStep (nopStep Unit) body)
        ⟨0, Nat.zero_lt_succ N⟩ he_inl
      simp only [Nat.zero_mul]
      exact ⟨τ, h, hinv, StepExecB.loopAt_done (repeatAtNext N q_entry) he_fam rfl⟩
    | succ rem ih =>
      intro done hdone τ h hinv _
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      rcases hstep done (by omega) τ h hinv with ⟨q_end, τ', h', hinv', hh', he_b⟩
      have he_inr := StepExecB.inr (nopStep Unit) body he_b
      have he_fam := StepExecB.family (fun (_ : Fin (N + 1)) => sumStep (nopStep Unit) body)
        ⟨rem + 1, by omega⟩ he_inr
      rcases ih (done + 1) (by omega) τ' h' hinv' (by omega) with ⟨τ_end, h_end, hinv_end, he_rest⟩
      have hnext_eq : repeatAtNext N q_entry (⟨rem + 1, by omega⟩, Sum.inr q_end) =
          some (⟨rem, by omega⟩, if rem = 0 then Sum.inl () else Sum.inr q_entry) := by
        cases rem with
        | zero => simp [repeatAtNext]
        | succ r' => simp [repeatAtNext]
      have hcomb := StepExecB.loopAt_step (repeatAtNext N q_entry) hh' he_fam hnext_eq he_rest
      refine ⟨τ_end, h_end, hinv_end, hcomb.weaken ((rem + 1) * (T_step + 2)) ?_⟩
      have : (rem + 1) * (T_step + 2) = (T_step + 2) + rem * (T_step + 2) := by ring
      omega
  simpa [repeatAtEntry] using haux N 0 (Nat.zero_add N) τ₀ h₀ hinv₀ hh₀

abbrev Repeat0Q (N : ℕ) (Q : Type) : Type := Fin (N + 1) × (Unit ⊕ Q)

def repeat0Body (N : ℕ) {Q : Type} (body : StepFn Q) : StepFn (Repeat0Q N Q) :=
  familyStep (fun (_ : Fin (N + 1)) => sumStep (nopStep Unit) body)

def repeat0 (N : ℕ) {Q : Type} (body : StepFn Q) (q_entry : Q) : StepFn (Repeat0Q N Q) :=
  loop0 (repeat0Body N body) (repeatAtNext N q_entry)

def repeat0Entry (N : ℕ) {Q : Type} (q_entry : Q) : Repeat0Q N Q :=
  (⟨N, Nat.lt_succ_self N⟩, if N = 0 then Sum.inl () else Sum.inr q_entry)

def repeat0Exit (N : ℕ) {Q : Type} : Repeat0Q N Q :=
  (⟨0, Nat.zero_lt_succ N⟩, Sum.inl ())

theorem repeat0_spec (N : ℕ) {Q : Type} (body : StepFn Q) (q_entry : Q) (B T_step : ℕ)
    (Inv : ℕ → ℕ → (ℕ → Bool) → Prop)
    (hstep : ∀ i < N, ∀ len τ, Inv i len τ →
      ∃ q_end len' τ', Inv (i + 1) len' τ' ∧ 1 ≤ len' ∧
        StepExec body B q_entry len τ 0 q_end len' τ' 0 T_step)
    (hbnd_len : ∀ len τ, Inv N len τ → len ≤ B ∧ 1 ≤ B)
    {len₀ : ℕ} {τ₀ : ℕ → Bool} (hinv₀ : Inv 0 len₀ τ₀) :
    ∃ len_end τ_end,
      Inv N len_end τ_end ∧
      StepExec (repeat0 N body q_entry) B
        (repeat0Entry N q_entry) len₀ τ₀ 0 (repeat0Exit N) len_end τ_end 0 (N * (T_step + 2)) := by
  have haux : ∀ rem done, (_hdone : done + rem = N) → ∀ len τ, Inv done len τ →
      ∃ len_end τ_end,
        Inv N len_end τ_end ∧
        StepExec (repeat0 N body q_entry) B
          (⟨rem, by omega⟩, if rem = 0 then Sum.inl () else Sum.inr q_entry) len τ 0
          (repeat0Exit N) len_end τ_end 0 (rem * (T_step + 2)) := by
    intro rem
    induction rem with
    | zero =>
      intro done hdone len τ hinv
      have hdeq : done = N := by omega
      subst done
      simp only [↓reduceIte]
      rcases hbnd_len len τ hinv with ⟨hlen_B, h1_B⟩
      have he_nop := nopStep_spec () len τ 0 hlen_B h1_B
      have he_inl := sumStep_inl_spec (nopStep Unit) body he_nop
      have he_fam := familyStep_spec (fun (_ : Fin (N + 1)) => sumStep (nopStep Unit) body)
        ⟨0, Nat.zero_lt_succ N⟩ he_inl
      simp only [Nat.zero_mul]
      exact ⟨len, τ, hinv, loop0_done (next := repeatAtNext N q_entry) he_fam rfl⟩
    | succ rem ih =>
      intro done hdone len τ hinv
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      rcases hstep done (by omega) len τ hinv with ⟨q_end, len', τ', hinv', hlen'_pos, he_b⟩
      have he_inr := sumStep_inr_spec (nopStep Unit) body he_b
      have he_fam := familyStep_spec (fun (_ : Fin (N + 1)) => sumStep (nopStep Unit) body)
        ⟨rem + 1, by omega⟩ he_inr
      rcases ih (done + 1) (by omega) len' τ' hinv' with ⟨len_end, τ_end, hinv_end, he_rest⟩
      have hnext_eq : repeatAtNext N q_entry (⟨rem + 1, by omega⟩, Sum.inr q_end) =
          some (⟨rem, by omega⟩, if rem = 0 then Sum.inl () else Sum.inr q_entry) := by
        cases rem with
        | zero => simp [repeatAtNext]
        | succ r' => simp [repeatAtNext]
      have hcomb := loop0_step (next := repeatAtNext N q_entry) hlen'_pos he_fam hnext_eq he_rest
      refine ⟨len_end, τ_end, hinv_end, hcomb.weaken ((rem + 1) * (T_step + 2)) ?_⟩
      have : (rem + 1) * (T_step + 2) = (T_step + 2) + rem * (T_step + 2) := by ring
      omega
  simpa [repeat0Entry] using haux N 0 (Nat.zero_add N) len₀ τ₀ hinv₀

/-! ### Phase 1.1: Raw Binary Sliding Window (`rawSlideToEnd`) & Expansion to `[S_raw]` -/

def RawWin (pos w k : ℕ) (leftBits : List Bool) (τ : ℕ → Bool) : Prop :=
  leftBits.length = pos ∧
  k ≤ w ∧
  (∀ p < pos, τ p = leftBits.getD p false) ∧
  τ pos = false ∧ τ (pos + 1) = false ∧
  (∀ i < w, τ (pos + 2 + 2 * i) = true ∧ τ (pos + 2 + 2 * i + 1) = decide (i < k)) ∧
  τ (pos + 2 * w + 2) = false

def rawInitLead : StepFn (Fin 3) :=
  fun st _ =>
    if st = 0 then some (1, false, QCSD_HeadDir.right)
    else if st = 1 then some (2, false, QCSD_HeadDir.right)
    else none

def rawInitPair : StepFn (Fin 5 × Bool) :=
  fun (ph, _r) b =>
    if ph = 0 then
      if b then some ((1, false), true, QCSD_HeadDir.right)
      else some ((4, false), false, QCSD_HeadDir.right)
    else if ph = 1 then
      if b then some ((3, false), true, QCSD_HeadDir.right)
      else some ((2, true), false, QCSD_HeadDir.left)
    else if ph = 2 then
      some ((4, true), false, QCSD_HeadDir.right)
    else none

def rawInitPairNext : Fin 5 × Bool → Option (Fin 5 × Bool)
  | (3, _) => some (0, false)
  | _ => none

abbrev RawInitWinQ : Type := Fin 3 ⊕ (Bool × (Bool × (Fin 5 × Bool)))

def rawInitWin : StepFn RawInitWinQ :=
  seqAt rawInitLead (loopAt rawInitPair rawInitPairNext) (fun _ => (true, (0, false)))

theorem rawInitWin_spec (B L_bnd n : ℕ) (rest : List Bool) {τ₀ : ℕ → Bool}
    (hLB : L_bnd ≤ B) (hn : 2 ≤ n) (hL : n + 4 ≤ L_bnd)
    (hτ₀ : ∀ p, τ₀ p = QCSD_tapeRead (QCSD_natToUnary n ++ rest) p) :
    let w := (n - 2) / 2
    let r := decide ((n - 2) % 2 = 1)
    let midRest := (if r then [false] else []) ++ rest
    ∃ τ₁ : ℕ → Bool,
      RawWin 0 w w [] τ₁ ∧
      (∀ p, 2 * w + 3 ≤ p → τ₁ p = midRest.getD (p - (2 * w + 3)) false) ∧
      StepExecB rawInitWin B L_bnd (Sum.inl 0) τ₀ 0
        (Sum.inr (true, (true, (4, r)))) τ₁ (2 * w + 3) (4 * n + 10) := by
  intro w r midRest
  have hnw : n = 2 * w + 2 + (if r then 1 else 0) := by
    dsimp only [w, r]
    split_ifs with hr <;> simp only [decide_eq_true_eq] at hr <;> omega
  have hτ_lt : ∀ p < n, τ₀ p = true := by
    intro p hp
    rw [hτ₀ p, QCSD_tapeRead, QCSD_natToUnary, List.append_assoc,
        getD_append_left _ _ _ (by simp; omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp [hp]
  have hτ_n : τ₀ n = false := by
    rw [hτ₀ n, QCSD_tapeRead, QCSD_natToUnary, List.append_assoc,
        getD_append_right _ _ _ (by simp)]
    simp
  have hτ_rest : ∀ p, n + 1 ≤ p → τ₀ p = rest.getD (p - (n + 1)) false := by
    intro p hp
    rw [hτ₀ p, QCSD_tapeRead, QCSD_natToUnary,
        getD_append_right _ _ _ (by simp; omega)]
    simp [List.length_append, List.length_replicate]
  -- Lead: write false at 0, 1; head 0 -> 2
  let τa := Function.update (Function.update τ₀ 0 false) 1 false
  have he_lead : StepExecB rawInitLead B L_bnd 0 τ₀ 0 2 τa 2 2 := by
    refine StepExecB.step 1 false .right (Function.update τ₀ 0 false) 1 rfl (by omega) rfl rfl ?_
    refine StepExecB.step 2 false .right τa 2 rfl (by omega) rfl rfl ?_
    exact StepExecB.done hLB (by omega) (fun _ => rfl)
  have hτa_ge2 : ∀ p, 2 ≤ p → τa p = τ₀ p := by
    intro p hp; dsimp only [τa]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  -- Loop scanning remaining `rem` pairs from `2 + 2 * (w - rem)` to `2 + 2 * w`:
  have hloop : ∀ rem, rem ≤ w →
      ∃ τ₁ : ℕ → Bool,
        RawWin 0 w w [] τ₁ ∧
        (∀ p, 2 * w + 3 ≤ p → τ₁ p = midRest.getD (p - (2 * w + 3)) false) ∧
        StepExecB (loopAt rawInitPair rawInitPairNext) B L_bnd
          (true, (0, false)) τa (2 + 2 * (w - rem))
          (true, (4, r)) τ₁ (2 * w + 3) (4 * rem + 4) := by
    intro rem
    induction rem with
    | zero =>
      intro _
      simp only [Nat.sub_zero, Nat.mul_zero, Nat.zero_add]
      cases hr : r with
      | false =>
        have hne : n = 2 + 2 * w := by rw [hr] at hnw; simp at hnw; omega
        have h0 : τa (2 + 2 * w) = false := by rw [hτa_ge2 _ (by omega), ← hne, hτ_n]
        have he1 : StepExecB rawInitPair B L_bnd (0, false) τa (2 + 2 * w) (4, false) τa (2 * w + 3) 1 := by
          refine StepExecB.step (4, false) false .right τa (2 * w + 3)
            (by simp [rawInitPair, h0]) (by omega) (update_eq_self_of_eq h0) (by simp [moveHead]; omega) ?_
          exact StepExecB.done hLB (by omega) (fun _ => rfl)
        refine ⟨τa, ?_, ?_, (StepExecB.loopAt_done rawInitPairNext he1 rfl).weaken 4 (by omega)⟩
        · refine ⟨rfl, Nat.le_refl w, fun p hp => by omega, ?_, ?_, ?_, by rw [show 0 + 2 * w + 2 = 2 + 2 * w by omega]; exact h0⟩
          · dsimp only [τa]; rw [Function.update_of_ne (by omega), Function.update_self]
          · simp [τa]
          · intro i hi
            rw [hτa_ge2 _ (by omega), hτa_ge2 _ (by omega),
                hτ_lt _ (by omega), hτ_lt _ (by omega)]
            simp [hi]
        · intro p hp
          rw [hτa_ge2 p (by omega), hτ_rest p (by omega)]
          simp [midRest, hr, show p - (n + 1) = p - (2 * w + 3) by omega]
      | true =>
        have hne : n = 2 + 2 * w + 1 := by rw [hr] at hnw; simp at hnw; omega
        have h0 : τa (2 + 2 * w) = true := by rw [hτa_ge2 _ (by omega), hτ_lt _ (by omega)]
        have h1 : τa (2 + 2 * w + 1) = false := by rw [hτa_ge2 _ (by omega), ← hne, hτ_n]
        let τ₁ := Function.update τa (2 + 2 * w) false
        have he3 : StepExecB rawInitPair B L_bnd (0, false) τa (2 + 2 * w) (4, true) τ₁ (2 * w + 3) 3 := by
          refine StepExecB.step (1, false) true .right τa (2 + 2 * w + 1)
            (by simp [rawInitPair, h0]) (by omega) (update_eq_self_of_eq h0) rfl ?_
          refine StepExecB.step (2, true) false .left τa (2 + 2 * w)
            (by simp [rawInitPair, h1]) (by omega) (update_eq_self_of_eq h1) (by simp [moveHead]) ?_
          refine StepExecB.step (4, true) false .right τ₁ (2 * w + 3)
            rfl (by omega) rfl (by simp [moveHead]; omega) ?_
          exact StepExecB.done hLB (by omega) (fun _ => rfl)
        refine ⟨τ₁, ?_, ?_, (StepExecB.loopAt_done rawInitPairNext he3 rfl).weaken 4 (by omega)⟩
        · refine ⟨rfl, Nat.le_refl w, fun p hp => by omega, ?_, ?_, ?_, ?_⟩
          · dsimp only [τ₁, τa]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
          · dsimp only [τ₁, τa]; rw [Function.update_of_ne (by omega), Function.update_self]
          · intro i hi
            dsimp only [τ₁]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                hτa_ge2 _ (by omega), hτa_ge2 _ (by omega),
                hτ_lt _ (by omega), hτ_lt _ (by omega)]
            simp [hi]
          · dsimp only [τ₁]; rw [show 0 + 2 * w + 2 = 2 + 2 * w by omega, Function.update_self]
        · intro p hp
          dsimp only [τ₁]
          rw [Function.update_of_ne (by omega), hτa_ge2 p (by omega)]
          by_cases hp0 : p = 2 * w + 3
          · subst hp0
            rw [show 2 * w + 3 = n by omega, hτ_n]
            simp [midRest, hr]
          · rw [hτ_rest p (by omega)]
            have hsub : p - (2 * w + 3) = (p - (n + 1)) + 1 := by omega
            simp [midRest, hr, hsub]
    | succ rem ih =>
      intro hrem_le
      let j := w - (rem + 1)
      have h0 : τa (2 + 2 * j) = true := by rw [hτa_ge2 _ (by omega), hτ_lt _ (by omega)]
      have h1 : τa (2 + 2 * j + 1) = true := by rw [hτa_ge2 _ (by omega), hτ_lt _ (by omega)]
      have he2 : StepExecB rawInitPair B L_bnd (0, false) τa (2 + 2 * j) (3, false) τa (2 + 2 * (w - rem)) 2 := by
        refine StepExecB.step (1, false) true .right τa (2 + 2 * j + 1)
          (by simp [rawInitPair, h0]) (by omega) (update_eq_self_of_eq h0) rfl ?_
        refine StepExecB.step (3, false) true .right τa (2 + 2 * (w - rem))
          (by simp [rawInitPair, h1]) (by omega) (update_eq_self_of_eq h1) (by simp [moveHead, j]; omega) ?_
        exact StepExecB.done hLB (by omega) (fun _ => rfl)
      rcases ih (by omega) with ⟨τ₁, hwin, hrest_eq, he_rest⟩
      refine ⟨τ₁, hwin, hrest_eq,
        (StepExecB.loopAt_step rawInitPairNext (by omega) he2 rfl he_rest).weaken (4 * (rem + 1) + 4) (by omega)⟩
  rcases hloop w (Nat.le_refl w) with ⟨τ₁, hwin, hrest_eq, he_lp⟩
  simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at he_lp
  have he_tot := (StepExecB.seqAt (s₂ := loopAt rawInitPair rawInitPairNext)
    (f := fun _ => (true, (0, false))) (by omega) he_lead he_lp).weaken (4 * n + 10) (by omega)
  exact ⟨τ₁, hwin, hrest_eq, he_tot⟩

/-! #### `rawSlideRight1`: slide window 1 cell right, depositing `τ (pos + 2*w + 3)` at `pos` -/

def rawSlideReadB : StepFn (Fin 3 × Bool) :=
  fun (ph, bp) b =>
    if ph = 0 then some ((1, b), false, QCSD_HeadDir.left)
    else if ph = 1 then some ((2, bp), b, QCSD_HeadDir.left)
    else none

def rawSlidePairL (bp : Bool) : StepFn (Fin 10 × Bool × Bool) :=
  fun (ph, x, _done) b =>
    if ph = 0 then some ((1, b, false), b, QCSD_HeadDir.left)
    else if ph = 1 then
      if b then some ((2, x, false), true, QCSD_HeadDir.right)
      else some ((7, false, true), bp, QCSD_HeadDir.right)
    else if ph = 2 then some ((3, x, false), true, QCSD_HeadDir.right)
    else if ph = 3 then some ((4, false, false), x, QCSD_HeadDir.left)
    else if ph = 4 then some ((5, false, false), b, QCSD_HeadDir.left)
    else if ph = 5 then some ((6, false, false), b, QCSD_HeadDir.left)
    else if ph = 7 then some ((8, false, true), false, QCSD_HeadDir.right)
    else if ph = 8 then some ((9, false, true), false, QCSD_HeadDir.right)
    else none

def rawSlidePairLNext : Fin 10 × Bool × Bool → Option (Fin 10 × Bool × Bool)
  | (_, _, false) => some (0, false, false)
  | _ => none

def rawWalkPairR (setMark : Bool) : StepFn (Fin 3 × Bool) :=
  fun (ph, _done) b =>
    if ph = 0 then
      if b then some ((1, false), true, QCSD_HeadDir.right)
      else some ((2, true), false, QCSD_HeadDir.right)
    else if ph = 1 then
      some ((2, false), if setMark then true else b, QCSD_HeadDir.right)
    else none

def rawWalkPairRNext : Fin 3 × Bool → Option (Fin 3 × Bool)
  | (_, false) => some (0, false)
  | _ => none

abbrev RawSlideRight1Q : Type :=
  (Fin 3 × Bool) ⊕
  (Bool × ((Bool × (Bool × (Fin 10 × Bool × Bool))) ⊕ (Bool × (Bool × (Fin 3 × Bool)))))

def rawSlideRight1 : StepFn RawSlideRight1Q :=
  seqAt rawSlideReadB
    (seqAt (familyStep (fun bp => loopAt (rawSlidePairL bp) rawSlidePairLNext))
      (loopAt (rawWalkPairR false) rawWalkPairRNext)
      (fun _ => (true, (0, false))))
    (fun (_, bp) => Sum.inl (bp, (true, (0, false, false))))

theorem rawWalkPairR_spec (setMark : Bool) (B L_bnd pos w k : ℕ) (leftBits : List Bool)
    (hLB : L_bnd ≤ B) (hB : pos + 2 * w + 4 ≤ L_bnd) :
    ∀ rem {τ : ℕ → Bool},
      rem ≤ w →
      RawWin pos w (if setMark then w - rem else k) leftBits τ →
      (∀ i, w - rem ≤ i → i < w → setMark = true → τ (pos + 2 + 2 * i + 1) = false) →
      ∃ τ_end : ℕ → Bool,
        RawWin pos w (if setMark then w else k) leftBits τ_end ∧
        (∀ p, p < pos + 2 ∨ pos + 2 * w + 2 ≤ p → τ_end p = τ p) ∧
        StepExecB (loopAt (rawWalkPairR setMark) rawWalkPairRNext) B L_bnd
          (true, (0, false)) τ (pos + 2 + 2 * (w - rem))
          (true, (2, true)) τ_end (pos + 2 * w + 3) (4 * rem + 2) := by
  intro rem
  induction rem with
  | zero =>
    intro τ _ hwin _
    simp only [Nat.sub_zero, Nat.mul_zero, Nat.zero_add] at hwin ⊢
    have hsent : τ (pos + 2 + 2 * w) = false := by
      have := hwin.2.2.2.2.2.2
      rwa [show pos + 2 + 2 * w = pos + 2 * w + 2 by omega]
    have he1 : StepExecB (rawWalkPairR setMark) B L_bnd (0, false) τ (pos + 2 + 2 * w)
        (2, true) τ (pos + 2 * w + 3) 1 := by
      refine StepExecB.step (2, true) false .right τ (pos + 2 * w + 3)
        (by simp [rawWalkPairR, hsent]) (by omega) (update_eq_self_of_eq hsent) (by simp [moveHead]; omega) ?_
      exact StepExecB.done hLB (by omega) (fun _ => rfl)
    exact ⟨τ, hwin, fun _ _ => rfl, (StepExecB.loopAt_done rawWalkPairRNext he1 rfl).weaken 2 (by omega)⟩
  | succ rem ih =>
    intro τ hrem_le hwin hmarks
    let j := w - (rem + 1)
    have hj_lt : j < w := by omega
    have h0 : τ (pos + 2 + 2 * j) = true := (hwin.2.2.2.2.2.1 j hj_lt).1
    let v1 := if setMark then true else τ (pos + 2 + 2 * j + 1)
    let τ' := Function.update τ (pos + 2 + 2 * j + 1) v1
    have he2 : StepExecB (rawWalkPairR setMark) B L_bnd (0, false) τ (pos + 2 + 2 * j)
        (2, false) τ' (pos + 2 + 2 * (w - rem)) 2 := by
      refine StepExecB.step (1, false) true .right τ (pos + 2 + 2 * j + 1)
        (by simp [rawWalkPairR, h0]) (by omega) (update_eq_self_of_eq h0) rfl ?_
      refine StepExecB.step (2, false) v1 .right τ' (pos + 2 + 2 * (w - rem))
        rfl (by omega) rfl (by simp [moveHead, j]; omega) ?_
      exact StepExecB.done hLB (by omega) (fun _ => rfl)
    have hwin' : RawWin pos w (if setMark then w - rem else k) leftBits τ' := by
      rcases hwin with ⟨hl, hkw, hlt, hp0, hp1, hpairs, hsent⟩
      refine ⟨hl, by cases setMark <;> simp only [↓reduceIte, Bool.false_eq_true] at hkw ⊢ <;> omega, ?_, ?_, ?_, ?_, ?_⟩
      · intro p hp; dsimp only [τ']; rw [Function.update_of_ne (by omega)]; exact hlt p hp
      · dsimp only [τ']; rw [Function.update_of_ne (by omega)]; exact hp0
      · dsimp only [τ']; rw [Function.update_of_ne (by omega)]; exact hp1
      · intro i hi
        dsimp only [τ']
        rw [Function.update_of_ne (by omega)]
        refine ⟨(hpairs i hi).1, ?_⟩
        by_cases hij : i = j
        · subst hij
          rw [Function.update_self]
          cases setMark with
          | false => simpa [v1] using (hpairs j hj_lt).2
          | true => simp [v1, j]; omega
        · rw [Function.update_of_ne (by omega), (hpairs i hi).2]
          cases setMark with
          | false => rfl
          | true =>
            have : (i < w - (rem + 1)) ↔ (i < w - rem) := by omega
            simp [this]
      · dsimp only [τ']; rw [Function.update_of_ne (by omega)]; exact hsent
    rcases ih (τ := τ') (by omega) hwin' (fun i hi1 hi2 hsm => by
        dsimp only [τ']; rw [Function.update_of_ne (by omega)]; exact hmarks i (by omega) hi2 hsm)
      with ⟨τ_end, hwin_end, hout_end, he_rest⟩
    refine ⟨τ_end, hwin_end, ?_,
      (StepExecB.loopAt_step rawWalkPairRNext (by omega) he2 rfl he_rest).weaken (4 * (rem + 1) + 2) (by omega)⟩
    intro p hp
    rw [hout_end p hp]
    dsimp only [τ']; rw [Function.update_of_ne (by omega)]

theorem rawSlideRight1_spec (B L_bnd pos w k : ℕ) (leftBits : List Bool) {τ : ℕ → Bool}
    (hLB : L_bnd ≤ B) (hB : pos + 2 * w + 6 ≤ L_bnd)
    (hwin : RawWin pos w k leftBits τ) :
    let b := τ (pos + 2 * w + 3)
    ∃ q_end, ∃ τ_end : ℕ → Bool,
      RawWin (pos + 1) w k (leftBits ++ [b]) τ_end ∧
      (∀ p, pos + 2 * w + 4 ≤ p → τ_end p = τ p) ∧
      StepExecB rawSlideRight1 B L_bnd (Sum.inl (0, false)) τ (pos + 2 * w + 3)
        q_end τ_end ((pos + 1) + 2 * w + 3) (12 * w + 25) := by
  intro b
  rcases hwin with ⟨hllen, hkw, hlt, hp0, hp1, hpairs, hsent⟩
  let τa := Function.update τ (pos + 2 * w + 3) false
  have he_read : StepExecB rawSlideReadB B L_bnd (0, false) τ (pos + 2 * w + 3)
      (2, b) τa (pos + 2 * w + 1) 2 := by
    refine StepExecB.step (1, b) false .left τa (pos + 2 * w + 2) rfl (by omega) rfl (by simp [moveHead]) ?_
    refine StepExecB.step (2, b) (τa (pos + 2 * w + 2)) .left τa (pos + 2 * w + 1)
      rfl (by omega) (by simp) (by simp [moveHead]) ?_
    exact StepExecB.done hLB (by omega) (fun _ => rfl)
  -- Shift-left loop over `j` from `w` down to `0`:
  have hshift : ∀ j ≤ w, ∀ {τc : ℕ → Bool},
      (∀ p < pos, τc p = leftBits.getD p false) →
      τc pos = false → τc (pos + 1) = false →
      (∀ i < j, τc (pos + 2 + 2 * i) = true ∧ τc (pos + 2 + 2 * i + 1) = decide (i < k)) →
      (∀ i, j ≤ i → i < w → τc (pos + 3 + 2 * i) = true ∧ τc (pos + 3 + 2 * i + 1) = decide (i < k)) →
      τc (pos + 2 * w + 3) = false →
      (∀ p, pos + 2 * w + 4 ≤ p → τc p = τ p) →
      ∃ τm : ℕ → Bool,
        RawWin (pos + 1) w k (leftBits ++ [b]) τm ∧
        (∀ p, pos + 2 * w + 4 ≤ p → τm p = τ p) ∧
        StepExecB (loopAt (rawSlidePairL b) rawSlidePairLNext) B L_bnd
          (true, (0, false, false)) τc (pos + 2 * j + 1)
          (true, (9, false, true)) τm (pos + 3) (8 * j + 5) := by
    intro j
    induction j with
    | zero =>
      intro _ τc hclt hcp0 hcp1 _ hcr hcs hcout
      let u1 := Function.update τc pos b
      let u2 := Function.update u1 (pos + 1) false
      let u3 := Function.update u2 (pos + 2) false
      have he4 : StepExecB (rawSlidePairL b) B L_bnd (0, false, false) τc (pos + 1)
          (9, false, true) u3 (pos + 3) 4 := by
        refine StepExecB.step (1, false, false) false .left τc pos
          (by simp [rawSlidePairL, hcp1]) (by omega) (update_eq_self_of_eq hcp1) (by simp [moveHead]) ?_
        refine StepExecB.step (7, false, true) b .right u1 (pos + 1)
          (by simp [rawSlidePairL, hcp0]) (by omega) rfl rfl ?_
        refine StepExecB.step (8, false, true) false .right u2 (pos + 2) rfl (by omega) rfl rfl ?_
        refine StepExecB.step (9, false, true) false .right u3 (pos + 3) rfl (by omega) rfl rfl ?_
        exact StepExecB.done hLB (by omega) (fun _ => rfl)
      refine ⟨u3, ?_, ?_, (StepExecB.loopAt_done rawSlidePairLNext he4 rfl).weaken 5 (by omega)⟩
      · refine ⟨by simp [hllen], hkw, ?_, ?_, ?_, ?_, ?_⟩
        · intro p hp
          dsimp only [u3, u2, u1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          by_cases hpp : p = pos
          · subst hpp; rw [Function.update_self, getD_append_right _ _ _ (by omega)]; simp [hllen]
          · rw [Function.update_of_ne hpp, getD_append_left _ _ _ (by omega)]; exact hclt p (by omega)
        · dsimp only [u3, u2, u1]; rw [Function.update_of_ne (by omega), Function.update_self]
        · dsimp only [u3, u2, u1]; rw [Function.update_self]
        · intro i hi
          dsimp only [u3, u2, u1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          have h := hcr i (Nat.zero_le i) hi
          simpa [show pos + 1 + 2 + 2 * i = pos + 3 + 2 * i by omega] using h
        · dsimp only [u3, u2, u1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          rwa [show pos + 1 + 2 * w + 2 = pos + 2 * w + 3 by omega]
      · intro p hp
        dsimp only [u3, u2, u1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hcout p hp
    | succ j ih =>
      intro hj_le τc hclt hcp0 hcp1 hcl hcr hcs hcout
      have hpair := hcl j (Nat.lt_succ_self j)
      have h1_v : τc (pos + 2 * (j + 1) + 1) = decide (j < k) := by
        simpa [show pos + 2 * (j + 1) + 1 = pos + 2 + 2 * j + 1 by omega] using hpair.2
      have h0_v : τc (pos + 2 * (j + 1)) = true := by
        simpa [show pos + 2 * (j + 1) = pos + 2 + 2 * j by omega] using hpair.1
      let x := decide (j < k)
      let v1 := Function.update τc (pos + 2 * (j + 1) + 1) true
      let v2 := Function.update v1 (pos + 2 * (j + 1) + 2) x
      have he6 : StepExecB (rawSlidePairL b) B L_bnd (0, false, false) τc (pos + 2 * (j + 1) + 1)
          (6, false, false) v2 (pos + 2 * j + 1) 6 := by
        refine StepExecB.step (1, x, false) x .left τc (pos + 2 * (j + 1))
          (by simp [rawSlidePairL, h1_v, x]) (by omega) (update_eq_self_of_eq h1_v) (by simp [moveHead]) ?_
        refine StepExecB.step (2, x, false) true .right τc (pos + 2 * (j + 1) + 1)
          (by simp [rawSlidePairL, h0_v]) (by omega) (update_eq_self_of_eq h0_v) rfl ?_
        refine StepExecB.step (3, x, false) true .right v1 (pos + 2 * (j + 1) + 2) rfl (by omega) rfl rfl ?_
        refine StepExecB.step (4, false, false) x .left v2 (pos + 2 * (j + 1) + 1) rfl (by omega) rfl (by simp [moveHead]) ?_
        refine StepExecB.step (5, false, false) (v2 (pos + 2 * (j + 1) + 1)) .left v2 (pos + 2 * (j + 1))
          rfl (by omega) (by simp) (by simp [moveHead]) ?_
        refine StepExecB.step (6, false, false) (v2 (pos + 2 * (j + 1))) .left v2 (pos + 2 * j + 1)
          rfl (by omega) (by simp) (by simp [moveHead]; omega) ?_
        exact StepExecB.done hLB (by omega) (fun _ => rfl)
      rcases ih (by omega) (τc := v2)
          (fun p hp => by dsimp only [v2, v1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hclt p hp)
          (by dsimp only [v2, v1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hcp0)
          (by dsimp only [v2, v1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hcp1)
          (fun i hi => by
            dsimp only [v2, v1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hcl i (by omega))
          (fun i hi1 hi2 => by
            dsimp only [v2, v1]
            by_cases hij : i = j
            · subst hij
              rw [show pos + 3 + 2 * i = pos + 2 * (i + 1) + 1 by omega,
                  show pos + 2 * (i + 1) + 1 + 1 = pos + 2 * (i + 1) + 2 by omega,
                  Function.update_of_ne (by omega), Function.update_self, Function.update_self]
              exact ⟨rfl, rfl⟩
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hcr i (by omega) hi2)
          (by dsimp only [v2, v1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hcs)
          (fun p hp => by dsimp only [v2, v1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hcout p hp)
        with ⟨τm, hwin_m, hout_m, he_rest⟩
      refine ⟨τm, hwin_m, hout_m,
        (StepExecB.loopAt_step rawSlidePairLNext (by omega) he6 rfl he_rest).weaken (8 * (j + 1) + 5) (by omega)⟩
  rcases hshift w (Nat.le_refl w) (τc := τa)
      (fun p hp => by dsimp only [τa]; rw [Function.update_of_ne (by omega)]; exact hlt p hp)
      (by dsimp only [τa]; rw [Function.update_of_ne (by omega)]; exact hp0)
      (by dsimp only [τa]; rw [Function.update_of_ne (by omega)]; exact hp1)
      (fun i hi => by
        dsimp only [τa]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hpairs i hi)
      (fun i hi1 hi2 => by omega)
      (by simp [τa])
      (fun p hp => by dsimp only [τa]; rw [Function.update_of_ne (by omega)])
    with ⟨τm, hwin_m, hout_m, he_sh⟩
  have he_sh_fam := StepExecB.family (fun bp => loopAt (rawSlidePairL bp) rawSlidePairLNext) b he_sh
  rcases rawWalkPairR_spec false B L_bnd (pos + 1) w k (leftBits ++ [b]) hLB (by omega) w (Nat.le_refl w)
      (by simpa using hwin_m) (by simp)
    with ⟨τ_end, hwin_end, hout_w, he_wk⟩
  simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at he_wk
  have hpos3 : pos + 1 + 2 = pos + 3 := by omega
  rw [hpos3] at he_wk
  have he_inner := StepExecB.seqAt (s₂ := loopAt (rawWalkPairR false) rawWalkPairRNext)
    (f := fun _ => (true, (0, false))) (by omega) he_sh_fam he_wk
  have he_tot : StepExecB rawSlideRight1 B L_bnd (Sum.inl (0, false)) τ (pos + 2 * w + 3)
      (Sum.inr (true, Sum.inr (true, (true, (2, true))))) τ_end ((pos + 1) + 2 * w + 3)
      (2 + 2 + ((8 * w + 5) + 2 + (4 * w + 2))) := by
    unfold rawSlideRight1
    exact StepExecB.seqAt (by omega) he_read (by simpa using he_inner)
  refine ⟨_, τ_end, by simpa using hwin_end, ?_, he_tot.weaken (12 * w + 25) (by omega)⟩
  intro p hp
  rw [hout_w p (Or.inr (by omega)), hout_m p hp]

/-! #### `rawDecWinMark`: decrement mark counter `k` (or reset `0 -> w` returning `wasZero = true`) -/

def rawStepLeft2 : StepFn (Fin 3) :=
  fun ph b =>
    if ph = 0 then some (1, b, QCSD_HeadDir.left)
    else if ph = 1 then some (2, b, QCSD_HeadDir.left)
    else none

def rawDecPairL : StepFn (Fin 7 × Bool × Bool) :=
  fun (ph, x, _wz) b =>
    if ph = 0 then some ((1, b, false), b, QCSD_HeadDir.left)
    else if ph = 1 then
      if !b then some ((2, false, true), false, QCSD_HeadDir.right)
      else if x then some ((3, false, false), true, QCSD_HeadDir.right)
      else some ((5, false, false), true, QCSD_HeadDir.left)
    else if ph = 2 then some ((6, false, true), b, QCSD_HeadDir.right)
    else if ph = 3 then some ((6, false, false), false, QCSD_HeadDir.right)
    else none

def rawDecPairLNext : Fin 7 × Bool × Bool → Option (Fin 7 × Bool × Bool)
  | (5, _, _) => some (0, false, false)
  | _ => none

abbrev RawDecWinMarkQ : Type :=
  Fin 3 ⊕
  (Bool ×
    ((Bool × (Fin 7 × Bool × Bool)) ⊕
     (Bool × ((Bool × (Fin 3 × Bool)) ⊕ (Bool × (Fin 3 × Bool))))))

def rawDecWinMark : StepFn RawDecWinMarkQ :=
  seqAt rawStepLeft2
    (seqAt (loopAt rawDecPairL rawDecPairLNext)
      (sumStep (loopAt (rawWalkPairR false) rawWalkPairRNext)
               (loopAt (rawWalkPairR true) rawWalkPairRNext))
      (fun (_, _, _, wz) => if wz then Sum.inr (true, (0, false)) else Sum.inl (true, (0, false))))
    (fun _ => Sum.inl (true, (0, false, false)))

def rawDecWinMarkWasZero : RawDecWinMarkQ → Bool
  | Sum.inr (true, Sum.inr (true, Sum.inr _)) => true
  | _ => false

theorem rawDecWinMark_spec (B L_bnd pos w k : ℕ) (leftBits : List Bool) {τ : ℕ → Bool}
    (hLB : L_bnd ≤ B) (hB : pos + 2 * w + 5 ≤ L_bnd)
    (hwin : RawWin pos w k leftBits τ) :
    ∃ q_end, ∃ τ_end : ℕ → Bool,
      rawDecWinMarkWasZero q_end = decide (k = 0) ∧
      RawWin pos w (if k = 0 then w else k - 1) leftBits τ_end ∧
      (∀ p, pos + 2 * w + 3 ≤ p → τ_end p = τ p) ∧
      StepExecB rawDecWinMark B L_bnd (Sum.inl 0) τ (pos + 2 * w + 3)
        q_end τ_end (pos + 2 * w + 3) (9 * w + 15) := by
  have he_l2 : StepExecB rawStepLeft2 B L_bnd 0 τ (pos + 2 * w + 3) 2 τ (pos + 2 * w + 1) 2 := by
    refine StepExecB.step 1 (τ (pos + 2 * w + 3)) .left τ (pos + 2 * w + 2) rfl (by omega) (by simp) (by simp [moveHead]) ?_
    refine StepExecB.step 2 (τ (pos + 2 * w + 2)) .left τ (pos + 2 * w + 1) rfl (by omega) (by simp) (by simp [moveHead]) ?_
    exact StepExecB.done hLB (by omega) (fun _ => rfl)
  -- Walk left from `pos + 2 * j + 1` down to `k` (`j = k` stops!)
  have hscan : ∀ d, d ≤ w - k →
      ∃ τm : ℕ → Bool,
        RawWin pos w (if k = 0 then 0 else k - 1) leftBits τm ∧
        (∀ p, p < pos + 2 ∨ pos + 2 * w + 2 ≤ p → τm p = τ p) ∧
        (∀ i, k ≤ i → i < w → τm (pos + 2 + 2 * i + 1) = false) ∧
        StepExecB (loopAt rawDecPairL rawDecPairLNext) B L_bnd
          (true, (0, false, false)) τ (pos + 2 * (k + d) + 1)
          (true, (6, false, decide (k = 0))) τm (pos + 2 + 2 * k) (4 * d + 4) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add]
      rcases hwin with ⟨hllen, hkw, hlt, hp0, hp1, hpairs, hsent⟩
      cases k with
      | zero =>
        have he3 : StepExecB rawDecPairL B L_bnd (0, false, false) τ (pos + 1)
            (6, false, true) τ (pos + 2) 3 := by
          refine StepExecB.step (1, false, false) false .left τ pos
            (by simp [rawDecPairL, hp1]) (by omega) (update_eq_self_of_eq hp1) (by simp [moveHead]) ?_
          refine StepExecB.step (2, false, true) false .right τ (pos + 1)
            (by simp [rawDecPairL, hp0]) (by omega) (update_eq_self_of_eq hp0) rfl ?_
          refine StepExecB.step (6, false, true) (τ (pos + 1)) .right τ (pos + 2) rfl (by omega) (by simp) rfl ?_
          exact StepExecB.done hLB (by omega) (fun _ => rfl)
        exact ⟨τ, ⟨hllen, hkw, hlt, hp0, hp1, hpairs, hsent⟩, fun _ _ => rfl,
          fun i _ hi => by simpa using (hpairs i hi).2,
          (StepExecB.loopAt_done rawDecPairLNext he3 rfl).weaken 4 (by omega)⟩
      | succ k' =>
        have hk_lt : k' < w := by omega
        have hp_k := hpairs k' hk_lt
        have h1_v : τ (pos + 2 * (k' + 1) + 1) = true := by
          have := hp_k.2
          simp only [Nat.lt_succ_self, decide_true] at this
          rwa [show pos + 2 * (k' + 1) + 1 = pos + 2 + 2 * k' + 1 by omega]
        have h0_v : τ (pos + 2 * (k' + 1)) = true := by
          have := hp_k.1
          rwa [show pos + 2 * (k' + 1) = pos + 2 + 2 * k' by omega]
        let τm := Function.update τ (pos + 2 * (k' + 1) + 1) false
        have he3 : StepExecB rawDecPairL B L_bnd (0, false, false) τ (pos + 2 * (k' + 1) + 1)
            (6, false, false) τm (pos + 2 + 2 * (k' + 1)) 3 := by
          refine StepExecB.step (1, true, false) true .left τ (pos + 2 * (k' + 1))
            (by simp [rawDecPairL, h1_v]) (by omega) (update_eq_self_of_eq h1_v) (by simp [moveHead]) ?_
          refine StepExecB.step (3, false, false) true .right τ (pos + 2 * (k' + 1) + 1)
            (by simp [rawDecPairL, h0_v]) (by omega) (update_eq_self_of_eq h0_v) rfl ?_
          refine StepExecB.step (6, false, false) false .right τm (pos + 2 + 2 * (k' + 1))
            rfl (by omega) rfl (by simp [moveHead]; omega) ?_
          exact StepExecB.done hLB (by omega) (fun _ => rfl)
        refine ⟨τm, ?_, ?_, ?_, (StepExecB.loopAt_done rawDecPairLNext he3 rfl).weaken 4 (by omega)⟩
        · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          refine ⟨hllen, by omega, ?_, ?_, ?_, ?_, ?_⟩
          · intro p hp; dsimp only [τm]; rw [Function.update_of_ne (by omega)]; exact hlt p hp
          · dsimp only [τm]; rw [Function.update_of_ne (by omega)]; exact hp0
          · dsimp only [τm]; rw [Function.update_of_ne (by omega)]; exact hp1
          · intro i hi
            dsimp only [τm]
            rw [Function.update_of_ne (by omega)]
            refine ⟨(hpairs i hi).1, ?_⟩
            by_cases hik : i = k'
            · subst hik
              rw [show pos + 2 + 2 * i + 1 = pos + 2 * (i + 1) + 1 by omega, Function.update_self]
              simp
            · rw [Function.update_of_ne (by omega), (hpairs i hi).2]
              have : (i < k' + 1) ↔ (i < k') := by omega
              simp [this]
          · dsimp only [τm]; rw [Function.update_of_ne (by omega)]; exact hsent
        · intro p hp; dsimp only [τm]; rw [Function.update_of_ne (by omega)]
        · intro i hi1 hi2
          dsimp only [τm]; rw [Function.update_of_ne (by omega), (hpairs i hi2).2]
          have : ¬ (i < k' + 1) := by omega
          simp [this]
    | succ d ih =>
      intro hd_le
      have hj_lt : k + d < w := by omega
      have hpair := hwin.2.2.2.2.2.1 (k + d) hj_lt
      have h1_v : τ (pos + 2 * (k + (d + 1)) + 1) = false := by
        have := hpair.2
        have hnot : ¬ (k + d < k) := by omega
        simp only [hnot, decide_false] at this
        rwa [show pos + 2 * (k + (d + 1)) + 1 = pos + 2 + 2 * (k + d) + 1 by omega]
      have h0_v : τ (pos + 2 * (k + (d + 1))) = true := by
        have := hpair.1
        rwa [show pos + 2 * (k + (d + 1)) = pos + 2 + 2 * (k + d) by omega]
      have he2 : StepExecB rawDecPairL B L_bnd (0, false, false) τ (pos + 2 * (k + (d + 1)) + 1)
          (5, false, false) τ (pos + 2 * (k + d) + 1) 2 := by
        refine StepExecB.step (1, false, false) false .left τ (pos + 2 * (k + (d + 1)))
          (by simp [rawDecPairL, h1_v]) (by omega) (update_eq_self_of_eq h1_v) (by simp [moveHead]) ?_
        refine StepExecB.step (5, false, false) true .left τ (pos + 2 * (k + d) + 1)
          (by simp [rawDecPairL, h0_v]) (by omega) (update_eq_self_of_eq h0_v) (by simp [moveHead]; omega) ?_
        exact StepExecB.done hLB (by omega) (fun _ => rfl)
      rcases ih (by omega) with ⟨τm, hwin_m, hout_m, hmk_m, he_rest⟩
      exact ⟨τm, hwin_m, hout_m, hmk_m,
        (StepExecB.loopAt_step rawDecPairLNext (by omega) he2 rfl he_rest).weaken (4 * (d + 1) + 4) (by omega)⟩
  have hkw := hwin.2.1
  rcases hscan (w - k) (Nat.le_refl _) with ⟨τm, hwin_m, hout_m, hmk_m, he_sc⟩
  rw [show k + (w - k) = w by omega] at he_sc
  by_cases hk0 : k = 0
  · subst hk0
    simp only [decide_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero] at hwin_m he_sc ⊢
    rcases rawWalkPairR_spec true B L_bnd pos w 0 leftBits hLB (by omega) w (Nat.le_refl w)
        (by simpa using hwin_m) (fun i _ hi _ => hmk_m i (Nat.zero_le i) hi)
      with ⟨τ_end, hwin_end, hout_w, he_wk⟩
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero, ↓reduceIte] at hwin_end he_wk
    have he_inr := StepExecB.inr (loopAt (rawWalkPairR false) rawWalkPairRNext)
      (loopAt (rawWalkPairR true) rawWalkPairRNext) he_wk
    have he_s2 := StepExecB.seqAt
      (s₂ := sumStep (loopAt (rawWalkPairR false) rawWalkPairRNext) (loopAt (rawWalkPairR true) rawWalkPairRNext))
      (f := fun (_, _, _, wz) => if wz then Sum.inr (true, (0, false)) else Sum.inl (true, (0, false)))
      (by omega) he_sc (by simpa using he_inr)
    have he_tot : StepExecB rawDecWinMark B L_bnd (Sum.inl 0) τ (pos + 2 * w + 3)
        (Sum.inr (true, Sum.inr (true, Sum.inr (true, (2, true))))) τ_end (pos + 2 * w + 3)
        (2 + 2 + ((4 * (w - 0) + 4) + 2 + (4 * w + 2))) := by
      unfold rawDecWinMark
      exact StepExecB.seqAt (by omega) he_l2 he_s2
    refine ⟨_, τ_end, rfl, hwin_end, ?_, he_tot.weaken (9 * w + 15) (by omega)⟩
    intro p hp; rw [hout_w p (Or.inr (by omega)), hout_m p (Or.inr (by omega))]
  · simp only [hk0, decide_false, ↓reduceIte] at hwin_m he_sc ⊢
    rcases rawWalkPairR_spec false B L_bnd pos w (k - 1) leftBits hLB (by omega) (w - k) (by omega)
        (by simpa using hwin_m) (by simp)
      with ⟨τ_end, hwin_end, hout_w, he_wk⟩
    simp only [show w - (w - k) = k by omega, Bool.false_eq_true, ↓reduceIte] at hwin_end he_wk
    have he_inl := StepExecB.inl (loopAt (rawWalkPairR false) rawWalkPairRNext)
      (loopAt (rawWalkPairR true) rawWalkPairRNext) he_wk
    have he_s2 := StepExecB.seqAt
      (s₂ := sumStep (loopAt (rawWalkPairR false) rawWalkPairRNext) (loopAt (rawWalkPairR true) rawWalkPairRNext))
      (f := fun (_, _, _, wz) => if wz then Sum.inr (true, (0, false)) else Sum.inl (true, (0, false)))
      (by omega) he_sc (by simpa using he_inl)
    have he_tot : StepExecB rawDecWinMark B L_bnd (Sum.inl 0) τ (pos + 2 * w + 3)
        (Sum.inr (true, Sum.inr (true, Sum.inl (true, (2, true))))) τ_end (pos + 2 * w + 3)
        (2 + 2 + ((4 * (w - k) + 4) + 2 + (4 * (w - k) + 2))) := by
      unfold rawDecWinMark
      exact StepExecB.seqAt (by omega) he_l2 he_s2
    refine ⟨_, τ_end, rfl, hwin_end, ?_, he_tot.weaken (9 * w + 15) (by omega)⟩
    intro p hp; rw [hout_w p (Or.inr (by omega)), hout_m p (Or.inr (by omega))]

/-! #### `rawSlideW` (slide `w` times & reset `k = w`) and `rawSlide16w28` (`16 * w + 28` slides) -/

abbrev RawSlideWBodyQ : Type := RawDecWinMarkQ ⊕ (Bool × (Unit ⊕ RawSlideRight1Q))

def rawSlideWBody : StepFn RawSlideWBodyQ :=
  seqAt rawDecWinMark (sumStep (nopStep Unit) rawSlideRight1)
    (fun q => if rawDecWinMarkWasZero q then Sum.inl () else Sum.inr (Sum.inl (0, false)))

def rawSlideWNext : RawSlideWBodyQ → Option RawSlideWBodyQ
  | Sum.inr (true, Sum.inr _) => some (Sum.inl (Sum.inl 0))
  | _ => none

def rawSlideW : StepFn (Bool × RawSlideWBodyQ) :=
  loopAt rawSlideWBody rawSlideWNext

theorem rawSlideW_spec (B L_bnd pos₀ w : ℕ) (left₀ tailBits : List Bool) {τ₀ : ℕ → Bool}
    (hLB : L_bnd ≤ B) (hB : pos₀ + 3 * w + 6 ≤ L_bnd)
    (hwin₀ : RawWin pos₀ w w left₀ τ₀)
    (htail₀ : ∀ p, pos₀ + 2 * w + 3 ≤ p → τ₀ p = tailBits.getD (p - (pos₀ + 2 * w + 3)) false) :
    ∃ τ_end : ℕ → Bool,
      RawWin (pos₀ + w) w w (left₀ ++ (List.range w).map (fun i => tailBits.getD i false)) τ_end ∧
      (∀ p, (pos₀ + w) + 2 * w + 3 ≤ p → τ_end p = tailBits.getD (p - (pos₀ + 2 * w + 3)) false) ∧
      StepExecB rawSlideW B L_bnd (true, Sum.inl (Sum.inl 0)) τ₀ (pos₀ + 2 * w + 3)
        (true, Sum.inr (true, Sum.inl ())) τ_end ((pos₀ + w) + 2 * w + 3)
        ((w + 1) * (21 * w + 46)) := by
  let S_it := 21 * w + 44
  have hloop : ∀ k d, d + k = w → ∀ τc,
      RawWin (pos₀ + d) w k (left₀ ++ (List.range d).map (fun i => tailBits.getD i false)) τc →
      (∀ p, (pos₀ + d) + 2 * w + 3 ≤ p → τc p = tailBits.getD (p - (pos₀ + 2 * w + 3)) false) →
      ∃ τ_end : ℕ → Bool,
        RawWin (pos₀ + w) w w (left₀ ++ (List.range w).map (fun i => tailBits.getD i false)) τ_end ∧
        (∀ p, (pos₀ + w) + 2 * w + 3 ≤ p → τ_end p = tailBits.getD (p - (pos₀ + 2 * w + 3)) false) ∧
        StepExecB rawSlideW B L_bnd (true, Sum.inl (Sum.inl 0)) τc ((pos₀ + d) + 2 * w + 3)
          (true, Sum.inr (true, Sum.inl ())) τ_end ((pos₀ + w) + 2 * w + 3)
          ((k + 1) * (S_it + 2)) := by
    intro k
    induction k with
    | zero =>
      intro d hd τc hwin_c htail_c
      have hdw : d = w := by omega
      subst d
      rcases rawDecWinMark_spec B L_bnd (pos₀ + w) w 0 _ hLB (by omega) hwin_c
        with ⟨q_dm, τ_dm, hwz, hwin_dm, hout_dm, he_dm⟩
      simp only [decide_true, ↓reduceIte] at hwz hwin_dm
      have he_nop : StepExecB (nopStep Unit) B L_bnd () τ_dm ((pos₀ + w) + 2 * w + 3)
          () τ_dm ((pos₀ + w) + 2 * w + 3) 0 := StepExecB.done hLB (by omega) (fun _ => rfl)
      have he_inl := StepExecB.inl (nopStep Unit) rawSlideRight1 he_nop
      have he_body_raw : StepExecB rawSlideWBody B L_bnd (Sum.inl (Sum.inl 0)) τc ((pos₀ + w) + 2 * w + 3)
          (Sum.inr (true, Sum.inl ())) τ_dm ((pos₀ + w) + 2 * w + 3) ((9 * w + 15) + 2 + 0) := by
        unfold rawSlideWBody
        exact StepExecB.seqAt (by omega) he_dm (by rw [hwz]; exact he_inl)
      have he_body := he_body_raw.weaken S_it (by dsimp only [S_it]; omega)
      refine ⟨τ_dm, hwin_dm, fun p hp => (hout_dm p hp).trans (htail_c p hp),
        (StepExecB.loopAt_done rawSlideWNext he_body rfl).weaken ((0 + 1) * (S_it + 2)) (by omega)⟩
    | succ k ih =>
      intro d hd τc hwin_c htail_c
      rcases rawDecWinMark_spec B L_bnd (pos₀ + d) w (k + 1) _ hLB (by omega) hwin_c
        with ⟨q_dm, τ_dm, hwz, hwin_dm, hout_dm, he_dm⟩
      simp only [Nat.succ_ne_zero, decide_false, ↓reduceIte, Nat.add_sub_cancel] at hwz hwin_dm
      rcases rawSlideRight1_spec B L_bnd (pos₀ + d) w k _ hLB (by omega) hwin_dm
        with ⟨q_sl, τ_sl, hwin_sl, hout_sl, he_sl⟩
      have hb_eq : τ_dm ((pos₀ + d) + 2 * w + 3) = tailBits.getD d false := by
        rw [hout_dm _ (Nat.le_refl _), htail_c _ (Nat.le_refl _)]
        congr 1; omega
      have hlist_eq : (left₀ ++ (List.range d).map (fun i => tailBits.getD i false)) ++ [τ_dm ((pos₀ + d) + 2 * w + 3)] =
          left₀ ++ (List.range (d + 1)).map (fun i => tailBits.getD i false) := by
        rw [hb_eq, List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
      have hpos_eq : pos₀ + d + 1 = pos₀ + (d + 1) := by omega
      rw [hlist_eq, hpos_eq] at hwin_sl
      rw [hpos_eq] at he_sl
      have he_inr := StepExecB.inr (nopStep Unit) rawSlideRight1 he_sl
      have he_body_raw : StepExecB rawSlideWBody B L_bnd (Sum.inl (Sum.inl 0)) τc ((pos₀ + d) + 2 * w + 3)
          (Sum.inr (true, Sum.inr q_sl)) τ_sl ((pos₀ + (d + 1)) + 2 * w + 3)
          ((9 * w + 15) + 2 + (12 * w + 25)) := by
        unfold rawSlideWBody
        exact StepExecB.seqAt (by omega) he_dm (by rw [hwz]; exact he_inr)
      have he_body := he_body_raw.weaken S_it (by dsimp only [S_it]; omega)
      rcases ih (d + 1) (by omega) τ_sl hwin_sl
          (fun p hp => (hout_sl p (by omega)).trans ((hout_dm p (by omega)).trans (htail_c p (by omega))))
        with ⟨τ_end, hwin_end, htail_end, he_rest⟩
      refine ⟨τ_end, hwin_end, htail_end,
        (StepExecB.loopAt_step rawSlideWNext (by omega) he_body rfl he_rest).weaken
          ((k + 1 + 1) * (S_it + 2)) ?_⟩
      have : (k + 1 + 1) * (S_it + 2) = (S_it + 2) + (k + 1) * (S_it + 2) := by ring
      omega
  simpa [S_it] using hloop w 0 (Nat.zero_add w) τ₀ (by simpa using hwin₀) (by simpa using htail₀)

abbrev RawSlide16w28Q : Type :=
  RepeatAtQ 16 (Bool × RawSlideWBodyQ) ⊕ (Bool × RepeatAtQ 28 RawSlideRight1Q)

def rawSlide16w28 : StepFn RawSlide16w28Q :=
  seqAt (repeatAt 16 rawSlideW (true, Sum.inl (Sum.inl 0)))
    (repeatAt 28 rawSlideRight1 (Sum.inl (0, false)))
    (fun _ => repeatAtEntry 28 (Sum.inl (0, false)))

def rawSlide16w28Entry : RawSlide16w28Q :=
  Sum.inl (repeatAtEntry 16 (true, Sum.inl (Sum.inl 0)))

def rawSlide16w28Exit : RawSlide16w28Q :=
  Sum.inr (true, repeatAtExit 28)

/-- Build the padded raw prefix `S_raw` of length `18 * w + 31` from `midRest` and `w`. -/
def makeSRaw (w : ℕ) (midRest : List Bool) : List Bool :=
  (List.range (16 * w + 28)).map (fun i => midRest.getD i false) ++
    [false, false] ++ List.replicate (2 * w) true ++ [false]

theorem makeSRaw_length (w : ℕ) (midRest : List Bool) :
    (makeSRaw w midRest).length = 18 * w + 31 := by
  simp [makeSRaw]; omega

theorem rawWin_to_makeSRaw (w : ℕ) (midRest : List Bool) {τ : ℕ → Bool}
    (hmid_le : midRest.length ≤ 16 * w + 28)
    (hwin : RawWin (16 * w + 28) w w ((List.range (16 * w + 28)).map (fun i => midRest.getD i false)) τ)
    (htail : ∀ p, (16 * w + 28) + 2 * w + 3 ≤ p → τ p = midRest.getD (p - (2 * w + 3)) false) :
    ∀ p, τ p = if p < (makeSRaw w midRest).length then (makeSRaw w midRest).getD p false else false := by
  rcases hwin with ⟨_, _, hlt, hp0, hp1, hpairs, hsent⟩
  let L0 := 16 * w + 28
  let pfx := (List.range L0).map (fun i => midRest.getD i false)
  have hpfx_len : pfx.length = L0 := by simp [pfx]
  intro p
  rw [makeSRaw_length]
  by_cases hp_lt : p < 18 * w + 31
  · simp only [hp_lt, ↓reduceIte]
    unfold makeSRaw
    by_cases hp1_lt : p < L0
    · rw [hlt p hp1_lt]
      simp only [List.append_assoc]
      rw [getD_append_left _ _ _ (by simp [L0, hp1_lt])]
    · by_cases hp_eq0 : p = L0
      · subst hp_eq0
        rw [hp0]
        simp only [List.append_assoc]
        rw [getD_append_right _ _ _ (by simp [L0])]
        simp [L0]
      · by_cases hp_eq1 : p = L0 + 1
        · subst hp_eq1
          rw [hp1]
          simp only [List.append_assoc]
          rw [getD_append_right _ _ _ (by simp [L0])]
          simp [L0]
        · by_cases hp_mid : p < L0 + 2 + 2 * w
          · let idx := p - (L0 + 2)
            have hi : idx / 2 < w := by omega
            have hpr := hpairs (idx / 2) hi
            have hval : τ p = true := by
              by_cases hpar : idx % 2 = 0
              · have : p = L0 + 2 + 2 * (idx / 2) := by omega
                rw [this]; exact hpr.1
              · have : p = L0 + 2 + 2 * (idx / 2) + 1 := by omega
                rw [this, hpr.2]; simp [hi]
            rw [hval]
            simp only [List.append_assoc]
            rw [getD_append_right _ _ _ (by simp; dsimp only [L0] at *; omega)]
            have hsub2 : p - ((List.range (16 * w + 28)).map (fun i => midRest.getD i false)).length = idx + 2 := by
              simp only [List.length_map, List.length_range]; dsimp only [L0, idx] at *; omega
            rw [hsub2]
            simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
            rw [getD_append_left _ _ _ (by simp; dsimp only [L0, idx] at *; omega), List.getD_eq_getElem?_getD,
                List.getElem?_replicate]
            have hidx_lt : idx < 2 * w := by dsimp only [L0, idx] at *; omega
            simp [hidx_lt]
          · have hp_end : p = L0 + 2 * w + 2 := by omega
            subst hp_end
            rw [hsent]
            simp only [List.append_assoc]
            rw [getD_append_right _ _ _ (by simp; dsimp only [L0]; omega)]
            have hsub2 : L0 + 2 * w + 2 - ((List.range (16 * w + 28)).map (fun i => midRest.getD i false)).length = 2 * w + 2 := by
              simp only [List.length_map, List.length_range]; dsimp only [L0]; omega
            rw [hsub2]
            simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
            rw [getD_append_right _ _ _ (by simp)]
            simp
  · simp only [hp_lt, ↓reduceIte]
    rw [htail p (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem rawSlide16w28_spec (B L_bnd w : ℕ) (midRest : List Bool) {τ₀ : ℕ → Bool}
    (hLB : L_bnd ≤ B) (hB : 18 * w + 36 ≤ L_bnd)
    (hmid_le : midRest.length ≤ 16 * w + 28)
    (hwin₀ : RawWin 0 w w [] τ₀)
    (htail₀ : ∀ p, 2 * w + 3 ≤ p → τ₀ p = midRest.getD (p - (2 * w + 3)) false) :
    ∃ τ_end : ℕ → Bool,
      (∀ p, τ_end p = if p < (makeSRaw w midRest).length then (makeSRaw w midRest).getD p false else false) ∧
      StepExecB rawSlide16w28 B L_bnd rawSlide16w28Entry τ₀ (2 * w + 3)
        rawSlide16w28Exit τ_end (makeSRaw w midRest).length
        (16 * ((w + 1) * (21 * w + 46) + 2) + 2 + 28 * (12 * w + 25 + 2)) := by
  let Inv1 : ℕ → (ℕ → Bool) → ℕ → Prop := fun i τ h =>
    h = i * w + 2 * w + 3 ∧
    RawWin (i * w) w w ((List.range (i * w)).map (fun j => midRest.getD j false)) τ ∧
    (∀ p, i * w + 2 * w + 3 ≤ p → τ p = midRest.getD (p - (2 * w + 3)) false)
  have h16 : ∀ i < 16, ∀ τ h, Inv1 i τ h →
      ∃ q_end τ' h', Inv1 (i + 1) τ' h' ∧ h' + 2 ≤ L_bnd ∧
        StepExecB rawSlideW B L_bnd (true, Sum.inl (Sum.inl 0)) τ h q_end τ' h' ((w + 1) * (21 * w + 46)) := by
    intro i hi τ h ⟨hh, hwin, htail⟩
    subst hh
    have hshift_tail : ∀ p, i * w + 2 * w + 3 ≤ p →
        τ p = (midRest.drop (i * w)).getD (p - (i * w + 2 * w + 3)) false := by
      intro p hp
      rw [htail p hp, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
      congr 2; omega
    rcases rawSlideW_spec B L_bnd (i * w) w _ (midRest.drop (i * w)) hLB (by nlinarith) hwin hshift_tail
      with ⟨τ', hwin', htail', he_w⟩
    have hmul : i * w + w = (i + 1) * w := by ring
    have hlist : (List.range (i * w)).map (fun j => midRest.getD j false) ++
        (List.range w).map (fun j => (midRest.drop (i * w)).getD j false) =
        (List.range ((i + 1) * w)).map (fun j => midRest.getD j false) := by
      apply List.ext_getElem (by simp; ring)
      intro idx h1 h2
      simp only [List.length_append, List.length_map, List.length_range] at h1 h2
      by_cases hlt : idx < i * w
      · rw [List.getElem_append_left (by simp [hlt])]; simp
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
        congr 2; omega
    rw [hmul, hlist] at hwin'
    rw [hmul] at htail' he_w
    refine ⟨_, τ', (i + 1) * w + 2 * w + 3, ⟨rfl, hwin', fun p hp => ?_⟩, by nlinarith, he_w⟩
    rw [htail' p hp, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2; omega
  rcases repeatAt_spec 16 rawSlideW (true, Sum.inl (Sum.inl 0)) B L_bnd ((w + 1) * (21 * w + 46))
      hLB Inv1 h16 (by simpa [Inv1] using ⟨rfl, hwin₀, htail₀⟩) (by omega)
    with ⟨τ16, h16_pos, ⟨hh16, hwin16, htail16⟩, he16⟩
  subst hh16
  let Inv2 : ℕ → (ℕ → Bool) → ℕ → Prop := fun i τ h =>
    h = (16 * w + i) + 2 * w + 3 ∧
    RawWin (16 * w + i) w w ((List.range (16 * w + i)).map (fun j => midRest.getD j false)) τ ∧
    (∀ p, (16 * w + i) + 2 * w + 3 ≤ p → τ p = midRest.getD (p - (2 * w + 3)) false)
  have h28 : ∀ i < 28, ∀ τ h, Inv2 i τ h →
      ∃ q_end τ' h', Inv2 (i + 1) τ' h' ∧ h' + 2 ≤ L_bnd ∧
        StepExecB rawSlideRight1 B L_bnd (Sum.inl (0, false)) τ h q_end τ' h' (12 * w + 25) := by
    intro i hi τ h ⟨hh, hwin, htail⟩
    subst hh
    rcases rawSlideRight1_spec B L_bnd (16 * w + i) w w _ hLB (by omega) hwin
      with ⟨q_sl, τ', hwin', hout', he_sl⟩
    have hb_eq : τ ((16 * w + i) + 2 * w + 3) = midRest.getD (16 * w + i) false := by
      rw [htail _ (Nat.le_refl _)]; congr 1; omega
    have hlist : (List.range (16 * w + i)).map (fun j => midRest.getD j false) ++
        [τ ((16 * w + i) + 2 * w + 3)] =
        (List.range (16 * w + (i + 1))).map (fun j => midRest.getD j false) := by
      rw [hb_eq, show 16 * w + (i + 1) = (16 * w + i) + 1 by omega,
          List.range_succ, List.map_append, List.map_singleton]
    have hadd : 16 * w + i + 1 = 16 * w + (i + 1) := by omega
    rw [hadd, hlist] at hwin'
    rw [hadd] at he_sl
    refine ⟨q_sl, τ', (16 * w + (i + 1)) + 2 * w + 3,
      ⟨rfl, hwin', fun p hp => (hout' p (by omega)).trans (htail p (by omega))⟩,
      by omega, he_sl⟩
  rcases repeatAt_spec 28 rawSlideRight1 (Sum.inl (0, false)) B L_bnd (12 * w + 25)
      hLB Inv2 h28 (by simpa [Inv2] using ⟨rfl, hwin16, htail16⟩) (by omega)
    with ⟨τ_end, h_end, ⟨hh_end, hwin_end, htail_end⟩, he28⟩
  subst hh_end
  have he_tot : StepExecB rawSlide16w28 B L_bnd rawSlide16w28Entry τ₀ (2 * w + 3)
      rawSlide16w28Exit τ_end (makeSRaw w midRest).length
      (16 * ((w + 1) * (21 * w + 46) + 2) + 2 + 28 * (12 * w + 25 + 2)) := by
    rw [makeSRaw_length]
    have hpos_eq : (16 * w + 28) + 2 * w + 3 = 18 * w + 31 := by omega
    rw [hpos_eq] at he28
    exact StepExecB.seqAt (by omega) he16 he28
  exact ⟨τ_end, rawWin_to_makeSRaw w midRest hmid_le hwin_end htail_end, he_tot⟩

/-! #### Complete Phase 1.1: `rawToInitWS` (`inp` → `TapeWS τ (3 * M_0) B [S_raw]` + `r : Bool`) -/

abbrev RawExpandTouchQ : Type :=
  (RawInitWinQ ⊕ (Bool × (Bool × (RawSlide16w28Q ⊕ (Bool × (Fin 11 ⊕ (Bool × (Bool × ExpandBodyQ)))))))) ⊕
  (Bool × LiftBlkQ Bool)

def rawSlideExpand : StepFn
    (RawInitWinQ ⊕ (Bool × (Bool × (RawSlide16w28Q ⊕ (Bool × (Fin 11 ⊕ (Bool × (Bool × ExpandBodyQ)))))))) :=
  seqAt rawInitWin
    (familyStep (fun (_ : Bool) =>
      seqAt rawSlide16w28 rawExpandToWS (fun _ => Sum.inl 0)))
    (fun q =>
      let r := match q with | Sum.inr (true, (true, (_, r))) => r | _ => false
      (r, Sum.inl rawSlide16w28Entry))

def rawToInitWS : StepFn RawExpandTouchQ :=
  seq0 rawSlideExpand
    (familyStep (fun (_ : Bool) => liftBlockStep blkTouchWall))
    (fun q =>
      let r := match q with | Sum.inr (true, (r, _)) => r | _ => false
      (r, liftBlkEntry false))

theorem stepFnIter_len_mono {Q : Type} (s : StepFn Q) :
    ∀ k (q : Q) len τ h (q' : Q) len' τ' h',
      stepFnIter s (q, len, τ, h) k = some (q', len', τ', h') → len ≤ len'
  | 0, _, _, _, _, _, _, _, _, heq => by cases heq; exact Nat.le_refl _
  | k + 1, q, len, τ, h, q', len', τ', h', heq => by
      simp only [stepFnIter, stepFnOnce] at heq
      cases hs : s q (τ h) with
      | none => rw [hs] at heq; simp at heq
      | some val =>
        rcases val with ⟨q₁, b₁, d₁⟩
        rw [hs] at heq
        have hrec := stepFnIter_len_mono s k q₁ (max len (h + 1)) _ _ q' len' τ' h' heq
        omega

theorem rawToInitWS_spec (B n : ℕ) (rest : List Bool)
    (hn : 2 ≤ n) (hinp_le : (QCSD_natToUnary n ++ rest).length ≤ 9 * n + 4)
    (hB : 3 * (18 * ((n - 2) / 2) + 33) ≤ B) :
    let inp := QCSD_natToUnary n ++ rest
    let w := (n - 2) / 2
    let r := decide ((n - 2) % 2 = 1)
    let midRest := (if r then [false] else []) ++ rest
    let S_raw := makeSRaw w midRest
    let M0 := (encodeWorkspace [S_raw]).length
    ∃ τ_ws : ℕ → Bool,
      M0 = 18 * w + 33 ∧
      TapeWS τ_ws (3 * M0) B [S_raw] ∧
      (∀ p, 3 * M0 ≤ p → τ_ws p = false) ∧
      StepExec rawToInitWS B (Sum.inl (Sum.inl (Sum.inl 0))) inp.length (fun p => QCSD_tapeRead inp p) 0
        (Sum.inr (r, liftBlkExit true)) (3 * M0) τ_ws 0 (30000 * (n + 2) ^ 2) := by
  intro inp w r midRest S_raw M0
  have hS_len : S_raw.length = 18 * w + 31 := makeSRaw_length w midRest
  have hM0_eq : M0 = 18 * w + 33 := by
    simp [M0, encodeWorkspace, encodeSegmentsAux, hS_len]
  have hnw : n = 2 * w + 2 + (if r then 1 else 0) := by
    dsimp only [w, r]
    split_ifs with hr <;> simp only [decide_eq_true_eq] at hr <;> omega
  have hr_le : (if r then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have hmid_le : midRest.length ≤ 16 * w + 28 := by
    have hinp_len : inp.length = n + 1 + rest.length := by simp [inp, QCSD_natToUnary]; omega
    have hml : midRest.length = (if r then 1 else 0) + rest.length := by
      dsimp only [midRest]; split_ifs <;> simp; omega
    dsimp only [inp] at hinp_len
    omega
  let L_bnd := 3 * M0
  have hLB : L_bnd ≤ B := by dsimp only [L_bnd]; omega
  have hinp_L : inp.length ≤ L_bnd := by dsimp only [L_bnd, inp]; omega
  rcases rawInitWin_spec B L_bnd n rest hLB hn (by dsimp only [L_bnd]; omega) (fun _ => rfl)
    with ⟨τ1, hwin1, htail1, he1⟩
  rcases rawSlide16w28_spec B L_bnd w midRest hLB (by dsimp only [L_bnd]; omega) hmid_le hwin1 htail1
    with ⟨τ2, hS2, he2⟩
  rcases rawExpandToWS_spec B L_bnd S_raw hLB (by dsimp only [L_bnd]; omega) hS2
    with ⟨q_ex, τ3, hws3, hout3, he3⟩
  have he23 := StepExecB.seqAt (s₂ := rawExpandToWS) (f := fun _ => Sum.inl 0) (by dsimp only [L_bnd]; rw [makeSRaw_length]; omega) he2 he3
  have he23_f := StepExecB.family (fun (_ : Bool) => seqAt rawSlide16w28 rawExpandToWS (fun _ => Sum.inl 0)) r he23
  have he123 : StepExecB rawSlideExpand B L_bnd (Sum.inl (Sum.inl 0)) (fun p => QCSD_tapeRead inp p) 0
      (Sum.inr (true, (r, Sum.inr (true, q_ex)))) τ3 0
      ((4 * n + 10) + 2 + ((16 * ((w + 1) * (21 * w + 46) + 2) + 2 + 28 * (12 * w + 25 + 2)) + 2 +
        ((S_raw.length + 2) * (20 * S_raw.length + 40)))) := by
    unfold rawSlideExpand
    exact StepExecB.seqAt (by dsimp only [L_bnd]; omega) he1 (by simpa using he23_f)
  rcases he123.2 inp.length hinp_L with ⟨len3, hlen3_L, hex123⟩
  have hlen3_pos : 1 ≤ len3 := by
    rcases hex123 with ⟨k, _, hiter, _, _⟩
    have hmono := stepFnIter_len_mono _ k _ _ _ _ _ _ _ _ hiter
    have hinp_pos : 1 ≤ inp.length := by simp [inp, QCSD_natToUnary]; omega
    omega
  have he_tw := familyStep_spec (fun (_ : Bool) => liftBlockStep blkTouchWall) r
    (blkTouchWall_spec B [S_raw] (by simp) hlen3_L hLB hws3)
  have he_tot : StepExec rawToInitWS B (Sum.inl (Sum.inl (Sum.inl 0))) inp.length (fun p => QCSD_tapeRead inp p) 0
      (Sum.inr (r, liftBlkExit true)) (3 * M0) τ3 0
      (((4 * n + 10) + 2 + ((16 * ((w + 1) * (21 * w + 46) + 2) + 2 + 28 * (12 * w + 25 + 2)) + 2 +
        ((S_raw.length + 2) * (20 * S_raw.length + 40)))) + 1 + (14 * M0 + 4)) := by
    unfold rawToInitWS
    exact seq0_spec hlen3_pos hex123 (by simpa using he_tw)
  have htime_le : ((4 * n + 10) + 2 + ((16 * ((w + 1) * (21 * w + 46) + 2) + 2 + 28 * (12 * w + 25 + 2)) + 2 +
      ((S_raw.length + 2) * (20 * S_raw.length + 40)))) + 1 + (14 * M0 + 4) ≤ 30000 * (n + 2) ^ 2 := by
    have hw_le : 2 * w ≤ n := by omega
    rw [hS_len, hM0_eq]
    nlinarith
  refine ⟨τ3, hM0_eq, ⟨by simp, Nat.le_refl _, hLB, hws3⟩, ?_, he_tot.weaken _ htime_le⟩
  intro p hp
  exact hout3 p (by omega)

/-! ### Phase 1.2A: Marked Grow, `extractSegN`, `blkIterSeg`, `wsInc_marked`, `blkLoadConst`, `wsMulInto` -/

theorem reMark_wall_iff {S : ℕ → Bool} {σ : ℕ → BlkSym} {j : ℕ} :
    reMark S σ j = blkWall ↔ σ j = blkWall := by
  unfold reMark
  rcases h : σ j with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> cases S j <;> simp [blkData, blkWall]

theorem reMark_sep_iff {S : ℕ → Bool} {σ : ℕ → BlkSym} {j : ℕ} :
    reMark S σ j = blkSep ↔ σ j = blkSep := by
  unfold reMark
  rcases h : σ j with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> cases S j <;> simp [blkData, blkSep]

/-- General marked version of `blkGrowLast_lift_spec`: works whenever marks `S` vanish at `j ≥ M_cur - 1`. -/
theorem blkGrowLast_reMark_spec (B : ℕ) (fillSym : BlkSym) (_hfill_nh : fillSym ≠ blkHome)
    (segs segs' : List (List Bool)) (S : ℕ → Bool)
    (hws_eq : encodeWorkspace segs' =
      (encodeWorkspace segs).take ((encodeWorkspace segs).length - 1) ++ [fillSym, blkWall])
    (hne : segs ≠ []) (_hne' : segs' ≠ [])
    (hS_hi : ∀ j, (encodeWorkspace segs).length - 1 ≤ j → S j = false)
    {τ₁ : ℕ → Bool} {σ₀ : ℕ → BlkSym}
    (hws₀ : MatchesWS σ₀ segs)
    (hread₁ : readBlk τ₁ = reMark S σ₀)
    (hB' : 3 * ((encodeWorkspace segs).length + 1) ≤ B) :
    let M_cur := (encodeWorkspace segs).length
    ∃ τ₂ : ℕ → Bool, ∃ σ₁ : ℕ → BlkSym,
      MatchesWS σ₁ segs' ∧
      readBlk τ₂ = reMark S σ₁ ∧
      (encodeWorkspace segs').length = M_cur + 1 ∧
      (∀ p, 3 * (M_cur + 1) ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (liftBlockStep (blkGrowLast fillSym)) B (liftBlkEntry 0) (3 * M_cur) τ₁ 0
        (liftBlkExit 2) (3 * (encodeWorkspace segs').length) τ₂ 0 (14 * M_cur + 18) := by
  intro M_cur
  have hM_ge2 : 2 ≤ M_cur := encodeWorkspace_len_ge2 segs hne
  have hlen_ws' : (encodeWorkspace segs').length = M_cur + 1 := by
    rw [hws_eq, List.length_append, List.length_take]
    simp [M_cur]; omega
  -- 1) Walk right `M_cur - 1` blocks from `0` to `M_cur - 1`
  have hwalk_right : ∀ d,
      d ≤ M_cur - 1 →
      stepFnIter (liftBlockStep (blkGrowLast fillSym))
        (liftBlkEntry 0, 3 * M_cur, τ₁, 3 * (M_cur - 1 - d)) (7 * d) =
        some (liftBlkEntry 0, 3 * M_cur, τ₁, 3 * (M_cur - 1)) ∧
      (∀ m ≤ 7 * d, ∀ q_m l_m τ_m h_m,
        stepFnIter (liftBlockStep (blkGrowLast fillSym))
          (liftBlkEntry 0, 3 * M_cur, τ₁, 3 * (M_cur - 1 - d)) m =
          some (q_m, l_m, τ_m, h_m) → l_m ≤ B ∧ h_m + 1 ≤ B) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [Nat.sub_zero, Nat.mul_zero]
      exact ⟨rfl, fun m hm _ _ _ _ heq => by
        obtain rfl : m = 0 := by omega
        cases heq; exact ⟨by omega, by omega⟩⟩
    | succ d ih =>
      intro hd
      let j := M_cur - 1 - (d + 1)
      have hj_lt : j < M_cur - 1 := by omega
      have hne_wall : readBlk τ₁ j ≠ blkWall := by
        rw [hread₁, ne_eq, reMark_wall_iff, hws₀ j (by omega)]
        exact encodeWorkspace_lt_wall_ne_wall segs hne hj_lt
      have hbs : blkGrowLast fillSym 0 (readBlk τ₁ j) = some (0, readBlk τ₁ j, QCSD_HeadDir.right) := by
        simp [blkGrowLast, hne_wall]
      have hone := liftBlockStep_one_relaxed (blkGrowLast fillSym) B (M_cur + 1) (3 * M_cur) τ₁ 0 0
        (readBlk τ₁ j) .right j (by omega) (by omega) hB' ⟨by simp, fun _ => by omega⟩ hbs
      have hw_self : writeBlk τ₁ j (readBlk τ₁ j) = τ₁ := writeBlk_readBlk_self τ₁ j
      have hmax_eq : max (3 * M_cur) (3 * j + 3) = 3 * M_cur := by omega
      have hnext_j : moveHead j .right = M_cur - 1 - d := by simp [moveHead]; omega
      rw [hw_self, hmax_eq, hnext_j] at hone
      rcases ih (by omega) with ⟨hrest, hbnd_r⟩
      refine ⟨?_, ?_⟩
      · rw [show 7 * (d + 1) = 7 + 7 * d by ring, stepFnIter_add, hone.1, Option.bind_some, hrest]
      · intro m hm q_m l_m τ_m h_m hm_eq
        by_cases hm7 : m ≤ 7
        · rcases stepFnIter_le_some hm7 hone.1 with ⟨cfg, hsub⟩
          rw [hsub] at hm_eq; cases hm_eq
          exact hone.2 m hm7 q_m l_m τ_m h_m hsub
        · have heq : m = 7 + (m - 7) := by omega
          rw [heq, stepFnIter_add, hone.1, Option.bind_some] at hm_eq
          exact hbnd_r (m - 7) (by omega) q_m l_m τ_m h_m hm_eq
  rcases hwalk_right (M_cur - 1) (Nat.le_refl _) with ⟨hwr, hbnd_wr⟩
  rw [Nat.sub_self, Nat.mul_zero] at hwr hbnd_wr
  -- 2) At `M_cur - 1`: write `fillSym`, step right to `M_cur`
  have hwall_at : readBlk τ₁ (M_cur - 1) = blkWall := by
    rw [hread₁, reMark_wall_iff, hws₀ (M_cur - 1) (by omega)]
    exact encodeWorkspace_last_wall segs hne
  have hbs_1 : blkGrowLast fillSym 0 (readBlk τ₁ (M_cur - 1)) = some (1, fillSym, QCSD_HeadDir.right) := by
    simp [blkGrowLast, hwall_at]
  have hone_1 := liftBlockStep_one_relaxed (blkGrowLast fillSym) B (M_cur + 1) (3 * M_cur) τ₁ 0 1
    fillSym .right (M_cur - 1) (by omega) (by omega) hB' ⟨by simp, fun _ => by omega⟩ hbs_1
  have hm1_l : max (3 * M_cur) (3 * (M_cur - 1) + 3) = 3 * M_cur := by omega
  have hm1_h : moveHead (M_cur - 1) .right = M_cur := by simp [moveHead]; omega
  rw [hm1_l, hm1_h] at hone_1
  let τ_a := writeBlk τ₁ (M_cur - 1) fillSym
  -- 3) At `M_cur`: write `blkWall`, step left to `M_cur - 1`, `len := 3 * (M_cur + 1)`
  have hbs_2 : blkGrowLast fillSym 1 (readBlk τ_a M_cur) = some (2, blkWall, QCSD_HeadDir.left) := rfl
  have hone_2 := liftBlockStep_one_relaxed (blkGrowLast fillSym) B (M_cur + 1) (3 * M_cur) τ_a 1 2
    blkWall .left M_cur (by omega) (by omega) hB' ⟨fun _ => by omega, by simp⟩ hbs_2
  have hm2_l : max (3 * M_cur) (3 * M_cur + 3) = 3 * (M_cur + 1) := by omega
  have hm2_h : moveHead M_cur .left = M_cur - 1 := by simp [moveHead]
  rw [hm2_l, hm2_h] at hone_2
  let τ_b := writeBlk τ_a M_cur blkWall
  let σ₁ := Function.update (Function.update σ₀ (M_cur - 1) fillSym) M_cur blkWall
  have hread_b : readBlk τ_b = reMark S σ₁ := by
    funext j
    dsimp only [τ_b, τ_a, σ₁]
    rw [readBlk_writeBlk, readBlk_writeBlk]
    by_cases hjM : j = M_cur
    · subst hjM
      simp only [↓reduceIte]
      rw [reMark_of_false _ (hS_hi M_cur (by omega))]
      simp
    · simp only [hjM, ↓reduceIte]
      by_cases hjM1 : j = M_cur - 1
      · subst hjM1
        simp only [↓reduceIte]
        rw [reMark_of_false _ (hS_hi (M_cur - 1) (Nat.le_refl _)),
            Function.update_of_ne (by omega), Function.update_self]
      · simp only [hjM1, ↓reduceIte]
        rw [congrFun hread₁ j]
        unfold reMark
        rw [Function.update_of_ne hjM, Function.update_of_ne hjM1]
  have hws₁ : MatchesWS σ₁ segs' := by
    intro j hj
    rw [hlen_ws'] at hj
    dsimp only [σ₁]
    rw [hws_eq]
    by_cases hjM : j = M_cur
    · subst hjM
      rw [Function.update_self]
      have htl : ((encodeWorkspace segs).take ((encodeWorkspace segs).length - 1)).length =
          (encodeWorkspace segs).length - 1 := by rw [List.length_take]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [htl]; dsimp only [M_cur]; omega)]
      have hsub1 : M_cur - ((encodeWorkspace segs).take ((encodeWorkspace segs).length - 1)).length = 1 := by
        rw [htl]; dsimp only [M_cur]; omega
      rw [hsub1]; rfl
    · rw [Function.update_of_ne hjM]
      by_cases hjM1 : j = M_cur - 1
      · subst hjM1
        rw [Function.update_self]
        have htl : ((encodeWorkspace segs).take ((encodeWorkspace segs).length - 1)).length =
            (encodeWorkspace segs).length - 1 := by rw [List.length_take]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [htl])]
        have hsub0 : M_cur - 1 - ((encodeWorkspace segs).take ((encodeWorkspace segs).length - 1)).length = 0 := by
          rw [htl]; dsimp only [M_cur]; omega
        rw [hsub0]; rfl
      · rw [Function.update_of_ne hjM1, hws₀ j (by dsimp only [M_cur] at *; omega)]
        have hj_lt : j < (encodeWorkspace segs).length - 1 := by dsimp only [M_cur] at *; omega
        have htl : j < ((encodeWorkspace segs).take ((encodeWorkspace segs).length - 1)).length := by
          rw [List.length_take]; omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left htl, List.getElem?_take_of_lt hj_lt]
  -- 4) Rewind from `M_cur - 1` to `0`
  have h0_at : readBlk τ_b 0 = blkHome := by
    rw [hread_b, reMark_home_iff, hws₁ 0 (by omega), encodeWorkspace_getD_zero]
  have hne_at : ∀ i, 1 ≤ i → i ≤ M_cur - 1 → readBlk τ_b i ≠ blkHome := by
    intro i hi1 hi2
    rw [hread_b, ne_eq, reMark_home_iff, hws₁ i (by omega)]
    exact encodeWorkspace_ne_home segs' hi1 (by omega)
  rcases blkRewind_aux (blkGrowLast fillSym) (M_cur + 1) 2
      (by simp [blkGrowLast]) (fun sym hne_s => by simp [blkGrowLast, hne_s])
      (M_cur - 1) (readBlk τ_b) (by omega) h0_at hne_at
    with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
  rcases liftBlockStep_iter_aux (blkGrowLast fillSym) B (M_cur + 1) (3 * (M_cur + 1)) (Nat.le_refl _) hB'
      (M_cur - 1) 2 τ_b (M_cur - 1) 2 (readBlk τ_b) 0 hiter_rw hnone_rw hbnd_rw hdir_rw
    with ⟨τ₂, hread₂, hout₂, k_rw, hk_rw, hiter_fin, hexit_fin, hbnd_fin⟩
  rw [hlen_ws']
  refine ⟨τ₂, σ₁, hws₁, hread₂.trans hread_b, rfl, ?_,
    7 * (M_cur - 1) + 7 + 7 + k_rw, by omega, ?_, hexit_fin, ?_⟩
  · intro p hp
    rw [hout₂ p hp]
    dsimp only [τ_b, τ_a]
    rw [writeBlk_outside _ M_cur p blkWall (Or.inr (by omega)),
        writeBlk_outside _ (M_cur - 1) p fillSym (Or.inr (by omega))]
  · rw [stepFnIter_add, stepFnIter_add, stepFnIter_add, hwr, Option.bind_some,
        hone_1.1, Option.bind_some, hone_2.1, Option.bind_some, hiter_fin]
  · intro m hm q_m l_m τ_m h_m hm_eq
    by_cases hm1 : m ≤ 7 * (M_cur - 1)
    · exact hbnd_wr m hm1 q_m l_m τ_m h_m hm_eq
    · by_cases hm2 : m ≤ 7 * (M_cur - 1) + 7
      · have heq : m = 7 * (M_cur - 1) + (m - 7 * (M_cur - 1)) := by omega
        rw [heq, stepFnIter_add, hwr, Option.bind_some] at hm_eq
        exact hone_1.2 _ (by omega) q_m l_m τ_m h_m hm_eq
      · by_cases hm3 : m ≤ 7 * (M_cur - 1) + 7 + 7
        · have heq : m = 7 * (M_cur - 1) + 7 + (m - (7 * (M_cur - 1) + 7)) := by omega
          rw [heq, stepFnIter_add, stepFnIter_add, hwr, Option.bind_some, hone_1.1, Option.bind_some] at hm_eq
          exact hone_2.2 _ (by omega) q_m l_m τ_m h_m hm_eq
        · have heq : m = 7 * (M_cur - 1) + 7 + 7 + (m - (7 * (M_cur - 1) + 7 + 7)) := by omega
          rw [heq, stepFnIter_add, stepFnIter_add, stepFnIter_add, hwr, Option.bind_some,
              hone_1.1, Option.bind_some, hone_2.1, Option.bind_some] at hm_eq
          exact hbnd_fin _ (by omega) q_m l_m τ_m h_m hm_eq

/-- Clean `TapeWS` helper: push empty segment `[]` at end of `segs`. -/
theorem pushEmptySeg_spec (B : ℕ) (segs : List (List Bool)) {τ₁ : ℕ → Bool}
    (htw : TapeWS τ₁ (3 * (encodeWorkspace segs).length) B segs)
    (hB' : 3 * ((encodeWorkspace segs).length + 1) ≤ B) :
    let M_cur := (encodeWorkspace segs).length
    ∃ τ₂ : ℕ → Bool,
      TapeWS τ₂ (3 * (encodeWorkspace (segs ++ [[]])).length) B (segs ++ [[]]) ∧
      (encodeWorkspace (segs ++ [[]])).length = M_cur + 1 ∧
      (∀ p, 3 * (M_cur + 1) ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (liftBlockStep (blkGrowLast blkSep)) B (liftBlkEntry 0) (3 * M_cur) τ₁ 0
        (liftBlkExit 2) (3 * (encodeWorkspace (segs ++ [[]])).length) τ₂ 0 (14 * M_cur + 18) :=
  blkGrowLast_lift_spec B blkSep (by decide) segs (segs ++ [[]])
    (encodeWorkspace_push_empty segs htw.1) (by simp) htw hB'

/-- Clean `TapeWS` helper: append bit `b` to the last segment of `segs`. -/
theorem appendBitLast_spec (B : ℕ) (b : Bool) (segs : List (List Bool)) {τ₁ : ℕ → Bool}
    (htw : TapeWS τ₁ (3 * (encodeWorkspace segs).length) B segs)
    (hB' : 3 * ((encodeWorkspace segs).length + 1) ≤ B) :
    let segs' := segs.set (segs.length - 1) (segs.getD (segs.length - 1) [] ++ [b])
    let M_cur := (encodeWorkspace segs).length
    ∃ τ₂ : ℕ → Bool,
      TapeWS τ₂ (3 * (encodeWorkspace segs').length) B segs' ∧
      (encodeWorkspace segs').length = M_cur + 1 ∧
      (∀ p, 3 * (M_cur + 1) ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (liftBlockStep (blkGrowLast (blkData false b))) B (liftBlkEntry 0) (3 * M_cur) τ₁ 0
        (liftBlkExit 2) (3 * (encodeWorkspace segs').length) τ₂ 0 (14 * M_cur + 18) :=
  blkGrowLast_lift_spec B (blkData false b) (by simp [blkData, blkHome]) segs _
    (encodeWorkspace_extend_last_bit b segs htw.1)
    (by intro h; have := congrArg List.length h; simp at this; exact htw.1 this)
    htw hB'

/-! #### `blkPopRightOneSeg0` & `extractSegN`: turn `[S_raw]` + `r` into `[S_clean, List.replicate n false]` -/

def makeSClean (w : ℕ) (midRest : List Bool) : List Bool :=
  (List.range (16 * w + 28)).map (fun i => midRest.getD i false) ++ List.replicate (2 * w + 3) false

def makeSPop (w k : ℕ) (midRest : List Bool) : List Bool :=
  (List.range (16 * w + 28)).map (fun i => midRest.getD i false) ++
    [false, false] ++ List.replicate (2 * w - k) true ++ List.replicate (k + 1) false

theorem makeSPop_zero (w : ℕ) (midRest : List Bool) :
    makeSPop w 0 midRest = makeSRaw w midRest := by
  simp [makeSPop, makeSRaw, List.append_assoc]

theorem makeSPop_end (w : ℕ) (midRest : List Bool) :
    makeSPop w (2 * w) midRest = makeSClean w midRest := by
  simp only [makeSPop, makeSClean, Nat.sub_self, List.replicate_zero, List.append_nil, List.append_assoc]
  rfl

theorem makeSPop_length (w k : ℕ) (hk : k ≤ 2 * w) (midRest : List Bool) :
    (makeSPop w k midRest).length = 18 * w + 31 := by
  simp [makeSPop]; omega

def popMarkPred (w k : ℕ) (j : ℕ) : Bool :=
  decide (16 * w + 31 + (2 * w - k) ≤ j ∧ j < 16 * w + 31 + 2 * w)

/-- Block step popping one trailing `1` from the `(1)^(2w)` suffix of `seg 0` (turning it into
a marked `0`), or clearing all `2*w` marks when hitting the `[0, 0]` delimiter. -/
def blkPopRightOneSeg0 : BlkStepFn (Fin 5 × Bool) :=
  fun (ph, found) sym =>
    if ph = 0 then
      if sym = blkSep then some ((1, false), blkSep, QCSD_HeadDir.left)
      else some ((0, false), sym, QCSD_HeadDir.right)
    else if ph = 1 then
      some ((2, false), sym, QCSD_HeadDir.left)
    else if ph = 2 then
      if (!sym.1) && sym.2.1 then some ((2, false), sym, QCSD_HeadDir.left)
      else if (!sym.1) && sym.2.2 then some ((3, true), blkData true false, QCSD_HeadDir.left)
      else some ((4, false), sym, QCSD_HeadDir.right)
    else if ph = 4 then
      if (!sym.1) && sym.2.1 then some ((4, false), blkData false false, QCSD_HeadDir.right)
      else some ((3, false), sym, QCSD_HeadDir.left)
    else
      if sym = blkHome then none
      else some ((3, found), sym, QCSD_HeadDir.left)

theorem blkPopRightOneSeg0_spec (w k : ℕ) (midRest s1 : List Bool)
    (hk : k ≤ 2 * w) (σ₀ : ℕ → BlkSym)
    (hws₀ : MatchesWS σ₀ [makeSPop w k midRest, s1]) :
    let segs := [makeSPop w k midRest, s1]
    let M_cur := (encodeWorkspace segs).length
    let S := popMarkPred w k
    let σ_in := reMark S σ₀
    if k < 2 * w then
      ∃ σ₁ : ℕ → BlkSym,
        MatchesWS σ₁ [makeSPop w (k + 1) midRest, s1] ∧
        BlkExec blkPopRightOneSeg0 M_cur (0, false) σ_in 0
          (3, true) (reMark (popMarkPred w (k + 1)) σ₁) 0 (4 * M_cur)
    else
      BlkExec blkPopRightOneSeg0 M_cur (0, false) σ_in 0
        (3, false) σ₀ 0 (4 * M_cur) := by
  intro segs M_cur S σ_in
  have hL0 : (makeSPop w k midRest).length = 18 * w + 31 := makeSPop_length w k hk midRest
  have hM_eq : M_cur = 18 * w + 31 + s1.length + 3 := by
    simp [M_cur, segs, encodeWorkspace, encodeSegmentsAux, hL0]; omega
  have hM_raw : (encodeWorkspace [makeSPop w k midRest, s1]).length = 18 * w + 31 + s1.length + 3 := hM_eq
  have hs0_start : segStart segs 0 = 1 := rfl
  have hsep_pos : 18 * w + 32 = segStart segs 0 + (segs.getD 0 []).length := by
    simp [segs, segStart, hL0]; omega
  have hsep_at : σ_in (18 * w + 32) = blkSep := by
    dsimp only [σ_in]
    rw [reMark_sep_iff, hws₀ (18 * w + 32) (by omega), hsep_pos]
    have := encodeWorkspace_seg_end segs (s := 0) (by simp [segs])
    simpa [segs] using this
  have hlt_sep : ∀ j < 18 * w + 32, σ_in j ≠ blkSep := by
    intro j hj
    dsimp only [σ_in]
    rw [ne_eq, reMark_sep_iff, hws₀ j (by omega)]
    cases j with
    | zero => rw [encodeWorkspace_getD_zero]; decide
    | succ j' =>
      have hj' : j' < (segs.getD 0 []).length := by simp [segs, hL0]; omega
      have hd := encodeWorkspace_seg_data segs (s := 0) (by simp [segs]) hj'
      rw [hs0_start, show 1 + j' = j' + 1 by omega] at hd
      rw [hd]; simp [blkData, blkSep]
  -- Phase 0: walk right from `0` to `18 * w + 32` (`blkSep`), then step left to `18 * w + 31`
  have hgo_sep : ∀ d ≤ 18 * w + 32,
      blkIter blkPopRightOneSeg0 ((0, false), σ_in, 18 * w + 32 - d) d =
        some ((0, false), σ_in, 18 * w + 32) ∧
      (∀ i ≤ d, ∀ q' σ' j', blkIter blkPopRightOneSeg0 ((0, false), σ_in, 18 * w + 32 - d) i =
        some (q', σ', j') → j' < M_cur) ∧
      (∀ i < d, ∀ q' σ' j' q'' sym' dir,
        blkIter blkPopRightOneSeg0 ((0, false), σ_in, 18 * w + 32 - d) i = some (q', σ', j') →
        blkPopRightOneSeg0 q' (σ' j') = some (q'', sym', dir) →
        (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_cur)) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨rfl, fun i hi _ _ _ heq => by obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi; cases heq; omega,
        fun i hi => by omega⟩
    | succ d ih =>
      intro hd
      have hne : σ_in (18 * w + 32 - (d + 1)) ≠ blkSep := hlt_sep _ (by omega)
      have hbs : blkPopRightOneSeg0 (0, false) (σ_in (18 * w + 32 - (d + 1))) =
          some ((0, false), σ_in (18 * w + 32 - (d + 1)), QCSD_HeadDir.right) := by
        simp only [blkPopRightOneSeg0, ↓reduceIte, hne]
      have hnext : moveHead (18 * w + 32 - (d + 1)) QCSD_HeadDir.right = 18 * w + 32 - d := by
        simp [moveHead]; omega
      rcases ih (by omega) with ⟨hit, hbd, hdr⟩
      refine ⟨?_, ?_, ?_⟩
      · simp only [blkIter, blkOnce, hbs, Function.update_eq_self, hnext]; exact hit
      · intro i hi q' σ' j' hi_eq
        cases i with
        | zero => cases hi_eq; omega
        | succ i' =>
          simp only [blkIter, blkOnce, hbs, Function.update_eq_self, hnext] at hi_eq
          exact hbd i' (by omega) q' σ' j' hi_eq
      · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
        cases i with
        | zero => cases hi_eq; rw [hbs] at hbs'; cases hbs'; exact ⟨by simp, fun _ => by omega⟩
        | succ i' =>
          simp only [blkIter, blkOnce, hbs, Function.update_eq_self, hnext] at hi_eq
          exact hdr i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
  rcases hgo_sep (18 * w + 32) (Nat.le_refl _) with ⟨hiter0, hbnd0, hdir0⟩
  rw [Nat.sub_self] at hiter0 hbnd0 hdir0
  -- 2 steps: at `18*w+32` (`blkSep`) left -> `(1, false)` at `18*w+31`, left -> `(2, false)` at `18*w+30`
  have hbs_s1 : blkPopRightOneSeg0 (0, false) (σ_in (18 * w + 32)) = some ((1, false), blkSep, QCSD_HeadDir.left) := by
    simp [blkPopRightOneSeg0, hsep_at]
  have hbs_s2 : blkPopRightOneSeg0 (1, false) (σ_in (18 * w + 31)) = some ((2, false), σ_in (18 * w + 31), QCSD_HeadDir.left) := rfl
  have hstep12 : blkIter blkPopRightOneSeg0 ((0, false), σ_in, 18 * w + 32) 2 =
      some ((2, false), σ_in, 18 * w + 30) := by
    have hupd : Function.update σ_in (18 * w + 32) blkSep = σ_in := update_eq_self_of_eq hsep_at
    simp [blkIter, blkOnce, hbs_s1, hbs_s2, hupd, moveHead]
  -- Helper: value of `σ₀` at index `1 + idx` in `makeSPop w k midRest`
  have hσ₀_seg0 : ∀ idx < 18 * w + 31, σ₀ (1 + idx) = blkData false ((makeSPop w k midRest).getD idx false) := by
    intro idx hidx
    have hd := encodeWorkspace_seg_data segs (s := 0) (by simp [segs]) (by simpa [segs, hL0] using hidx)
    exact (hws₀ (1 + idx) (by omega)).trans (by simpa [segs, segStart] using hd)
  -- Phase 2: walk left skipping `k` marked `0`s from `18 * w + 30` to `18 * w + 30 - k`
  have hskip_mk : ∀ d ≤ k,
      blkIter blkPopRightOneSeg0 ((2, false), σ_in, 16 * w + 31 + (2 * w - k) + d - 1) d =
        some ((2, false), σ_in, 16 * w + 31 + (2 * w - k) - 1) ∧
      (∀ i ≤ d, ∀ q' σ' j', blkIter blkPopRightOneSeg0 ((2, false), σ_in, 16 * w + 31 + (2 * w - k) + d - 1) i =
        some (q', σ', j') → j' < M_cur) ∧
      (∀ i < d, ∀ q' σ' j' q'' sym' dir,
        blkIter blkPopRightOneSeg0 ((2, false), σ_in, 16 * w + 31 + (2 * w - k) + d - 1) i = some (q', σ', j') →
        blkPopRightOneSeg0 q' (σ' j') = some (q'', sym', dir) →
        (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_cur)) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨rfl, fun i hi _ _ _ heq => by obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi; cases heq; omega,
        fun i hi => by omega⟩
    | succ d ih =>
      intro hd
      have hS_t : S (16 * w + 31 + (2 * w - k) + (d + 1) - 1) = true := by
        dsimp only [S, popMarkPred]; simp only [decide_eq_true_eq]; omega
      have hσ_d : σ₀ (16 * w + 31 + (2 * w - k) + (d + 1) - 1) =
          blkData false ((makeSPop w k midRest).getD (16 * w + 31 + (2 * w - k) + (d + 1) - 1 - 1) false) := by
        have := hσ₀_seg0 (16 * w + 31 + (2 * w - k) + (d + 1) - 1 - 1) (by omega)
        rwa [show 1 + (16 * w + 31 + (2 * w - k) + (d + 1) - 1 - 1) = 16 * w + 31 + (2 * w - k) + (d + 1) - 1 by omega] at this
      have hsym_mk : σ_in (16 * w + 31 + (2 * w - k) + (d + 1) - 1) =
          blkData true ((makeSPop w k midRest).getD (16 * w + 31 + (2 * w - k) + (d + 1) - 1 - 1) false) := by
        dsimp only [σ_in, reMark]; rw [hσ_d, hS_t]; rfl
      have hbs : blkPopRightOneSeg0 (2, false) (σ_in (16 * w + 31 + (2 * w - k) + (d + 1) - 1)) =
          some ((2, false), σ_in (16 * w + 31 + (2 * w - k) + (d + 1) - 1), QCSD_HeadDir.left) := by
        rw [hsym_mk]; simp [blkPopRightOneSeg0, blkData]
      have hnext : moveHead (16 * w + 31 + (2 * w - k) + (d + 1) - 1) QCSD_HeadDir.left =
          16 * w + 31 + (2 * w - k) + d - 1 := by
        simp [moveHead]
      rcases ih (by omega) with ⟨hit, hbd, hdr⟩
      refine ⟨?_, ?_, ?_⟩
      · simp only [blkIter, blkOnce, hbs, Function.update_eq_self, hnext]; exact hit
      · intro i hi q' σ' j' hi_eq
        cases i with
        | zero => cases hi_eq; omega
        | succ i' =>
          simp only [blkIter, blkOnce, hbs, Function.update_eq_self, hnext] at hi_eq
          exact hbd i' (by omega) q' σ' j' hi_eq
      · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
        cases i with
        | zero => cases hi_eq; rw [hbs] at hbs'; cases hbs'; exact ⟨fun _ => by omega, by simp⟩
        | succ i' =>
          simp only [blkIter, blkOnce, hbs, Function.update_eq_self, hnext] at hi_eq
          exact hdr i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
  rcases hskip_mk k (Nat.le_refl k) with ⟨hiter_sk, hbnd_sk, hdir_sk⟩
  have hstart_sk : 16 * w + 31 + (2 * w - k) + k - 1 = 18 * w + 30 := by omega
  rw [hstart_sk] at hiter_sk hbnd_sk hdir_sk
  let p_hit := 16 * w + 31 + (2 * w - k) - 1
  have hS_hit : S p_hit = false := by dsimp only [S, popMarkPred, p_hit]; simp only [decide_eq_false_iff_not]; omega
  split_ifs with hk_lt
  · -- Case `k < 2 * w`: at `p_hit` we see `blkData false true`, rewrite to `blkData true false`, rewind!
    have hbit_hit : (makeSPop w k midRest).getD (p_hit - 1) false = true := by
      unfold makeSPop
      simp only [List.append_assoc]
      rw [getD_append_right _ _ _ (by simp; dsimp only [p_hit]; omega)]
      have hsub1 : p_hit - 1 - ((List.range (16 * w + 28)).map (fun i => midRest.getD i false)).length =
          (2 * w - k - 1) + 2 := by simp; dsimp only [p_hit]; omega
      rw [hsub1]
      simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
      rw [getD_append_left _ _ _ (by simp; omega), List.getD_eq_getElem?_getD, List.getElem?_replicate]
      have hlt_rep : 2 * w - k - 1 < 2 * w - k := by omega
      simp [hlt_rep]
    have hsym_hit : σ_in p_hit = blkData false true := by
      dsimp only [σ_in]
      rw [reMark_of_false _ hS_hit]
      have := hσ₀_seg0 (p_hit - 1) (by omega)
      rw [show 1 + (p_hit - 1) = p_hit by omega, hbit_hit] at this
      exact this
    have hbs_hit : blkPopRightOneSeg0 (2, false) (σ_in p_hit) =
        some ((3, true), blkData true false, QCSD_HeadDir.left) := by
      rw [hsym_hit]; simp [blkPopRightOneSeg0, blkData]
    let σ₁ := Function.update σ₀ p_hit (blkData false false)
    have hws₁ : MatchesWS σ₁ [makeSPop w (k + 1) midRest, s1] := by
      have hset_eq : makeSPop w (k + 1) midRest = (makeSPop w k midRest).set (p_hit - 1) false := by
        apply List.ext_getElem (by rw [List.length_set, makeSPop_length w (k + 1) (by omega), hL0])
        intro idx h1 h2
        rw [List.getElem_set]
        have h1' : idx < 18 * w + 31 := by rwa [makeSPop_length w (k + 1) (by omega)] at h1
        have hget : ∀ m (hm : m ≤ 2 * w), (makeSPop w m midRest).getD idx false =
            if idx < 16 * w + 28 then midRest.getD idx false
            else if idx < 16 * w + 30 then false
            else if idx < 16 * w + 30 + (2 * w - m) then true
            else false := by
          intro m hm
          unfold makeSPop; simp only [List.append_assoc]
          by_cases c1 : idx < 16 * w + 28
          · simp only [c1, ↓reduceIte]
            rw [getD_append_left _ _ _ (by simp [c1]), List.getD_eq_getElem?_getD,
                List.getElem?_map, List.getElem?_range c1]; rfl
          · simp only [c1, ↓reduceIte]
            rw [getD_append_right _ _ _ (by simp; omega)]
            have hlen_r : ((List.range (16 * w + 28)).map (fun i => midRest.getD i false)).length = 16 * w + 28 := by simp
            rw [hlen_r]
            by_cases c2 : idx = 16 * w + 28
            · subst c2; simp
            · by_cases c3 : idx = 16 * w + 29
              · subst c3; simp
              · have hc23 : ¬ (idx < 16 * w + 30) := by omega
                simp only [hc23, ↓reduceIte]
                have hsub : idx - (16 * w + 28) = (idx - (16 * w + 30)) + 2 := by omega
                rw [hsub]
                simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
                by_cases c4 : idx < 16 * w + 30 + (2 * w - m)
                · simp only [c4, ↓reduceIte]
                  rw [getD_append_left _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
                      List.getElem?_replicate]
                  simp [show idx - (16 * w + 30) < 2 * w - m by omega]
                · simp only [c4, ↓reduceIte]
                  rw [getD_append_right _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
                      List.getElem?_replicate]
                  split_ifs <;> rfl
        have hLHS := hget (k + 1) (by omega)
        have hRHS := hget k hk
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at hLHS
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rwa [List.length_set] at h2)] at hRHS
        simp only [Option.getD_some] at hLHS hRHS
        rw [hLHS]
        by_cases heq : p_hit - 1 = idx
        · simp only [heq, ↓reduceIte]
          have h1' : ¬ (idx < 16 * w + 28) := by dsimp only [p_hit] at heq; omega
          have h2' : ¬ (idx < 16 * w + 30) := by dsimp only [p_hit] at heq; omega
          have h3' : ¬ (idx < 16 * w + 30 + (2 * w - (k + 1))) := by dsimp only [p_hit] at heq; omega
          simp only [h1', h2', h3', ↓reduceIte]
        · simp only [heq, ↓reduceIte]
          rw [hRHS]
          by_cases c1 : idx < 16 * w + 28
          · simp only [c1, ↓reduceIte]
          · simp only [c1, ↓reduceIte]
            by_cases c2 : idx < 16 * w + 30
            · simp only [c2, ↓reduceIte]
            · simp only [c2, ↓reduceIte]
              have hiff : (idx < 16 * w + 30 + (2 * w - (k + 1))) ↔ (idx < 16 * w + 30 + (2 * w - k)) := by
                dsimp only [p_hit] at heq; omega
              simp only [hiff]
      have hupd := MatchesWS_update_seg_set segs (s := 0) (v := p_hit - 1) (by simp [segs])
        (by simp [segs, hL0]; dsimp only [p_hit]; omega) false hws₀
      have hseg_set : segs.set 0 ((segs.getD 0 []).set (p_hit - 1) false) = [makeSPop w (k + 1) midRest, s1] := by
        simp [segs, hset_eq]
      rw [hseg_set, show segStart segs 0 + (p_hit - 1) = p_hit by simp [segs, segStart]; dsimp only [p_hit]; omega] at hupd
      exact hupd
    have hupd_re : Function.update σ_in p_hit (blkData true false) = reMark (popMarkPred w (k + 1)) σ₁ := by
      funext j
      by_cases hj : j = p_hit
      · subst hj
        rw [Function.update_self]
        dsimp only [σ₁, reMark]
        rw [Function.update_self]
        have hS1 : popMarkPred w (k + 1) p_hit = true := by
          dsimp only [popMarkPred, p_hit]; simp only [decide_eq_true_eq]; omega
        rw [hS1]; rfl
      · rw [Function.update_of_ne hj]
        dsimp only [σ_in, σ₁, reMark]
        rw [Function.update_of_ne hj]
        have hSp : popMarkPred w (k + 1) j = S j := by
          dsimp only [S, popMarkPred, p_hit] at hj ⊢
          by_cases h1 : 16 * w + 31 + (2 * w - (k + 1)) ≤ j ∧ j < 16 * w + 31 + 2 * w
          · have h2 : 16 * w + 31 + (2 * w - k) ≤ j ∧ j < 16 * w + 31 + 2 * w := by omega
            simp [h1, h2]
          · have h2 : ¬ (16 * w + 31 + (2 * w - k) ≤ j ∧ j < 16 * w + 31 + 2 * w) := by omega
            simp [h1, h2]
        rw [hSp]
    have hstep_hit : blkIter blkPopRightOneSeg0 ((2, false), σ_in, p_hit) 1 =
        some ((3, true), reMark (popMarkPred w (k + 1)) σ₁, p_hit - 1) := by
      simp [blkIter, blkOnce, hbs_hit, hupd_re, moveHead]
    have hM₁ : (encodeWorkspace [makeSPop w (k + 1) midRest, s1]).length = M_cur := by
      simp [M_cur, segs, encodeWorkspace, encodeSegmentsAux, hL0, makeSPop_length w (k + 1) (by omega)]
    have h0_at : reMark (popMarkPred w (k + 1)) σ₁ 0 = blkHome := by
      rw [reMark_home_iff, hws₁ 0 (by omega), encodeWorkspace_getD_zero]
    have hne_at : ∀ i, 1 ≤ i → i ≤ p_hit - 1 → reMark (popMarkPred w (k + 1)) σ₁ i ≠ blkHome := by
      intro i hi1 hi2
      rw [ne_eq, reMark_home_iff, hws₁ i (by omega)]
      exact encodeWorkspace_ne_home _ hi1 (by omega)
    rcases blkRewind_aux blkPopRightOneSeg0 M_cur (3, true)
        (by simp [blkPopRightOneSeg0]) (fun sym hne => by simp [blkPopRightOneSeg0, hne])
        (p_hit - 1) (reMark (popMarkPred w (k + 1)) σ₁) (by omega) h0_at hne_at
      with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
    refine ⟨σ₁, hws₁, (18 * w + 32) + 2 + k + 1 + (p_hit - 1), by omega, ?_, hnone_rw, ?_, ?_⟩
    · rw [blkIter_add, blkIter_add, blkIter_add, blkIter_add,
          hiter0, Option.bind_some, hstep12, Option.bind_some,
          hiter_sk, Option.bind_some, hstep_hit, Option.bind_some, hiter_rw]
    · intro i hi q' σ' j' hi_eq
      by_cases hi1 : i ≤ 18 * w + 32
      · rcases blkIter_le_some hi1 hiter0 with ⟨⟨_, _, _⟩, hsub⟩
        rw [hsub] at hi_eq; cases hi_eq; exact hbnd0 i hi1 q' σ' j' hsub
      · by_cases hi2 : i ≤ 18 * w + 32 + 2
        · have heq : i = 18 * w + 32 + (i - (18 * w + 32)) := by omega
          rw [heq, blkIter_add, hiter0, Option.bind_some] at hi_eq
          have : i - (18 * w + 32) = 1 ∨ i - (18 * w + 32) = 2 := by omega
          rcases this with h1 | h2
          · rw [h1] at hi_eq; simp [blkIter, blkOnce, hbs_s1, moveHead] at hi_eq; rcases hi_eq with ⟨_, _, rfl⟩; omega
          · rw [h2, hstep12] at hi_eq; cases hi_eq; omega
        · by_cases hi3 : i ≤ 18 * w + 32 + 2 + k
          · have heq : i = 18 * w + 32 + 2 + (i - (18 * w + 32 + 2)) := by omega
            rw [heq, blkIter_add, blkIter_add, hiter0, Option.bind_some, hstep12, Option.bind_some] at hi_eq
            exact hbnd_sk _ (by omega) q' σ' j' hi_eq
          · have heq : i = 18 * w + 32 + 2 + k + 1 + (i - (18 * w + 32 + 2 + k + 1)) := by omega
            rw [heq, blkIter_add, blkIter_add, blkIter_add, blkIter_add,
                hiter0, Option.bind_some, hstep12, Option.bind_some,
                hiter_sk, Option.bind_some, hstep_hit, Option.bind_some] at hi_eq
            exact hbnd_rw _ (by omega) q' σ' j' hi_eq
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      by_cases hi1 : i < 18 * w + 32
      · exact hdir0 i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
      · by_cases hi2 : i = 18 * w + 32
        · subst hi2; rw [hiter0] at hi_eq; cases hi_eq; rw [hbs_s1] at hbs'; cases hbs'; exact ⟨fun _ => by omega, by simp⟩
        · by_cases hi3 : i = 18 * w + 32 + 1
          · subst hi3
            rw [blkIter_add, hiter0, Option.bind_some] at hi_eq
            simp [blkIter, blkOnce, hbs_s1, update_eq_self_of_eq hsep_at, moveHead] at hi_eq
            rcases hi_eq with ⟨rfl, rfl, rfl⟩
            rw [hbs_s2] at hbs'; cases hbs'; exact ⟨fun _ => by omega, by simp⟩
          · by_cases hi4 : i < 18 * w + 32 + 2 + k
            · have heq : i = 18 * w + 32 + 2 + (i - (18 * w + 32 + 2)) := by omega
              rw [heq, blkIter_add, blkIter_add, hiter0, Option.bind_some, hstep12, Option.bind_some] at hi_eq
              exact hdir_sk _ (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
            · by_cases hi5 : i = 18 * w + 32 + 2 + k
              · subst hi5
                rw [blkIter_add, blkIter_add, hiter0, Option.bind_some, hstep12, Option.bind_some, hiter_sk] at hi_eq
                cases hi_eq; rw [hbs_hit] at hbs'; cases hbs'; exact ⟨fun _ => by omega, by simp⟩
              · have heq : i = 18 * w + 32 + 2 + k + 1 + (i - (18 * w + 32 + 2 + k + 1)) := by omega
                rw [heq, blkIter_add, blkIter_add, blkIter_add, blkIter_add,
                    hiter0, Option.bind_some, hstep12, Option.bind_some,
                    hiter_sk, Option.bind_some, hstep_hit, Option.bind_some] at hi_eq
                exact hdir_rw _ (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
  · -- Case `k = 2 * w`: at `p_hit = 16 * w + 30` we see `blkData false false`, sweep right clearing marks, rewind!
    have hkeq : k = 2 * w := by omega
    have hphit_eq : p_hit = 16 * w + 30 := by dsimp only [p_hit]; omega
    have hbit_hit : (makeSPop w k midRest).getD (p_hit - 1) false = false := by
      unfold makeSPop; simp only [List.append_assoc]
      rw [getD_append_right _ _ _ (by simp; omega)]
      have hsub1 : p_hit - 1 - ((List.range (16 * w + 28)).map (fun i => midRest.getD i false)).length = 1 := by
        simp; omega
      rw [hsub1]; rfl
    have hsym_hit : σ_in p_hit = blkData false false := by
      dsimp only [σ_in]
      rw [reMark_of_false _ hS_hit]
      have := hσ₀_seg0 (p_hit - 1) (by omega)
      rw [show 1 + (p_hit - 1) = p_hit by omega, hbit_hit] at this
      exact this
    have hbs_hit : blkPopRightOneSeg0 (2, false) (σ_in p_hit) =
        some ((4, false), blkData false false, QCSD_HeadDir.right) := by
      rw [hsym_hit]; simp [blkPopRightOneSeg0, blkData]
    have hstep_hit : blkIter blkPopRightOneSeg0 ((2, false), σ_in, p_hit) 1 =
        some ((4, false), σ_in, 16 * w + 31) := by
      have hupd : Function.update σ_in p_hit (blkData false false) = σ_in := update_eq_self_of_eq hsym_hit
      rw [blkIter, blkOnce, hbs_hit]
      simp only [blkIter, moveHead]
      rw [hupd, hphit_eq]
    -- Phase 4: sweep right clearing `2 * w` marks from `16 * w + 31` to `18 * w + 31`
    have hclr : ∀ rem off, off + rem = 2 * w →
        let S_r : ℕ → Bool := fun j => decide (16 * w + 31 + off ≤ j ∧ j < 16 * w + 31 + 2 * w)
        blkIter blkPopRightOneSeg0 ((4, false), reMark S_r σ₀, 16 * w + 31 + off) rem =
          some ((4, false), σ₀, 18 * w + 31) ∧
        (∀ i ≤ rem, ∀ q' σ' j',
          blkIter blkPopRightOneSeg0 ((4, false), reMark S_r σ₀, 16 * w + 31 + off) i = some (q', σ', j') → j' < M_cur) ∧
        (∀ i < rem, ∀ q' σ' j' q'' sym' dir,
          blkIter blkPopRightOneSeg0 ((4, false), reMark S_r σ₀, 16 * w + 31 + off) i = some (q', σ', j') →
          blkPopRightOneSeg0 q' (σ' j') = some (q'', sym', dir) →
          (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_cur)) := by
      intro rem
      induction rem with
      | zero =>
        intro off hoff S_r
        have hSr_f : reMark S_r σ₀ = σ₀ := by
          funext j; exact reMark_of_false σ₀ (by dsimp only [S_r]; simp only [decide_eq_false_iff_not]; omega)
        rw [hSr_f, show 16 * w + 31 + off = 18 * w + 31 by omega]
        exact ⟨rfl, fun i hi _ _ _ heq => by obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi; cases heq; omega,
          fun i hi => by omega⟩
      | succ rem ih =>
        intro off hoff S_r
        have hbit_f : (makeSPop w k midRest).getD (16 * w + 31 + off - 1) false = false := by
          unfold makeSPop; simp only [List.append_assoc]
          rw [getD_append_right _ _ _ (by simp; omega)]
          have hsub : 16 * w + 31 + off - 1 - ((List.range (16 * w + 28)).map (fun i => midRest.getD i false)).length = off + 2 := by
            simp; omega
          rw [hsub]
          simp [List.cons_append, List.nil_append, hkeq, List.getD_eq_getElem?_getD]
        have hσ_pos : σ₀ (16 * w + 31 + off) = blkData false false := by
          have := hσ₀_seg0 (16 * w + 31 + off - 1) (by omega)
          rw [show 1 + (16 * w + 31 + off - 1) = 16 * w + 31 + off by omega, hbit_f] at this
          exact this
        have hSr_t : S_r (16 * w + 31 + off) = true := by dsimp only [S_r]; simp only [decide_eq_true_eq]; omega
        have hsym_p : reMark S_r σ₀ (16 * w + 31 + off) = blkData true false := by
          dsimp only [reMark]; rw [hσ_pos, hSr_t]; rfl
        have hbs : blkPopRightOneSeg0 (4, false) (reMark S_r σ₀ (16 * w + 31 + off)) =
            some ((4, false), blkData false false, QCSD_HeadDir.right) := by
          rw [hsym_p]; simp [blkPopRightOneSeg0, blkData]
        let S_next : ℕ → Bool := fun j => decide (16 * w + 31 + (off + 1) ≤ j ∧ j < 16 * w + 31 + 2 * w)
        have hupd : Function.update (reMark S_r σ₀) (16 * w + 31 + off) (blkData false false) = reMark S_next σ₀ := by
          funext j
          by_cases hj : j = 16 * w + 31 + off
          · subst hj; rw [Function.update_self, reMark_of_false _ (by dsimp only [S_next]; simp only [decide_eq_false_iff_not]; omega), hσ_pos]
          · rw [Function.update_of_ne hj]
            have heq : S_r j = S_next j := by
              dsimp only [S_r, S_next] at hj ⊢
              by_cases h1 : 16 * w + 31 + off ≤ j ∧ j < 16 * w + 31 + 2 * w
              · have h2 : 16 * w + 31 + (off + 1) ≤ j ∧ j < 16 * w + 31 + 2 * w := by omega
                simp [h1, h2]
              · have h2 : ¬ (16 * w + 31 + (off + 1) ≤ j ∧ j < 16 * w + 31 + 2 * w) := by omega
                simp [h1, h2]
            simp [reMark, heq]
        rcases ih (off + 1) (by omega) with ⟨hit, hbd, hdr⟩
        have hnext : moveHead (16 * w + 31 + off) QCSD_HeadDir.right = 16 * w + 31 + (off + 1) := by simp [moveHead]; omega
        refine ⟨?_, ?_, ?_⟩
        · simp only [blkIter, blkOnce, hbs, hupd, hnext]; exact hit
        · intro i hi q' σ' j' hi_eq
          cases i with
          | zero => cases hi_eq; omega
          | succ i' =>
            simp only [blkIter, blkOnce, hbs, hupd, hnext] at hi_eq
            exact hbd i' (by omega) q' σ' j' hi_eq
        · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
          cases i with
          | zero => cases hi_eq; rw [hbs] at hbs'; cases hbs'; exact ⟨by simp, fun _ => by omega⟩
          | succ i' =>
            simp only [blkIter, blkOnce, hbs, hupd, hnext] at hi_eq
            exact hdr i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
    rcases hclr (2 * w) 0 (Nat.zero_add _) with ⟨hiter_cl, hbnd_cl, hdir_cl⟩
    have hS_eq_0 : (fun j => decide (16 * w + 31 + 0 ≤ j ∧ j < 16 * w + 31 + 2 * w)) = S := by
      funext j; dsimp only [S, popMarkPred]; simp [hkeq]
    simp only [Nat.add_zero] at hiter_cl hbnd_cl hdir_cl
    rw [hS_eq_0] at hiter_cl hbnd_cl hdir_cl
    -- At `18 * w + 31`: unmarked `blkData false false`, turn into rewind `(3, false)` at `18 * w + 30`
    have hsym_end : σ₀ (18 * w + 31) = blkData false false := by
      have := hσ₀_seg0 (18 * w + 30) (by omega)
      have hb : (makeSPop w k midRest).getD (18 * w + 30) false = false := by
        unfold makeSPop; simp only [List.append_assoc]
        rw [getD_append_right _ _ _ (by simp; omega)]
        have hsub : 18 * w + 30 - ((List.range (16 * w + 28)).map (fun i => midRest.getD i false)).length = 2 * w + 2 := by
          simp; omega
        rw [hsub]
        simp [List.cons_append, List.nil_append, hkeq, List.getD_eq_getElem?_getD]
      rw [show 1 + (18 * w + 30) = 18 * w + 31 by omega, hb] at this
      exact this
    have hbs_turn : blkPopRightOneSeg0 (4, false) (σ₀ (18 * w + 31)) =
        some ((3, false), blkData false false, QCSD_HeadDir.left) := by
      rw [hsym_end]; simp [blkPopRightOneSeg0, blkData]
    have hstep_turn : blkIter blkPopRightOneSeg0 ((4, false), σ₀, 18 * w + 31) 1 =
        some ((3, false), σ₀, 18 * w + 30) := by
      simp [blkIter, blkOnce, hbs_turn, update_eq_self_of_eq hsym_end, moveHead]
    have h0_at : σ₀ 0 = blkHome := (hws₀ 0 (by omega)).trans (encodeWorkspace_getD_zero _)
    have hne_at : ∀ i, 1 ≤ i → i ≤ 18 * w + 30 → σ₀ i ≠ blkHome := by
      intro i hi1 hi2; rw [hws₀ i (by omega)]; exact encodeWorkspace_ne_home _ hi1 (by omega)
    rcases blkRewind_aux blkPopRightOneSeg0 M_cur (3, false)
        (by simp [blkPopRightOneSeg0]) (fun sym hne => by simp [blkPopRightOneSeg0, hne])
        (18 * w + 30) σ₀ (by omega) h0_at hne_at
      with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
    refine ⟨(18 * w + 32) + 2 + k + 1 + 2 * w + 1 + (18 * w + 30), by omega, ?_, hnone_rw, ?_, ?_⟩
    · rw [blkIter_add, blkIter_add, blkIter_add, blkIter_add, blkIter_add, blkIter_add,
          hiter0, Option.bind_some, hstep12, Option.bind_some,
          hiter_sk, Option.bind_some, hstep_hit, Option.bind_some,
          hiter_cl, Option.bind_some, hstep_turn, Option.bind_some, hiter_rw]
    · intro i hi q' σ' j' hi_eq
      by_cases hi1 : i ≤ 18 * w + 32
      · rcases blkIter_le_some hi1 hiter0 with ⟨⟨_, _, _⟩, hsub⟩
        rw [hsub] at hi_eq; cases hi_eq; exact hbnd0 i hi1 q' σ' j' hsub
      · by_cases hi2 : i ≤ 18 * w + 32 + 2
        · have heq : i = 18 * w + 32 + (i - (18 * w + 32)) := by omega
          rw [heq, blkIter_add, hiter0, Option.bind_some] at hi_eq
          have : i - (18 * w + 32) = 1 ∨ i - (18 * w + 32) = 2 := by omega
          rcases this with h1 | h2
          · rw [h1] at hi_eq; simp [blkIter, blkOnce, hbs_s1, moveHead] at hi_eq; rcases hi_eq with ⟨_, _, rfl⟩; omega
          · rw [h2, hstep12] at hi_eq; cases hi_eq; omega
        · by_cases hi3 : i ≤ 18 * w + 32 + 2 + k
          · have heq : i = 18 * w + 32 + 2 + (i - (18 * w + 32 + 2)) := by omega
            rw [heq, blkIter_add, blkIter_add, hiter0, Option.bind_some, hstep12, Option.bind_some] at hi_eq
            exact hbnd_sk _ (by omega) q' σ' j' hi_eq
          · by_cases hi4 : i ≤ 18 * w + 32 + 2 + k + 1 + 2 * w
            · have heq : i = 18 * w + 32 + 2 + k + 1 + (i - (18 * w + 32 + 2 + k + 1)) := by omega
              rw [heq, blkIter_add, blkIter_add, blkIter_add, blkIter_add,
                  hiter0, Option.bind_some, hstep12, Option.bind_some,
                  hiter_sk, Option.bind_some, hstep_hit, Option.bind_some] at hi_eq
              exact hbnd_cl _ (by omega) q' σ' j' hi_eq
            · have heq : i = 18 * w + 32 + 2 + k + 1 + 2 * w + 1 + (i - (18 * w + 32 + 2 + k + 1 + 2 * w + 1)) := by omega
              rw [heq, blkIter_add, blkIter_add, blkIter_add, blkIter_add, blkIter_add, blkIter_add,
                  hiter0, Option.bind_some, hstep12, Option.bind_some,
                  hiter_sk, Option.bind_some, hstep_hit, Option.bind_some,
                  hiter_cl, Option.bind_some, hstep_turn, Option.bind_some] at hi_eq
              exact hbnd_rw _ (by omega) q' σ' j' hi_eq
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      by_cases hi1 : i < 18 * w + 32
      · exact hdir0 i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
      · by_cases hi2 : i = 18 * w + 32
        · subst hi2; rw [hiter0] at hi_eq; cases hi_eq; rw [hbs_s1] at hbs'; cases hbs'; exact ⟨fun _ => by omega, by simp⟩
        · by_cases hi3 : i = 18 * w + 32 + 1
          · subst hi3
            rw [blkIter_add, hiter0, Option.bind_some] at hi_eq
            simp [blkIter, blkOnce, hbs_s1, update_eq_self_of_eq hsep_at, moveHead] at hi_eq
            rcases hi_eq with ⟨rfl, rfl, rfl⟩
            rw [hbs_s2] at hbs'; cases hbs'; exact ⟨fun _ => by omega, by simp⟩
          · by_cases hi4 : i < 18 * w + 32 + 2 + k
            · have heq : i = 18 * w + 32 + 2 + (i - (18 * w + 32 + 2)) := by omega
              rw [heq, blkIter_add, blkIter_add, hiter0, Option.bind_some, hstep12, Option.bind_some] at hi_eq
              exact hdir_sk _ (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
            · by_cases hi5 : i = 18 * w + 32 + 2 + k
              · subst hi5
                rw [blkIter_add, blkIter_add, hiter0, Option.bind_some, hstep12, Option.bind_some, hiter_sk] at hi_eq
                cases hi_eq; rw [hbs_hit] at hbs'; cases hbs'; exact ⟨by simp, fun _ => by omega⟩
              · by_cases hi6 : i < 18 * w + 32 + 2 + k + 1 + 2 * w
                · have heq : i = 18 * w + 32 + 2 + k + 1 + (i - (18 * w + 32 + 2 + k + 1)) := by omega
                  rw [heq, blkIter_add, blkIter_add, blkIter_add, blkIter_add,
                      hiter0, Option.bind_some, hstep12, Option.bind_some,
                      hiter_sk, Option.bind_some, hstep_hit, Option.bind_some] at hi_eq
                  exact hdir_cl _ (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
                · by_cases hi7 : i = 18 * w + 32 + 2 + k + 1 + 2 * w
                  · subst hi7
                    rw [blkIter_add, blkIter_add, blkIter_add, blkIter_add,
                        hiter0, Option.bind_some, hstep12, Option.bind_some,
                        hiter_sk, Option.bind_some, hstep_hit, Option.bind_some, hiter_cl] at hi_eq
                    cases hi_eq; rw [hbs_turn] at hbs'; cases hbs'; exact ⟨fun _ => by omega, by simp⟩
                  · have heq : i = 18 * w + 32 + 2 + k + 1 + 2 * w + 1 + (i - (18 * w + 32 + 2 + k + 1 + 2 * w + 1)) := by omega
                    rw [heq, blkIter_add, blkIter_add, blkIter_add, blkIter_add, blkIter_add, blkIter_add,
                        hiter0, Option.bind_some, hstep12, Option.bind_some,
                        hiter_sk, Option.bind_some, hstep_hit, Option.bind_some,
                        hiter_cl, Option.bind_some, hstep_turn, Option.bind_some] at hi_eq
                    exact hdir_rw _ (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

abbrev Extract2wLoopQ : Type :=
  LiftBlkQ (Fin 5 × Bool) ⊕ (Unit ⊕ LiftBlkQ (Fin 3))

def extract2wBody : StepFn Extract2wLoopQ :=
  seq0 (liftBlockStep blkPopRightOneSeg0)
    (sumStep (nopStep Unit) (liftBlockStep (blkGrowLast (blkData false false))))
    (fun q => if q.1.2 then Sum.inr (liftBlkEntry 0) else Sum.inl ())

def extract2wNext : Extract2wLoopQ → Option Extract2wLoopQ
  | Sum.inr (Sum.inr _) => some (Sum.inl (liftBlkEntry (0, false)))
  | _ => none

def extract2wLoop : StepFn Extract2wLoopQ :=
  loop0 extract2wBody extract2wNext

abbrev ExtractSegNQ : Type :=
  Bool × (LiftBlkQ (Fin 3) ⊕
    (LiftBlkQ (Fin 3) ⊕
      (LiftBlkQ (Fin 3) ⊕
        ((Unit ⊕ LiftBlkQ (Fin 3)) ⊕ Extract2wLoopQ))))

def extractSegNFor (r : Bool) :
    StepFn (LiftBlkQ (Fin 3) ⊕
      (LiftBlkQ (Fin 3) ⊕
        (LiftBlkQ (Fin 3) ⊕
          ((Unit ⊕ LiftBlkQ (Fin 3)) ⊕ Extract2wLoopQ)))) :=
  seq0 (liftBlockStep (blkGrowLast blkSep))
    (seq0 (liftBlockStep (blkGrowLast (blkData false false)))
      (seq0 (liftBlockStep (blkGrowLast (blkData false false)))
        (seq0 (sumStep (nopStep Unit) (liftBlockStep (blkGrowLast (blkData false false))))
          extract2wLoop
          (fun _ => Sum.inl (liftBlkEntry (0, false))))
        (fun _ => Sum.inl (if r then Sum.inr (liftBlkEntry 0) else Sum.inl ())))
      (fun _ => Sum.inl (liftBlkEntry 0)))
    (fun _ => Sum.inl (liftBlkEntry 0))

def extractSegN : StepFn ExtractSegNQ :=
  familyStep extractSegNFor

theorem extractSegN_spec (B n : ℕ) (midRest : List Bool) (hn : 2 ≤ n)
    {τ₀ : ℕ → Bool}
    (htw₀ : TapeWS τ₀ (3 * (encodeWorkspace [makeSRaw ((n - 2) / 2) midRest]).length) B
      [makeSRaw ((n - 2) / 2) midRest])
    (hclean₀ : ∀ p, 3 * (encodeWorkspace [makeSRaw ((n - 2) / 2) midRest]).length ≤ p → τ₀ p = false)
    (hB : 3 * ((encodeWorkspace [makeSClean ((n - 2) / 2) midRest, List.replicate n false]).length) ≤ B) :
    let w := (n - 2) / 2
    let r := decide ((n - 2) % 2 = 1)
    let segs_end := [makeSClean w midRest, List.replicate n false]
    let M_end := (encodeWorkspace segs_end).length
    ∃ τ_end : ℕ → Bool,
      M_end = 18 * w + 34 + n ∧
      TapeWS τ_end (3 * M_end) B segs_end ∧
      (∀ p, 3 * M_end ≤ p → τ_end p = false) ∧
      StepExec extractSegN B (r, Sum.inl (liftBlkEntry 0))
        (3 * (encodeWorkspace [makeSRaw w midRest]).length) τ₀ 0
        (r, Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))) (3 * M_end) τ_end 0
        ((n + 5) * (50 * M_end + 40)) := by
  intro w r segs_end M_end
  have hnw : n = 2 * w + 2 + (if r then 1 else 0) := by
    dsimp only [w, r]; split_ifs with hr <;> simp only [decide_eq_true_eq] at hr <;> omega
  have hM_end_eq : M_end = 18 * w + 34 + n := by
    simp [M_end, segs_end, encodeWorkspace, encodeSegmentsAux, makeSClean]; omega
  have hB_end : 3 * M_end ≤ B := hB
  have hM0_val : (encodeWorkspace [makeSRaw w midRest]).length = 18 * w + 33 := by
    simp [encodeWorkspace, encodeSegmentsAux, makeSRaw]; omega
  -- 1) Push empty seg 1, append 2 + r falses
  rcases pushEmptySeg_spec B [makeSRaw w midRest] htw₀ (by omega)
    with ⟨τ1, htw1, hM1, hout1, he1⟩
  simp only [List.singleton_append] at htw1 hM1 he1
  have hM1_val : (encodeWorkspace [makeSRaw w midRest, []]).length = 18 * w + 34 := by omega
  have hclean1 : ∀ p, 3 * (encodeWorkspace [makeSRaw w midRest, []]).length ≤ p → τ1 p = false := by
    intro p hp
    rw [hout1 p (by omega)]
    exact hclean₀ p (by change 3 * (encodeWorkspace [makeSRaw w midRest]).length ≤ p; omega)
  rcases appendBitLast_spec B false [makeSRaw w midRest, []] htw1 (by omega)
    with ⟨τ2, htw2, hM2, hout2, he2⟩
  simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel,
    List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.nil_append] at htw2 hM2 he2
  have hM2_val : (encodeWorkspace [makeSRaw w midRest, [false]]).length = 18 * w + 35 := by omega
  have hclean2 : ∀ p, 3 * (encodeWorkspace [makeSRaw w midRest, [false]]).length ≤ p → τ2 p = false := by
    intro p hp; rw [hout2 p (by omega)]; exact hclean1 p (by omega)
  rcases appendBitLast_spec B false [makeSRaw w midRest, [false]] htw2 (by omega)
    with ⟨τ3, htw3, hM3, hout3, he3⟩
  simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel,
    List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.singleton_append] at htw3 hM3 he3
  have hM3_val : (encodeWorkspace [makeSRaw w midRest, [false, false]]).length = 18 * w + 36 := by omega
  have hclean3 : ∀ p, 3 * (encodeWorkspace [makeSRaw w midRest, [false, false]]).length ≤ p → τ3 p = false := by
    intro p hp; rw [hout3 p (by omega)]; exact hclean2 p (by omega)
  let initLen := 2 + if r then 1 else 0
  have hstep_r : ∃ q_r, ∃ τ4 : ℕ → Bool,
      TapeWS τ4 (3 * (encodeWorkspace [makeSRaw w midRest, List.replicate initLen false]).length) B
        [makeSRaw w midRest, List.replicate initLen false] ∧
      (∀ p, 3 * (encodeWorkspace [makeSRaw w midRest, List.replicate initLen false]).length ≤ p → τ4 p = false) ∧
      StepExec (sumStep (nopStep Unit) (liftBlockStep (blkGrowLast (blkData false false)))) B
        (if r then Sum.inr (liftBlkEntry 0) else Sum.inl ())
        (3 * (encodeWorkspace [makeSRaw w midRest, [false, false]]).length) τ3 0
        q_r (3 * (encodeWorkspace [makeSRaw w midRest, List.replicate initLen false]).length) τ4 0
        (14 * M_end + 18) := by
    cases hr : r with
    | false =>
      have hrep : List.replicate initLen false = [false, false] := by simp [initLen, hr]
      rw [hrep]
      exact ⟨Sum.inl (), τ3, htw3, hclean3,
        (sumStep_inl_spec (nopStep Unit) _ (nopStep_spec (B := B) () _ τ3 0 htw3.2.2.1 (by omega))).weaken _ (by omega)⟩
    | true =>
      have hnw_t : n = 2 * w + 3 := by simp [hr] at hnw; omega
      have hrep : List.replicate initLen false = [false, false, false] := by simp [initLen, hr]
      rw [hrep]
      rcases appendBitLast_spec B false [makeSRaw w midRest, [false, false]] htw3 (by omega)
        with ⟨τ4, htw4, hM4, hout4, he4⟩
      simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel,
        List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero,
        List.cons_append, List.nil_append] at htw4 hM4 he4
      have hM4_val : (encodeWorkspace [makeSRaw w midRest, [false, false, false]]).length = 18 * w + 37 := by omega
      have hM_le : (encodeWorkspace [makeSRaw w midRest, [false, false]]).length ≤ M_end := by omega
      refine ⟨Sum.inr (liftBlkExit 2), τ4, htw4, ?_,
        (sumStep_inr_spec (nopStep Unit) _ he4).weaken (14 * M_end + 18) (by omega)⟩
      intro p hp
      rw [hout4 p (by omega)]
      exact hclean3 p (by omega)
  rcases hstep_r with ⟨q_r, τ4, htw4, hclean4, he4⟩
  -- 2) Run `extract2wLoop` (`rem` from `2 * w` down to `0`, `k = 2 * w - rem`)
  let S_it := 44 * M_end + 30
  have hloop : ∀ rem k, k + rem = 2 * w →
      ∀ {τc : ℕ → Bool} {σ₀ : ℕ → BlkSym},
        let segs_c := [makeSPop w k midRest, List.replicate (initLen + k) false]
        let M_c := (encodeWorkspace segs_c).length
        MatchesWS σ₀ segs_c →
        readBlk τc = reMark (popMarkPred w k) σ₀ →
        (∀ p, 3 * M_c ≤ p → τc p = false) →
        ∃ τ_end : ℕ → Bool,
          TapeWS τ_end (3 * M_end) B segs_end ∧
          (∀ p, 3 * M_end ≤ p → τ_end p = false) ∧
          StepExec extract2wLoop B (Sum.inl (liftBlkEntry (0, false))) (3 * M_c) τc 0
            (Sum.inr (Sum.inl ())) (3 * M_end) τ_end 0 ((rem + 1) * (S_it + 2)) := by
    intro rem
    induction rem with
    | zero =>
      intro k hk τc σ₀ segs_c M_c hws_c hread_c hcl_c
      have hkw : k = 2 * w := by omega
      subst hkw
      have hsegs_eq : segs_c = segs_end := by
        dsimp only [segs_c, segs_end, initLen]
        rw [makeSPop_end, show 2 + (if r then 1 else 0) + 2 * w = n by omega]
      have hMc_eq : M_c = M_end := congrArg (fun l => (encodeWorkspace l).length) hsegs_eq
      have hpop := blkPopRightOneSeg0_spec w (2 * w) midRest (List.replicate (initLen + 2 * w) false)
        (Nat.le_refl _) σ₀ hws_c
      simp only [Nat.lt_irrefl, ↓reduceIte] at hpop
      rw [← hread_c] at hpop
      rcases liftBlockStep_spec blkPopRightOneSeg0 B M_c (3 * M_c) τc
          (0, false) (3, false) σ₀ 0 0 (4 * M_c) (Nat.le_refl _) (by omega) hpop
        with ⟨τ_p, hread_p, hout_p, he_p⟩
      simp only [Nat.mul_zero] at he_p
      have hlen_pos : 1 ≤ 3 * M_c := by omega
      have he_nop := sumStep_inl_spec (nopStep Unit) (liftBlockStep (blkGrowLast (blkData false false)))
        (nopStep_spec (B := B) () (3 * M_c) τ_p 0 (by omega) (by omega))
      have he_body : StepExec extract2wBody B (Sum.inl (liftBlkEntry (0, false))) (3 * M_c) τc 0
          (Sum.inr (Sum.inl ())) (3 * M_c) τ_p 0 S_it := by
        unfold extract2wBody
        exact (seq0_spec hlen_pos he_p (by simpa [liftBlkExit] using he_nop)).weaken S_it
          (by dsimp only [S_it]; omega)
      have hdone : StepExec extract2wLoop B (Sum.inl (liftBlkEntry (0, false))) (3 * M_c) τc 0
          (Sum.inr (Sum.inl ())) (3 * M_end) τ_p 0 ((0 + 1) * (S_it + 2)) := by
        rw [← hMc_eq]
        exact (loop0_done (next := extract2wNext) he_body rfl).weaken ((0 + 1) * (S_it + 2)) (by omega)
      refine ⟨τ_p, ⟨List.cons_ne_nil _ _, Nat.le_refl _, hB_end, ?_⟩, ?_, hdone⟩
      · rw [hread_p, ← hsegs_eq]; exact hws_c
      · intro p hp; rw [hout_p p (by omega)]; exact hcl_c p (by omega)
    | succ rem ih =>
      intro k hk τc σ₀ segs_c M_c hws_c hread_c hcl_c
      have hMc_lt : M_c + 1 ≤ M_end := by
        have : M_c = 18 * w + 34 + (initLen + k) := by
          simp only [M_c, segs_c, encodeWorkspace, encodeSegmentsAux, List.length_cons, List.length_nil,
            List.length_append, List.length_map, List.length_replicate,
            makeSPop_length w k (by omega)]
          omega
        dsimp only [initLen] at this; omega
      have hpop := blkPopRightOneSeg0_spec w k midRest (List.replicate (initLen + k) false)
        (by omega) σ₀ hws_c
      have hk_lt : k < 2 * w := by omega
      simp only [hk_lt, ↓reduceIte] at hpop
      rcases hpop with ⟨σ₁, hws₁, hblk_p⟩
      rw [← hread_c] at hblk_p
      rcases liftBlockStep_spec blkPopRightOneSeg0 B M_c (3 * M_c) τc
          (0, false) (3, true) (reMark (popMarkPred w (k + 1)) σ₁) 0 0 (4 * M_c)
          (Nat.le_refl _) (by omega) hblk_p
        with ⟨τ_p, hread_p, hout_p, he_p⟩
      simp only [Nat.mul_zero] at he_p
      let segs_p := [makeSPop w (k + 1) midRest, List.replicate (initLen + k) false]
      let segs_next := [makeSPop w (k + 1) midRest, List.replicate (initLen + (k + 1)) false]
      have hMp_eq : (encodeWorkspace segs_p).length = M_c := by
        simp only [segs_p, M_c, segs_c, encodeWorkspace, encodeSegmentsAux, List.length_cons,
          List.length_append, List.length_map, List.length_replicate,
          makeSPop_length w k (by omega), makeSPop_length w (k + 1) (by omega)]
      have hnext_eq : segs_next = segs_p.set (segs_p.length - 1) (segs_p.getD (segs_p.length - 1) [] ++ [false]) := by
        dsimp only [segs_next, segs_p]
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
          List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero]
        rw [show initLen + (k + 1) = (initLen + k) + 1 by omega, List.replicate_succ']
      have hws_next_eq : encodeWorkspace segs_next =
          (encodeWorkspace segs_p).take ((encodeWorkspace segs_p).length - 1) ++
            [blkData false false, blkWall] := by
        rw [hnext_eq]; exact encodeWorkspace_extend_last_bit false segs_p (List.cons_ne_nil _ _)
      have hS_hi : ∀ j, (encodeWorkspace segs_p).length - 1 ≤ j → popMarkPred w (k + 1) j = false := by
        intro j hj
        have hlen_p : (encodeWorkspace segs_p).length = 18 * w + 34 + (initLen + k) := by
          simp only [segs_p, encodeWorkspace, encodeSegmentsAux, List.length_cons, List.length_nil,
            List.length_append, List.length_map, List.length_replicate,
            makeSPop_length w (k + 1) (by omega)]
          omega
        dsimp only [popMarkPred]; simp only [decide_eq_false_iff_not]; omega
      rcases blkGrowLast_reMark_spec B (blkData false false) (by decide) segs_p segs_next
          (popMarkPred w (k + 1)) hws_next_eq (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) hS_hi
          hws₁ hread_p (by omega)
        with ⟨τ_g, σ₂, hws₂, hread₂, hM_g, hout_g, he_g⟩
      rw [hMp_eq] at he_g hM_g hout_g
      have hlen_p_pos : 1 ≤ 3 * M_c := by have := encodeWorkspace_len_ge2 segs_c (by simp [segs_c]); omega
      have he_inr := sumStep_inr_spec (nopStep Unit) (liftBlockStep (blkGrowLast (blkData false false))) he_g
      have he_body : StepExec extract2wBody B (Sum.inl (liftBlkEntry (0, false))) (3 * M_c) τc 0
          (Sum.inr (Sum.inr (liftBlkExit 2))) (3 * (encodeWorkspace segs_next).length) τ_g 0 S_it := by
        unfold extract2wBody
        exact (seq0_spec hlen_p_pos he_p (by simpa [liftBlkExit] using he_inr)).weaken S_it
          (by dsimp only [S_it]; omega)
      have hcl_g : ∀ p, 3 * (encodeWorkspace segs_next).length ≤ p → τ_g p = false := by
        intro p hp
        rw [hout_g p (by omega), hout_p p (by omega)]
        exact hcl_c p (by omega)
      rcases ih (k + 1) (by omega) hws₂ hread₂ hcl_g with ⟨τ_end, htw_end, hcl_end, he_rest⟩
      have hlen_g_pos : 1 ≤ 3 * (encodeWorkspace segs_next).length := by omega
      have hcomb := (loop0_step (next := extract2wNext) hlen_g_pos he_body rfl he_rest).weaken
        ((rem + 1 + 1) * (S_it + 2)) (by
          have : (rem + 1 + 1) * (S_it + 2) = (S_it + 2) + (rem + 1) * (S_it + 2) := by ring
          omega)
      exact ⟨τ_end, htw_end, hcl_end, hcomb⟩
  have htw4_pop : TapeWS τ4 (3 * (encodeWorkspace [makeSPop w 0 midRest, List.replicate (initLen + 0) false]).length) B
      [makeSPop w 0 midRest, List.replicate (initLen + 0) false] := by
    simpa [makeSPop_zero] using htw4
  have hread4 : readBlk τ4 = reMark (popMarkPred w 0) (readBlk τ4) := by
    funext j
    exact (reMark_of_false (readBlk τ4) (by dsimp only [popMarkPred]; simp only [decide_eq_false_iff_not]; omega)).symm
  rcases hloop (2 * w) 0 (Nat.zero_add _) htw4_pop.2.2.2 hread4 (by simpa [makeSPop_zero] using hclean4)
    with ⟨τ_end, htw_end, hcl_end, he_lp⟩
  simp only [makeSPop_zero, Nat.add_zero] at he_lp
  have he45 := seq0_spec (f := fun _ => Sum.inl (liftBlkEntry (0, false))) (TapeWS_pos htw4) he4 he_lp
  have he35 := seq0_spec (f := fun _ => Sum.inl (if r then Sum.inr (liftBlkEntry 0) else Sum.inl ()))
    (TapeWS_pos htw3) he3 he45
  have he25 := seq0_spec (f := fun _ => Sum.inl (liftBlkEntry 0)) (TapeWS_pos htw2) he2 he35
  have he15 := seq0_spec (f := fun _ => Sum.inl (liftBlkEntry 0)) (TapeWS_pos htw1) he1 he25
  have he_fam := familyStep_spec extractSegNFor r he15
  have hM0_le : (encodeWorkspace [makeSRaw w midRest]).length ≤ M_end := by
    simp [encodeWorkspace, encodeSegmentsAux, makeSRaw]; omega
  have hM1_le : (encodeWorkspace [makeSRaw w midRest, []]).length ≤ M_end := by
    simp [encodeWorkspace, encodeSegmentsAux, makeSRaw]; omega
  have hM2_le : (encodeWorkspace [makeSRaw w midRest, [false]]).length ≤ M_end := by
    simp [encodeWorkspace, encodeSegmentsAux, makeSRaw]; omega
  have htime : 14 * (encodeWorkspace [makeSRaw w midRest]).length + 18 + 1 +
      (14 * (encodeWorkspace [makeSRaw w midRest, []]).length + 18 + 1 +
        (14 * (encodeWorkspace [makeSRaw w midRest, [false]]).length + 18 + 1 +
          (14 * M_end + 18 + 1 + (2 * w + 1) * (S_it + 2)))) ≤ (n + 5) * (50 * M_end + 40) := by
    have h2w : 2 * w + 1 ≤ n := by omega
    have h1 : (2 * w + 1) * (S_it + 2) ≤ n * (44 * M_end + 32) :=
      Nat.mul_le_mul h2w (by dsimp only [S_it]; omega)
    nlinarith
  exact ⟨τ_end, hM_end_eq, htw_end, hcl_end, he_fam.weaken _ htime⟩

/-! #### Universal Segment Iterator `blkIterSeg` (mark next bit or unmark all) -/

/-- State `(rem, ph, found, bit)` for `blkIterSeg`:
- `ph = 0`: walk to segment `s`, skip marked bits; on unmarked data bit, mark it & rewind (`ph = 1, found = true, bit = b`);
  on `blkSep`/`blkWall`, rewind clearing all marks (`ph = 2, found = false`). -/
def blkIterSeg (MaxSeg : ℕ) : BlkStepFn (Fin (MaxSeg + 1) × Fin 3 × Bool × Bool) :=
  fun (rem, ph, found, bit) sym =>
    if ph = 0 then
      if sym = blkHome then some ((rem, 0, false, false), blkHome, QCSD_HeadDir.right)
      else if hrem : 0 < rem.val then
        let prev : Fin (MaxSeg + 1) := ⟨rem.val - 1, by omega⟩
        if sym = blkSep then some ((prev, 0, false, false), blkSep, QCSD_HeadDir.right)
        else some ((rem, 0, false, false), sym, QCSD_HeadDir.right)
      else if !sym.1 then
        if sym.2.1 then some ((0, 0, false, false), sym, QCSD_HeadDir.right)
        else some ((0, 1, true, sym.2.2), blkData true sym.2.2, QCSD_HeadDir.left)
      else some ((0, 2, false, false), sym, QCSD_HeadDir.left)
    else if ph = 1 then
      if sym = blkHome then none
      else some ((0, 1, true, bit), sym, QCSD_HeadDir.left)
    else
      if sym = blkHome then none
      else some ((0, 2, false, false), if !sym.1 then blkData false sym.2.2 else sym, QCSD_HeadDir.left)

theorem blkIterSeg_spec (MaxSeg : ℕ) (segs : List (List Bool)) {s k : ℕ}
    (hs : s < segs.length) (hs_m : s ≤ MaxSeg) (hk : k ≤ (segs.getD s []).length)
    (σ₀ : ℕ → BlkSym) (hws₀ : MatchesWS σ₀ segs) :
    let M_blk := (encodeWorkspace segs).length
    let σ_in := reMark (segMarkPred segs s k) σ₀
    if k < (segs.getD s []).length then
      BlkExec (blkIterSeg MaxSeg) M_blk (⟨s, by omega⟩, 0, false, false) σ_in 0
        (0, 1, true, (segs.getD s []).getD k false)
        (reMark (segMarkPred segs s (k + 1)) σ₀) 0 (3 * M_blk)
    else
      BlkExec (blkIterSeg MaxSeg) M_blk (⟨s, by omega⟩, 0, false, false) σ_in 0
        (0, 2, false, false) σ₀ 0 (3 * M_blk) := by
  intro M_blk σ_in
  let go : ℕ → Fin (MaxSeg + 1) × Fin 3 × Bool × Bool := fun r =>
    (⟨if h : r ≤ MaxSeg then r else 0, by split_ifs <;> omega⟩, 0, false, false)
  have hgo_s : go s = (⟨s, by omega⟩, 0, false, false) := by simp [go, hs_m]
  have hgo_0 : go 0 = (0, 0, false, false) := by ext <;> simp [go]
  rcases blkGoToSeg_reMark_aux (blkIterSeg MaxSeg) segs (segMarkPred segs s k) σ₀ hws₀ go hs
      (by simp [go, hs_m, blkIterSeg])
      (fun r hr m b => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        simp [go, hr1, blkIterSeg, blkHome, blkData, blkSep])
      (fun r hr => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        have hr0 : r ≤ MaxSeg := by omega
        have hpos : 0 < (if h : r + 1 ≤ MaxSeg then r + 1 else 0) := by simp [hr1]
        simp only [go, blkIterSeg, ↓reduceIte, show blkSep ≠ blkHome by decide, dite_true, hpos]
        congr 1; ext <;> simp [hr1, hr0])
    with ⟨hiter_go, hbnd_go, hdir_go⟩
  rw [hgo_s, hgo_0] at hiter_go
  rw [hgo_s] at hbnd_go hdir_go
  have hsb := segStart_bound segs s hs
  have hs1 := segStart_pos segs s
  -- Skip `k` marked blocks in segment `s`
  have hskip : ∀ rem off, off + rem = k →
      blkIter (blkIterSeg MaxSeg) ((0, 0, false, false), σ_in, segStart segs s + off) rem =
        some ((0, 0, false, false), σ_in, segStart segs s + k) ∧
      (∀ i ≤ rem, ∀ q' σ' j',
        blkIter (blkIterSeg MaxSeg) ((0, 0, false, false), σ_in, segStart segs s + off) i = some (q', σ', j') → j' < M_blk) ∧
      (∀ i < rem, ∀ q' σ' j' q'' sym' dir,
        blkIter (blkIterSeg MaxSeg) ((0, 0, false, false), σ_in, segStart segs s + off) i = some (q', σ', j') →
        blkIterSeg MaxSeg q' (σ' j') = some (q'', sym', dir) →
        (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
    intro rem
    induction rem with
    | zero =>
      intro off hoff
      have : off = k := by omega
      subst off
      exact ⟨rfl, fun i hi _ _ _ heq => by obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi; cases heq; omega,
        fun i hi => by omega⟩
    | succ rem ih =>
      intro off hoff
      have hoff_L : off < (segs.getD s []).length := by omega
      have hbase : σ₀ (segStart segs s + off) = blkData false ((segs.getD s []).getD off false) :=
        (hws₀ _ (by omega)).trans (encodeWorkspace_seg_data segs hs hoff_L)
      have hSt : segMarkPred segs s k (segStart segs s + off) = true := by
        simp only [segMarkPred, segMarkRange, decide_eq_true_eq]; omega
      have hsym : σ_in (segStart segs s + off) = blkData true ((segs.getD s []).getD off false) := by
        dsimp only [σ_in, reMark]; rw [hbase, hSt]; rfl
      have hbs : blkIterSeg MaxSeg (0, 0, false, false) (σ_in (segStart segs s + off)) =
          some ((0, 0, false, false), σ_in (segStart segs s + off), QCSD_HeadDir.right) := by
        rw [hsym]; simp [blkIterSeg, blkHome, blkData]
      have hadd : segStart segs s + off + 1 = segStart segs s + (off + 1) := by omega
      rcases ih (off + 1) (by omega) with ⟨hit, hbd, hdr⟩
      refine ⟨?_, ?_, ?_⟩
      · simp only [blkIter, blkOnce, hbs, Function.update_eq_self, moveHead, hadd]; exact hit
      · intro i hi q' σ' j' hi_eq
        cases i with
        | zero => cases hi_eq; omega
        | succ i' =>
          simp only [blkIter, blkOnce, hbs, Function.update_eq_self, moveHead, hadd] at hi_eq
          exact hbd i' (by omega) q' σ' j' hi_eq
      · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
        cases i with
        | zero => cases hi_eq; rw [hbs] at hbs'; cases hbs'; exact ⟨by simp, fun _ => by omega⟩
        | succ i' =>
          simp only [blkIter, blkOnce, hbs, Function.update_eq_self, moveHead, hadd] at hi_eq
          exact hdr i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
  rcases hskip k 0 (Nat.zero_add k) with ⟨hiter_sk, hbnd_sk, hdir_sk⟩
  simp only [Nat.add_zero] at hiter_sk hbnd_sk hdir_sk
  split_ifs with hk_lt
  · -- `k < (segs.getD s []).length`: mark bit `k`, rewind with `ph = 1`
    let b := (segs.getD s []).getD k false
    have hbase : σ₀ (segStart segs s + k) = blkData false b :=
      (hws₀ _ (by omega)).trans (encodeWorkspace_seg_data segs hs hk_lt)
    have hSf : segMarkPred segs s k (segStart segs s + k) = false := by
      simp only [segMarkPred, segMarkRange, decide_eq_false_iff_not]; omega
    have hsym : σ_in (segStart segs s + k) = blkData false b := by
      dsimp only [σ_in]; rw [reMark_of_false _ hSf, hbase]
    have hbs : blkIterSeg MaxSeg (0, 0, false, false) (σ_in (segStart segs s + k)) =
        some ((0, 1, true, b), blkData true b, QCSD_HeadDir.left) := by
      rw [hsym]; simp [blkIterSeg, blkHome, blkData]
    have hupd : Function.update σ_in (segStart segs s + k) (blkData true b) =
        reMark (segMarkPred segs s (k + 1)) σ₀ := by
      funext j
      by_cases hj : j = segStart segs s + k
      · subst hj; rw [Function.update_self]
        have hSt : segMarkPred segs s (k + 1) (segStart segs s + k) = true := by
          simp only [segMarkPred, segMarkRange, decide_eq_true_eq]; omega
        dsimp only [reMark]; rw [hbase, hSt]; rfl
      · rw [Function.update_of_ne hj]
        have heq : segMarkPred segs s k j = segMarkPred segs s (k + 1) j := by
          simp only [segMarkPred, segMarkRange, Nat.add_zero]
          have hiff : (segStart segs s ≤ j ∧ j < segStart segs s + min k (segs.getD s []).length) ↔
              (segStart segs s ≤ j ∧ j < segStart segs s + min (k + 1) (segs.getD s []).length) := by omega
          simp only [hiff]
        simp [σ_in, reMark, heq]
    have hturn : blkIter (blkIterSeg MaxSeg) ((0, 0, false, false), σ_in, segStart segs s + k) 1 =
        some ((0, 1, true, b), reMark (segMarkPred segs s (k + 1)) σ₀, segStart segs s + k - 1) := by
      simp [blkIter, blkOnce, hbs, hupd, moveHead]
    have h0_at : reMark (segMarkPred segs s (k + 1)) σ₀ 0 = blkHome := by
      rw [reMark_home_iff, hws₀ 0 (by omega), encodeWorkspace_getD_zero]
    have hne_at : ∀ i, 1 ≤ i → i ≤ segStart segs s + k - 1 →
        reMark (segMarkPred segs s (k + 1)) σ₀ i ≠ blkHome := by
      intro i hi1 hi2; rw [ne_eq, reMark_home_iff, hws₀ i (by omega)]; exact encodeWorkspace_ne_home _ hi1 (by omega)
    rcases blkRewind_aux (blkIterSeg MaxSeg) M_blk (0, 1, true, b)
        (by simp [blkIterSeg]) (fun sym hne => by simp [blkIterSeg, hne])
        (segStart segs s + k - 1) (reMark (segMarkPred segs s (k + 1)) σ₀) (by omega) h0_at hne_at
      with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
    refine ⟨segStart segs s + k + 1 + (segStart segs s + k - 1), by omega, ?_, hnone_rw, ?_, ?_⟩
    · rw [blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
          hiter_sk, Option.bind_some, hturn, Option.bind_some, hiter_rw]
    · intro i hi q' σ' j' hi_eq
      by_cases hi1 : i ≤ segStart segs s
      · rcases blkIter_le_some hi1 hiter_go with ⟨⟨_, _, _⟩, hsub⟩
        rw [hsub] at hi_eq; cases hi_eq; exact hbnd_go i hi1 q' σ' j' hsub
      · by_cases hi2 : i ≤ segStart segs s + k
        · have heq : i = segStart segs s + (i - segStart segs s) := by omega
          rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
          exact hbnd_sk _ (by omega) q' σ' j' hi_eq
        · have heq : i = segStart segs s + k + 1 + (i - (segStart segs s + k + 1)) := by omega
          rw [heq, blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
              hiter_sk, Option.bind_some, hturn, Option.bind_some] at hi_eq
          exact hbnd_rw _ (by omega) q' σ' j' hi_eq
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      by_cases hi1 : i < segStart segs s
      · exact hdir_go i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
      · by_cases hi2 : i < segStart segs s + k
        · have heq : i = segStart segs s + (i - segStart segs s) := by omega
          rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
          exact hdir_sk _ (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
        · by_cases hi3 : i = segStart segs s + k
          · subst hi3
            rw [blkIter_add, hiter_go, Option.bind_some, hiter_sk] at hi_eq
            cases hi_eq; rw [hbs] at hbs'; cases hbs'; exact ⟨fun _ => by omega, by simp⟩
          · have heq : i = segStart segs s + k + 1 + (i - (segStart segs s + k + 1)) := by omega
            rw [heq, blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
                hiter_sk, Option.bind_some, hturn, Option.bind_some] at hi_eq
            exact hdir_rw _ (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
  · -- `k = (segs.getD s []).length`: hit `blkSep`/`blkWall`, rewind clearing ALL marks back to `σ₀`!
    have hkeq : k = (segs.getD s []).length := by omega
    have hend_sym : σ₀ (segStart segs s + k) = if s + 1 < segs.length then blkSep else blkWall := by
      have hd := encodeWorkspace_seg_end segs hs
      rw [← hkeq] at hd
      exact (hws₀ _ (by omega)).trans hd
    have hSf : segMarkPred segs s k (segStart segs s + k) = false := by
      simp only [segMarkPred, segMarkRange, decide_eq_false_iff_not]; omega
    have hsym_end : σ_in (segStart segs s + k) = if s + 1 < segs.length then blkSep else blkWall := by
      dsimp only [σ_in]; rw [reMark_of_false _ hSf, hend_sym]
    have hnot_data : (σ_in (segStart segs s + k)).1 = true := by
      rw [hsym_end]; split_ifs <;> rfl
    have hne_home : σ_in (segStart segs s + k) ≠ blkHome := by
      rw [hsym_end]; split_ifs <;> decide
    have hbs_end : blkIterSeg MaxSeg (0, 0, false, false) (σ_in (segStart segs s + k)) =
        some ((0, 2, false, false), σ_in (segStart segs s + k), QCSD_HeadDir.left) := by
      simp [blkIterSeg, hne_home, hnot_data]
    have hturn : blkIter (blkIterSeg MaxSeg) ((0, 0, false, false), σ_in, segStart segs s + k) 1 =
        some ((0, 2, false, false), σ_in, segStart segs s + k - 1) := by
      simp [blkIter, blkOnce, hbs_end, Function.update_eq_self, moveHead]
    -- Rewind clearing marks from `j` down to `0`, keeping `S_le j := fun i => segMarkPred segs s k i && decide (i ≤ j)`
    have hrew_clr : ∀ j, j ≤ segStart segs s + k - 1 →
        let S_j : ℕ → Bool := fun i => segMarkPred segs s k i && decide (i ≤ j)
        blkIter (blkIterSeg MaxSeg) ((0, 2, false, false), reMark S_j σ₀, j) j =
          some ((0, 2, false, false), σ₀, 0) ∧
        (∀ i ≤ j, ∀ q' σ' j',
          blkIter (blkIterSeg MaxSeg) ((0, 2, false, false), reMark S_j σ₀, j) i = some (q', σ', j') → j' < M_blk) ∧
        (∀ i < j, ∀ q' σ' j' q'' sym' dir,
          blkIter (blkIterSeg MaxSeg) ((0, 2, false, false), reMark S_j σ₀, j) i = some (q', σ', j') →
          blkIterSeg MaxSeg q' (σ' j') = some (q'', sym', dir) →
          (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
      intro j
      induction j with
      | zero =>
        intro _ S_0
        have hS0 : reMark S_0 σ₀ = σ₀ := by
          funext i
          apply reMark_of_false
          dsimp only [S_0, segMarkPred, segMarkRange]
          by_cases hi0 : i = 0
          · subst hi0
            have hnot : ¬ (segStart segs s + 0 ≤ 0 ∧ 0 < segStart segs s + min k (segs.getD s []).length) := by omega
            simp only [hnot, decide_false, Bool.false_and]
          · have hnot : ¬ (i ≤ 0) := by omega
            simp only [hnot, decide_false, Bool.and_false]
        rw [hS0]
        exact ⟨rfl, fun i hi _ _ _ heq => by obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi; cases heq; omega,
          fun i hi => by omega⟩
      | succ j ih =>
        intro hj S_j1
        have hne_h : reMark S_j1 σ₀ (j + 1) ≠ blkHome := by
          rw [ne_eq, reMark_home_iff, hws₀ (j + 1) (by omega)]
          exact encodeWorkspace_ne_home segs (by omega) (by omega)
        have hunm_eq : (if !(reMark S_j1 σ₀ (j + 1)).1 then blkData false (reMark S_j1 σ₀ (j + 1)).2.2
            else reMark S_j1 σ₀ (j + 1)) = σ₀ (j + 1) := by
          have hσ0_unm : ∀ sym, sym = (encodeWorkspace segs).getD (j + 1) blkHome →
              (if !sym.1 then blkData false sym.2.2 else sym) = sym := by
            intro sym hsym
            have hmem : (encodeWorkspace segs).getD (j + 1) blkHome ∈ encodeWorkspace segs := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
              exact List.getElem_mem _
            have hnot_mk : ∀ x ∈ encodeWorkspace segs, !x.1 → x.2.1 = false := by
              intro x hx
              simp only [encodeWorkspace, List.mem_cons] at hx
              rcases hx with rfl | hx
              · simp [blkHome]
              · -- Every element of `encodeSegmentsAux` is `blkData false _`, `blkSep`, or `blkWall`
                clear * - hx
                induction segs with
                | nil => simp [encodeSegmentsAux] at hx
                | cons hd tl ih_s =>
                  cases tl with
                  | nil =>
                    simp only [encodeSegmentsAux, List.mem_append, List.mem_map, List.mem_singleton] at hx
                    rcases hx with ⟨b, _, rfl⟩ | rfl <;> simp [blkData, blkWall]
                  | cons hd2 tl2 =>
                    simp only [encodeSegmentsAux, List.mem_append, List.mem_map, List.mem_singleton] at hx
                    rcases hx with (⟨b, _, rfl⟩ | rfl) | hrest
                    · simp [blkData]
                    · simp [blkSep]
                    · exact ih_s hrest
            rw [hsym]
            by_cases h1 : ((encodeWorkspace segs).getD (j + 1) blkHome).1 = false
            · have hm := hnot_mk _ hmem (by rw [h1]; rfl)
              rcases h_eq : (encodeWorkspace segs).getD (j + 1) blkHome with ⟨a, b, c⟩
              rw [h_eq] at h1 hm
              dsimp only at h1 hm
              subst h1; subst hm; rfl
            · have h1t : ((encodeWorkspace segs).getD (j + 1) blkHome).1 = true :=
                Bool.eq_true_of_not_eq_false h1
              simp only [h1t, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have h0 := hσ0_unm (σ₀ (j + 1)) (hws₀ (j + 1) (by omega))
          unfold reMark
          rcases h_eq : σ₀ (j + 1) with ⟨a, b, c⟩
          rw [h_eq] at h0
          clear * - h0
          cases a <;> cases b <;> cases c <;> cases S_j1 (j + 1) <;>
            first | rfl | exact h0
        have hbs : blkIterSeg MaxSeg (0, 2, false, false) (reMark S_j1 σ₀ (j + 1)) =
            some ((0, 2, false, false), σ₀ (j + 1), QCSD_HeadDir.left) := by
          rw [blkIterSeg]
          simp only [hne_h, ↓reduceIte, hunm_eq]
          rfl
        let S_j : ℕ → Bool := fun i => segMarkPred segs s k i && decide (i ≤ j)
        have hupd : Function.update (reMark S_j1 σ₀) (j + 1) (σ₀ (j + 1)) = reMark S_j σ₀ := by
          funext i
          by_cases hi : i = j + 1
          · subst hi; rw [Function.update_self, reMark_of_false _ (by dsimp only [S_j]; simp)]
          · rw [Function.update_of_ne hi]
            have heq : S_j1 i = S_j i := by
              dsimp only [S_j1, S_j]
              by_cases hle : i ≤ j
              · have hle1 : i ≤ j + 1 := by omega
                simp [hle, hle1]
              · have hle1 : ¬ (i ≤ j + 1) := by omega
                simp [hle, hle1]
            simp [reMark, heq]
        rcases ih (by omega) with ⟨hit, hbd, hdr⟩
        refine ⟨?_, ?_, ?_⟩
        · simp only [blkIter, blkOnce, hbs, hupd, moveHead, Nat.add_sub_cancel]; exact hit
        · intro i hi q' σ' j' hi_eq
          cases i with
          | zero => cases hi_eq; omega
          | succ i' =>
            simp only [blkIter, blkOnce, hbs, hupd, moveHead, Nat.add_sub_cancel] at hi_eq
            exact hbd i' (by omega) q' σ' j' hi_eq
        · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
          cases i with
          | zero => cases hi_eq; rw [hbs] at hbs'; cases hbs'; exact ⟨fun _ => by omega, by simp⟩
          | succ i' =>
            simp only [blkIter, blkOnce, hbs, hupd, moveHead, Nat.add_sub_cancel] at hi_eq
            exact hdr i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
    rcases hrew_clr (segStart segs s + k - 1) (Nat.le_refl _) with ⟨hiter_rw, hbnd_rw, hdir_rw⟩
    have hS_full : (fun i => segMarkPred segs s k i && decide (i ≤ segStart segs s + k - 1)) =
        segMarkPred segs s k := by
      funext i
      cases hmp : segMarkPred segs s k i
      · simp
      · simp only [Bool.true_and, decide_eq_true_eq]
        simp only [segMarkPred, segMarkRange, decide_eq_true_eq] at hmp
        omega
    rw [hS_full] at hiter_rw hbnd_rw hdir_rw
    have hnone_0 : blkIterSeg MaxSeg (0, 2, false, false) (σ₀ 0) = none := by
      have h0 : σ₀ 0 = blkHome := (hws₀ 0 (by omega)).trans (encodeWorkspace_getD_zero _)
      simp [blkIterSeg, h0]
    refine ⟨segStart segs s + k + 1 + (segStart segs s + k - 1), by omega, ?_, hnone_0, ?_, ?_⟩
    · rw [blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
          hiter_sk, Option.bind_some, hturn, Option.bind_some, hiter_rw]
    · intro i hi q' σ' j' hi_eq
      by_cases hi1 : i ≤ segStart segs s
      · rcases blkIter_le_some hi1 hiter_go with ⟨⟨_, _, _⟩, hsub⟩
        rw [hsub] at hi_eq; cases hi_eq; exact hbnd_go i hi1 q' σ' j' hsub
      · by_cases hi2 : i ≤ segStart segs s + k
        · have heq : i = segStart segs s + (i - segStart segs s) := by omega
          rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
          exact hbnd_sk _ (by omega) q' σ' j' hi_eq
        · have heq : i = segStart segs s + k + 1 + (i - (segStart segs s + k + 1)) := by omega
          rw [heq, blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
              hiter_sk, Option.bind_some, hturn, Option.bind_some] at hi_eq
          exact hbnd_rw _ (by omega) q' σ' j' hi_eq
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      by_cases hi1 : i < segStart segs s
      · exact hdir_go i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
      · by_cases hi2 : i < segStart segs s + k
        · have heq : i = segStart segs s + (i - segStart segs s) := by omega
          rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
          exact hdir_sk _ (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
        · by_cases hi3 : i = segStart segs s + k
          · subst hi3
            rw [blkIter_add, hiter_go, Option.bind_some, hiter_sk] at hi_eq
            cases hi_eq; rw [hbs_end] at hbs'; cases hbs'; exact ⟨fun _ => by omega, by simp⟩
          · have heq : i = segStart segs s + k + 1 + (i - (segStart segs s + k + 1)) := by omega
            rw [heq, blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
                hiter_sk, Option.bind_some, hturn, Option.bind_some] at hi_eq
            exact hdir_rw _ (by omega) q' σ' j' q'' sym' dir hi_eq hbs'

/-! #### `wsCopySegToLast` and `wsAppendSegLenBit` (built from `blkIterSeg` + `blkGrowLast`) -/

abbrev WsCopyLastQ (MaxSeg : ℕ) : Type :=
  LiftBlkQ (Fin (MaxSeg + 1) × Fin 3 × Bool × Bool) ⊕
    (Unit ⊕ (LiftBlkQ (Fin 3) ⊕ LiftBlkQ (Fin 3)))

def wsCopySegToLastBody (MaxSeg : ℕ) (overrideBit : Option Bool) : StepFn (WsCopyLastQ MaxSeg) :=
  seq0 (liftBlockStep (blkIterSeg MaxSeg))
    (sumStep (nopStep Unit)
      (sumStep (liftBlockStep (blkGrowLast (blkData false false)))
               (liftBlockStep (blkGrowLast (blkData false true)))))
    (fun q =>
      if q.1.2.2.1 then
        let b := overrideBit.getD q.1.2.2.2
        if b then Sum.inr (Sum.inr (liftBlkEntry 0))
        else Sum.inr (Sum.inl (liftBlkEntry 0))
      else Sum.inl ())

def wsCopySegToLastNext (MaxSeg : ℕ) (s : Fin (MaxSeg + 1)) :
    WsCopyLastQ MaxSeg → Option (WsCopyLastQ MaxSeg)
  | Sum.inr (Sum.inr _) => some (Sum.inl (liftBlkEntry (s, 0, false, false)))
  | _ => none

def wsCopySegToLast (MaxSeg : ℕ) (s : Fin (MaxSeg + 1)) (overrideBit : Option Bool) :
    StepFn (WsCopyLastQ MaxSeg) :=
  loop0 (wsCopySegToLastBody MaxSeg overrideBit) (wsCopySegToLastNext MaxSeg s)

theorem wsCopySegToLast_spec (MaxSeg B : ℕ) (s : Fin (MaxSeg + 1)) (overrideBit : Option Bool)
    (segs : List (List Bool)) (hs : s.val + 1 < segs.length)
    {τ₀ : ℕ → Bool}
    (htw₀ : TapeWS τ₀ (3 * (encodeWorkspace segs).length) B segs)
    (hclean₀ : ∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₀ p = false)
    (hB' : 3 * ((encodeWorkspace segs).length + (segs.getD s.val []).length) ≤ B) :
    let srcBits := segs.getD s.val []
    let appBits := match overrideBit with | none => srcBits | some b => List.replicate srcBits.length b
    let segs_end := segs.set (segs.length - 1) (segs.getD (segs.length - 1) [] ++ appBits)
    let M_end := (encodeWorkspace segs_end).length
    ∃ τ_end : ℕ → Bool,
      M_end = (encodeWorkspace segs).length + srcBits.length ∧
      TapeWS τ_end (3 * M_end) B segs_end ∧
      (∀ p, 3 * M_end ≤ p → τ_end p = false) ∧
      StepExec (wsCopySegToLast MaxSeg s overrideBit) B (Sum.inl (liftBlkEntry (s, 0, false, false)))
        (3 * (encodeWorkspace segs).length) τ₀ 0
        (Sum.inr (Sum.inl ())) (3 * M_end) τ_end 0
        ((srcBits.length + 1) * (36 * M_end + 30)) := by
  intro srcBits appBits segs_end M_end
  have hM_end_eq : M_end = (encodeWorkspace segs).length + srcBits.length := by
    have hne : segs ≠ [] := htw₀.1
    have hne' : segs_end ≠ [] := by
      intro h; have := congrArg List.length h; simp [segs_end] at this
      exact hne this
    have hlen_app : appBits.length = srcBits.length := by
      cases overrideBit <;> simp [appBits]
    have h1 : (encodeWorkspace segs_end).length = 1 + (segs_end.map (fun l => l.length + 1)).sum := by
      simp only [encodeWorkspace, List.length_cons, length_encodeSegmentsAux _ hne']; omega
    have h2 : (encodeWorkspace segs).length = 1 + (segs.map (fun l => l.length + 1)).sum := by
      simp only [encodeWorkspace, List.length_cons, length_encodeSegmentsAux _ hne]; omega
    -- Show sum increases by `appBits.length` when extending the last element
    have hsum : ∀ (L : List (List Bool)) (ext : List Bool), L ≠ [] →
        ((L.set (L.length - 1) (L.getD (L.length - 1) [] ++ ext)).map (fun l => l.length + 1)).sum =
        (L.map (fun l => l.length + 1)).sum + ext.length := by
      intro L ext
      induction L with
      | nil => intro h; contradiction
      | cons hd tl ih =>
        intro _
        cases tl with
        | nil => simp; omega
        | cons hd2 tl2 =>
          have hsub : (hd :: hd2 :: tl2).length - 1 = (hd2 :: tl2).length - 1 + 1 := by simp
          rw [hsub, List.set_cons_succ, List.getD_cons_succ, List.map_cons, List.sum_cons,
              List.map_cons, List.sum_cons, ih (by simp)]
          omega
    dsimp only [M_end, segs_end] at h1 ⊢
    rw [h1, h2, hsum segs appBits hne, hlen_app]; omega
  have hB_end : 3 * M_end ≤ B := by dsimp only [srcBits] at hM_end_eq; omega
  let S_it := 36 * M_end + 28
  have hloop : ∀ rem k, k + rem = srcBits.length →
      ∀ {τc : ℕ → Bool} {σ₀ : ℕ → BlkSym},
        let pfx_app := appBits.take k
        let segs_c := segs.set (segs.length - 1) (segs.getD (segs.length - 1) [] ++ pfx_app)
        let M_c := (encodeWorkspace segs_c).length
        M_c = (encodeWorkspace segs).length + k →
        MatchesWS σ₀ segs_c →
        readBlk τc = reMark (segMarkPred segs_c s.val k) σ₀ →
        (∀ p, 3 * M_c ≤ p → τc p = false) →
        ∃ τ_end : ℕ → Bool,
          TapeWS τ_end (3 * M_end) B segs_end ∧
          (∀ p, 3 * M_end ≤ p → τ_end p = false) ∧
          StepExec (wsCopySegToLast MaxSeg s overrideBit) B (Sum.inl (liftBlkEntry (s, 0, false, false)))
            (3 * M_c) τc 0 (Sum.inr (Sum.inl ())) (3 * M_end) τ_end 0
            ((rem + 1) * (S_it + 2)) := by
    intro rem
    induction rem with
    | zero =>
      intro k hk τc σ₀ pfx_app segs_c M_c hMc hws_c hread_c hcl_c
      have hkeq : k = srcBits.length := by omega
      subst hkeq
      have hlen_app : appBits.length = srcBits.length := by cases overrideBit <;> simp [appBits]
      have hpfx_eq : pfx_app = appBits := by dsimp only [pfx_app]; rw [← hlen_app, List.take_length]
      have hsegs_eq : segs_c = segs_end := by simp [segs_c, segs_end, hpfx_eq]
      have hMc_end : M_c = M_end := congrArg (fun l => (encodeWorkspace l).length) hsegs_eq
      have hseg_s : segs_c.getD s.val [] = srcBits := by
        dsimp only [segs_c]; rw [getD_set_ne_seg _ (by omega)]
      have hit := blkIterSeg_spec MaxSeg segs_c (s := s.val) (k := srcBits.length)
        (by simp [segs_c]; omega) (Nat.le_of_lt_succ s.isLt) (by rw [hseg_s]) σ₀ hws_c
      simp only [hseg_s, Nat.lt_irrefl, ↓reduceIte] at hit
      rw [← hread_c] at hit
      rcases liftBlockStep_spec (blkIterSeg MaxSeg) B M_c (3 * M_c) τc
          (s, 0, false, false) (0, 2, false, false) σ₀ 0 0 (3 * M_c)
          (Nat.le_refl _) (by omega) hit
        with ⟨τ_p, hread_p, hout_p, he_p⟩
      simp only [Nat.mul_zero] at he_p
      have hne_c : segs_c ≠ [] := by
        intro h; have := congrArg List.length h; simp [segs_c] at this; exact htw₀.1 this
      have hlen_pos : 1 ≤ 3 * M_c := by
        have := encodeWorkspace_len_ge2 segs_c hne_c; omega
      have he_nop := sumStep_inl_spec (nopStep Unit)
        (sumStep (liftBlockStep (blkGrowLast (blkData false false)))
                 (liftBlockStep (blkGrowLast (blkData false true))))
        (nopStep_spec (B := B) () (3 * M_c) τ_p 0 (by rw [hMc_end]; exact hB_end) (by omega))
      have he_body : StepExec (wsCopySegToLastBody MaxSeg overrideBit) B
          (Sum.inl (liftBlkEntry (s, 0, false, false))) (3 * M_c) τc 0
          (Sum.inr (Sum.inl ())) (3 * M_c) τ_p 0 S_it := by
        unfold wsCopySegToLastBody
        exact (seq0_spec hlen_pos he_p (by simpa [liftBlkExit] using he_nop)).weaken S_it
          (by dsimp only [S_it]; omega)
      have hdone : StepExec (wsCopySegToLast MaxSeg s overrideBit) B
          (Sum.inl (liftBlkEntry (s, 0, false, false))) (3 * M_c) τc 0
          (Sum.inr (Sum.inl ())) (3 * M_end) τ_p 0 ((0 + 1) * (S_it + 2)) := by
        rw [← hMc_end]
        exact (loop0_done (next := wsCopySegToLastNext MaxSeg s) he_body rfl).weaken
          ((0 + 1) * (S_it + 2)) (by omega)
      have hne_end : segs_end ≠ [] := by
        intro h; have := congrArg List.length h; simp [segs_end] at this; exact htw₀.1 this
      refine ⟨τ_p, ⟨hne_end, Nat.le_refl _, hB_end, ?_⟩, ?_, hdone⟩
      · rw [hread_p, ← hsegs_eq]; exact hws_c
      · intro p hp; rw [hout_p p (by omega)]; exact hcl_c p (by omega)
    | succ rem ih =>
      intro k hk τc σ₀ pfx_app segs_c M_c hMc hws_c hread_c hcl_c
      have hseg_s : segs_c.getD s.val [] = srcBits := by
        dsimp only [segs_c]; rw [getD_set_ne_seg _ (by omega)]
      have hk_lt : k < srcBits.length := by omega
      have hne_c : segs_c ≠ [] := by
        intro h; have := congrArg List.length h; simp [segs_c] at this; exact htw₀.1 this
      have hit := blkIterSeg_spec MaxSeg segs_c (s := s.val) (k := k)
        (by simp [segs_c]; omega) (Nat.le_of_lt_succ s.isLt) (by rw [hseg_s]; omega) σ₀ hws_c
      simp only [hseg_s, hk_lt, ↓reduceIte] at hit
      rw [← hread_c] at hit
      rcases liftBlockStep_spec (blkIterSeg MaxSeg) B M_c (3 * M_c) τc
          (s, 0, false, false) (0, 1, true, srcBits.getD k false)
          (reMark (segMarkPred segs_c s.val (k + 1)) σ₀) 0 0 (3 * M_c)
          (Nat.le_refl _) (by omega) hit
        with ⟨τ_p, hread_p, hout_p, he_p⟩
      simp only [Nat.mul_zero] at he_p
      let b_out := overrideBit.getD (srcBits.getD k false)
      have hb_app : appBits.take (k + 1) = pfx_app ++ [b_out] := by
        dsimp only [pfx_app, b_out, appBits]
        cases overrideBit with
        | none =>
          simp only [Option.getD_none]
          rw [List.take_succ_eq_append_getElem hk_lt]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt]
        | some b =>
          simp only [Option.getD_some]
          rw [List.take_replicate, List.take_replicate,
              Nat.min_eq_left (by omega : k + 1 ≤ srcBits.length),
              Nat.min_eq_left (by omega : k ≤ srcBits.length),
              List.replicate_succ']
      let segs_next := segs.set (segs.length - 1) (segs.getD (segs.length - 1) [] ++ appBits.take (k + 1))
      have hnext_set : segs_next = segs_c.set (segs_c.length - 1) (segs_c.getD (segs_c.length - 1) [] ++ [b_out]) := by
        dsimp only [segs_next, segs_c]
        have hlen_c : (segs.set (segs.length - 1) (segs.getD (segs.length - 1) [] ++ pfx_app)).length = segs.length := by simp
        rw [hlen_c, getD_set_self_seg _ (by omega), List.set_set, List.append_assoc, hb_app]
      have hne_next : segs_next ≠ [] := by
        intro h; have := congrArg List.length h; simp [segs_next] at this; exact htw₀.1 this
      have hws_next_eq : encodeWorkspace segs_next =
          (encodeWorkspace segs_c).take ((encodeWorkspace segs_c).length - 1) ++
            [blkData false b_out, blkWall] := by
        rw [hnext_set]; exact encodeWorkspace_extend_last_bit b_out segs_c hne_c
      have hS_hi : ∀ j, (encodeWorkspace segs_c).length - 1 ≤ j → segMarkPred segs_c s.val (k + 1) j = false := by
        intro j hj
        have hs_lt_c : s.val + 1 < segs_c.length := by simp [segs_c]; omega
        have hsb := segStart_bound segs_c s.val (by omega)
        have hss_succ := segStart_succ_eq segs_c hs_lt_c
        have hsb1 := segStart_bound segs_c (s.val + 1) hs_lt_c
        simp only [segMarkPred, segMarkRange, decide_eq_false_iff_not]; omega
      rcases blkGrowLast_reMark_spec B (blkData false b_out) (by simp [blkData, blkHome]) segs_c segs_next
          (segMarkPred segs_c s.val (k + 1)) hws_next_eq hne_c hne_next hS_hi
          hws_c hread_p (by omega)
        with ⟨τ_g, σ₂, hws₂, hread₂, hM_g, hout_g, he_g⟩
      -- Show `segMarkPred segs_c s (k+1) = segMarkPred segs_next s (k+1)` because `s < last`
      have hpred_eq : segMarkPred segs_c s.val (k + 1) = segMarkPred segs_next s.val (k + 1) := by
        have hss_eq : segStart segs_next s.val = segStart segs_c s.val := by
          rw [hnext_set]
          have haux_ss : ∀ (L : List (List Bool)) (idx : ℕ) (newLast : List Bool),
              idx + 1 < L.length →
              segStart (L.set (L.length - 1) newLast) idx = segStart L idx := by
            intro L
            induction L with
            | nil => intro _ _ h; simp at h
            | cons hd tl ih_l =>
              intro idx newLast hidx
              cases tl with
              | nil => simp at hidx
              | cons hd2 tl2 =>
                have hsub : (hd :: hd2 :: tl2).length - 1 = (hd2 :: tl2).length - 1 + 1 := by simp
                rw [hsub, List.set_cons_succ]
                cases idx with
                | zero => rfl
                | succ idx' =>
                  simp only [segStart]
                  congr 1
                  exact ih_l idx' newLast (by simp at hidx ⊢; omega)
          exact haux_ss segs_c s.val _ (by simp [segs_c]; omega)
        have hget_eq : segs_next.getD s.val [] = segs_c.getD s.val [] := by
          rw [hnext_set, getD_set_ne_seg _ (by simp [segs_c]; omega)]
        funext j; simp only [segMarkPred, segMarkRange, hss_eq, hget_eq]
      rw [hpred_eq] at hread₂
      have hlen_p_pos : 1 ≤ 3 * M_c := by have := encodeWorkspace_len_ge2 segs_c hne_c; omega
      have he_body : ∃ q_g, StepExec (wsCopySegToLastBody MaxSeg overrideBit) B
          (Sum.inl (liftBlkEntry (s, 0, false, false))) (3 * M_c) τc 0
          (Sum.inr (Sum.inr q_g)) (3 * (encodeWorkspace segs_next).length) τ_g 0 S_it := by
        cases hb : b_out with
        | false =>
          rw [hb] at he_g
          have he_branch := sumStep_inr_spec (nopStep Unit)
            (sumStep (liftBlockStep (blkGrowLast (blkData false false)))
                     (liftBlockStep (blkGrowLast (blkData false true))))
            (sumStep_inl_spec (liftBlockStep (blkGrowLast (blkData false false)))
              (liftBlockStep (blkGrowLast (blkData false true))) he_g)
          refine ⟨Sum.inl (liftBlkExit 2), ?_⟩
          unfold wsCopySegToLastBody
          have he_branch' : StepExec (sumStep (nopStep Unit)
              (sumStep (liftBlockStep (blkGrowLast (blkData false false)))
                       (liftBlockStep (blkGrowLast (blkData false true))))) B
              (if (liftBlkExit (0, 1, true, srcBits.getD k false)).1.2.2.1 then
                let b := overrideBit.getD (liftBlkExit (0, 1, true, srcBits.getD k false)).1.2.2.2
                if b then Sum.inr (Sum.inr (liftBlkEntry 0)) else Sum.inr (Sum.inl (liftBlkEntry 0))
              else Sum.inl ())
              (3 * M_c) τ_p 0
              (Sum.inr (Sum.inl (liftBlkExit 2))) (3 * (encodeWorkspace segs_next).length) τ_g 0
              (14 * (encodeWorkspace segs_c).length + 18) := by
            change StepExec _ B (if true then if b_out then _ else _ else _) _ _ _ _ _ _ _ _
            simp only [hb, Bool.false_eq_true, ↓reduceIte]
            exact he_branch
          have hseq := seq0_spec (f := fun q : LiftBlkQ (Fin (MaxSeg + 1) × Fin 3 × Bool × Bool) =>
              if q.1.2.2.1 then
                let b := overrideBit.getD q.1.2.2.2
                if b then Sum.inr (Sum.inr (liftBlkEntry 0)) else Sum.inr (Sum.inl (liftBlkEntry 0))
              else Sum.inl ())
            hlen_p_pos he_p he_branch'
          exact hseq.weaken S_it (by dsimp only [S_it]; omega)
        | true =>
          rw [hb] at he_g
          have he_branch := sumStep_inr_spec (nopStep Unit)
            (sumStep (liftBlockStep (blkGrowLast (blkData false false)))
                     (liftBlockStep (blkGrowLast (blkData false true))))
            (sumStep_inr_spec (liftBlockStep (blkGrowLast (blkData false false)))
              (liftBlockStep (blkGrowLast (blkData false true))) he_g)
          refine ⟨Sum.inr (liftBlkExit 2), ?_⟩
          unfold wsCopySegToLastBody
          have he_branch' : StepExec (sumStep (nopStep Unit)
              (sumStep (liftBlockStep (blkGrowLast (blkData false false)))
                       (liftBlockStep (blkGrowLast (blkData false true))))) B
              (if (liftBlkExit (0, 1, true, srcBits.getD k false)).1.2.2.1 then
                let b := overrideBit.getD (liftBlkExit (0, 1, true, srcBits.getD k false)).1.2.2.2
                if b then Sum.inr (Sum.inr (liftBlkEntry 0)) else Sum.inr (Sum.inl (liftBlkEntry 0))
              else Sum.inl ())
              (3 * M_c) τ_p 0
              (Sum.inr (Sum.inr (liftBlkExit 2))) (3 * (encodeWorkspace segs_next).length) τ_g 0
              (14 * (encodeWorkspace segs_c).length + 18) := by
            change StepExec _ B (if true then if b_out then _ else _ else _) _ _ _ _ _ _ _ _
            simp only [hb, ↓reduceIte]
            exact he_branch
          have hseq := seq0_spec (f := fun q : LiftBlkQ (Fin (MaxSeg + 1) × Fin 3 × Bool × Bool) =>
              if q.1.2.2.1 then
                let b := overrideBit.getD q.1.2.2.2
                if b then Sum.inr (Sum.inr (liftBlkEntry 0)) else Sum.inr (Sum.inl (liftBlkEntry 0))
              else Sum.inl ())
            hlen_p_pos he_p he_branch'
          exact hseq.weaken S_it (by dsimp only [S_it]; omega)
      rcases he_body with ⟨q_g, he_b⟩
      have hcl_g : ∀ p, 3 * (encodeWorkspace segs_next).length ≤ p → τ_g p = false := by
        intro p hp; rw [hout_g p (by omega), hout_p p (by omega)]; exact hcl_c p (by omega)
      have hM_next : (encodeWorkspace segs_next).length = (encodeWorkspace segs).length + (k + 1) := by
        dsimp only [M_c] at hM_g hMc; omega
      rcases ih (k + 1) (by omega) hM_next hws₂ hread₂ hcl_g with ⟨τ_end, htw_end, hcl_end, he_rest⟩
      have hlen_g_pos : 1 ≤ 3 * (encodeWorkspace segs_next).length := by omega
      have hcomb := (loop0_step (next := wsCopySegToLastNext MaxSeg s) hlen_g_pos he_b rfl he_rest).weaken
        ((rem + 1 + 1) * (S_it + 2)) (by
          have : (rem + 1 + 1) * (S_it + 2) = (S_it + 2) + (rem + 1) * (S_it + 2) := by ring
          omega)
      exact ⟨τ_end, htw_end, hcl_end, hcomb⟩
  have hsegs0 : segs.set (segs.length - 1) (segs.getD (segs.length - 1) [] ++ appBits.take 0) = segs := by
    simp only [List.take_zero, List.append_nil]
    apply List.ext_getElem (by simp)
    intro idx h1 h2
    rw [List.getElem_set]
    split_ifs with heq
    · subst heq; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    · rfl
  have hread0 : readBlk τ₀ = reMark (segMarkPred segs s.val 0) (readBlk τ₀) := by
    funext j; exact (reMark_of_false _ (by simp [segMarkPred, segMarkRange])).symm
  have hres := hloop srcBits.length 0 (Nat.zero_add _) (τc := τ₀) (σ₀ := readBlk τ₀)
    (by rw [hsegs0, Nat.add_zero]) (by rw [hsegs0]; exact htw₀.2.2.2) (by rw [hsegs0]; exact hread0)
    (by rw [hsegs0]; exact hclean₀)
  simp only [hsegs0] at hres
  rcases hres with ⟨τ_end, htw_end, hcl_end, he_tot⟩
  exact ⟨τ_end, hM_end_eq, htw_end, hcl_end, he_tot⟩

/-! #### Marked `wsInc_marked_spec` and `wsAddSegLen` -/

theorem wsInc_marked_spec (MaxSeg B : ℕ) (segs : List (List Bool)) {arrSeg k s w v : ℕ}
    (harr_s : arrSeg < s) (hs : s < segs.length) (hs_max : s ≤ MaxSeg)
    (hseg : segs.getD s [] = natToBitsLE w v) (hv : v + 1 < 2 ^ w)
    {len : ℕ} {τ₁ : ℕ → Bool} (htw : TapeMarkedWS τ₁ len B segs arrSeg k) :
    ∃ τ₂ : ℕ → Bool,
      TapeMarkedWS τ₂ len B (segs.set s (natToBitsLE w (v + 1))) arrSeg k ∧
      (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (wsInc MaxSeg) B (wsIncEntry MaxSeg ⟨s, by omega⟩) len τ₁ 0
        (liftBlkExit (0, true)) len τ₂ 0 (21 * (encodeWorkspace segs).length + 4) := by
  rcases htw with ⟨hsegs, hW_le, hlen_B, σ₀, hws₀, hread₁⟩
  let M_blk := (encodeWorkspace segs).length
  let S := segMarkPred segs arrSeg k
  let go : ℕ → Fin (MaxSeg + 1) × Bool := fun r =>
    (⟨if h : r ≤ MaxSeg then r else 0, by split_ifs <;> omega⟩, false)
  have hgo_s : go s = (⟨s, by omega⟩, false) := by simp [go, hs_max]
  have hgo_0 : go 0 = (0, false) := by ext <;> simp [go]
  rcases blkGoToSeg_reMark_aux (blkTransformSeg MaxSeg stepBitInc) segs S σ₀ hws₀ go hs
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
  rcases blkTransformSeg_scan_aux MaxSeg stepBitInc segs hs (segs.getD s []) [] σ₀ (by simp) hws0_unm
    with ⟨σ_end₀, hws_end₀, k_sc, hk_sc, hiter_sc₀, _, hbnd_sc₀, hdir_sc₀⟩
  simp only [List.nil_append, List.length_nil, Nat.add_zero] at hws_end₀ hiter_sc₀ hbnd_sc₀ hdir_sc₀
  rw [hseg, applyTransform_inc, incBits_natToBitsLE hv] at hws_end₀
  have hS_after : ∀ j, segStart segs s ≤ j → S j = false := by
    intro j hj
    have hmono := segStart_mono segs (show arrSeg + 1 ≤ s by omega) hs
    have hsucc_arr := segStart_succ_eq segs (show arrSeg + 1 < segs.length by omega)
    simp only [S, segMarkPred, segMarkRange, decide_eq_false_iff_not]; omega
  have hscan_map := blkIter_transform_reMark_scan MaxSeg stepBitInc S (segStart segs s) hS_after
  have hsb := segStart_bound segs s hs
  have hexec_inc : BlkExec (blkTransformSeg MaxSeg stepBitInc) M_blk
      (⟨s, by omega⟩, false) (readBlk τ₁) 0 (0, true) (reMark S σ_end₀) 0 (3 * M_blk) := by
    rw [hread₁]
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
      · rcases blkIter_le_some hi1 hiter_go with ⟨⟨_, _, _⟩, hsub⟩
        rw [hsub] at hi_eq; cases hi_eq; exact hbnd_go i hi1 q' σ' j' hsub
      · have heq : i = segStart segs s + (i - segStart segs s) := by omega
        rw [heq, blkIter_add, hiter_go, Option.bind_some,
            (hscan_map _ false σ₀ (segStart segs s) (fun _ => Nat.le_refl _)).1] at hi_eq
        rcases hsub : blkIter (blkTransformSeg MaxSeg stepBitInc) ((0, false), σ₀, segStart segs s)
            (i - segStart segs s) with _ | ⟨qi, σi, ji⟩
        · rw [hsub] at hi_eq; simp at hi_eq
        · rw [hsub] at hi_eq; cases hi_eq; exact hbnd_sc₀ (i - segStart segs s) (by omega) q' σi j' hsub
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      by_cases hi1 : i < segStart segs s
      · exact hdir_go i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
      · have heq : i = segStart segs s + (i - segStart segs s) := by omega
        rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
        rcases hscan_map (i - segStart segs s) false σ₀ (segStart segs s) (fun _ => Nat.le_refl _)
          with ⟨hsub_map, hsub_inv⟩
        rw [hsub_map] at hi_eq
        rcases hsub : blkIter (blkTransformSeg MaxSeg stepBitInc) ((0, false), σ₀, segStart segs s)
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
              have hbs0 : blkTransformSeg MaxSeg stepBitInc (rem_i, true) (σi j') =
                  some ((rem_i, true), σi j', QCSD_HeadDir.left) := by simp [blkTransformSeg, hhome]
              rw [← hbs'.2.2]
              exact hdir_sc₀ (i - segStart segs s) (by omega) (rem_i, true) σi j' _ _ _ hsub hbs0
  rcases liftBlockStep_spec (blkTransformSeg MaxSeg stepBitInc) B M_blk len τ₁
      (⟨s, by omega⟩, false) (0, true) (reMark S σ_end₀) 0 0 (3 * M_blk) hW_le hlen_B hexec_inc
    with ⟨τ₂, hread₂, hout₂, he₂⟩
  simp only [Nat.mul_zero] at he₂
  let segs' := segs.set s (natToBitsLE w (v + 1))
  have hlen_s' : (natToBitsLE w (v + 1)).length = (segs.getD s []).length := by
    rw [hseg, length_natToBitsLE, length_natToBitsLE]
  have hM' : (encodeWorkspace segs').length = M_blk := length_encodeWorkspace_set hs hlen_s'
  have hS_eq : segMarkPred segs' arrSeg k = S := by
    funext j
    simp only [S, segs', segMarkPred, segMarkRange,
      segStart_set_eq segs s arrSeg _ hs hlen_s',
      getD_set_ne_seg segs (by omega : s ≠ arrSeg)]
  have hne_set : segs' ≠ [] := by simp [segs', hsegs]
  exact ⟨τ₂, ⟨hne_set, by rw [hM']; exact hW_le, hlen_B, σ_end₀, hws_end₀, by rw [hread₂, hS_eq]⟩,
    hout₂, he₂.weaken (21 * M_blk + 4) (by omega)⟩

abbrev WsAddSegLenQ (MaxSeg mult : ℕ) : Type :=
  LiftBlkQ (Fin (MaxSeg + 1) × Fin 3 × Bool × Bool) ⊕
    (Unit ⊕ Repeat0Q mult (LiftBlkQ (Fin (MaxSeg + 1) × Bool)))

def wsAddSegLenBody (MaxSeg mult : ℕ) (dst : Fin (MaxSeg + 1)) : StepFn (WsAddSegLenQ MaxSeg mult) :=
  seq0 (liftBlockStep (blkIterSeg MaxSeg))
    (sumStep (nopStep Unit) (repeat0 mult (wsInc MaxSeg) (wsIncEntry MaxSeg dst)))
    (fun q => if q.1.2.2.1 then Sum.inr (repeat0Entry mult (wsIncEntry MaxSeg dst)) else Sum.inl ())

def wsAddSegLenNext (MaxSeg mult : ℕ) (s : Fin (MaxSeg + 1)) :
    WsAddSegLenQ MaxSeg mult → Option (WsAddSegLenQ MaxSeg mult)
  | Sum.inr (Sum.inr _) => some (Sum.inl (liftBlkEntry (s, 0, false, false)))
  | _ => none

def wsAddSegLen (MaxSeg mult : ℕ) (s dst : Fin (MaxSeg + 1)) : StepFn (WsAddSegLenQ MaxSeg mult) :=
  loop0 (wsAddSegLenBody MaxSeg mult dst) (wsAddSegLenNext MaxSeg mult s)

theorem wsAddSegLen_spec (MaxSeg mult B w v : ℕ) (s dst : Fin (MaxSeg + 1))
    (segs : List (List Bool)) (hs_dst : s.val < dst.val) (hdst : dst.val < segs.length)
    (hseg_dst : segs.getD dst.val [] = natToBitsLE w v)
    (hv_bound : v + mult * (segs.getD s.val []).length < 2 ^ w)
    {len : ℕ} {τ₀ : ℕ → Bool} (htw₀ : TapeWS τ₀ len B segs) :
    let M_blk := (encodeWorkspace segs).length
    let L_s := (segs.getD s.val []).length
    ∃ τ_end : ℕ → Bool,
      TapeWS τ_end len B (segs.set dst.val (natToBitsLE w (v + mult * L_s))) ∧
      (∀ p, 3 * M_blk ≤ p → τ_end p = τ₀ p) ∧
      StepExec (wsAddSegLen MaxSeg mult s dst) B (Sum.inl (liftBlkEntry (s, 0, false, false))) len τ₀ 0
        (Sum.inr (Sum.inl ())) len τ_end 0
        ((L_s + 1) * (21 * M_blk + 6 + mult * (21 * M_blk + 6) + 2)) := by
  intro M_blk L_s
  have hlen_pos := TapeWS_pos htw₀
  have hlen_B := htw₀.2.2.1
  let S_it := 21 * M_blk + 6 + mult * (21 * M_blk + 6)
  have hloop : ∀ rem k, k + rem = L_s →
      ∀ {τc : ℕ → Bool},
        let segs_c := segs.set dst.val (natToBitsLE w (v + mult * k))
        TapeMarkedWS τc len B segs_c s.val k →
        ∃ τ_end : ℕ → Bool,
          TapeWS τ_end len B (segs.set dst.val (natToBitsLE w (v + mult * L_s))) ∧
          (∀ p, 3 * M_blk ≤ p → τ_end p = τc p) ∧
          StepExec (wsAddSegLen MaxSeg mult s dst) B (Sum.inl (liftBlkEntry (s, 0, false, false))) len τc 0
            (Sum.inr (Sum.inl ())) len τ_end 0 ((rem + 1) * (S_it + 2)) := by
    intro rem
    induction rem with
    | zero =>
      intro k hk τc segs_c htm_c
      have hkeq : k = L_s := by omega
      subst hkeq
      rcases htm_c with ⟨hne_c, hW_c, hlen_Bc, σ₀, hws_c, hread_c⟩
      have hMc : (encodeWorkspace segs_c).length = M_blk :=
        length_encodeWorkspace_set hdst (by rw [hseg_dst, length_natToBitsLE, length_natToBitsLE])
      have hseg_s : segs_c.getD s.val [] = segs.getD s.val [] := getD_set_ne_seg segs (by omega : dst.val ≠ s.val) _
      have hit := blkIterSeg_spec MaxSeg segs_c (s := s.val) (k := L_s)
        (by simp [segs_c]; omega) (Nat.le_of_lt_succ s.isLt) (by rw [hseg_s]) σ₀ hws_c
      have hnl : ¬ (L_s < (segs_c.getD s.val []).length) := by rw [hseg_s]; exact Nat.lt_irrefl _
      simp only [hnl, ↓reduceIte] at hit
      rw [← hread_c, hMc] at hit
      rcases liftBlockStep_spec (blkIterSeg MaxSeg) B M_blk len τc
          (s, 0, false, false) (0, 2, false, false) σ₀ 0 0 (3 * M_blk)
          (by rwa [← hMc]) hlen_Bc (by exact hit)
        with ⟨τ_p, hread_p, hout_p, he_p⟩
      simp only [Nat.mul_zero] at he_p
      have he_nop := sumStep_inl_spec (nopStep Unit) (repeat0 mult (wsInc MaxSeg) (wsIncEntry MaxSeg dst))
        (nopStep_spec () len τ_p 0 hlen_Bc (by omega))
      have he_body : StepExec (wsAddSegLenBody MaxSeg mult dst) B
          (Sum.inl (liftBlkEntry (s, 0, false, false))) len τc 0
          (Sum.inr (Sum.inl ())) len τ_p 0 S_it := by
        unfold wsAddSegLenBody
        exact (seq0_spec hlen_pos he_p (by simpa [liftBlkExit] using he_nop)).weaken S_it
          (by dsimp only [S_it]; omega)
      have hdone := (loop0_done (next := wsAddSegLenNext MaxSeg mult s) he_body rfl).weaken
        ((0 + 1) * (S_it + 2)) (by omega)
      exact ⟨τ_p, ⟨hne_c, hW_c, hlen_Bc, by rw [hread_p]; exact hws_c⟩, hout_p, hdone⟩
    | succ rem ih =>
      intro k hk τc segs_c htm_c
      rcases htm_c with ⟨hne_c, hW_c, hlen_Bc, σ₀, hws_c, hread_c⟩
      have hMc : (encodeWorkspace segs_c).length = M_blk :=
        length_encodeWorkspace_set hdst (by rw [hseg_dst, length_natToBitsLE, length_natToBitsLE])
      have hseg_s : segs_c.getD s.val [] = segs.getD s.val [] := getD_set_ne_seg segs (by omega : dst.val ≠ s.val) _
      have hk_lt : k < (segs.getD s.val []).length := by dsimp only [L_s] at hk; omega
      have hit := blkIterSeg_spec MaxSeg segs_c (s := s.val) (k := k)
        (by simp [segs_c]; omega) (Nat.le_of_lt_succ s.isLt) (by rw [hseg_s]; omega) σ₀ hws_c
      simp only [hseg_s, hk_lt, ↓reduceIte] at hit
      rw [← hread_c, hMc] at hit
      rcases liftBlockStep_spec (blkIterSeg MaxSeg) B M_blk len τc
          (s, 0, false, false) (0, 1, true, (segs.getD s.val []).getD k false)
          (reMark (segMarkPred segs_c s.val (k + 1)) σ₀) 0 0 (3 * M_blk)
          (by rwa [← hMc]) hlen_Bc (by exact hit)
        with ⟨τ_p, hread_p, hout_p, he_p⟩
      simp only [Nat.mul_zero] at he_p
      -- Run `repeat0 mult (wsInc MaxSeg) (wsIncEntry MaxSeg dst)` maintaining `TapeMarkedWS ... s (k+1)`!
      let InvI : ℕ → ℕ → (ℕ → Bool) → Prop := fun j l_cur τ_cur =>
        l_cur = len ∧
        TapeMarkedWS τ_cur len B (segs.set dst.val (natToBitsLE w (v + mult * k + j))) s.val (k + 1) ∧
        (∀ p, 3 * M_blk ≤ p → τ_cur p = τ_p p)
      have hinc_step : ∀ j < mult, ∀ l_cur τ_cur, InvI j l_cur τ_cur →
          ∃ q_e l' τ', InvI (j + 1) l' τ' ∧ 1 ≤ l' ∧
            StepExec (wsInc MaxSeg) B (wsIncEntry MaxSeg dst) l_cur τ_cur 0 q_e l' τ' 0 (21 * M_blk + 4) := by
        intro j hj l_cur τ_cur ⟨hl_eq, htm_j, hout_j⟩
        subst l_cur
        let segs_j := segs.set dst.val (natToBitsLE w (v + mult * k + j))
        have hMj : (encodeWorkspace segs_j).length = M_blk :=
          length_encodeWorkspace_set hdst (by rw [hseg_dst, length_natToBitsLE, length_natToBitsLE])
        have hv_lt : v + mult * k + j + 1 < 2 ^ w := by
          have : mult * k + j + 1 ≤ mult * L_s := by
            have : mult * (k + 1) ≤ mult * L_s := Nat.mul_le_mul_left mult (by omega)
            rw [Nat.mul_add, Nat.mul_one] at this; omega
          dsimp only [L_s] at this; omega
        rcases wsInc_marked_spec MaxSeg B segs_j hs_dst (by simp [segs_j]; omega)
            (Nat.le_of_lt_succ dst.isLt) (getD_set_self_seg segs hdst _) hv_lt htm_j
          with ⟨τ_j', htm_j', hout_j', he_j⟩
        rw [hMj] at hout_j' he_j
        simp only [segs_j, List.set_set] at htm_j'
        rw [show v + mult * k + j + 1 = v + mult * k + (j + 1) by omega] at htm_j'
        exact ⟨_, len, τ_j', ⟨rfl, htm_j', fun p hp => (hout_j' p hp).trans (hout_j p hp)⟩, hlen_pos, he_j⟩
      rcases repeat0_spec mult (wsInc MaxSeg) (wsIncEntry MaxSeg dst) B (21 * M_blk + 4) InvI hinc_step
          (fun _ _ ⟨hl_eq, _⟩ => ⟨hl_eq ▸ hlen_Bc, by omega⟩)
          ⟨rfl, ⟨hne_c, hW_c, hlen_Bc, σ₀, hws_c, hread_p⟩, fun _ _ => rfl⟩
        with ⟨len_m, τ_m, ⟨hlen_m_eq, htm_m, hout_m⟩, he_rep⟩
      subst len_m
      have he_inr := sumStep_inr_spec (nopStep Unit) (repeat0 mult (wsInc MaxSeg) (wsIncEntry MaxSeg dst)) he_rep
      have he_body : StepExec (wsAddSegLenBody MaxSeg mult dst) B
          (Sum.inl (liftBlkEntry (s, 0, false, false))) len τc 0
          (Sum.inr (Sum.inr (repeat0Exit mult))) len τ_m 0 S_it := by
        unfold wsAddSegLenBody
        have hseq := seq0_spec
          (f := fun q : LiftBlkQ (Fin (MaxSeg + 1) × Fin 3 × Bool × Bool) =>
            if q.1.2.2.1 then Sum.inr (repeat0Entry mult (wsIncEntry MaxSeg dst)) else Sum.inl ())
          hlen_pos he_p (by simpa [liftBlkExit] using he_inr)
        exact hseq.weaken S_it (by
          dsimp only [S_it]
          have : 21 * M_blk + 4 + 2 = 21 * M_blk + 6 := by omega
          rw [this]; omega)
      have hmul_eq : v + mult * k + mult = v + mult * (k + 1) := by ring
      rw [hmul_eq] at htm_m
      rcases ih (k + 1) (by omega) htm_m with ⟨τ_end, htw_end, hout_end, he_rest⟩
      have hcomb := (loop0_step (next := wsAddSegLenNext MaxSeg mult s) hlen_pos he_body rfl he_rest).weaken
        ((rem + 1 + 1) * (S_it + 2)) (by
          have : (rem + 1 + 1) * (S_it + 2) = (S_it + 2) + (rem + 1) * (S_it + 2) := by ring
          omega)
      exact ⟨τ_end, htw_end, fun p hp => (hout_end p hp).trans ((hout_m p hp).trans (hout_p p hp)), hcomb⟩
  have hsegs0 : segs.set dst.val (natToBitsLE w (v + mult * 0)) = segs := by
    simp only [Nat.mul_zero, Nat.add_zero]
    apply List.ext_getElem (by simp)
    intro idx h1 h2
    rw [List.getElem_set]
    split_ifs with heq
    · subst heq
      have := hseg_dst
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at this
      exact this.symm
    · rfl
  have htm0 : TapeMarkedWS τ₀ len B (segs.set dst.val (natToBitsLE w (v + mult * 0))) s.val 0 := by
    rw [hsegs0]
    exact ⟨htw₀.1, htw₀.2.1, htw₀.2.2.1, readBlk τ₀, htw₀.2.2.2,
      by funext j; exact (reMark_of_false _ (by simp [segMarkPred, segMarkRange])).symm⟩
  exact hloop L_s 0 (Nat.zero_add _) htm0

/-! #### `blkLoadConst`: load any `K : ℕ` in binary in ONE sweep (`O(log K)` states!) -/

theorem natToBitsLE_getD (w v i : ℕ) :
    (natToBitsLE w v).getD i false = if i < w then v.testBit i else false := by
  induction w generalizing v i with
  | zero => simp [natToBitsLE]
  | succ w ih =>
    cases i with
    | zero =>
      simp only [natToBitsLE, List.getD_cons_zero, Nat.zero_lt_succ, ↓reduceIte,
        Nat.testBit_zero]
    | succ i' =>
      simp only [natToBitsLE, List.getD_cons_succ, ih, Nat.succ_lt_succ_iff, Nat.testBit_succ]

theorem testBit_eq_false_of_lt_two_pow {K b i : ℕ} (hK : K < 2 ^ b) (hi : b ≤ i) :
    K.testBit i = false := by
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hK (Nat.pow_le_pow_right (by decide) hi))

theorem lt_two_pow_log_succ (K : ℕ) : K < 2 ^ (Nat.log 2 K + 1) := by
  by_cases hK : K = 0
  · subst hK; simp
  · exact Nat.lt_pow_succ_log_self (by decide) K

/-- Load constant `K : ℕ` into zeroed segment `s` of width `w ≥ Nat.log 2 K + 1` in ONE pass. -/
def blkLoadConst (MaxSeg K : ℕ) :
    BlkStepFn (Fin (MaxSeg + 1) × Fin (Nat.log 2 K + 2) × Bool) :=
  fun (rem, idx, rewinding) sym =>
    if rewinding then
      if sym = blkHome then none
      else some ((0, 0, true), sym, QCSD_HeadDir.left)
    else if sym = blkHome then
      some ((rem, 0, false), blkHome, QCSD_HeadDir.right)
    else if hrem : 0 < rem.val then
      let prev : Fin (MaxSeg + 1) := ⟨rem.val - 1, by omega⟩
      if sym = blkSep then some ((prev, 0, false), blkSep, QCSD_HeadDir.right)
      else some ((rem, 0, false), sym, QCSD_HeadDir.right)
    else if hidx : idx.val < Nat.log 2 K + 1 then
      some ((0, ⟨idx.val + 1, by omega⟩, false), blkData false (K.testBit idx.val), QCSD_HeadDir.right)
    else
      some ((0, 0, true), sym, QCSD_HeadDir.left)

theorem wsLoadConst_spec (MaxSeg B K : ℕ) (segs : List (List Bool)) {s w : ℕ}
    (hs : s < segs.length) (hs_m : s ≤ MaxSeg)
    (hseg : segs.getD s [] = natToBitsLE w 0)
    (hw_ge : Nat.log 2 K + 1 ≤ w)
    {len : ℕ} {τ₁ : ℕ → Bool} (htw : TapeWS τ₁ len B segs) :
    let M_blk := (encodeWorkspace segs).length
    ∃ τ₂ : ℕ → Bool,
      TapeWS τ₂ len B (segs.set s (natToBitsLE w K)) ∧
      (∀ p, 3 * M_blk ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (liftBlockStep (blkLoadConst MaxSeg K)) B
        (liftBlkEntry (⟨s, by omega⟩, 0, false)) len τ₁ 0
        (liftBlkExit (0, 0, true)) len τ₂ 0 (21 * M_blk + 4) := by
  intro M_blk
  rcases htw with ⟨hsegs, hW_le, hlen_B, hws₀⟩
  let nb := Nat.log 2 K + 1
  let σ₀ := readBlk τ₁
  let go : ℕ → Fin (MaxSeg + 1) × Fin (Nat.log 2 K + 2) × Bool := fun r =>
    (⟨if h : r ≤ MaxSeg then r else 0, by split_ifs <;> omega⟩, 0, false)
  have hgo_s : go s = (⟨s, by omega⟩, 0, false) := by simp [go, hs_m]
  have hgo_0 : go 0 = (0, 0, false) := by ext <;> simp [go]
  rcases blkGoToSeg_reMark_aux (blkLoadConst MaxSeg K) segs (fun _ => false) σ₀ hws₀ go hs
      (by simp [go, hs_m, blkLoadConst])
      (fun r hr m b => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        simp [go, hr1, blkLoadConst, blkHome, blkData, blkSep])
      (fun r hr => by
        have hr1 : r + 1 ≤ MaxSeg := by omega
        have hr0 : r ≤ MaxSeg := by omega
        have hpos : 0 < (if h : r + 1 ≤ MaxSeg then r + 1 else 0) := by simp [hr1]
        simp only [go, blkLoadConst, Bool.false_eq_true, ↓reduceIte,
          show blkSep ≠ blkHome by decide, dite_true, hpos]
        congr 1; ext <;> simp [hr1, hr0])
    with ⟨hiter_go, hbnd_go, hdir_go⟩
  have hrm0 : reMark (fun _ => false) σ₀ = σ₀ := by funext j; exact reMark_of_false _ rfl
  rw [hrm0, hgo_s, hgo_0] at hiter_go
  rw [hrm0, hgo_s] at hbnd_go hdir_go
  have hsb := segStart_bound segs s hs
  have hs1 := segStart_pos segs s
  have hlen_s : (segs.getD s []).length = w := by rw [hseg, length_natToBitsLE]
  -- Write bits `0 .. nb - 1`
  let partialBits (t : ℕ) : List Bool :=
    (List.range w).map (fun i => if i < t then K.testBit i else false)
  have hpb_len : ∀ t, (partialBits t).length = w := fun _ => by simp [partialBits]
  have hpb_0 : partialBits 0 = natToBitsLE w 0 := by
    apply List.ext_getElem (by rw [hpb_len, length_natToBitsLE])
    intro i h1 h2; rw [hpb_len] at h1
    simp [partialBits, natToBitsLE_zero]
  have hpb_nb : partialBits nb = natToBitsLE w K := by
    apply List.ext_getElem (by rw [hpb_len, length_natToBitsLE])
    intro i h1 h2; rw [hpb_len] at h1
    have hgd := natToBitsLE_getD w K i
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at hgd
    simp only [Option.getD_some, h1, ↓reduceIte] at hgd
    rw [hgd]
    simp only [partialBits, List.getElem_map, List.getElem_range]
    split_ifs with hi
    · rfl
    · exact (testBit_eq_false_of_lt_two_pow (lt_two_pow_log_succ K) (by omega)).symm
  have hwrite : ∀ rem t, (htr : t + rem = nb) → ∀ σc,
      MatchesWS σc (segs.set s (partialBits t)) →
      ∃ σ_w, MatchesWS σ_w (segs.set s (partialBits nb)) ∧
        blkIter (blkLoadConst MaxSeg K) ((0, ⟨t, by omega⟩, false), σc, segStart segs s + t) rem =
          some ((0, ⟨nb, by omega⟩, false), σ_w, segStart segs s + nb) ∧
        (∀ i ≤ rem, ∀ q' σ' j',
          blkIter (blkLoadConst MaxSeg K) ((0, ⟨t, by omega⟩, false), σc, segStart segs s + t) i =
            some (q', σ', j') → j' < M_blk) ∧
        (∀ i < rem, ∀ q' σ' j' q'' sym' dir,
          blkIter (blkLoadConst MaxSeg K) ((0, ⟨t, by omega⟩, false), σc, segStart segs s + t) i =
            some (q', σ', j') →
          blkLoadConst MaxSeg K q' (σ' j') = some (q'', sym', dir) →
          (dir = QCSD_HeadDir.left → 1 ≤ j') ∧ (dir = QCSD_HeadDir.right → j' + 1 < M_blk)) := by
    intro rem
    induction rem with
    | zero =>
      intro t htr σc hws_c
      have ht_eq : t = nb := by omega
      subst t
      exact ⟨σc, hws_c, rfl, fun i hi _ _ _ heq => by obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi; cases heq; omega,
        fun i hi => by omega⟩
    | succ rem ih =>
      intro t htr σc hws_c
      have hne_h : σc (segStart segs s + t) ≠ blkHome := by
        have hM_c : (encodeWorkspace (segs.set s (partialBits t))).length = M_blk :=
          length_encodeWorkspace_set hs (by rw [hpb_len, hlen_s])
        rw [hws_c _ (by omega)]
        exact encodeWorkspace_ne_home _ (by omega) (by omega)
      have ht_lt : t < Nat.log 2 K + 1 := by dsimp only [nb] at htr; omega
      have hbs : blkLoadConst MaxSeg K (0, ⟨t, by omega⟩, false) (σc (segStart segs s + t)) =
          some ((0, ⟨t + 1, by omega⟩, false), blkData false (K.testBit t), QCSD_HeadDir.right) := by
        simp [blkLoadConst, hne_h, ht_lt]
      have hss_eq : segStart (segs.set s (partialBits t)) s = segStart segs s :=
        segStart_set_eq segs s s (partialBits t) hs (by rw [hpb_len, hlen_s])
      have hws_next : MatchesWS (Function.update σc (segStart segs s + t) (blkData false (K.testBit t)))
          (segs.set s (partialBits (t + 1))) := by
        have hupd := MatchesWS_update_seg_set (segs.set s (partialBits t)) (s := s) (v := t)
          (by simp; omega) (by rw [getD_set_self_seg _ hs, hpb_len]; omega) (K.testBit t) hws_c
        rw [hss_eq, getD_set_self_seg _ hs, List.set_set] at hupd
        have hset_pb : (partialBits t).set t (K.testBit t) = partialBits (t + 1) := by
          apply List.ext_getElem (by simp [hpb_len])
          intro idx h1 h2; rw [List.length_set, hpb_len] at h1
          rw [List.getElem_set]
          simp only [partialBits, List.getElem_map, List.getElem_range]
          by_cases heq : t = idx
          · subst heq; simp
          · have hiff : (idx < t + 1) ↔ (idx < t) := by omega
            simp [heq, hiff]
        rwa [hset_pb] at hupd
      rcases ih (t + 1) (by omega) _ hws_next with ⟨σ_w, hws_w, hit, hbd, hdr⟩
      have hadd : segStart segs s + t + 1 = segStart segs s + (t + 1) := by omega
      refine ⟨σ_w, hws_w, ?_, ?_, ?_⟩
      · simp only [blkIter, blkOnce, hbs, moveHead, hadd]; exact hit
      · intro i hi q' σ' j' hi_eq
        cases i with
        | zero => cases hi_eq; omega
        | succ i' =>
          simp only [blkIter, blkOnce, hbs, moveHead, hadd] at hi_eq
          exact hbd i' (by omega) q' σ' j' hi_eq
      · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
        cases i with
        | zero => cases hi_eq; rw [hbs] at hbs'; cases hbs'; exact ⟨by simp, fun _ => by omega⟩
        | succ i' =>
          simp only [blkIter, blkOnce, hbs, moveHead, hadd] at hi_eq
          exact hdr i' (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
  have hset0 : segs.set s (partialBits 0) = segs := by
    rw [hpb_0]
    apply List.ext_getElem (by simp)
    intro i h1 h2; rw [List.getElem_set]; split_ifs with heq
    · subst heq; have := hseg; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at this; exact this.symm
    · rfl
  rcases hwrite nb 0 (Nat.zero_add nb) σ₀ (by rw [hset0]; exact hws₀)
    with ⟨σ_w, hws_w, hiter_w, hbnd_w, hdir_w⟩
  have hfin0 : (⟨0, by omega⟩ : Fin (Nat.log 2 K + 2)) = 0 := rfl
  simp only [Nat.add_zero, hfin0] at hiter_w hbnd_w hdir_w
  rw [hpb_nb] at hws_w
  have hM_w : (encodeWorkspace (segs.set s (natToBitsLE w K))).length = M_blk :=
    length_encodeWorkspace_set hs (by rw [length_natToBitsLE, hlen_s])
  have hne_end : σ_w (segStart segs s + nb) ≠ blkHome := by
    rw [hws_w _ (by omega)]; exact encodeWorkspace_ne_home _ (by omega) (by omega)
  have hbs_turn : blkLoadConst MaxSeg K (0, ⟨nb, by omega⟩, false) (σ_w (segStart segs s + nb)) =
      some ((0, 0, true), σ_w (segStart segs s + nb), QCSD_HeadDir.left) := by
    simp [blkLoadConst, hne_end, nb]
  have hturn : blkIter (blkLoadConst MaxSeg K) ((0, ⟨nb, by omega⟩, false), σ_w, segStart segs s + nb) 1 =
      some ((0, 0, true), σ_w, segStart segs s + nb - 1) := by
    simp [blkIter, blkOnce, hbs_turn, Function.update_eq_self, moveHead]
  have h0_w : σ_w 0 = blkHome := (hws_w 0 (by omega)).trans (encodeWorkspace_getD_zero _)
  have hne_w : ∀ i, 1 ≤ i → i ≤ segStart segs s + nb - 1 → σ_w i ≠ blkHome := by
    intro i hi1 hi2; rw [hws_w i (by omega)]; exact encodeWorkspace_ne_home _ hi1 (by omega)
  rcases blkRewind_aux (blkLoadConst MaxSeg K) M_blk (0, 0, true)
      (by simp [blkLoadConst]) (fun sym hne => by simp [blkLoadConst, hne])
      (segStart segs s + nb - 1) σ_w (by omega) h0_w hne_w
    with ⟨hiter_rw, hnone_rw, hbnd_rw, hdir_rw⟩
  have hblk_exec : BlkExec (blkLoadConst MaxSeg K) M_blk
      (⟨s, by omega⟩, 0, false) (readBlk τ₁) 0 (0, 0, true) σ_w 0 (3 * M_blk) := by
    refine ⟨segStart segs s + nb + 1 + (segStart segs s + nb - 1), by omega, ?_, hnone_rw, ?_, ?_⟩
    · rw [blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
          hiter_w, Option.bind_some, hturn, Option.bind_some, hiter_rw]
    · intro i hi q' σ' j' hi_eq
      by_cases hi1 : i ≤ segStart segs s
      · rcases blkIter_le_some hi1 hiter_go with ⟨⟨_, _, _⟩, hsub⟩
        rw [hsub] at hi_eq; cases hi_eq; exact hbnd_go i hi1 q' σ' j' hsub
      · by_cases hi2 : i ≤ segStart segs s + nb
        · have heq : i = segStart segs s + (i - segStart segs s) := by omega
          rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
          exact hbnd_w _ (by omega) q' σ' j' hi_eq
        · have heq : i = segStart segs s + nb + 1 + (i - (segStart segs s + nb + 1)) := by omega
          rw [heq, blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
              hiter_w, Option.bind_some, hturn, Option.bind_some] at hi_eq
          exact hbnd_rw _ (by omega) q' σ' j' hi_eq
    · intro i hi q' σ' j' q'' sym' dir hi_eq hbs'
      by_cases hi1 : i < segStart segs s
      · exact hdir_go i hi1 q' σ' j' q'' sym' dir hi_eq hbs'
      · by_cases hi2 : i < segStart segs s + nb
        · have heq : i = segStart segs s + (i - segStart segs s) := by omega
          rw [heq, blkIter_add, hiter_go, Option.bind_some] at hi_eq
          exact hdir_w _ (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
        · by_cases hi3 : i = segStart segs s + nb
          · subst hi3
            rw [blkIter_add, hiter_go, Option.bind_some, hiter_w] at hi_eq
            cases hi_eq; rw [hbs_turn] at hbs'; cases hbs'; exact ⟨fun _ => by omega, by simp⟩
          · have heq : i = segStart segs s + nb + 1 + (i - (segStart segs s + nb + 1)) := by omega
            rw [heq, blkIter_add, blkIter_add, blkIter_add, hiter_go, Option.bind_some,
                hiter_w, Option.bind_some, hturn, Option.bind_some] at hi_eq
            exact hdir_rw _ (by omega) q' σ' j' q'' sym' dir hi_eq hbs'
  rcases liftBlockStep_spec (blkLoadConst MaxSeg K) B M_blk len τ₁
      (⟨s, by omega⟩, 0, false) (0, 0, true) σ_w 0 0 (3 * M_blk) hW_le hlen_B hblk_exec
    with ⟨τ₂, hread₂, hout₂, he₂⟩
  simp only [Nat.mul_zero] at he₂
  exact ⟨τ₂, ⟨by simp [hsegs], by rw [hM_w]; exact hW_le, hlen_B, by rw [hread₂]; exact hws_w⟩,
    hout₂, he₂.weaken (21 * M_blk + 4) (by omega)⟩

/-! #### `wsMulInto`: multiply register `s_b := s_b * s_a` using scratch `s_c, s_d, s_e` -/

abbrev WsAddLoopQ (MaxSeg : ℕ) : Type :=
  WsDecJzQ MaxSeg ⊕ (Unit ⊕ LiftBlkQ (Fin (MaxSeg + 1) × Bool))

def wsAddLoopBody (MaxSeg : ℕ) (dst : Fin (MaxSeg + 1)) : StepFn (WsAddLoopQ MaxSeg) :=
  seq0 (wsDecJz MaxSeg)
    (sumStep (nopStep Unit) (wsInc MaxSeg))
    (fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (wsIncEntry MaxSeg dst))

def wsAddLoopNext (MaxSeg : ℕ) (cnt : Fin (MaxSeg + 1)) :
    WsAddLoopQ MaxSeg → Option (WsAddLoopQ MaxSeg)
  | Sum.inr (Sum.inr _) => some (Sum.inl (wsDecJzEntry MaxSeg cnt))
  | _ => none

def wsAddLoop (MaxSeg : ℕ) (cnt dst : Fin (MaxSeg + 1)) : StepFn (WsAddLoopQ MaxSeg) :=
  loop0 (wsAddLoopBody MaxSeg dst) (wsAddLoopNext MaxSeg cnt)

theorem wsAddLoop_spec (MaxSeg B w : ℕ) (cnt dst : Fin (MaxSeg + 1))
    (h_ne : cnt.val ≠ dst.val) :
    ∀ rem acc (segs : List (List Bool)) len (τ₁ : ℕ → Bool),
      cnt.val < segs.length → dst.val < segs.length →
      acc + rem < 2 ^ w →
      segs.getD cnt.val [] = natToBitsLE w rem →
      segs.getD dst.val [] = natToBitsLE w acc →
      TapeWS τ₁ len B segs →
      ∃ τ₂ : ℕ → Bool,
        TapeWS τ₂ len B ((segs.set cnt.val (natToBitsLE w 0)).set dst.val (natToBitsLE w (acc + rem))) ∧
        (∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₂ p = τ₁ p) ∧
        StepExec (wsAddLoop MaxSeg cnt dst) B (Sum.inl (wsDecJzEntry MaxSeg cnt)) len τ₁ 0
          (Sum.inr (Sum.inl ())) len τ₂ 0 ((rem + 1) * (63 * (encodeWorkspace segs).length + 20)) := by
  intro rem
  induction rem with
  | zero =>
    intro acc segs len τ₁ hc hd hbound hsc hsd htw
    have hlen_pos := TapeWS_pos htw
    have hlen_B := htw.2.2.1
    rcases wsDecJz_spec MaxSeg B segs hc (Nat.le_of_lt_succ cnt.isLt) hsc (by omega) htw
      with ⟨q_d, τ_m, hz, htw_m, hout_m, he_d⟩
    simp only [decide_true, ↓reduceIte] at hz htw_m
    have he_nop := sumStep_inl_spec (nopStep Unit) (wsInc MaxSeg) (nopStep_spec () len τ_m 0 hlen_B (by omega))
    have hbody := seq0_spec
      (f := fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (wsIncEntry MaxSeg dst))
      hlen_pos he_d (by simpa [hz] using he_nop)
    have hdone := (loop0_done (next := wsAddLoopNext MaxSeg cnt) hbody rfl).weaken
      ((0 + 1) * (63 * (encodeWorkspace segs).length + 20)) (by omega)
    have hnoop : (segs.set cnt.val (natToBitsLE w 0)).set dst.val (natToBitsLE w (acc + 0)) = segs := by
      apply List.ext_getElem (by simp)
      intro i h1 h2; simp only [Nat.add_zero, List.getElem_set]
      split_ifs with c1 c2
      · subst c1; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at hsd; exact hsd.symm
      · subst c2; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at hsc; exact hsc.symm
      · rfl
    rw [hnoop]
    exact ⟨τ_m, htw_m, hout_m, hdone⟩
  | succ rem ih =>
    intro acc segs len τ₁ hc hd hbound hsc hsd htw
    have hlen_pos := TapeWS_pos htw
    rcases wsDecJz_spec MaxSeg B segs hc (Nat.le_of_lt_succ cnt.isLt) hsc (by omega) htw
      with ⟨q_d, τ_d, hz, htw_d, hout_d, he_d⟩
    simp only [Nat.succ_ne_zero, decide_false, ↓reduceIte, Nat.add_sub_cancel] at hz htw_d
    let segs₁ := segs.set cnt.val (natToBitsLE w rem)
    have hM₁ : (encodeWorkspace segs₁).length = (encodeWorkspace segs).length :=
      length_encodeWorkspace_set hc (by rw [hsc, length_natToBitsLE, length_natToBitsLE])
    rcases wsInc_spec MaxSeg B segs₁ (by simp [segs₁]; omega) (Nat.le_of_lt_succ dst.isLt)
        (by dsimp only [segs₁]; rw [getD_set_ne_seg _ h_ne]; exact hsd) (by omega) htw_d
      with ⟨τ_i, htw_i, hout_i, he_i⟩
    rw [hM₁] at hout_i he_i
    let segs₂ := segs₁.set dst.val (natToBitsLE w (acc + 1))
    have hM₂ : (encodeWorkspace segs₂).length = (encodeWorkspace segs).length :=
      (length_encodeWorkspace_set (by simp [segs₁]; omega)
        (by dsimp only [segs₁]; rw [getD_set_ne_seg _ h_ne, hsd, length_natToBitsLE, length_natToBitsLE])).trans hM₁
    have he_inr := sumStep_inr_spec (nopStep Unit) (wsInc MaxSeg) he_i
    have hbody := seq0_spec
      (f := fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (wsIncEntry MaxSeg dst))
      hlen_pos he_d (by simpa [hz] using he_inr)
    rcases ih (acc + 1) segs₂ len τ_i (by simp [segs₂, segs₁]; omega) (by simp [segs₂, segs₁]; omega)
        (by omega) (by dsimp only [segs₂, segs₁]; rw [getD_set_ne_seg _ h_ne.symm, getD_set_self_seg _ hc])
        (by dsimp only [segs₂]; rw [getD_set_self_seg _ (by simp [segs₁]; omega)]) htw_i
      with ⟨τ_end, htw_end, hout_end, he_rest⟩
    rw [hM₂] at hout_end he_rest
    have hsegs_eq : (segs₂.set cnt.val (natToBitsLE w 0)).set dst.val (natToBitsLE w (acc + 1 + rem)) =
        (segs.set cnt.val (natToBitsLE w 0)).set dst.val (natToBitsLE w (acc + (rem + 1))) := by
      rw [show acc + 1 + rem = acc + (rem + 1) by omega]
      apply List.ext_getElem (by simp [segs₂, segs₁])
      intro i _ _; simp only [segs₂, segs₁, List.getElem_set]; split_ifs <;> rfl
    rw [hsegs_eq] at htw_end
    have hcomb := (loop0_step (next := wsAddLoopNext MaxSeg cnt) hlen_pos hbody rfl he_rest).weaken
      ((rem + 1 + 1) * (63 * (encodeWorkspace segs).length + 20)) (by
        have : (rem + 1 + 1) * (63 * (encodeWorkspace segs).length + 20) =
            (63 * (encodeWorkspace segs).length + 20) + (rem + 1) * (63 * (encodeWorkspace segs).length + 20) := by ring
        omega)
    exact ⟨τ_end, htw_end, fun p hp => (hout_end p hp).trans ((hout_i p hp).trans (hout_d p hp)), hcomb⟩

abbrev WsMulLoopQ (MaxSeg : ℕ) : Type :=
  WsDecJzQ MaxSeg ⊕
    (Unit ⊕ ((SegTriple MaxSeg × WsCopyInnerQ MaxSeg) ⊕ WsAddLoopQ MaxSeg))

def wsMulLoopBody (MaxSeg : ℕ) (s_a s_c s_d s_e : Fin (MaxSeg + 1)) : StepFn (WsMulLoopQ MaxSeg) :=
  seq0 (wsDecJz MaxSeg)
    (sumStep (nopStep Unit)
      (seq0 (wsCopy MaxSeg) (wsAddLoop MaxSeg s_d s_c)
        (fun _ => Sum.inl (wsDecJzEntry MaxSeg s_d))))
    (fun q => if wsDecJzWasZero q then Sum.inl ()
      else Sum.inr (Sum.inl (wsCopyEntry MaxSeg (s_d, s_a, s_e))))

def wsMulLoopNext (MaxSeg : ℕ) (s_b : Fin (MaxSeg + 1)) :
    WsMulLoopQ MaxSeg → Option (WsMulLoopQ MaxSeg)
  | Sum.inr (Sum.inr _) => some (Sum.inl (wsDecJzEntry MaxSeg s_b))
  | _ => none

abbrev WsMulIntoQ (MaxSeg : ℕ) : Type :=
  LiftBlkQ (Fin (MaxSeg + 1) × Bool) ⊕
    (WsMulLoopQ MaxSeg ⊕
      ((SegTriple MaxSeg × WsCopyInnerQ MaxSeg) ⊕ LiftBlkQ (Fin (MaxSeg + 1) × Bool)))

def wsMulInto (MaxSeg : ℕ) (s_b s_a s_c s_d s_e : Fin (MaxSeg + 1)) : StepFn (WsMulIntoQ MaxSeg) :=
  seq0 (wsZero MaxSeg)
    (seq0 (loop0 (wsMulLoopBody MaxSeg s_a s_c s_d s_e) (wsMulLoopNext MaxSeg s_b))
      (seq0 (wsCopy MaxSeg) (wsZero MaxSeg) (fun _ => wsZeroEntry MaxSeg s_c))
      (fun _ => Sum.inl (wsCopyEntry MaxSeg (s_b, s_c, s_d))))
    (fun _ => Sum.inl (Sum.inl (wsDecJzEntry MaxSeg s_b)))

theorem wsMulInto_spec (MaxSeg B w va vb : ℕ) (s_b s_a s_c s_d s_e : Fin (MaxSeg + 1))
    (segs : List (List Bool))
    (hba : s_b.val ≠ s_a.val) (hbc : s_b.val ≠ s_c.val) (hbd : s_b.val ≠ s_d.val) (hbe : s_b.val ≠ s_e.val)
    (hac : s_a.val ≠ s_c.val) (had : s_a.val ≠ s_d.val) (hae : s_a.val ≠ s_e.val)
    (hcd : s_c.val ≠ s_d.val) (hce : s_c.val ≠ s_e.val) (hde : s_d.val ≠ s_e.val)
    (hbL : s_b.val < segs.length) (haL : s_a.val < segs.length) (hcL : s_c.val < segs.length)
    (hdL : s_d.val < segs.length) (heL : s_e.val < segs.length)
    (hseg_b : segs.getD s_b.val [] = natToBitsLE w vb)
    (hseg_a : segs.getD s_a.val [] = natToBitsLE w va)
    (hlen_c : (segs.getD s_c.val []).length = w)
    (hlen_d : (segs.getD s_d.val []).length = w)
    (hlen_e : (segs.getD s_e.val []).length = w)
    (hva_pow : va < 2 ^ w) (hvb_pow : vb < 2 ^ w) (hprod_pow : vb * va < 2 ^ w)
    {len : ℕ} {τ₀ : ℕ → Bool} (htw₀ : TapeWS τ₀ len B segs) :
    let M_blk := (encodeWorkspace segs).length
    ∃ segs_end, ∃ τ_end : ℕ → Bool,
      segs_end.length = segs.length ∧
      (encodeWorkspace segs_end).length = M_blk ∧
      segs_end.getD s_b.val [] = natToBitsLE w (vb * va) ∧
      segs_end.getD s_a.val [] = natToBitsLE w va ∧
      (segs_end.getD s_c.val []).length = w ∧
      (segs_end.getD s_d.val []).length = w ∧
      (segs_end.getD s_e.val []).length = w ∧
      (∀ idx, idx ≠ s_b.val → idx ≠ s_c.val → idx ≠ s_d.val → idx ≠ s_e.val →
        segs_end.getD idx [] = segs.getD idx []) ∧
      TapeWS τ_end len B segs_end ∧
      (∀ p, 3 * M_blk ≤ p → τ_end p = τ₀ p) ∧
      StepExec (wsMulInto MaxSeg s_b s_a s_c s_d s_e) B (Sum.inl (wsZeroEntry MaxSeg s_c)) len τ₀ 0
        (Sum.inr (Sum.inr (Sum.inr (liftBlkExit (0, true))))) len τ_end 0
        ((vb + 2) * ((va + 2) * (250 * M_blk + 100)) + (vb * va + 2) * (160 * M_blk + 60) + 100 * M_blk + 50) := by
  intro M_blk
  have hlen_pos := TapeWS_pos htw₀
  have hlen_B := htw₀.2.2.1
  -- 1) wsZero s_c
  rcases wsZero_spec MaxSeg B segs hcL (Nat.le_of_lt_succ s_c.isLt) hlen_c htw₀
    with ⟨τ1, htw1, hout1, he1⟩
  let segs1 := segs.set s_c.val (natToBitsLE w 0)
  have hM1 : (encodeWorkspace segs1).length = M_blk :=
    length_encodeWorkspace_set hcL (by rw [hlen_c, length_natToBitsLE])
  -- 2) Multiply loop: `rem` from `vb` down to `0`
  let S_ml := (va + 2) * (240 * M_blk + 90)
  have hloop : ∀ rem acc (segs_x : List (List Bool)) (τx : ℕ → Bool),
      rem + acc = vb →
      segs_x.length = segs.length →
      (encodeWorkspace segs_x).length = M_blk →
      segs_x.getD s_b.val [] = natToBitsLE w rem →
      segs_x.getD s_a.val [] = natToBitsLE w va →
      segs_x.getD s_c.val [] = natToBitsLE w (acc * va) →
      (segs_x.getD s_d.val []).length = w →
      (segs_x.getD s_e.val []).length = w →
      (∀ idx, idx ≠ s_b.val → idx ≠ s_c.val → idx ≠ s_d.val → idx ≠ s_e.val →
        segs_x.getD idx [] = segs.getD idx []) →
      TapeWS τx len B segs_x →
      ∃ segs_y, ∃ τy : ℕ → Bool,
        segs_y.length = segs.length ∧
        (encodeWorkspace segs_y).length = M_blk ∧
        segs_y.getD s_b.val [] = natToBitsLE w 0 ∧
        segs_y.getD s_a.val [] = natToBitsLE w va ∧
        segs_y.getD s_c.val [] = natToBitsLE w (vb * va) ∧
        (segs_y.getD s_d.val []).length = w ∧
        (segs_y.getD s_e.val []).length = w ∧
        (∀ idx, idx ≠ s_b.val → idx ≠ s_c.val → idx ≠ s_d.val → idx ≠ s_e.val →
          segs_y.getD idx [] = segs.getD idx []) ∧
        TapeWS τy len B segs_y ∧
        (∀ p, 3 * M_blk ≤ p → τy p = τx p) ∧
        StepExec (loop0 (wsMulLoopBody MaxSeg s_a s_c s_d s_e) (wsMulLoopNext MaxSeg s_b)) B
          (Sum.inl (wsDecJzEntry MaxSeg s_b)) len τx 0
          (Sum.inr (Sum.inl ())) len τy 0 ((rem + 1) * (S_ml + 2)) := by
    intro rem
    induction rem with
    | zero =>
      intro acc segs_x τx hsum hlen_x hMx hxb hxa hxc hxd hxe hoth htw_x
      have hacc : acc = vb := by omega
      subst hacc
      rcases wsDecJz_spec MaxSeg B segs_x (by omega) (Nat.le_of_lt_succ s_b.isLt) hxb (by omega) htw_x
        with ⟨q_d, τ_d, hz, htw_d, hout_d, he_d⟩
      rw [hMx] at hout_d he_d
      simp only [decide_true, ↓reduceIte] at hz htw_d
      have he_nop := sumStep_inl_spec (nopStep Unit)
        (seq0 (wsCopy MaxSeg) (wsAddLoop MaxSeg s_d s_c) (fun _ => Sum.inl (wsDecJzEntry MaxSeg s_d)))
        (nopStep_spec () len τ_d 0 hlen_B (by omega))
      have he_body : StepExec (wsMulLoopBody MaxSeg s_a s_c s_d s_e) B
          (Sum.inl (wsDecJzEntry MaxSeg s_b)) len τx 0 (Sum.inr (Sum.inl ())) len τ_d 0 S_ml := by
        unfold wsMulLoopBody
        exact (seq0_spec hlen_pos he_d (by simpa [hz] using he_nop)).weaken S_ml
          (by dsimp only [S_ml]; have : 2 * (240 * M_blk + 90) ≤ (va + 2) * (240 * M_blk + 90) :=
            Nat.mul_le_mul_right _ (by omega); omega)
      have hdone := (loop0_done (next := wsMulLoopNext MaxSeg s_b) he_body rfl).weaken
        ((0 + 1) * (S_ml + 2)) (by omega)
      exact ⟨segs_x, τ_d, hlen_x, hMx, hxb, hxa, hxc, hxd, hxe, hoth, htw_d, hout_d, hdone⟩
    | succ rem ih =>
      intro acc segs_x τx hsum hlen_x hMx hxb hxa hxc hxd hxe hoth htw_x
      -- a) wsDecJz s_b: `rem + 1 -> rem`
      rcases wsDecJz_spec MaxSeg B segs_x (by omega) (Nat.le_of_lt_succ s_b.isLt) hxb (by omega) htw_x
        with ⟨q_d, τ_d, hz, htw_d, hout_d, he_d⟩
      rw [hMx] at hout_d he_d
      simp only [Nat.succ_ne_zero, decide_false, ↓reduceIte, Nat.add_sub_cancel] at hz htw_d
      let sx1 := segs_x.set s_b.val (natToBitsLE w rem)
      have hMx1 : (encodeWorkspace sx1).length = M_blk :=
        (length_encodeWorkspace_set (by omega) (by rw [hxb, length_natToBitsLE, length_natToBitsLE])).trans hMx
      -- b) wsCopy (s_d, s_a, s_e)
      rcases wsCopy_spec MaxSeg B sx1 (dst := s_d.val) (src := s_a.val) (tmp := s_e.val)
          (w := w) (v := va)
          (by simp [sx1]; omega) (by simp [sx1]; omega) (by simp [sx1]; omega)
          (Nat.le_of_lt_succ s_d.isLt) (Nat.le_of_lt_succ s_a.isLt) (Nat.le_of_lt_succ s_e.isLt)
          had.symm hde hae
          (by dsimp only [sx1]; rw [getD_set_ne_seg _ hbd]; exact hxd)
          (by dsimp only [sx1]; rw [getD_set_ne_seg _ hba]; exact hxa)
          (by dsimp only [sx1]; rw [getD_set_ne_seg _ hbe]; exact hxe)
          hva_pow htw_d
        with ⟨q_cp, τ_cp, htw_cp, hout_cp, he_cp⟩
      rw [hMx1] at hout_cp he_cp
      let sx2_0 := sx1.set s_d.val (natToBitsLE w va)
      let sx2 := sx2_0.set s_e.val (natToBitsLE w 0)
      have hMx2 : (encodeWorkspace sx2).length = M_blk := by
        have h1 := length_encodeWorkspace_set (segs := sx1) (s := s_d.val) (newSeg := natToBitsLE w va)
          (by simp [sx1]; omega) (by dsimp only [sx1]; rw [getD_set_ne_seg _ hbd, hxd, length_natToBitsLE])
        have h2 := length_encodeWorkspace_set (segs := sx2_0) (s := s_e.val) (newSeg := natToBitsLE w 0)
          (by simp [sx2_0, sx1]; omega)
          (by dsimp only [sx2_0, sx1]; rw [getD_set_ne_seg _ hde, getD_set_ne_seg _ hbe, hxe, length_natToBitsLE])
        exact h2.trans (h1.trans hMx1)
      -- c) wsAddLoop s_d s_c: `s_c += va`, `s_d := 0`
      have hacc1_pow : acc * va + va < 2 ^ w := by
        have hle : (acc + 1) * va ≤ vb * va := Nat.mul_le_mul_right va (by omega)
        rw [Nat.add_mul, Nat.one_mul] at hle; omega
      rcases wsAddLoop_spec MaxSeg B w s_d s_c hcd.symm va (acc * va) sx2 len τ_cp
          (by simp [sx2, sx2_0, sx1]; omega) (by simp [sx2, sx2_0, sx1]; omega) hacc1_pow
          (by dsimp only [sx2, sx2_0]; rw [getD_set_ne_seg _ hde.symm, getD_set_self_seg _ (by simp [sx1]; omega)])
          (by dsimp only [sx2, sx2_0, sx1]; rw [getD_set_ne_seg _ hce.symm, getD_set_ne_seg _ hcd.symm, getD_set_ne_seg _ hbc]; exact hxc)
          htw_cp
        with ⟨τ_ad, htw_ad, hout_ad, he_ad⟩
      rw [hMx2] at hout_ad he_ad
      let sx3 := (sx2.set s_d.val (natToBitsLE w 0)).set s_c.val (natToBitsLE w (acc * va + va))
      have hMx3 : (encodeWorkspace sx3).length = M_blk := by
        have h1 := length_encodeWorkspace_set (segs := sx2) (s := s_d.val) (newSeg := natToBitsLE w 0)
          (by simp [sx2, sx2_0, sx1]; omega)
          (by dsimp only [sx2, sx2_0]; rw [getD_set_ne_seg _ hde.symm, getD_set_self_seg _ (by simp [sx1]; omega), length_natToBitsLE, length_natToBitsLE])
        have h2 := length_encodeWorkspace_set (segs := sx2.set s_d.val (natToBitsLE w 0)) (s := s_c.val)
          (newSeg := natToBitsLE w (acc * va + va))
          (by simp [sx2, sx2_0, sx1]; omega)
          (by rw [getD_set_ne_seg _ hcd.symm]; dsimp only [sx2, sx2_0, sx1]; rw [getD_set_ne_seg _ hce.symm, getD_set_ne_seg _ hcd.symm, getD_set_ne_seg _ hbc, hxc, length_natToBitsLE, length_natToBitsLE])
        exact h2.trans (h1.trans hMx2)
      have he_ca := seq0_spec (f := fun _ => Sum.inl (wsDecJzEntry MaxSeg s_d)) hlen_pos he_cp he_ad
      have he_inr := sumStep_inr_spec (nopStep Unit) _ he_ca
      have hbody_time : 42 * M_blk + 10 + 1 +
          ((va + 2) * (150 * M_blk + 50) + 1 + (va + 1) * (63 * M_blk + 20)) ≤ S_ml := by
        dsimp only [S_ml]
        have h1 : (va + 1) * (63 * M_blk + 20) ≤ (va + 2) * (63 * M_blk + 20) :=
          Nat.mul_le_mul_right _ (by omega)
        have h2 : 2 * (27 * M_blk + 20) ≤ (va + 2) * (27 * M_blk + 20) :=
          Nat.mul_le_mul_right _ (by omega)
        nlinarith
      have he_body : StepExec (wsMulLoopBody MaxSeg s_a s_c s_d s_e) B
          (Sum.inl (wsDecJzEntry MaxSeg s_b)) len τx 0
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))) len τ_ad 0 S_ml := by
        unfold wsMulLoopBody
        exact (seq0_spec hlen_pos he_d (by simpa [hz] using he_inr)).weaken S_ml hbody_time
      have hmul_step : (acc + 1) * va = acc * va + va := by ring
      rcases ih (acc + 1) sx3 τ_ad (by omega) (by simp [sx3, sx2, sx2_0, sx1, hlen_x]) hMx3
          (by dsimp only [sx3, sx2, sx2_0, sx1]; rw [getD_set_ne_seg _ hbc.symm, getD_set_ne_seg _ hbd.symm,
              getD_set_ne_seg _ hbe.symm, getD_set_ne_seg _ hbd.symm, getD_set_self_seg _ (by omega)])
          (by dsimp only [sx3, sx2, sx2_0, sx1]; rw [getD_set_ne_seg _ hac.symm, getD_set_ne_seg _ had.symm,
              getD_set_ne_seg _ hae.symm, getD_set_ne_seg _ had.symm, getD_set_ne_seg _ hba]; exact hxa)
          (by dsimp only [sx3]; rw [getD_set_self_seg _ (by simp [sx2, sx2_0, sx1]; omega), hmul_step])
          (by dsimp only [sx3]; rw [getD_set_ne_seg _ hcd, getD_set_self_seg _ (by simp [sx2, sx2_0, sx1]; omega), length_natToBitsLE])
          (by dsimp only [sx3, sx2]; rw [getD_set_ne_seg _ hce, getD_set_ne_seg _ hde, getD_set_self_seg _ (by simp [sx2_0, sx1]; omega), length_natToBitsLE])
          (fun idx h1 h2 h3 h4 => by
            dsimp only [sx3, sx2, sx2_0, sx1]
            rw [getD_set_ne_seg _ h2.symm, getD_set_ne_seg _ h3.symm, getD_set_ne_seg _ h4.symm,
                getD_set_ne_seg _ h3.symm, getD_set_ne_seg _ h1.symm]
            exact hoth idx h1 h2 h3 h4)
          htw_ad
        with ⟨segs_y, τy, hly, hMy, hyb, hya, hyc, hyd, hye, hyoth, htw_y, hout_y, he_rest⟩
      have hcomb := (loop0_step (next := wsMulLoopNext MaxSeg s_b) hlen_pos he_body rfl he_rest).weaken
        ((rem + 1 + 1) * (S_ml + 2)) (by
          have : (rem + 1 + 1) * (S_ml + 2) = (S_ml + 2) + (rem + 1) * (S_ml + 2) := by ring
          omega)
      exact ⟨segs_y, τy, hly, hMy, hyb, hya, hyc, hyd, hye, hyoth, htw_y,
        fun p hp => (hout_y p hp).trans ((hout_ad p hp).trans ((hout_cp p hp).trans (hout_d p hp))), hcomb⟩
  rcases hloop vb 0 segs1 τ1 (by omega) (by simp [segs1]) hM1
      (by dsimp only [segs1]; rw [getD_set_ne_seg _ hbc.symm]; exact hseg_b)
      (by dsimp only [segs1]; rw [getD_set_ne_seg _ hac.symm]; exact hseg_a)
      (by dsimp only [segs1]; rw [Nat.zero_mul, getD_set_self_seg segs hcL])
      (by dsimp only [segs1]; rw [getD_set_ne_seg _ hcd]; exact hlen_d)
      (by dsimp only [segs1]; rw [getD_set_ne_seg _ hce]; exact hlen_e)
      (fun idx _ h2 _ _ => by dsimp only [segs1]; exact getD_set_ne_seg segs h2.symm _)
      htw1
    with ⟨segs_y, τy, hly, hMy, hyb, hya, hyc, hyd, hye, hyoth, htw_y, hout_y, he_lp⟩
  -- 3) wsCopy (s_b, s_c, s_d): `s_b := vb * va`
  rcases wsCopy_spec MaxSeg B segs_y (dst := s_b.val) (src := s_c.val) (tmp := s_d.val)
      (w := w) (v := vb * va)
      (by omega) (by omega) (by omega)
      (Nat.le_of_lt_succ s_b.isLt) (Nat.le_of_lt_succ s_c.isLt) (Nat.le_of_lt_succ s_d.isLt)
      hbc hbd hcd (by rw [hyb, length_natToBitsLE]) hyc hyd hprod_pow htw_y
    with ⟨q_cp2, τ_cp2, htw_cp2, hout_cp2, he_cp2⟩
  rw [hMy] at hout_cp2 he_cp2
  let segs_z0 := segs_y.set s_b.val (natToBitsLE w (vb * va))
  let segs_z := segs_z0.set s_d.val (natToBitsLE w 0)
  have hMz : (encodeWorkspace segs_z).length = M_blk := by
    have h1 := length_encodeWorkspace_set (segs := segs_y) (s := s_b.val) (newSeg := natToBitsLE w (vb * va))
      (by omega) (by rw [hyb, length_natToBitsLE, length_natToBitsLE])
    have h2 := length_encodeWorkspace_set (segs := segs_z0) (s := s_d.val) (newSeg := natToBitsLE w 0)
      (by simp [segs_z0]; omega) (by dsimp only [segs_z0]; rw [getD_set_ne_seg _ hbd, hyd, length_natToBitsLE])
    exact h2.trans (h1.trans hMy)
  -- 4) wsZero s_c
  rcases wsZero_spec MaxSeg B segs_z (w := w) (by simp [segs_z, segs_z0]; omega) (Nat.le_of_lt_succ s_c.isLt)
      (by dsimp only [segs_z, segs_z0]; rw [getD_set_ne_seg _ hcd.symm, getD_set_ne_seg _ hbc, hyc, length_natToBitsLE])
      htw_cp2
    with ⟨τ_end, htw_end, hout_end, he_z2⟩
  rw [hMz] at hout_end he_z2
  let segs_end := segs_z.set s_c.val (natToBitsLE w 0)
  have hMend : (encodeWorkspace segs_end).length = M_blk :=
    (length_encodeWorkspace_set (by simp [segs_z, segs_z0]; omega)
      (by dsimp only [segs_z, segs_z0]; rw [getD_set_ne_seg _ hcd.symm, getD_set_ne_seg _ hbc, hyc, length_natToBitsLE, length_natToBitsLE])).trans hMz
  have he34 := seq0_spec (f := fun _ => wsZeroEntry MaxSeg s_c) hlen_pos he_cp2 he_z2
  have he24 := seq0_spec (f := fun _ => Sum.inl (wsCopyEntry MaxSeg (s_b, s_c, s_d))) hlen_pos he_lp he34
  have he14 : StepExec (wsMulInto MaxSeg s_b s_a s_c s_d s_e) B (Sum.inl (wsZeroEntry MaxSeg s_c)) len τ₀ 0
      (Sum.inr (Sum.inr (Sum.inr (liftBlkExit (0, true))))) len τ_end 0
      ((21 * M_blk + 4) + 1 + (((vb + 1) * (S_ml + 2)) + 1 +
        (((vb * va + 2) * (150 * M_blk + 50)) + 1 + (21 * M_blk + 4)))) := by
    unfold wsMulInto
    exact seq0_spec hlen_pos he1 he24
  have htime : (21 * M_blk + 4) + 1 + (((vb + 1) * (S_ml + 2)) + 1 +
      (((vb * va + 2) * (150 * M_blk + 50)) + 1 + (21 * M_blk + 4))) ≤
      (vb + 2) * ((va + 2) * (250 * M_blk + 100)) + (vb * va + 2) * (160 * M_blk + 60) + 100 * M_blk + 50 := by
    have h1 : (vb + 1) * (S_ml + 2) ≤ (vb + 2) * ((va + 2) * (250 * M_blk + 100)) := by
      apply Nat.mul_le_mul (by omega)
      dsimp only [S_ml]
      have : 2 * (10 * M_blk + 10) ≤ (va + 2) * (10 * M_blk + 10) := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    have h2 : (vb * va + 2) * (150 * M_blk + 50) ≤ (vb * va + 2) * (160 * M_blk + 60) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨segs_end, τ_end, by simp [segs_end, segs_z, segs_z0, hly], hMend, ?_, ?_, ?_, ?_, ?_, ?_, htw_end,
    fun p hp => (hout_end p hp).trans ((hout_cp2 p hp).trans ((hout_y p hp).trans (hout1 p hp))),
    he14.weaken _ htime⟩
  · dsimp only [segs_end, segs_z, segs_z0]
    rw [getD_set_ne_seg _ hbc.symm, getD_set_ne_seg _ hbd.symm, getD_set_self_seg _ (by omega)]
  · dsimp only [segs_end, segs_z, segs_z0]
    rw [getD_set_ne_seg _ hac.symm, getD_set_ne_seg _ had.symm, getD_set_ne_seg _ hba]; exact hya
  · dsimp only [segs_end]; rw [getD_set_self_seg _ (by simp [segs_z, segs_z0]; omega), length_natToBitsLE]
  · dsimp only [segs_end, segs_z]; rw [getD_set_ne_seg _ hcd, getD_set_self_seg _ (by simp [segs_z0]; omega), length_natToBitsLE]
  · dsimp only [segs_end, segs_z, segs_z0]
    rw [getD_set_ne_seg _ hce, getD_set_ne_seg _ hde, getD_set_ne_seg _ hbe]; exact hye
  · intro idx h1 h2 h3 h4
    dsimp only [segs_end, segs_z, segs_z0]
    rw [getD_set_ne_seg _ h2.symm, getD_set_ne_seg _ h3.symm, getD_set_ne_seg _ h1.symm]
    exact hyoth idx h1 h2 h3 h4

/-! ### Phase 1.2B: Full Workspace Initializer (`initWSProg`) -/

theorem natToBitsLE_zero_eq_replicate (w : ℕ) : natToBitsLE w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [natToBitsLE, List.replicate_succ, ih]

theorem encodeWorkspace_length_eq (segs : List (List Bool)) (hne : segs ≠ []) :
    (encodeWorkspace segs).length = 1 + (segs.map (fun l => l.length + 1)).sum := by
  simp only [encodeWorkspace, List.length_cons, length_encodeSegmentsAux segs hne]; omega

theorem encodeWorkspace_append_length (segs extra : List (List Bool)) (hne : segs ≠ []) :
    (encodeWorkspace (segs ++ extra)).length =
      (encodeWorkspace segs).length + (extra.map (fun l => l.length + 1)).sum := by
  have hne' : segs ++ extra ≠ [] := by intro h; exact hne (List.append_eq_nil_iff.mp h).1
  rw [encodeWorkspace_length_eq _ hne', encodeWorkspace_length_eq _ hne, List.map_append, List.sum_append]
  omega

theorem sum_map_length_add_one (segs : List (List Bool)) :
    (segs.map (fun l => l.length + 1)).sum = segs.length + (segs.map List.length).sum := by
  induction segs with
  | nil => simp
  | cons hd tl ih => simp [ih]; omega

theorem makeSClean_getD (w : ℕ) (midRest : List Bool) (hmid : midRest.length ≤ 16 * w + 28) (j : ℕ) :
    (makeSClean w midRest).getD j false = midRest.getD j false := by
  unfold makeSClean
  by_cases hj : j < 16 * w + 28
  · rw [getD_append_left _ _ _ (by simp; omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  · rw [getD_append_right _ _ _ (by simp; omega)]
    have hrep : (List.replicate (2 * w + 3) false).getD (j - ((List.range (16 * w + 28)).map (fun i => midRest.getD i false)).length) false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs <;> rfl
    rw [hrep]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem seg_inp_matches_inp (n : ℕ) (rest : List Bool) (hn : 2 ≤ n)
    (hrest_len : (QCSD_natToUnary n ++ rest).length ≤ 9 * n + 4) :
    let w := (n - 2) / 2
    let r := decide ((n - 2) % 2 = 1)
    let midRest := (if r then [false] else []) ++ rest
    let seg_inp := List.replicate n true ++ (if r then [] else [false]) ++ makeSClean w midRest
    ∀ i, seg_inp.getD i false = (QCSD_natToUnary n ++ rest).getD i false := by
  intro w r midRest seg_inp i
  have hnw : n = 2 * w + 2 + (if r then 1 else 0) := by
    dsimp only [w, r]; split_ifs with hr <;> simp only [decide_eq_true_eq] at hr <;> omega
  have hmid_le : midRest.length ≤ 16 * w + 28 := by
    have hinp_len : (QCSD_natToUnary n ++ rest).length = n + 1 + rest.length := by
      simp [QCSD_natToUnary]; omega
    have hml : midRest.length = (if r then 1 else 0) + rest.length := by
      dsimp only [midRest]; cases hr : r <;> simp; omega
    have hr_le : (if r then 1 else 0) ≤ 1 := by split_ifs <;> omega
    omega
  have hsc := makeSClean_getD w midRest hmid_le
  dsimp only [seg_inp, QCSD_natToUnary]
  cases hr : r with
  | true =>
    simp only [↓reduceIte, List.append_nil]
    rw [List.append_assoc]
    by_cases hi : i < n
    · rw [getD_append_left _ _ _ (by simp; omega), getD_append_left _ _ _ (by simp; omega)]
    · rw [getD_append_right _ _ _ (by simp; omega), getD_append_right _ _ _ (by simp; omega)]
      simp only [List.length_replicate]
      rw [hsc (i - n)]
      dsimp only [midRest]; simp only [hr, ↓reduceIte]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    conv_lhs => rw [List.append_assoc]
    conv_rhs => rw [List.append_assoc]
    by_cases hi : i < n
    · conv_lhs => rw [getD_append_left _ _ _ (by simp; omega)]
      conv_rhs => rw [getD_append_left _ _ _ (by simp; omega)]
    · conv_lhs => rw [getD_append_right _ _ _ (by simp; omega)]
      conv_rhs => rw [getD_append_right _ _ _ (by simp; omega)]
      simp only [List.length_replicate, List.cons_append, List.nil_append]
      cases hsub : i - n with
      | zero => rfl
      | succ k =>
        simp only [List.getD_cons_succ]
        rw [hsc k]
        dsimp only [midRest]; simp only [hr, Bool.false_eq_true, ↓reduceIte, List.nil_append]

/-! #### Stage C: `buildSegInp` (`[S_clean, segN]` + `r` -> `[S_clean, segN, seg_inp]`) -/

abbrev BuildSegInpInnerQ (R : ℕ) : Type :=
  LiftBlkQ (Fin 3) ⊕
    (WsCopyLastQ (8 + R + 5) ⊕
      ((Unit ⊕ LiftBlkQ (Fin 3)) ⊕
        WsCopyLastQ (8 + R + 5)))

abbrev BuildSegInpQ (R : ℕ) : Type := Bool × BuildSegInpInnerQ R

def buildSegInpFor (R : ℕ) (r : Bool) : StepFn (BuildSegInpInnerQ R) :=
  let MaxSeg := 8 + R + 5
  seq0 (liftBlockStep (blkGrowLast blkSep))
    (seq0 (wsCopySegToLast MaxSeg ⟨1, by omega⟩ (some true))
      (seq0 (sumStep (nopStep Unit) (liftBlockStep (blkGrowLast (blkData false false))))
        (wsCopySegToLast MaxSeg ⟨0, by omega⟩ none)
        (fun _ => Sum.inl (liftBlkEntry (⟨0, by omega⟩, 0, false, false))))
      (fun _ => Sum.inl (if r then Sum.inl () else Sum.inr (liftBlkEntry 0))))
    (fun _ => Sum.inl (Sum.inl (liftBlkEntry (⟨1, by omega⟩, 0, false, false))))

def buildSegInp (R : ℕ) : StepFn (BuildSegInpQ R) :=
  familyStep (buildSegInpFor R)

theorem buildSegInp_spec (R B n : ℕ) (r : Bool) (S_clean : List Bool)
    {τ₀ : ℕ → Bool}
    (htw₀ : TapeWS τ₀ (3 * (encodeWorkspace [S_clean, List.replicate n false]).length) B
      [S_clean, List.replicate n false])
    (hclean₀ : ∀ p, 3 * (encodeWorkspace [S_clean, List.replicate n false]).length ≤ p → τ₀ p = false)
    (hB : 3 * (encodeWorkspace [S_clean, List.replicate n false,
        List.replicate n true ++ (if r then [] else [false]) ++ S_clean]).length ≤ B) :
    let seg_inp := List.replicate n true ++ (if r then [] else [false]) ++ S_clean
    let segs_end := [S_clean, List.replicate n false, seg_inp]
    let M_end := (encodeWorkspace segs_end).length
    ∃ τ_end : ℕ → Bool,
      M_end = (encodeWorkspace [S_clean, List.replicate n false]).length + 1 + seg_inp.length ∧
      TapeWS τ_end (3 * M_end) B segs_end ∧
      (∀ p, 3 * M_end ≤ p → τ_end p = false) ∧
      StepExec (buildSegInp R) B (r, Sum.inl (liftBlkEntry 0))
        (3 * (encodeWorkspace [S_clean, List.replicate n false]).length) τ₀ 0
        (r, Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))) (3 * M_end) τ_end 0
        ((n + S_clean.length + 4) * (40 * M_end + 40)) := by
  intro seg_inp segs_end M_end
  let MaxSeg := 8 + R + 5
  have hM_end : M_end = (encodeWorkspace [S_clean, List.replicate n false]).length + 1 + seg_inp.length := by
    have h1 := encodeWorkspace_append_length [S_clean, List.replicate n false] [seg_inp] (by simp)
    simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h1
    dsimp only [M_end, segs_end]; omega
  have hseg_inp_len : seg_inp.length = n + (if r then 0 else 1) + S_clean.length := by
    dsimp only [seg_inp]; cases hr : r <;> simp; omega
  have hB_end : 3 * M_end ≤ B := hB
  -- 1) push empty seg 2
  rcases pushEmptySeg_spec B [S_clean, List.replicate n false] htw₀ (by omega)
    with ⟨τ1, htw1, hM1, hout1, he1⟩
  simp only [List.cons_append, List.nil_append] at htw1 hM1 he1
  have hcl1 : ∀ p, 3 * (encodeWorkspace [S_clean, List.replicate n false, []]).length ≤ p → τ1 p = false := by
    intro p hp; rw [hout1 p (by omega)]; exact hclean₀ p (by omega)
  -- 2) copy seg 1 (override true) into seg 2
  rcases wsCopySegToLast_spec MaxSeg B ⟨1, by omega⟩ (some true)
      [S_clean, List.replicate n false, []] (by simp) htw1 hcl1 (by simp; omega)
    with ⟨τ2, hM2, htw2, hcl2, he2⟩
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero,
    List.nil_append, List.length_replicate] at hM2 htw2 hcl2 he2
  -- 3) if ¬r append false to seg 2
  let mid2 := List.replicate n true ++ (if r then [] else [false])
  have hstep3 : ∃ q3, ∃ τ3 : ℕ → Bool,
      (encodeWorkspace [S_clean, List.replicate n false, mid2]).length =
        (encodeWorkspace [S_clean, List.replicate n false]).length + 1 + n + (if r then 0 else 1) ∧
      TapeWS τ3 (3 * (encodeWorkspace [S_clean, List.replicate n false, mid2]).length) B
        [S_clean, List.replicate n false, mid2] ∧
      (∀ p, 3 * (encodeWorkspace [S_clean, List.replicate n false, mid2]).length ≤ p → τ3 p = false) ∧
      StepExec (sumStep (nopStep Unit) (liftBlockStep (blkGrowLast (blkData false false)))) B
        (if r then Sum.inl () else Sum.inr (liftBlkEntry 0))
        (3 * (encodeWorkspace [S_clean, List.replicate n false, List.replicate n true]).length) τ2 0
        q3 (3 * (encodeWorkspace [S_clean, List.replicate n false, mid2]).length) τ3 0
        (14 * M_end + 18) := by
    cases hr : r with
    | true =>
      have hmid_eq : mid2 = List.replicate n true := by simp [mid2, hr]
      rw [hmid_eq]
      have h1B : 1 ≤ B := by have := TapeWS_pos htw2; have := htw2.2.2.1; omega
      exact ⟨Sum.inl (), τ2, by simp only [↓reduceIte]; omega, htw2, hcl2,
        (sumStep_inl_spec (nopStep Unit) _ (nopStep_spec (B := B) () _ τ2 0 htw2.2.2.1 h1B)).weaken _ (by omega)⟩
    | false =>
      have hmid_eq : mid2 = List.replicate n true ++ [false] := by simp [mid2, hr]
      rw [hmid_eq]
      have hB3 : 3 * ((encodeWorkspace [S_clean, List.replicate n false, List.replicate n true]).length + 1) ≤ B := by
        simp only [hr, Bool.false_eq_true, ↓reduceIte] at hseg_inp_len; omega
      rcases appendBitLast_spec B false [S_clean, List.replicate n false, List.replicate n true] htw2 hB3
        with ⟨τ3, htw3, hM3, hout3, he3⟩
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
        List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero] at htw3 hM3 he3
      have hM2_le : (encodeWorkspace [S_clean, List.replicate n false, List.replicate n true]).length ≤ M_end := by omega
      refine ⟨Sum.inr (liftBlkExit 2), τ3, by simp only [Bool.false_eq_true, ↓reduceIte]; omega, htw3, ?_,
        (sumStep_inr_spec (nopStep Unit) _ he3).weaken (14 * M_end + 18) (by omega)⟩
      intro p hp; rw [hout3 p (by omega)]; exact hcl2 p (by omega)
  rcases hstep3 with ⟨q3, τ3, hM3, htw3, hcl3, he3⟩
  -- 4) copy seg 0 (`S_clean`) into seg 2
  rcases wsCopySegToLast_spec MaxSeg B ⟨0, by omega⟩ none
      [S_clean, List.replicate n false, mid2] (by simp) htw3 hcl3 (by simp; omega)
    with ⟨τ4, hM4, htw4, hcl4, he4⟩
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero] at hM4 htw4 hcl4 he4
  have hlen0_pos := TapeWS_pos htw₀
  have hlen1_pos := TapeWS_pos htw1
  have hlen2_pos := TapeWS_pos htw2
  have hlen3_pos := TapeWS_pos htw3
  have he34 := seq0_spec (f := fun _ => Sum.inl (liftBlkEntry ((⟨0, by omega⟩ : Fin (MaxSeg + 1)), 0, false, false))) hlen3_pos he3 he4
  have he24 := seq0_spec (f := fun _ => Sum.inl (if r then Sum.inl () else Sum.inr (liftBlkEntry 0))) hlen2_pos he2 he34
  have he14 : StepExec (buildSegInpFor R r) B (Sum.inl (liftBlkEntry 0))
      (3 * (encodeWorkspace [S_clean, List.replicate n false]).length) τ₀ 0
      (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))) (3 * M_end) τ4 0
      ((n + S_clean.length + 4) * (40 * M_end + 40)) := by
    unfold buildSegInpFor
    have hseq := seq0_spec (f := fun _ => Sum.inl (Sum.inl (liftBlkEntry ((⟨1, by omega⟩ : Fin (MaxSeg + 1)), 0, false, false))))
      hlen1_pos he1 he24
    have hM2_le : (encodeWorkspace [S_clean, List.replicate n false, List.replicate n true]).length ≤ M_end := by omega
    have hM0_le : (encodeWorkspace [S_clean, List.replicate n false]).length ≤ M_end := by omega
    have h2_le : (n + 1) * (36 * (encodeWorkspace [S_clean, List.replicate n false, List.replicate n true]).length + 30) ≤
        (n + 1) * (36 * M_end + 30) := Nat.mul_le_mul_left _ (by omega)
    have htot_t : (14 * (encodeWorkspace [S_clean, List.replicate n false]).length + 18) + 1 +
        ((n + 1) * (36 * (encodeWorkspace [S_clean, List.replicate n false, List.replicate n true]).length + 30) + 1 +
          ((14 * M_end + 18) + 1 + (S_clean.length + 1) * (36 * M_end + 30))) ≤
        (n + S_clean.length + 4) * (40 * M_end + 40) := by
      have hexp : (n + S_clean.length + 4) * (40 * M_end + 40) =
          (n + 1) * (40 * M_end + 40) + (S_clean.length + 1) * (40 * M_end + 40) + 2 * (40 * M_end + 40) := by ring
      have h_a : (n + 1) * (36 * M_end + 30) ≤ (n + 1) * (40 * M_end + 40) := Nat.mul_le_mul_left _ (by omega)
      have h_b : (S_clean.length + 1) * (36 * M_end + 30) ≤ (S_clean.length + 1) * (40 * M_end + 40) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    exact hseq.weaken _ htot_t
  exact ⟨τ4, hM_end, htw4, hcl4, familyStep_spec (buildSegInpFor R) r he14⟩

/-! #### Stages D, F, H: `pushZeroReg` and `pushZeroRegs` -/

abbrev PushZeroRegQ (R wMul wAdd : ℕ) : Type :=
  LiftBlkQ (Fin 3) ⊕
    (Repeat0Q wAdd (LiftBlkQ (Fin 3)) ⊕
      Repeat0Q wMul (WsCopyLastQ (8 + R + 5)))

def pushZeroReg (R wMul wAdd : ℕ) : StepFn (PushZeroRegQ R wMul wAdd) :=
  let MaxSeg := 8 + R + 5
  seq0 (liftBlockStep (blkGrowLast blkSep))
    (seq0 (repeat0 wAdd (liftBlockStep (blkGrowLast (blkData false false))) (liftBlkEntry 0))
      (repeat0 wMul (wsCopySegToLast MaxSeg ⟨1, by omega⟩ (some false))
        (Sum.inl (liftBlkEntry (⟨1, by omega⟩, 0, false, false))))
      (fun _ => repeat0Entry wMul (Sum.inl (liftBlkEntry (⟨1, by omega⟩, 0, false, false)))))
    (fun _ => Sum.inl (repeat0Entry wAdd (liftBlkEntry 0)))

def pushZeroRegEntry (R wMul wAdd : ℕ) : PushZeroRegQ R wMul wAdd :=
  Sum.inl (liftBlkEntry 0)

theorem pushZeroReg_spec (R wMul wAdd B n : ℕ) (segs : List (List Bool))
    (hlen2 : 2 ≤ segs.length)
    (hseg1 : segs.getD 1 [] = List.replicate n false)
    {τ₀ : ℕ → Bool}
    (htw₀ : TapeWS τ₀ (3 * (encodeWorkspace segs).length) B segs)
    (hclean₀ : ∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₀ p = false)
    (hB : 3 * ((encodeWorkspace segs).length + 1 + (wMul * n + wAdd)) ≤ B) :
    let w_reg := wMul * n + wAdd
    let segs_end := segs ++ [natToBitsLE w_reg 0]
    let M_end := (encodeWorkspace segs_end).length
    ∃ q_end, ∃ τ_end : ℕ → Bool,
      M_end = (encodeWorkspace segs).length + 1 + w_reg ∧
      TapeWS τ_end (3 * M_end) B segs_end ∧
      (∀ p, 3 * M_end ≤ p → τ_end p = false) ∧
      StepExec (pushZeroReg R wMul wAdd) B (pushZeroRegEntry R wMul wAdd)
        (3 * (encodeWorkspace segs).length) τ₀ 0
        q_end (3 * M_end) τ_end 0
        ((wMul * (n + 1) + wAdd + 2) * (40 * M_end + 40)) := by
  intro w_reg segs_end M_end
  let MaxSeg := 8 + R + 5
  have hne : segs ≠ [] := htw₀.1
  have hM_end : M_end = (encodeWorkspace segs).length + 1 + w_reg := by
    have h1 := encodeWorkspace_append_length segs [natToBitsLE w_reg 0] hne
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, length_natToBitsLE] at h1
    dsimp only [M_end, segs_end]; omega
  have hB_end : 3 * M_end ≤ B := by dsimp only [w_reg] at hM_end; omega
  -- 1) push empty seg
  rcases pushEmptySeg_spec B segs htw₀ (by omega) with ⟨τ1, htw1, hM1, hout1, he1⟩
  have hcl1 : ∀ p, 3 * (encodeWorkspace (segs ++ [[]])).length ≤ p → τ1 p = false := by
    intro p hp; rw [hout1 p (by omega)]; exact hclean₀ p (by omega)
  -- 2) repeat0 wAdd appendBitLast false
  let InvA : ℕ → ℕ → (ℕ → Bool) → Prop := fun j l_cur τ_cur =>
    let s_j := segs ++ [List.replicate j false]
    let M_j := (encodeWorkspace s_j).length
    M_j = (encodeWorkspace segs).length + 1 + j ∧
    l_cur = 3 * M_j ∧
    TapeWS τ_cur (3 * M_j) B s_j ∧
    (∀ p, 3 * M_j ≤ p → τ_cur p = false)
  have hstepA : ∀ j < wAdd, ∀ l_cur τ_cur, InvA j l_cur τ_cur →
      ∃ q_e l' τ', InvA (j + 1) l' τ' ∧ 1 ≤ l' ∧
        StepExec (liftBlockStep (blkGrowLast (blkData false false))) B (liftBlkEntry 0)
          l_cur τ_cur 0 q_e l' τ' 0 (14 * M_end + 18) := by
    intro j hj l_cur τ_cur ⟨hMj, hl_eq, htw_j, hcl_j⟩
    subst l_cur
    let s_j := segs ++ [List.replicate j false]
    have hMj_eq : (encodeWorkspace s_j).length = (encodeWorkspace segs).length + 1 + j := hMj
    have hB_j : 3 * ((encodeWorkspace s_j).length + 1) ≤ B := by dsimp only [w_reg] at hM_end; omega
    rcases appendBitLast_spec B false s_j htw_j hB_j with ⟨τ', htw', hM', hout', he'⟩
    have hs_next : s_j.set (s_j.length - 1) (s_j.getD (s_j.length - 1) [] ++ [false]) =
        segs ++ [List.replicate (j + 1) false] := by
      dsimp only [s_j]
      have hlen_sj : (segs ++ [List.replicate j false]).length - 1 = segs.length := by simp
      rw [hlen_sj, List.set_append]
      simp only [Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, List.set_cons_zero]
      have hget : (segs ++ [List.replicate j false]).getD segs.length [] = List.replicate j false := by
        rw [getD_append_right _ _ _ (Nat.le_refl _), Nat.sub_self]; rfl
      rw [hget, List.replicate_succ']
    rw [hs_next] at htw' hM' he'
    have hMj_le : (encodeWorkspace s_j).length ≤ M_end := by dsimp only [w_reg] at hM_end; omega
    refine ⟨liftBlkExit 2, 3 * (encodeWorkspace (segs ++ [List.replicate (j + 1) false])).length, τ',
      ⟨by omega, rfl, htw', fun p hp => by rw [hout' p (by omega)]; exact hcl_j p (by omega)⟩,
      TapeWS_pos htw', he'.weaken (14 * M_end + 18) (by omega)⟩
  rcases repeat0_spec wAdd (liftBlockStep (blkGrowLast (blkData false false))) (liftBlkEntry 0)
      B (14 * M_end + 18) InvA hstepA
      (fun l_cur _ ⟨_, hl0, htw0, _⟩ => ⟨by rw [hl0]; exact htw0.2.2.1,
        by have := TapeWS_pos htw0; have := htw0.2.2.1; omega⟩)
      (len₀ := 3 * (encodeWorkspace (segs ++ [[]])).length)
      ⟨by simpa using hM1, rfl, by simpa using htw1, by simpa using hcl1⟩
    with ⟨len2, τ2, ⟨hM2, hlen2_eq, htw2, hcl2⟩, he2⟩
  subst len2
  -- 3) repeat0 wMul (wsCopySegToLast MaxSeg 1 (some false))
  let InvM : ℕ → ℕ → (ℕ → Bool) → Prop := fun j l_cur τ_cur =>
    let s_j := segs ++ [List.replicate (wAdd + j * n) false]
    let M_j := (encodeWorkspace s_j).length
    M_j = (encodeWorkspace segs).length + 1 + (wAdd + j * n) ∧
    l_cur = 3 * M_j ∧
    TapeWS τ_cur (3 * M_j) B s_j ∧
    (∀ p, 3 * M_j ≤ p → τ_cur p = false)
  have hstepM : ∀ j < wMul, ∀ l_cur τ_cur, InvM j l_cur τ_cur →
      ∃ q_e l' τ', InvM (j + 1) l' τ' ∧ 1 ≤ l' ∧
        StepExec (wsCopySegToLast MaxSeg ⟨1, by omega⟩ (some false)) B
          (Sum.inl (liftBlkEntry (⟨1, by omega⟩, 0, false, false)))
          l_cur τ_cur 0 q_e l' τ' 0 ((n + 1) * (36 * M_end + 30)) := by
    intro j hj l_cur τ_cur ⟨hMj, hl_eq, htw_j, hcl_j⟩
    subst l_cur
    let s_j := segs ++ [List.replicate (wAdd + j * n) false]
    have hMj_eq : (encodeWorkspace s_j).length = (encodeWorkspace segs).length + 1 + (wAdd + j * n) := hMj
    have hs1_j : s_j.getD 1 [] = List.replicate n false := by
      dsimp only [s_j]; rw [getD_append_left _ _ _ (by omega), hseg1]
    have hjn_le : (j + 1) * n ≤ wMul * n := Nat.mul_le_mul_right n (by omega)
    have hjn_add : (j + 1) * n = j * n + n := by ring
    have hB_j : 3 * ((encodeWorkspace s_j).length + (s_j.getD 1 []).length) ≤ B := by
      rw [hs1_j, List.length_replicate]; dsimp only [w_reg] at hM_end; omega
    rcases wsCopySegToLast_spec MaxSeg B ⟨1, by omega⟩ (some false) s_j (by simp [s_j]; omega)
        htw_j hcl_j hB_j
      with ⟨τ', hM', htw', hcl', he'⟩
    have hs_next : s_j.set (s_j.length - 1) (s_j.getD (s_j.length - 1) [] ++ List.replicate (s_j.getD 1 []).length false) =
        segs ++ [List.replicate (wAdd + (j + 1) * n) false] := by
      dsimp only [s_j]
      have hlen_sj : (segs ++ [List.replicate (wAdd + j * n) false]).length - 1 = segs.length := by simp
      rw [hlen_sj, List.set_append]
      simp only [Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, List.set_cons_zero]
      have hget : (segs ++ [List.replicate (wAdd + j * n) false]).getD segs.length [] =
          List.replicate (wAdd + j * n) false := by
        rw [getD_append_right _ _ _ (Nat.le_refl _), Nat.sub_self]; rfl
      rw [hget, hs1_j, List.length_replicate, ← List.replicate_add,
          show wAdd + j * n + n = wAdd + (j + 1) * n by ring]
    rw [hs_next] at hM' htw' hcl' he'
    rw [hs1_j, List.length_replicate] at hM' he'
    have hM'_le : (encodeWorkspace (segs ++ [List.replicate (wAdd + (j + 1) * n) false])).length ≤ M_end := by
      dsimp only [w_reg] at hM_end; omega
    refine ⟨Sum.inr (Sum.inl ()), 3 * (encodeWorkspace (segs ++ [List.replicate (wAdd + (j + 1) * n) false])).length, τ',
      ⟨by omega, rfl, htw', hcl'⟩,
      TapeWS_pos htw',
      he'.weaken ((n + 1) * (36 * M_end + 30)) (Nat.mul_le_mul_left (n + 1) (by omega))⟩
  rcases repeat0_spec wMul (wsCopySegToLast MaxSeg ⟨1, by omega⟩ (some false))
      (Sum.inl (liftBlkEntry (⟨1, by omega⟩, 0, false, false)))
      B ((n + 1) * (36 * M_end + 30)) InvM hstepM
      (fun l_cur _ ⟨_, hl0, htw0, _⟩ => ⟨by rw [hl0]; exact htw0.2.2.1,
        by have := TapeWS_pos htw0; have := htw0.2.2.1; omega⟩)
      (len₀ := 3 * (encodeWorkspace (segs ++ [List.replicate wAdd false])).length)
      ⟨by simpa using hM2, by simp, by simpa using htw2, by simpa using hcl2⟩
    with ⟨len3, τ3, ⟨hM3, hlen3_eq, htw3, hcl3⟩, he3⟩
  subst len3
  have hrep_eq : List.replicate (wAdd + wMul * n) false = natToBitsLE w_reg 0 := by
    rw [natToBitsLE_zero_eq_replicate, show wAdd + wMul * n = w_reg by dsimp only [w_reg]; omega]
  rw [hrep_eq] at hM3 htw3 hcl3 he3
  have he23 := seq0_spec (f := fun _ => repeat0Entry wMul (Sum.inl (liftBlkEntry ((⟨1, by omega⟩ : Fin (MaxSeg + 1)), 0, false, false))))
    (TapeWS_pos htw2) he2 he3
  have he13 : StepExec (pushZeroReg R wMul wAdd) B (pushZeroRegEntry R wMul wAdd)
      (3 * (encodeWorkspace segs).length) τ₀ 0
      (Sum.inr (Sum.inr (repeat0Exit wMul))) (3 * M_end) τ3 0
      ((wMul * (n + 1) + wAdd + 2) * (40 * M_end + 40)) := by
    unfold pushZeroReg pushZeroRegEntry
    have hseq := seq0_spec (f := fun _ => Sum.inl (repeat0Entry wAdd (liftBlkEntry 0)))
      (TapeWS_pos htw1) he1 he23
    have htime : 14 * (encodeWorkspace segs).length + 18 + 1 +
        (wAdd * (14 * M_end + 18 + 2) + 1 + wMul * ((n + 1) * (36 * M_end + 30) + 2)) ≤
        (wMul * (n + 1) + wAdd + 2) * (40 * M_end + 40) := by
      have h18 : 14 * M_end + 18 + 2 = 14 * M_end + 20 := by omega
      rw [h18]
      have h1 : wAdd * (14 * M_end + 20) ≤ wAdd * (40 * M_end + 40) := Nat.mul_le_mul_left _ (by omega)
      have h2 : wMul * ((n + 1) * (36 * M_end + 30) + 2) ≤ wMul * ((n + 1) * (40 * M_end + 40)) := by
        apply Nat.mul_le_mul_left
        have : 1 * (4 * M_end + 10) ≤ (n + 1) * (4 * M_end + 10) := Nat.mul_le_mul_right _ (by omega)
        have : (n + 1) * (40 * M_end + 40) = (n + 1) * (36 * M_end + 30) + (n + 1) * (4 * M_end + 10) := by ring
        omega
      have hexp : (wMul * (n + 1) + wAdd + 2) * (40 * M_end + 40) =
          wMul * ((n + 1) * (40 * M_end + 40)) + wAdd * (40 * M_end + 40) + 2 * (40 * M_end + 40) := by ring
      omega
    exact hseq.weaken _ htime
  exact ⟨_, τ3, hM_end, htw3, hcl3, he13⟩

def pushZeroRegs (R wMul wAdd count : ℕ) : StepFn (Repeat0Q count (PushZeroRegQ R wMul wAdd)) :=
  repeat0 count (pushZeroReg R wMul wAdd) (pushZeroRegEntry R wMul wAdd)

def pushZeroRegsEntry (R wMul wAdd count : ℕ) : Repeat0Q count (PushZeroRegQ R wMul wAdd) :=
  repeat0Entry count (pushZeroRegEntry R wMul wAdd)

theorem pushZeroRegs_spec (R wMul wAdd count B n : ℕ) (segs : List (List Bool))
    (hlen2 : 2 ≤ segs.length)
    (hseg1 : segs.getD 1 [] = List.replicate n false)
    {τ₀ : ℕ → Bool}
    (htw₀ : TapeWS τ₀ (3 * (encodeWorkspace segs).length) B segs)
    (hclean₀ : ∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₀ p = false)
    (hB : 3 * ((encodeWorkspace segs).length + count * (wMul * n + wAdd + 1)) ≤ B) :
    let w_reg := wMul * n + wAdd
    let segs_end := segs ++ List.replicate count (natToBitsLE w_reg 0)
    let M_end := (encodeWorkspace segs_end).length
    ∃ τ_end : ℕ → Bool,
      M_end = (encodeWorkspace segs).length + count * (w_reg + 1) ∧
      TapeWS τ_end (3 * M_end) B segs_end ∧
      (∀ p, 3 * M_end ≤ p → τ_end p = false) ∧
      StepExec (pushZeroRegs R wMul wAdd count) B (pushZeroRegsEntry R wMul wAdd count)
        (3 * (encodeWorkspace segs).length) τ₀ 0
        (repeat0Exit count) (3 * M_end) τ_end 0
        (count * ((wMul * (n + 1) + wAdd + 2) * (40 * M_end + 40) + 2)) := by
  intro w_reg segs_end M_end
  have hne : segs ≠ [] := htw₀.1
  have hrep_sum : ∀ k, ((List.replicate k (natToBitsLE w_reg 0)).map (fun l => l.length + 1)).sum = k * (w_reg + 1) := by
    intro k; induction k with
    | zero => simp
    | succ k ih => simp [List.replicate_succ, length_natToBitsLE]; ring
  have hM_end : M_end = (encodeWorkspace segs).length + count * (w_reg + 1) := by
    rw [show M_end = (encodeWorkspace (segs ++ List.replicate count (natToBitsLE w_reg 0))).length from rfl,
        encodeWorkspace_append_length _ _ hne, hrep_sum]
  have hB_end : 3 * M_end ≤ B := by dsimp only [w_reg] at hM_end; omega
  let Inv : ℕ → ℕ → (ℕ → Bool) → Prop := fun j l_cur τ_cur =>
    let s_j := segs ++ List.replicate j (natToBitsLE w_reg 0)
    let M_j := (encodeWorkspace s_j).length
    M_j = (encodeWorkspace segs).length + j * (w_reg + 1) ∧
    l_cur = 3 * M_j ∧
    TapeWS τ_cur (3 * M_j) B s_j ∧
    (∀ p, 3 * M_j ≤ p → τ_cur p = false)
  have hstep : ∀ j < count, ∀ l_cur τ_cur, Inv j l_cur τ_cur →
      ∃ q_e l' τ', Inv (j + 1) l' τ' ∧ 1 ≤ l' ∧
        StepExec (pushZeroReg R wMul wAdd) B (pushZeroRegEntry R wMul wAdd)
          l_cur τ_cur 0 q_e l' τ' 0 ((wMul * (n + 1) + wAdd + 2) * (40 * M_end + 40)) := by
    intro j hj l_cur τ_cur ⟨hMj, hl_eq, htw_j, hcl_j⟩
    subst l_cur
    let s_j := segs ++ List.replicate j (natToBitsLE w_reg 0)
    have hMj_eq : (encodeWorkspace s_j).length = (encodeWorkspace segs).length + j * (w_reg + 1) := hMj
    have hmul_le : (j + 1) * (w_reg + 1) ≤ count * (w_reg + 1) := Nat.mul_le_mul_right _ (by omega)
    have hmul_eq : (j + 1) * (w_reg + 1) = j * (w_reg + 1) + (w_reg + 1) := by ring
    rcases pushZeroReg_spec R wMul wAdd B n s_j (by simp [s_j]; omega)
        (by dsimp only [s_j]; rw [getD_append_left _ _ _ (by omega), hseg1])
        htw_j hcl_j (by dsimp only [w_reg] at hMj_eq hmul_le hmul_eq hM_end; omega)
      with ⟨q_e, τ', hM', htw', hcl', he'⟩
    have hs_next : s_j ++ [natToBitsLE w_reg 0] = segs ++ List.replicate (j + 1) (natToBitsLE w_reg 0) := by
      dsimp only [s_j]; rw [List.append_assoc, ← List.replicate_succ']
    rw [hs_next] at hM' htw' hcl' he'
    change (encodeWorkspace (segs ++ List.replicate (j + 1) (natToBitsLE w_reg 0))).length =
      (encodeWorkspace s_j).length + 1 + w_reg at hM'
    have hM'_eq : (encodeWorkspace (segs ++ List.replicate (j + 1) (natToBitsLE w_reg 0))).length =
        (encodeWorkspace segs).length + (j + 1) * (w_reg + 1) := by omega
    have hM'_le : (encodeWorkspace (segs ++ List.replicate (j + 1) (natToBitsLE w_reg 0))).length ≤ M_end := by omega
    refine ⟨q_e, 3 * (encodeWorkspace (segs ++ List.replicate (j + 1) (natToBitsLE w_reg 0))).length, τ',
      ⟨hM'_eq, rfl, htw', hcl'⟩, TapeWS_pos htw',
      he'.weaken _ (Nat.mul_le_mul_left _ (by omega))⟩
  rcases repeat0_spec count (pushZeroReg R wMul wAdd) (pushZeroRegEntry R wMul wAdd)
      B ((wMul * (n + 1) + wAdd + 2) * (40 * M_end + 40)) Inv hstep
      (fun l_cur _ ⟨_, hl0, htw0, _⟩ => ⟨by rw [hl0]; exact htw0.2.2.1,
        by have := TapeWS_pos htw0; have := htw0.2.2.1; omega⟩)
      (len₀ := 3 * (encodeWorkspace segs).length)
      ⟨by simp, by simp, by simpa using htw₀, by simpa using hclean₀⟩
    with ⟨len_end, τ_end, ⟨_, hlen_eq, htw_end, hcl_end⟩, he_rep⟩
  subst len_end
  exact ⟨τ_end, hM_end, htw_end, hcl_end, he_rep⟩

/-! #### Stage E: `computeLbuf` (`seg 4 := K_L * (n + 2) ^ d_L`) -/

abbrev ComputeLbufQ (R K_L d_L : ℕ) : Type :=
  let MaxSeg := 8 + R + 5
  WsAddSegLenQ MaxSeg 1 ⊕
    (LiftBlkQ (Fin (MaxSeg + 1) × Bool) ⊕
      (LiftBlkQ (Fin (MaxSeg + 1) × Bool) ⊕
        (LiftBlkQ (Fin (MaxSeg + 1) × Fin (Nat.log 2 K_L + 2) × Bool) ⊕
          Repeat0Q d_L (WsMulIntoQ MaxSeg))))

def computeLbuf (R K_L d_L : ℕ) : StepFn (ComputeLbufQ R K_L d_L) :=
  let MaxSeg := 8 + R + 5
  let s1 : Fin (MaxSeg + 1) := ⟨1, by omega⟩
  let s3 : Fin (MaxSeg + 1) := ⟨3, by omega⟩
  let s4 : Fin (MaxSeg + 1) := ⟨4, by omega⟩
  let s5 : Fin (MaxSeg + 1) := ⟨5, by omega⟩
  let s6 : Fin (MaxSeg + 1) := ⟨6, by omega⟩
  let s7 : Fin (MaxSeg + 1) := ⟨7, by omega⟩
  seq0 (wsAddSegLen MaxSeg 1 s1 s3)
    (seq0 (wsInc MaxSeg)
      (seq0 (wsInc MaxSeg)
        (seq0 (liftBlockStep (blkLoadConst MaxSeg K_L))
          (repeat0 d_L (wsMulInto MaxSeg s4 s3 s5 s6 s7) (Sum.inl (wsZeroEntry MaxSeg s5)))
          (fun _ => repeat0Entry d_L (Sum.inl (wsZeroEntry MaxSeg s5))))
        (fun _ => Sum.inl (liftBlkEntry (s4, 0, false))))
      (fun _ => Sum.inl (wsIncEntry MaxSeg s3)))
    (fun _ => Sum.inl (wsIncEntry MaxSeg s3))

def computeLbufEntry (R K_L d_L : ℕ) : ComputeLbufQ R K_L d_L :=
  Sum.inl (Sum.inl (liftBlkEntry (⟨1, by omega⟩, 0, false, false)))

theorem computeLbuf_spec (R K_L d_L B n w_reg : ℕ) (segs : List (List Bool))
    (hlen8 : segs.length = 8)
    (hseg1 : segs.getD 1 [] = List.replicate n false)
    (hseg3 : segs.getD 3 [] = natToBitsLE w_reg 0)
    (hseg4 : segs.getD 4 [] = natToBitsLE w_reg 0)
    (hseg5 : segs.getD 5 [] = natToBitsLE w_reg 0)
    (hseg6 : segs.getD 6 [] = natToBitsLE w_reg 0)
    (hseg7 : segs.getD 7 [] = natToBitsLE w_reg 0)
    (hlogK : Nat.log 2 K_L + 1 ≤ w_reg)
    (hn2_pow : n + 2 < 2 ^ w_reg)
    (hL_pow : K_L * (n + 2) ^ d_L < 2 ^ w_reg)
    {len : ℕ} {τ₀ : ℕ → Bool}
    (htw₀ : TapeWS τ₀ len B segs) :
    let M_blk := (encodeWorkspace segs).length
    let L_buf := K_L * (n + 2) ^ d_L
    ∃ segs_end, ∃ τ_end : ℕ → Bool,
      segs_end.length = 8 ∧
      (encodeWorkspace segs_end).length = M_blk ∧
      (∀ idx < 3, segs_end.getD idx [] = segs.getD idx []) ∧
      segs_end.getD 4 [] = natToBitsLE w_reg L_buf ∧
      TapeWS τ_end len B segs_end ∧
      (∀ p, 3 * M_blk ≤ p → τ_end p = τ₀ p) ∧
      StepExec (computeLbuf R K_L d_L) B (computeLbufEntry R K_L d_L) len τ₀ 0
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (repeat0Exit d_L))))) len τ_end 0
        ((d_L + 2) * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250)))) := by
  intro M_blk L_buf
  let MaxSeg := 8 + R + 5
  let s1 : Fin (MaxSeg + 1) := ⟨1, by omega⟩
  let s3 : Fin (MaxSeg + 1) := ⟨3, by omega⟩
  let s4 : Fin (MaxSeg + 1) := ⟨4, by omega⟩
  let s5 : Fin (MaxSeg + 1) := ⟨5, by omega⟩
  let s6 : Fin (MaxSeg + 1) := ⟨6, by omega⟩
  let s7 : Fin (MaxSeg + 1) := ⟨7, by omega⟩
  have hlen_pos := TapeWS_pos htw₀
  have hlen_B := htw₀.2.2.1
  -- 1) wsAddSegLen 1 s1 s3: seg 3 := n
  rcases wsAddSegLen_spec MaxSeg 1 B w_reg 0 s1 s3 segs
      (by dsimp only [s1, s3]; omega) (by dsimp only [s3]; omega) hseg3
      (by rw [hseg1, List.length_replicate]; omega) htw₀
    with ⟨τ1, htw1, hout1, he1⟩
  rw [hseg1, List.length_replicate, Nat.one_mul, Nat.zero_add] at htw1
  rw [hseg1, List.length_replicate] at he1
  let segs1 := segs.set 3 (natToBitsLE w_reg n)
  have hM1 : (encodeWorkspace segs1).length = M_blk :=
    length_encodeWorkspace_set (by omega) (by rw [hseg3, length_natToBitsLE, length_natToBitsLE])
  -- 2) wsInc s3: seg 3 := n + 1
  rcases wsInc_spec MaxSeg B segs1 (s := 3) (w := w_reg) (v := n)
      (by simp [segs1]; omega) (by omega) (getD_set_self_seg segs (by omega) _) (by omega) htw1
    with ⟨τ2, htw2, hout2, he2⟩
  rw [hM1] at hout2 he2
  simp only [segs1, List.set_set] at htw2
  let segs2 := segs.set 3 (natToBitsLE w_reg (n + 1))
  have hM2 : (encodeWorkspace segs2).length = M_blk :=
    length_encodeWorkspace_set (by omega) (by rw [hseg3, length_natToBitsLE, length_natToBitsLE])
  -- 3) wsInc s3: seg 3 := n + 2
  rcases wsInc_spec MaxSeg B segs2 (s := 3) (w := w_reg) (v := n + 1)
      (by simp [segs2]; omega) (by omega) (getD_set_self_seg segs (by omega) _) (by omega) htw2
    with ⟨τ3, htw3, hout3, he3⟩
  rw [hM2] at hout3 he3
  simp only [segs2, List.set_set] at htw3
  let segs3 := segs.set 3 (natToBitsLE w_reg (n + 2))
  have hM3 : (encodeWorkspace segs3).length = M_blk :=
    length_encodeWorkspace_set (by omega) (by rw [hseg3, length_natToBitsLE, length_natToBitsLE])
  -- 4) wsLoadConst K_L into s4: seg 4 := K_L
  rcases wsLoadConst_spec MaxSeg B K_L segs3 (s := 4) (w := w_reg)
      (by simp [segs3]; omega) (by omega)
      (by dsimp only [segs3]; rw [getD_set_ne_seg _ (by omega), hseg4])
      hlogK htw3
    with ⟨τ4, htw4, hout4, he4⟩
  rw [hM3] at hout4 he4
  let segs4 := segs3.set 4 (natToBitsLE w_reg K_L)
  have hM4 : (encodeWorkspace segs4).length = M_blk :=
    (length_encodeWorkspace_set (by simp [segs3]; omega)
      (by dsimp only [segs3]; rw [getD_set_ne_seg _ (by omega), hseg4, length_natToBitsLE, length_natToBitsLE])).trans hM3
  -- 5) repeat0 d_L (wsMulInto s4 s3 s5 s6 s7)
  have hpow_le : ∀ j ≤ d_L, K_L * (n + 2) ^ j ≤ L_buf := by
    intro j hj
    exact Nat.mul_le_mul_left K_L (Nat.pow_le_pow_right (by omega) hj)
  let T_mul := (L_buf + 2) * ((n + 5) * (450 * M_blk + 200))
  let Inv : ℕ → ℕ → (ℕ → Bool) → Prop := fun j l_cur τ_cur =>
    l_cur = len ∧
    ∃ sx : List (List Bool),
      sx.length = 8 ∧
      (encodeWorkspace sx).length = M_blk ∧
      (∀ idx < 3, sx.getD idx [] = segs.getD idx []) ∧
      sx.getD 3 [] = natToBitsLE w_reg (n + 2) ∧
      sx.getD 4 [] = natToBitsLE w_reg (K_L * (n + 2) ^ j) ∧
      (sx.getD 5 []).length = w_reg ∧
      (sx.getD 6 []).length = w_reg ∧
      (sx.getD 7 []).length = w_reg ∧
      TapeWS τ_cur len B sx ∧
      (∀ p, 3 * M_blk ≤ p → τ_cur p = τ4 p)
  have hstep : ∀ j < d_L, ∀ l_cur τ_cur, Inv j l_cur τ_cur →
      ∃ q_e l' τ', Inv (j + 1) l' τ' ∧ 1 ≤ l' ∧
        StepExec (wsMulInto MaxSeg s4 s3 s5 s6 s7) B (Sum.inl (wsZeroEntry MaxSeg s5))
          l_cur τ_cur 0 q_e l' τ' 0 T_mul := by
    intro j hj l_cur τ_cur ⟨hl_eq, sx, hlx, hMx, hothx, hx3, hx4, hx5, hx6, hx7, htw_x, hout_x⟩
    subst l_cur
    have hvb_le : K_L * (n + 2) ^ j ≤ L_buf := hpow_le j (by omega)
    have hprod_eq : K_L * (n + 2) ^ j * (n + 2) = K_L * (n + 2) ^ (j + 1) := by
      rw [Nat.pow_succ]; ring
    have hprod_le : K_L * (n + 2) ^ j * (n + 2) ≤ L_buf := by
      rw [hprod_eq]; exact hpow_le (j + 1) (by omega)
    rcases wsMulInto_spec MaxSeg B w_reg (n + 2) (K_L * (n + 2) ^ j) s4 s3 s5 s6 s7 sx
        (by dsimp only [s3, s4]; omega) (by dsimp only [s4, s5]; omega)
        (by dsimp only [s4, s6]; omega) (by dsimp only [s4, s7]; omega)
        (by dsimp only [s3, s5]; omega) (by dsimp only [s3, s6]; omega)
        (by dsimp only [s3, s7]; omega) (by dsimp only [s5, s6]; omega)
        (by dsimp only [s5, s7]; omega) (by dsimp only [s6, s7]; omega)
        (by dsimp only [s4]; omega) (by dsimp only [s3]; omega)
        (by dsimp only [s5]; omega) (by dsimp only [s6]; omega) (by dsimp only [s7]; omega)
        hx4 hx3 hx5 hx6 hx7 hn2_pow (by omega) (by omega) htw_x
      with ⟨sy, τy, hly, hMy, hy4, hy3, hy5, hy6, hy7, hyoth, htw_y, hout_y, he_mul⟩
    rw [hMx] at hMy hout_y he_mul
    rw [hprod_eq] at hy4
    have htm : (K_L * (n + 2) ^ j + 2) * ((n + 2 + 2) * (250 * M_blk + 100)) +
        (K_L * (n + 2) ^ j * (n + 2) + 2) * (160 * M_blk + 60) + 100 * M_blk + 50 ≤ T_mul := by
      dsimp only [T_mul]
      have h1 : (K_L * (n + 2) ^ j + 2) * ((n + 2 + 2) * (250 * M_blk + 100)) ≤
          (L_buf + 2) * ((n + 5) * (250 * M_blk + 100)) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega))
      have h2 : (K_L * (n + 2) ^ j * (n + 2) + 2) * (160 * M_blk + 60) ≤
          (L_buf + 2) * ((n + 5) * (160 * M_blk + 60)) := by
        apply Nat.mul_le_mul (by omega)
        exact Nat.le_mul_of_pos_left _ (by omega)
      have h3 : 100 * M_blk + 50 ≤ (L_buf + 2) * ((n + 5) * (40 * M_blk + 40)) := by
        have : 10 * (40 * M_blk + 40) ≤ (L_buf + 2) * ((n + 5) * (40 * M_blk + 40)) := by
          have ha : 2 * 5 ≤ (L_buf + 2) * (n + 5) := Nat.mul_le_mul (by omega) (by omega)
          have := Nat.mul_le_mul_right (40 * M_blk + 40) ha
          simpa [Nat.mul_assoc] using this
        omega
      have hexp : (L_buf + 2) * ((n + 5) * (450 * M_blk + 200)) =
          (L_buf + 2) * ((n + 5) * (250 * M_blk + 100)) +
          (L_buf + 2) * ((n + 5) * (160 * M_blk + 60)) +
          (L_buf + 2) * ((n + 5) * (40 * M_blk + 40)) := by ring
      omega
    refine ⟨_, len, τy, ⟨rfl, sy, by omega, hMy, ?_, hy3, hy4, hy5, hy6, hy7, htw_y,
        fun p hp => (hout_y p hp).trans (hout_x p hp)⟩, hlen_pos, he_mul.weaken T_mul htm⟩
    intro idx hidx
    rw [hyoth idx (by dsimp only [s4]; omega) (by dsimp only [s5]; omega)
        (by dsimp only [s6]; omega) (by dsimp only [s7]; omega)]
    exact hothx idx hidx
  have hinv0 : Inv 0 len τ4 := by
    refine ⟨rfl, segs4, by simp [segs4, segs3, hlen8], hM4, ?_, ?_, ?_, ?_, ?_, ?_, htw4, fun _ _ => rfl⟩
    · intro idx hidx; dsimp only [segs4, segs3]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]
    · dsimp only [segs4, segs3]; rw [getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by omega)]
    · dsimp only [segs4]; rw [Nat.pow_zero, Nat.mul_one, getD_set_self_seg _ (by simp [segs3]; omega)]
    · dsimp only [segs4, segs3]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), hseg5, length_natToBitsLE]
    · dsimp only [segs4, segs3]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), hseg6, length_natToBitsLE]
    · dsimp only [segs4, segs3]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), hseg7, length_natToBitsLE]
  rcases repeat0_spec d_L (wsMulInto MaxSeg s4 s3 s5 s6 s7) (Sum.inl (wsZeroEntry MaxSeg s5))
      B T_mul Inv hstep (fun _ _ ⟨hl_eq, _⟩ => ⟨by rw [hl_eq]; exact hlen_B, by omega⟩) hinv0
    with ⟨len_end, τ_end, ⟨hlen_eq, segs_end, hl_end, hM_end, hoth_end, _, h4_end, _, _, _, htw_end, hout_end⟩, he5⟩
  subst len_end
  have he45 := seq0_spec (f := fun _ => repeat0Entry d_L (Sum.inl (wsZeroEntry MaxSeg s5))) hlen_pos he4 he5
  have he35 := seq0_spec (f := fun _ => Sum.inl (liftBlkEntry (s4, 0, false))) hlen_pos he3 he45
  have he25 := seq0_spec (f := fun _ => Sum.inl (wsIncEntry MaxSeg s3)) hlen_pos he2 he35
  have he15 : StepExec (computeLbuf R K_L d_L) B (computeLbufEntry R K_L d_L) len τ₀ 0
      (Sum.inr (Sum.inr (Sum.inr (Sum.inr (repeat0Exit d_L))))) len τ_end 0
      ((d_L + 2) * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250)))) := by
    unfold computeLbuf computeLbufEntry
    have hseq := seq0_spec (f := fun _ => Sum.inl (wsIncEntry MaxSeg s3)) hlen_pos he1 he25
    have htime : (n + 1) * (21 * M_blk + 6 + 1 * (21 * M_blk + 6) + 2) + 1 +
        ((21 * M_blk + 4) + 1 + ((21 * M_blk + 4) + 1 + ((21 * M_blk + 4) + 1 + d_L * (T_mul + 2)))) ≤
        (d_L + 2) * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250))) := by
      have hpre : (n + 1) * (21 * M_blk + 6 + 1 * (21 * M_blk + 6) + 2) + 1 +
          ((21 * M_blk + 4) + 1 + ((21 * M_blk + 4) + 1 + ((21 * M_blk + 4) + 1))) ≤
          2 * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250))) := by
        have h1 : (n + 1) * (21 * M_blk + 6 + 1 * (21 * M_blk + 6) + 2) ≤ (n + 5) * (42 * M_blk + 30) :=
          Nat.mul_le_mul (by omega) (by omega)
        have h2 : (n + 5) * (42 * M_blk + 30) + 63 * M_blk + 16 ≤ (n + 5) * (105 * M_blk + 50) := by
          have : 1 * (63 * M_blk + 20) ≤ (n + 5) * (63 * M_blk + 20) := Nat.mul_le_mul_right _ (by omega)
          have : (n + 5) * (105 * M_blk + 50) = (n + 5) * (42 * M_blk + 30) + (n + 5) * (63 * M_blk + 20) := by ring
          omega
        have h3 : (n + 5) * (105 * M_blk + 50) ≤ (L_buf + 2) * ((n + 5) * (500 * M_blk + 250)) := by
          have ha : (n + 5) * (105 * M_blk + 50) ≤ (n + 5) * (500 * M_blk + 250) := Nat.mul_le_mul_left _ (by omega)
          have hb := Nat.le_mul_of_pos_left ((n + 5) * (500 * M_blk + 250)) (show 0 < L_buf + 2 by omega)
          omega
        omega
      have hloop_le : d_L * (T_mul + 2) ≤ d_L * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250))) := by
        apply Nat.mul_le_mul_left
        dsimp only [T_mul]
        have : 2 ≤ (L_buf + 2) * ((n + 5) * (50 * M_blk + 50)) := by
          have : 1 * (1 * 50) ≤ (L_buf + 2) * ((n + 5) * (50 * M_blk + 50)) :=
            Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
          omega
        have hexp : (L_buf + 2) * ((n + 5) * (500 * M_blk + 250)) =
            (L_buf + 2) * ((n + 5) * (450 * M_blk + 200)) + (L_buf + 2) * ((n + 5) * (50 * M_blk + 50)) := by ring
        omega
      have hexp : (d_L + 2) * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250))) =
          d_L * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250))) +
          2 * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250))) := by ring
      omega
    exact hseq.weaken _ htime
  exact ⟨segs_end, τ_end, hl_end, hM_end, hoth_end, h4_end, htw_end,
    fun p hp => (hout_end p hp).trans ((hout4 p hp).trans ((hout3 p hp).trans ((hout2 p hp).trans (hout1 p hp)))),
    he15⟩

/-! #### Stage G: `growOutBuf` (allocate `outBuf` of length `L_buf` by draining `seg 4`) -/

abbrev GrowOutBufLoopQ (R : ℕ) : Type :=
  WsDecJzQ (8 + R + 5) ⊕ (Unit ⊕ LiftBlkQ (Fin 3))

def growOutBufBody (R : ℕ) : StepFn (GrowOutBufLoopQ R) :=
  seq0 (wsDecJz (8 + R + 5))
    (sumStep (nopStep Unit) (liftBlockStep (blkGrowLast (blkData false false))))
    (fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (liftBlkEntry 0))

def growOutBufNext (R : ℕ) : GrowOutBufLoopQ R → Option (GrowOutBufLoopQ R)
  | Sum.inr (Sum.inr _) => some (Sum.inl (wsDecJzEntry (8 + R + 5) ⟨4, by omega⟩))
  | _ => none

abbrev GrowOutBufQ (R : ℕ) : Type :=
  LiftBlkQ (Fin 3) ⊕ GrowOutBufLoopQ R

def growOutBuf (R : ℕ) : StepFn (GrowOutBufQ R) :=
  seq0 (liftBlockStep (blkGrowLast blkSep))
    (loop0 (growOutBufBody R) (growOutBufNext R))
    (fun _ => Sum.inl (wsDecJzEntry (8 + R + 5) ⟨4, by omega⟩))

theorem growOutBuf_spec (R B w_reg L_buf : ℕ) (segs : List (List Bool))
    (hlen5 : 5 ≤ segs.length)
    (hseg4 : segs.getD 4 [] = natToBitsLE w_reg L_buf)
    (hL_pow : L_buf < 2 ^ w_reg)
    {τ₀ : ℕ → Bool}
    (htw₀ : TapeWS τ₀ (3 * (encodeWorkspace segs).length) B segs)
    (hclean₀ : ∀ p, 3 * (encodeWorkspace segs).length ≤ p → τ₀ p = false)
    (hB : 3 * ((encodeWorkspace segs).length + 1 + L_buf) ≤ B) :
    let segs_end := segs.set 4 (natToBitsLE w_reg 0) ++ [List.replicate L_buf false]
    let M_end := (encodeWorkspace segs_end).length
    ∃ τ_end : ℕ → Bool,
      M_end = (encodeWorkspace segs).length + 1 + L_buf ∧
      TapeWS τ_end (3 * M_end) B segs_end ∧
      (∀ p, 3 * M_end ≤ p → τ_end p = false) ∧
      StepExec (growOutBuf R) B (Sum.inl (liftBlkEntry 0))
        (3 * (encodeWorkspace segs).length) τ₀ 0
        (Sum.inr (Sum.inr (Sum.inl ()))) (3 * M_end) τ_end 0
        ((L_buf + 2) * (60 * M_end + 40)) := by
  intro segs_end M_end
  let MaxSeg := 8 + R + 5
  have hne : segs ≠ [] := htw₀.1
  have hM_end : M_end = (encodeWorkspace segs).length + 1 + L_buf := by
    have hne4 : segs.set 4 (natToBitsLE w_reg 0) ≠ [] := by
      intro h; have := congrArg List.length h; simp only [List.length_set, List.length_nil] at this; omega
    have h1 := encodeWorkspace_append_length (segs.set 4 (natToBitsLE w_reg 0)) [List.replicate L_buf false] hne4
    have h2 := length_encodeWorkspace_set (segs := segs) (s := 4) (newSeg := natToBitsLE w_reg 0)
      (by omega) (by rw [hseg4, length_natToBitsLE, length_natToBitsLE])
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_replicate] at h1
    dsimp only [M_end, segs_end]; omega
  -- 1) push empty seg
  rcases pushEmptySeg_spec B segs htw₀ (by omega) with ⟨τ1, htw1, hM1, hout1, he1⟩
  have hcl1 : ∀ p, 3 * (encodeWorkspace (segs ++ [[]])).length ≤ p → τ1 p = false := by
    intro p hp; rw [hout1 p (by omega)]; exact hclean₀ p (by omega)
  -- 2) loop draining seg 4 while appending false to last seg
  let S_it := 58 * M_end + 34
  have hloop : ∀ rem acc (τc : ℕ → Bool),
      rem + acc = L_buf →
      let segs_c := segs.set 4 (natToBitsLE w_reg rem) ++ [List.replicate acc false]
      let M_c := (encodeWorkspace segs_c).length
      M_c = (encodeWorkspace segs).length + 1 + acc →
      TapeWS τc (3 * M_c) B segs_c →
      (∀ p, 3 * M_c ≤ p → τc p = false) →
      ∃ τ_end : ℕ → Bool,
        TapeWS τ_end (3 * M_end) B segs_end ∧
        (∀ p, 3 * M_end ≤ p → τ_end p = false) ∧
        StepExec (loop0 (growOutBufBody R) (growOutBufNext R)) B
          (Sum.inl (wsDecJzEntry MaxSeg ⟨4, by omega⟩)) (3 * M_c) τc 0
          (Sum.inr (Sum.inl ())) (3 * M_end) τ_end 0 ((rem + 1) * (S_it + 2)) := by
    intro rem
    induction rem with
    | zero =>
      intro acc τc hsum segs_c M_c hMc htw_c hcl_c
      have hacc : acc = L_buf := by omega
      subst hacc
      have hMc_eq : M_c = M_end := by omega
      have hlen_pos := TapeWS_pos htw_c
      rcases wsDecJz_spec MaxSeg B segs_c (s := 4) (w := w_reg) (v := 0)
          (by simp [segs_c]; omega) (by omega)
          (by dsimp only [segs_c]; rw [getD_append_left _ _ _ (by simp; omega), getD_set_self_seg _ (by omega)])
          (by omega) htw_c
        with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
      simp only [decide_true, ↓reduceIte] at hz_dz htw_dz
      have he_nop := sumStep_inl_spec (nopStep Unit) (liftBlockStep (blkGrowLast (blkData false false)))
        (nopStep_spec (B := B) () (3 * M_c) τ_dz 0 htw_dz.2.2.1 (by omega))
      have he_body : StepExec (growOutBufBody R) B (Sum.inl (wsDecJzEntry MaxSeg ⟨4, by omega⟩))
          (3 * M_c) τc 0 (Sum.inr (Sum.inl ())) (3 * M_c) τ_dz 0 S_it := by
        unfold growOutBufBody
        exact (seq0_spec hlen_pos he_dz (by rw [hz_dz]; exact he_nop)).weaken S_it (by dsimp only [S_it]; omega)
      have hdone : StepExec (loop0 (growOutBufBody R) (growOutBufNext R)) B
          (Sum.inl (wsDecJzEntry MaxSeg ⟨4, by omega⟩)) (3 * M_c) τc 0
          (Sum.inr (Sum.inl ())) (3 * M_end) τ_dz 0 ((0 + 1) * (S_it + 2)) := by
        rw [← hMc_eq]
        exact (loop0_done (next := growOutBufNext R) he_body rfl).weaken _ (by omega)
      refine ⟨τ_dz, by rw [← hMc_eq]; exact htw_dz, ?_, hdone⟩
      intro p hp; rw [hout_dz p (by omega)]; exact hcl_c p (by omega)
    | succ rem ih =>
      intro acc τc hsum segs_c M_c hMc htw_c hcl_c
      have hlen_pos := TapeWS_pos htw_c
      rcases wsDecJz_spec MaxSeg B segs_c (s := 4) (w := w_reg) (v := rem + 1)
          (by simp [segs_c]; omega) (by omega)
          (by dsimp only [segs_c]; rw [getD_append_left _ _ _ (by simp; omega), getD_set_self_seg _ (by omega)])
          (by omega) htw_c
        with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
      simp only [Nat.succ_ne_zero, decide_false, ↓reduceIte, Nat.add_sub_cancel] at hz_dz htw_dz
      let segs_d := segs.set 4 (natToBitsLE w_reg rem) ++ [List.replicate acc false]
      have hsd_eq : segs_c.set 4 (natToBitsLE w_reg rem) = segs_d := by
        dsimp only [segs_c, segs_d]
        rw [List.set_append]
        simp only [List.length_set, show 4 < segs.length by omega, ↓reduceIte, List.set_set]
      rw [hsd_eq] at htw_dz
      have hMd : (encodeWorkspace segs_d).length = M_c := by
        rw [← hsd_eq]
        exact length_encodeWorkspace_set (by simp [segs_c]; omega)
          (by dsimp only [segs_c]; rw [getD_append_left _ _ _ (by simp; omega), getD_set_self_seg _ (by omega),
            length_natToBitsLE, length_natToBitsLE])
      rw [← hMd] at htw_dz
      rcases appendBitLast_spec B false segs_d htw_dz (by omega) with ⟨τ_g, htw_g, hM_g, hout_g, he_g⟩
      let segs_next := segs.set 4 (natToBitsLE w_reg rem) ++ [List.replicate (acc + 1) false]
      have hsn_eq : segs_d.set (segs_d.length - 1) (segs_d.getD (segs_d.length - 1) [] ++ [false]) = segs_next := by
        dsimp only [segs_d, segs_next]
        have hlen_sd : (segs.set 4 (natToBitsLE w_reg rem) ++ [List.replicate acc false]).length - 1 =
            (segs.set 4 (natToBitsLE w_reg rem)).length := by simp
        rw [hlen_sd, List.set_append]
        simp only [Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, List.set_cons_zero]
        have hget : (segs.set 4 (natToBitsLE w_reg rem) ++ [List.replicate acc false]).getD
            (segs.set 4 (natToBitsLE w_reg rem)).length [] = List.replicate acc false := by
          rw [getD_append_right _ _ _ (Nat.le_refl _), Nat.sub_self]; rfl
        rw [hget, List.replicate_succ']
      rw [hsn_eq] at htw_g hM_g he_g
      rw [hMd] at hM_g hout_g he_g
      have he_inr := sumStep_inr_spec (nopStep Unit) (liftBlockStep (blkGrowLast (blkData false false))) he_g
      have he_body : StepExec (growOutBufBody R) B (Sum.inl (wsDecJzEntry MaxSeg ⟨4, by omega⟩))
          (3 * M_c) τc 0 (Sum.inr (Sum.inr (liftBlkExit 2))) (3 * (encodeWorkspace segs_next).length) τ_g 0 S_it := by
        unfold growOutBufBody
        exact (seq0_spec hlen_pos he_dz (by rw [hz_dz]; exact he_inr)).weaken S_it (by dsimp only [S_it]; omega)
      have hcl_g : ∀ p, 3 * (encodeWorkspace segs_next).length ≤ p → τ_g p = false := by
        intro p hp; rw [hout_g p (by omega), hout_dz p (by omega)]; exact hcl_c p (by omega)
      rcases ih (acc + 1) τ_g (by omega) (by dsimp only [segs_next] at hM_g; omega) htw_g hcl_g
        with ⟨τ_end, htw_end, hcl_end, he_rest⟩
      have hcomb := (loop0_step (next := growOutBufNext R) (TapeWS_pos htw_g) he_body rfl he_rest).weaken
        ((rem + 1 + 1) * (S_it + 2)) (by
          have : (rem + 1 + 1) * (S_it + 2) = (S_it + 2) + (rem + 1) * (S_it + 2) := by ring
          omega)
      exact ⟨τ_end, htw_end, hcl_end, hcomb⟩
  have hsegs0 : segs.set 4 (natToBitsLE w_reg L_buf) = segs := by
    apply List.ext_getElem (by simp)
    intro i h1 h2; rw [List.getElem_set]; split_ifs with heq
    · subst heq; have := hseg4; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at this; exact this.symm
    · rfl
  rcases hloop L_buf 0 τ1 (Nat.add_zero L_buf)
      (by simpa [hsegs0] using hM1) (by simpa [hsegs0] using htw1) (by simpa [hsegs0] using hcl1)
    with ⟨τ_end, htw_end, hcl_end, he_lp⟩
  rw [hsegs0, List.replicate_zero] at he_lp
  have he_tot : StepExec (growOutBuf R) B (Sum.inl (liftBlkEntry 0))
      (3 * (encodeWorkspace segs).length) τ₀ 0
      (Sum.inr (Sum.inr (Sum.inl ()))) (3 * M_end) τ_end 0
      ((L_buf + 2) * (60 * M_end + 40)) := by
    unfold growOutBuf
    have hseq := seq0_spec (f := fun _ => Sum.inl (wsDecJzEntry MaxSeg ⟨4, by omega⟩)) (TapeWS_pos htw1) he1 he_lp
    have htime : 14 * (encodeWorkspace segs).length + 18 + 1 + (L_buf + 1) * (S_it + 2) ≤
        (L_buf + 2) * (60 * M_end + 40) := by
      have h1 : (L_buf + 1) * (S_it + 2) ≤ (L_buf + 1) * (60 * M_end + 40) :=
        Nat.mul_le_mul_left _ (by dsimp only [S_it]; omega)
      have hexp : (L_buf + 2) * (60 * M_end + 40) = (L_buf + 1) * (60 * M_end + 40) + (60 * M_end + 40) := by ring
      omega
    exact hseq.weaken _ htime
  exact ⟨τ_end, hM_end, htw_end, hcl_end, he_tot⟩

/-! #### Stage I: `computeSegW` (`seg (8 + R + 5) := 3 * M_blk`) -/

abbrev SumSegLensQ (R : ℕ) : Type :=
  Fin (8 + R + 5) × WsAddSegLenQ (8 + R + 5) 3

def sumSegLensBody (R : ℕ) : StepFn (SumSegLensQ R) :=
  familyStep (fun s : Fin (8 + R + 5) =>
    wsAddSegLen (8 + R + 5) 3 ⟨s.val, by omega⟩ ⟨8 + R + 5, by omega⟩)

def sumSegLensNext (R : ℕ) : SumSegLensQ R → Option (SumSegLensQ R)
  | (s, _) =>
      if h : s.val + 1 < 8 + R + 5 then
        some (⟨s.val + 1, h⟩, Sum.inl (liftBlkEntry (⟨s.val + 1, by omega⟩, 0, false, false)))
      else none

abbrev ComputeSegWQ (R : ℕ) : Type :=
  SumSegLensQ R ⊕
    (WsAddSegLenQ (8 + R + 5) 3 ⊕
      Repeat0Q (3 * (8 + R + 7)) (LiftBlkQ (Fin (8 + R + 5 + 1) × Bool)))

def computeSegW (R : ℕ) : StepFn (ComputeSegWQ R) :=
  let MaxSeg := 8 + R + 5
  seq0 (loop0 (sumSegLensBody R) (sumSegLensNext R))
    (seq0 (wsAddSegLen MaxSeg 3 ⟨8 + R + 4, by omega⟩ ⟨8 + R + 5, by omega⟩)
      (repeat0 (3 * (8 + R + 7)) (wsInc MaxSeg) (wsIncEntry MaxSeg ⟨8 + R + 5, by omega⟩))
      (fun _ => repeat0Entry (3 * (8 + R + 7)) (wsIncEntry MaxSeg ⟨8 + R + 5, by omega⟩)))
    (fun _ => Sum.inl (Sum.inl (liftBlkEntry (⟨8 + R + 4, by omega⟩, 0, false, false))))

def computeSegWEntry (R : ℕ) : ComputeSegWQ R :=
  Sum.inl (⟨0, by omega⟩, Sum.inl (liftBlkEntry (⟨0, by omega⟩, 0, false, false)))

theorem sum_take_succ_getD (segs : List (List Bool)) {idx : ℕ} (hidx : idx < segs.length) :
    ((segs.take (idx + 1)).map List.length).sum =
      ((segs.take idx).map List.length).sum + (segs.getD idx []).length := by
  rw [List.take_succ_eq_append_getElem hidx, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
  rfl

theorem computeSegW_spec (R B w_reg : ℕ) (segs : List (List Bool))
    (hlen : segs.length = 8 + R + 6)
    (hseg4 : (segs.getD (8 + R + 4) []).length = w_reg)
    (hsegW : segs.getD (8 + R + 5) [] = natToBitsLE w_reg 0)
    (hW_pow : 3 * (encodeWorkspace segs).length < 2 ^ w_reg)
    {len : ℕ} {τ₀ : ℕ → Bool}
    (htw₀ : TapeWS τ₀ len B segs) :
    let M_blk := (encodeWorkspace segs).length
    let segs_end := segs.set (8 + R + 5) (natToBitsLE w_reg (3 * M_blk))
    ∃ τ_end : ℕ → Bool,
      (encodeWorkspace segs_end).length = M_blk ∧
      TapeWS τ_end len B segs_end ∧
      (∀ p, 3 * M_blk ≤ p → τ_end p = τ₀ p) ∧
      StepExec (computeSegW R) B (computeSegWEntry R) len τ₀ 0
        (Sum.inr (Sum.inr (repeat0Exit (3 * (8 + R + 7))))) len τ_end 0
        ((R + 20) * ((M_blk + 1) * (100 * M_blk + 60))) := by
  intro M_blk segs_end
  let MaxSeg := 8 + R + 5
  have hlen_pos := TapeWS_pos htw₀
  have hlen_B := htw₀.2.2.1
  have hM_sum : M_blk = (8 + R + 7) + (segs.map List.length).sum := by
    have h1 := encodeWorkspace_length_eq segs htw₀.1
    rw [sum_map_length_add_one, hlen] at h1
    dsimp only [M_blk]; omega
  have htake_le : ∀ k ≤ segs.length, ((segs.take k).map List.length).sum ≤ (segs.map List.length).sum := by
    intro k hk
    have hsp := List.take_append_drop k segs
    conv_rhs => rw [← hsp, List.map_append, List.sum_append]
    omega
  have hseg_le : ∀ k < segs.length, (segs.getD k []).length ≤ M_blk := by
    intro k hk
    have h1 := sum_take_succ_getD segs hk
    have h2 := htake_le (k + 1) (by omega)
    omega
  -- 1) loop over `idx = 0 .. 8 + R + 4`
  let S_sl := (M_blk + 1) * (84 * M_blk + 42)
  have hloop : ∀ rem idx (hidx : idx < 8 + R + 5),
      idx + rem = 8 + R + 5 →
      ∀ (τc : ℕ → Bool),
        let acc := 3 * ((segs.take idx).map List.length).sum
        TapeWS τc len B (segs.set (8 + R + 5) (natToBitsLE w_reg acc)) →
        ∃ q_lp, ∃ τ1 : ℕ → Bool,
          TapeWS τ1 len B (segs.set (8 + R + 5) (natToBitsLE w_reg (3 * ((segs.take (8 + R + 5)).map List.length).sum))) ∧
          (∀ p, 3 * M_blk ≤ p → τ1 p = τc p) ∧
          StepExec (loop0 (sumSegLensBody R) (sumSegLensNext R)) B
            (⟨idx, hidx⟩, Sum.inl (liftBlkEntry (⟨idx, by omega⟩, 0, false, false))) len τc 0
            q_lp len τ1 0 (rem * (S_sl + 2)) := by
    intro rem
    induction rem with
    | zero => intro idx hidx hsum; omega
    | succ rem ih =>
      intro idx hidx hsum τc acc htw_c
      let segs_c := segs.set (8 + R + 5) (natToBitsLE w_reg acc)
      have hMc : (encodeWorkspace segs_c).length = M_blk :=
        length_encodeWorkspace_set (by omega) (by rw [hsegW, length_natToBitsLE, length_natToBitsLE])
      have hget_idx : segs_c.getD idx [] = segs.getD idx [] := getD_set_ne_seg segs (by omega) _
      have hacc_next : acc + 3 * (segs_c.getD idx []).length = 3 * ((segs.take (idx + 1)).map List.length).sum := by
        rw [hget_idx, sum_take_succ_getD segs (by omega)]; dsimp only [acc]; ring
      have hnext_pow : acc + 3 * (segs_c.getD idx []).length < 2 ^ w_reg := by
        rw [hacc_next]
        have := htake_le (idx + 1) (by omega)
        omega
      rcases wsAddSegLen_spec MaxSeg 3 B w_reg acc ⟨idx, by omega⟩ ⟨8 + R + 5, by omega⟩ segs_c
          (by simp; omega) (by simp [segs_c]; omega)
          (getD_set_self_seg segs (by omega) _) hnext_pow htw_c
        with ⟨τ_a, htw_a, hout_a, he_a⟩
      rw [hMc] at hout_a he_a
      rw [hacc_next] at htw_a
      simp only [segs_c, List.set_set] at htw_a
      have hlen_idx_le : (segs_c.getD idx []).length ≤ M_blk := by rw [hget_idx]; exact hseg_le idx (by omega)
      have he_body : StepExec (sumSegLensBody R) B
          (⟨idx, hidx⟩, Sum.inl (liftBlkEntry (⟨idx, by omega⟩, 0, false, false))) len τc 0
          (⟨idx, hidx⟩, Sum.inr (Sum.inl ())) len τ_a 0 S_sl := by
        unfold sumSegLensBody
        have hfam := familyStep_spec (fun s : Fin (8 + R + 5) =>
            wsAddSegLen MaxSeg 3 ⟨s.val, by omega⟩ ⟨8 + R + 5, by omega⟩)
          ⟨idx, hidx⟩ he_a
        exact hfam.weaken S_sl (Nat.mul_le_mul (by change (segs_c.getD idx []).length + 1 ≤ M_blk + 1; omega) (by omega))
      cases rem with
      | zero =>
        have hidx_eq : idx + 1 = 8 + R + 5 := by omega
        rw [hidx_eq] at htw_a
        have hnext_none : sumSegLensNext R (⟨idx, hidx⟩, Sum.inr (Sum.inl ())) = none := by
          simp [sumSegLensNext]; omega
        have hdone := (loop0_done (next := sumSegLensNext R) he_body hnext_none).weaken
          (1 * (S_sl + 2)) (by omega)
        exact ⟨_, τ_a, htw_a, hout_a, hdone⟩
      | succ rem' =>
        have hidx1 : idx + 1 < 8 + R + 5 := by omega
        rcases ih (idx + 1) hidx1 (by omega) τ_a htw_a with ⟨q_lp, τ1, htw1, hout1, he_rest⟩
        have hnext_some : sumSegLensNext R (⟨idx, hidx⟩, Sum.inr (Sum.inl ())) =
            some (⟨idx + 1, hidx1⟩, Sum.inl (liftBlkEntry (⟨idx + 1, by omega⟩, 0, false, false))) := by
          simp [sumSegLensNext, hidx1]
        have hcomb := (loop0_step (next := sumSegLensNext R) hlen_pos he_body hnext_some he_rest).weaken
          ((rem' + 1 + 1) * (S_sl + 2)) (by
            have : (rem' + 1 + 1) * (S_sl + 2) = (S_sl + 2) + (rem' + 1) * (S_sl + 2) := by ring
            omega)
        exact ⟨q_lp, τ1, htw1, fun p hp => (hout1 p hp).trans (hout_a p hp), hcomb⟩
  have hsegs0 : segs.set (8 + R + 5) (natToBitsLE w_reg (3 * ((segs.take 0).map List.length).sum)) = segs := by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.mul_zero]
    apply List.ext_getElem (by simp)
    intro i h1 h2; rw [List.getElem_set]; split_ifs with heq
    · subst heq; have := hsegW; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at this; exact this.symm
    · rfl
  rcases hloop (8 + R + 5) 0 (by omega) (Nat.zero_add _) τ₀ (by rw [hsegs0]; exact htw₀)
    with ⟨q_lp, τ1, htw1, hout1, he1⟩
  -- 2) add 3 * len(8 + R + 4) = 3 * w_reg = 3 * len(8 + R + 5)
  let sum_pre := ((segs.take (8 + R + 5)).map List.length).sum
  let segs1 := segs.set (8 + R + 5) (natToBitsLE w_reg (3 * sum_pre))
  have hM1 : (encodeWorkspace segs1).length = M_blk :=
    length_encodeWorkspace_set (by omega) (by rw [hsegW, length_natToBitsLE, length_natToBitsLE])
  have hget_4 : segs1.getD (8 + R + 4) [] = segs.getD (8 + R + 4) [] := getD_set_ne_seg segs (by omega) _
  have hsum_all : sum_pre + w_reg = (segs.map List.length).sum := by
    have h1 := sum_take_succ_getD segs (idx := 8 + R + 5) (by omega)
    have htake_all : segs.take (8 + R + 5 + 1) = segs := List.take_of_length_le (by omega)
    rw [htake_all, hsegW, length_natToBitsLE] at h1
    dsimp only [sum_pre]; omega
  rcases wsAddSegLen_spec MaxSeg 3 B w_reg (3 * sum_pre) ⟨8 + R + 4, by omega⟩ ⟨8 + R + 5, by omega⟩ segs1
      (by simp) (by simp [segs1]; omega)
      (getD_set_self_seg segs (by omega) _) (by rw [hget_4, hseg4]; omega) htw1
    with ⟨τ2, htw2, hout2, he2⟩
  rw [hM1] at hout2 he2
  rw [hget_4, hseg4] at htw2 he2
  have h3all : 3 * sum_pre + 3 * w_reg = 3 * (segs.map List.length).sum := by omega
  rw [h3all] at htw2
  simp only [segs1, List.set_set] at htw2
  -- 3) repeat0 (3 * (8 + R + 7)) wsInc segW
  let base_v := 3 * (segs.map List.length).sum
  let InvI : ℕ → ℕ → (ℕ → Bool) → Prop := fun j l_cur τ_cur =>
    l_cur = len ∧
    TapeWS τ_cur len B (segs.set (8 + R + 5) (natToBitsLE w_reg (base_v + j))) ∧
    (∀ p, 3 * M_blk ≤ p → τ_cur p = τ2 p)
  have hstepI : ∀ j < 3 * (8 + R + 7), ∀ l_cur τ_cur, InvI j l_cur τ_cur →
      ∃ q_e l' τ', InvI (j + 1) l' τ' ∧ 1 ≤ l' ∧
        StepExec (wsInc MaxSeg) B (wsIncEntry MaxSeg ⟨8 + R + 5, by omega⟩)
          l_cur τ_cur 0 q_e l' τ' 0 (21 * M_blk + 4) := by
    intro j hj l_cur τ_cur ⟨hl_eq, htw_j, hout_j⟩
    subst l_cur
    let sj := segs.set (8 + R + 5) (natToBitsLE w_reg (base_v + j))
    have hMj : (encodeWorkspace sj).length = M_blk :=
      length_encodeWorkspace_set (by omega) (by rw [hsegW, length_natToBitsLE, length_natToBitsLE])
    rcases wsInc_spec MaxSeg B sj (s := 8 + R + 5) (w := w_reg) (v := base_v + j)
        (by simp [sj]; omega) (by omega) (getD_set_self_seg segs (by omega) _)
        (by dsimp only [base_v]; omega) htw_j
      with ⟨τ', htw', hout', he'⟩
    rw [hMj] at hout' he'
    simp only [sj, List.set_set] at htw'
    rw [show base_v + j + 1 = base_v + (j + 1) by omega] at htw'
    exact ⟨_, len, τ', ⟨rfl, htw', fun p hp => (hout' p hp).trans (hout_j p hp)⟩, hlen_pos, he'⟩
  rcases repeat0_spec (3 * (8 + R + 7)) (wsInc MaxSeg) (wsIncEntry MaxSeg ⟨8 + R + 5, by omega⟩)
      B (21 * M_blk + 4) InvI hstepI
      (fun _ _ ⟨hl_eq, _⟩ => ⟨by rw [hl_eq]; exact hlen_B, by omega⟩)
      ⟨rfl, by simpa [base_v] using htw2, fun _ _ => rfl⟩
    with ⟨len_end, τ_end, ⟨hlen_eq, htw_end, hout_end⟩, he3⟩
  subst len_end
  have hfinal_v : base_v + 3 * (8 + R + 7) = 3 * M_blk := by dsimp only [base_v]; omega
  rw [hfinal_v] at htw_end
  have hM_end : (encodeWorkspace segs_end).length = M_blk :=
    length_encodeWorkspace_set (by omega) (by rw [hsegW, length_natToBitsLE, length_natToBitsLE])
  have he23 := seq0_spec (f := fun _ => repeat0Entry (3 * (8 + R + 7)) (wsIncEntry MaxSeg ⟨8 + R + 5, by omega⟩))
    hlen_pos he2 he3
  have he13 : StepExec (computeSegW R) B (computeSegWEntry R) len τ₀ 0
      (Sum.inr (Sum.inr (repeat0Exit (3 * (8 + R + 7))))) len τ_end 0
      ((R + 20) * ((M_blk + 1) * (100 * M_blk + 60))) := by
    unfold computeSegW computeSegWEntry
    have hseq := seq0_spec (f := fun _ => Sum.inl (Sum.inl (liftBlkEntry ((⟨8 + R + 4, by omega⟩ : Fin (MaxSeg + 1)), 0, false, false))))
      hlen_pos he1 he23
    have hw_le_M : w_reg ≤ M_blk := by rw [← hseg4]; exact hseg_le (8 + R + 4) (by omega)
    have h2_le : (w_reg + 1) * (21 * M_blk + 6 + 3 * (21 * M_blk + 6) + 2) ≤ S_sl :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3_le : 3 * (8 + R + 7) * (21 * M_blk + 4 + 2) ≤ (R + 20) * ((M_blk + 1) * (10 * M_blk + 10)) := by
      have ha : 3 * (8 + R + 7) ≤ 3 * (R + 20) := by omega
      have hb : 3 * (21 * M_blk + 6) ≤ (M_blk + 1) * (10 * M_blk + 10) := by
        have hM_ge : 2 ≤ M_blk := encodeWorkspace_len_ge2 segs htw₀.1
        nlinarith
      calc 3 * (8 + R + 7) * (21 * M_blk + 4 + 2)
          ≤ 3 * (R + 20) * (21 * M_blk + 6) := Nat.mul_le_mul ha (by omega)
        _ = (R + 20) * (3 * (21 * M_blk + 6)) := by ring
        _ ≤ (R + 20) * ((M_blk + 1) * (10 * M_blk + 10)) := Nat.mul_le_mul_left _ hb
    have h12_le : (8 + R + 5) * (S_sl + 2) + 1 + (S_sl + 1) ≤ (R + 20) * ((M_blk + 1) * (90 * M_blk + 50)) := by
      have hS2 : S_sl + 2 ≤ (M_blk + 1) * (90 * M_blk + 50) := by
        dsimp only [S_sl]
        have : 1 * (6 * M_blk + 8) ≤ (M_blk + 1) * (6 * M_blk + 8) := Nat.mul_le_mul_right _ (by omega)
        have : (M_blk + 1) * (90 * M_blk + 50) = (M_blk + 1) * (84 * M_blk + 42) + (M_blk + 1) * (6 * M_blk + 8) := by ring
        omega
      calc (8 + R + 5) * (S_sl + 2) + 1 + (S_sl + 1)
          ≤ (8 + R + 6) * (S_sl + 2) := by ring_nf; omega
        _ ≤ (R + 20) * (S_sl + 2) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (R + 20) * ((M_blk + 1) * (90 * M_blk + 50)) := Nat.mul_le_mul_left _ hS2
    have hexp : (R + 20) * ((M_blk + 1) * (100 * M_blk + 60)) =
        (R + 20) * ((M_blk + 1) * (90 * M_blk + 50)) +
        (R + 20) * ((M_blk + 1) * (10 * M_blk + 10)) := by ring
    exact hseq.weaken _ (by omega)
  exact ⟨τ_end, hM_end, htw_end, fun p hp => (hout_end p hp).trans ((hout2 p hp).trans (hout1 p hp)), he13⟩

/-! #### Full Phase 1 Initializer `initWSProg` + `initWSProg_spec` -/

def initMblk (R wMul wAdd K_L d_L n : ℕ) : ℕ :=
  let w := (n - 2) / 2
  let r := decide ((n - 2) % 2 = 1)
  let w_reg := wMul * n + wAdd
  let L_buf := K_L * (n + 2) ^ d_L
  (8 + R + 7) + (18 * w + 31) + n + (n + (if r then 0 else 1) + 18 * w + 31) + (R + 10) * w_reg + L_buf

def initWSTimeBound (R wMul wAdd d_L n L_buf M_blk : ℕ) : ℕ :=
  30000 * (n + 2) ^ 2 +
  (n + 5) * (50 * M_blk + 40) +
  (n + M_blk + 4) * (40 * M_blk + 40) +
  (R + 10) * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) +
  (d_L + 2) * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250))) +
  (L_buf + 2) * (60 * M_blk + 40) +
  (R + 20) * ((M_blk + 1) * (100 * M_blk + 60)) + 30

abbrev InitWSPrefixQ (R wMul wAdd K_L d_L : ℕ) : Type :=
  RawExpandTouchQ ⊕
    (ExtractSegNQ ⊕
      (BuildSegInpQ R ⊕
        (Repeat0Q 5 (PushZeroRegQ R wMul wAdd) ⊕
          ComputeLbufQ R K_L d_L)))

def initWSPrefix (R wMul wAdd K_L d_L : ℕ) : StepFn (InitWSPrefixQ R wMul wAdd K_L d_L) :=
  seq0 rawToInitWS
    (seq0 extractSegN
      (seq0 (buildSegInp R)
        (seq0 (pushZeroRegs R wMul wAdd 5)
          (computeLbuf R K_L d_L)
          (fun _ => computeLbufEntry R K_L d_L))
        (fun _ => Sum.inl (pushZeroRegsEntry R wMul wAdd 5)))
      (fun q => Sum.inl (q.1, Sum.inl (liftBlkEntry 0))))
    (fun q =>
      let r := match q with | Sum.inr (b, _) => b | Sum.inl _ => false
      Sum.inl (r, Sum.inl (liftBlkEntry 0)))

def initWSPrefixEntry (R wMul wAdd K_L d_L : ℕ) : InitWSPrefixQ R wMul wAdd K_L d_L :=
  Sum.inl (Sum.inl (Sum.inl (Sum.inl 0)))

private lemma initWSPrefix_time_le {n wMul wAdd d_L L_buf M_blk M2v M3v M8v Slen : ℕ}
    (h2 : M2v ≤ M_blk) (h3 : M3v ≤ M_blk) (h8 : M8v ≤ M_blk) (hS : Slen ≤ M_blk) :
    30000 * (n + 2) ^ 2 + 1 +
      ((n + 5) * (50 * M2v + 40) + 1 +
        ((n + Slen + 4) * (40 * M3v + 40) + 1 +
          (5 * ((wMul * (n + 1) + wAdd + 2) * (40 * M8v + 40) + 2) + 1 +
            (d_L + 2) * ((L_buf + 2) * ((n + 5) * (500 * M8v + 250)))))) ≤
    30000 * (n + 2) ^ 2 +
      (n + 5) * (50 * M_blk + 40) +
      (n + M_blk + 4) * (40 * M_blk + 40) +
      5 * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) +
      (d_L + 2) * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250))) + 10 := by
  have hB : (n + 5) * (50 * M2v + 40) ≤ (n + 5) * (50 * M_blk + 40) :=
    Nat.mul_le_mul_left _ (by omega)
  have hC : (n + Slen + 4) * (40 * M3v + 40) ≤ (n + M_blk + 4) * (40 * M_blk + 40) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hD : 5 * ((wMul * (n + 1) + wAdd + 2) * (40 * M8v + 40) + 2) ≤
      5 * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) :=
    Nat.mul_le_mul_left 5 (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 2)
  have hE : (d_L + 2) * ((L_buf + 2) * ((n + 5) * (500 * M8v + 250))) ≤
      (d_L + 2) * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250))) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega)))
  linarith

private lemma initWSSuffix_time_le {R n wMul wAdd L_buf M_blk MFv MGv : ℕ}
    (hF : MFv ≤ M_blk) (hG : MGv ≤ M_blk) :
    (R + 2) * ((wMul * (n + 1) + wAdd + 2) * (40 * MFv + 40) + 2) + 1 +
      ((L_buf + 2) * (60 * MGv + 40) + 1 +
        (3 * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) + 1 +
          (R + 20) * ((M_blk + 1) * (100 * M_blk + 60)))) ≤
    (R + 5) * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) +
      (L_buf + 2) * (60 * M_blk + 40) +
      (R + 20) * ((M_blk + 1) * (100 * M_blk + 60)) + 10 := by
  have hF_t : (R + 2) * ((wMul * (n + 1) + wAdd + 2) * (40 * MFv + 40) + 2) ≤
      (R + 2) * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 2)
  have hG_t : (L_buf + 2) * (60 * MGv + 40) ≤ (L_buf + 2) * (60 * M_blk + 40) :=
    Nat.mul_le_mul_left _ (by omega)
  have hFH : (R + 2) * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) +
      3 * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) =
      (R + 5) * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) := by ring
  linarith

theorem initWSPrefix_spec (R wMul wAdd K_L d_L B n : ℕ) (rest : List Bool)
    (hn : 2 ≤ n)
    (hinp_len : (QCSD_natToUnary n ++ rest).length ≤ 9 * n + 4)
    (hlogK : Nat.log 2 K_L + 1 ≤ wMul * n + wAdd)
    (hn2_pow : n + 2 < 2 ^ (wMul * n + wAdd))
    (hL_pow : K_L * (n + 2) ^ d_L < 2 ^ (wMul * n + wAdd))
    (hB : 3 * initMblk R wMul wAdd K_L d_L n ≤ B) :
    let inp := QCSD_natToUnary n ++ rest
    let w := (n - 2) / 2
    let r := decide ((n - 2) % 2 = 1)
    let w_reg := wMul * n + wAdd
    let L_buf := K_L * (n + 2) ^ d_L
    let M_blk := initMblk R wMul wAdd K_L d_L n
    let M8 := 3 + (18 * w + 31) + n + (n + (if r then 0 else 1) + 18 * w + 31) + 1 + 5 * (w_reg + 1)
    ∃ segs_E, ∃ q_E, ∃ τE : ℕ → Bool,
      segs_E.length = 8 ∧
      (encodeWorkspace segs_E).length = M8 ∧
      M8 ≤ M_blk ∧
      segs_E.getD 1 [] = List.replicate n false ∧
      (∀ i, (segs_E.getD 2 []).getD i false = inp.getD i false) ∧
      segs_E.getD 4 [] = natToBitsLE w_reg L_buf ∧
      TapeWS τE (3 * M8) B segs_E ∧
      (∀ p, 3 * M8 ≤ p → τE p = false) ∧
      StepExec (initWSPrefix R wMul wAdd K_L d_L) B (initWSPrefixEntry R wMul wAdd K_L d_L)
        inp.length (fun p => QCSD_tapeRead inp p) 0
        q_E (3 * M8) τE 0
        (30000 * (n + 2) ^ 2 +
          (n + 5) * (50 * M_blk + 40) +
          (n + M_blk + 4) * (40 * M_blk + 40) +
          5 * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) +
          (d_L + 2) * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250))) + 10) := by
  intro inp w r w_reg L_buf M_blk M8
  let midRest := (if r then [false] else []) ++ rest
  let S_clean := makeSClean w midRest
  let segN := List.replicate n false
  let seg_inp := List.replicate n true ++ (if r then [] else [false]) ++ S_clean
  have hS_clean_len : S_clean.length = 18 * w + 31 := by
    simp [S_clean, makeSClean]; omega
  have hseg_inp_len : seg_inp.length = n + (if r then 0 else 1) + 18 * w + 31 := by
    dsimp only [seg_inp]; rw [List.length_append, List.length_append, List.length_replicate, hS_clean_len]
    cases hr : r <;> simp <;> omega
  let segs_2 := [S_clean, segN]
  let segs_3 := [S_clean, segN, seg_inp]
  let segs_8 := segs_3 ++ List.replicate 5 (natToBitsLE w_reg 0)
  have hM2_val : (encodeWorkspace segs_2).length = 18 * w + 34 + n := by
    simp only [segs_2, encodeWorkspace, encodeSegmentsAux, List.length_cons, List.length_append,
      List.length_map, List.length_nil, hS_clean_len, segN, List.length_replicate]; omega
  have hM3_val : (encodeWorkspace segs_3).length = 3 + (18 * w + 31) + n + seg_inp.length + 1 := by
    simp only [segs_3, encodeWorkspace, encodeSegmentsAux, List.length_cons, List.length_append,
      List.length_map, List.length_nil, hS_clean_len, segN, List.length_replicate]; omega
  have hM_blk_val : M_blk = (8 + R + 7) + (18 * w + 31) + n + seg_inp.length + (R + 10) * w_reg + L_buf := by
    dsimp only [M_blk, initMblk, w_reg, L_buf, w, r]
    rw [hseg_inp_len]
  have hB_end : 3 * M_blk ≤ B := hB
  have hM8_eq : M8 = (encodeWorkspace segs_3).length + 5 * (w_reg + 1) := by
    dsimp only [M8]; rw [hM3_val, hseg_inp_len]
  have hM8_le : M8 ≤ M_blk := by
    have : 5 * w_reg ≤ (R + 10) * w_reg := Nat.mul_le_mul_right w_reg (by omega)
    omega
  have hM2_le : (encodeWorkspace segs_2).length ≤ M_blk := by omega
  have hM3_le : (encodeWorkspace segs_3).length ≤ M_blk := by omega
  -- Stage A: rawToInitWS
  rcases rawToInitWS_spec B n rest hn hinp_len (by
      have : 18 * ((n - 2) / 2) + 33 ≤ M_blk := by dsimp only [w] at hM_blk_val; omega
      omega)
    with ⟨τA, hMA, htwA, hclA, heA⟩
  -- Stage B: extractSegN
  rcases extractSegN_spec B n midRest hn htwA hclA (by
      have : (encodeWorkspace [makeSClean ((n - 2) / 2) midRest, List.replicate n false]).length =
          (encodeWorkspace segs_2).length := rfl
      omega)
    with ⟨τB, hMB, htwB, hclB, heB⟩
  -- Stage C: buildSegInp
  rcases buildSegInp_spec R B n r S_clean htwB hclB (by
      change 3 * (encodeWorkspace segs_3).length ≤ B; omega)
    with ⟨τC, hMC, htwC, hclC, heC⟩
  -- Stage D: pushZeroRegs 5
  rcases pushZeroRegs_spec R wMul wAdd 5 B n segs_3
      (by simp only [segs_3, List.length_cons, List.length_nil]; omega)
      (by rfl) htwC hclC
      (by change 3 * ((encodeWorkspace segs_3).length + 5 * (w_reg + 1)) ≤ B; omega)
    with ⟨τD, hMD, htwD, hclD, heD⟩
  have hlen_segs8 : segs_8.length = 8 := by
    simp only [segs_8, segs_3, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  have hM8_val : (encodeWorkspace segs_8).length = M8 := by
    have : (encodeWorkspace segs_8).length = (encodeWorkspace segs_3).length + 5 * (w_reg + 1) := hMD
    omega
  have h8_rep : ∀ k < 5, segs_8.getD (3 + k) [] = natToBitsLE w_reg 0 := by
    intro k hk
    dsimp only [segs_8]
    rw [getD_append_right segs_3 _ [] (by simp only [segs_3, List.length_cons, List.length_nil]; omega),
        show 3 + k - segs_3.length = k by simp only [segs_3, List.length_cons, List.length_nil]; omega,
        List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp only [hk, ↓reduceIte, Option.getD_some]
  -- Stage E: computeLbuf
  rcases computeLbuf_spec R K_L d_L B n w_reg segs_8 hlen_segs8
      (by dsimp only [segs_8]; rw [getD_append_left segs_3 _ [] (by simp only [segs_3, List.length_cons, List.length_nil]; omega)]; rfl)
      (h8_rep 0 (by omega)) (h8_rep 1 (by omega)) (h8_rep 2 (by omega))
      (h8_rep 3 (by omega)) (h8_rep 4 (by omega))
      hlogK hn2_pow hL_pow htwD
    with ⟨segs_E, τE, hlE, hME, hothE, hE4, htwE, houtE, heE⟩
  -- Replace all `encodeWorkspace ...` lengths with pure ℕ expressions before composing `seq0_spec`
  have hposA : 1 ≤ 3 * (18 * w + 33) := by omega
  have hposB : 1 ≤ 3 * (18 * w + 34 + n) := by omega
  have hposC : 1 ≤ 3 * (3 + (18 * w + 31) + n + seg_inp.length + 1) := by omega
  have hposD : 1 ≤ 3 * M8 := by dsimp only [M8]; omega
  have hMA' : (encodeWorkspace [makeSRaw w midRest]).length = 18 * w + 33 := hMA
  rw [hMA'] at heA heB
  rw [hM2_val] at heB heC
  rw [hM3_val] at heC heD
  rw [hM8_val] at hME htwE houtE heE heD hclD
  have hclE : ∀ p, 3 * M8 ≤ p → τE p = false := fun p hp => (houtE p hp).trans (hclD p hp)
  have heDE := seq0_spec (f := fun _ => computeLbufEntry R K_L d_L) hposD heD heE
  have heCE := seq0_spec (f := fun _ => Sum.inl (pushZeroRegsEntry R wMul wAdd 5)) hposC heC heDE
  have heBE := seq0_spec (f := fun q : ExtractSegNQ => Sum.inl (q.1, Sum.inl (liftBlkEntry 0))) hposB heB heCE
  have hseq := seq0_spec
    (f := fun q : RawExpandTouchQ =>
      let r := match q with | Sum.inr (b, _) => b | Sum.inl _ => false
      Sum.inl (r, Sum.inl (liftBlkEntry 0)))
    hposA heA heBE
  have hM2_le' : 18 * w + 34 + n ≤ M_blk := by clear * - hM2_val hM2_le; omega
  have hM3_le' : 3 + (18 * w + 31) + n + seg_inp.length + 1 ≤ M_blk := by clear * - hM3_val hM3_le; omega
  have hS_le : S_clean.length ≤ M_blk := by clear * - hS_clean_len hM_blk_val; omega
  have htime := initWSPrefix_time_le (n := n) (wMul := wMul) (wAdd := wAdd) (d_L := d_L)
    (L_buf := L_buf) (M_blk := M_blk) hM2_le' hM3_le' hM8_le hS_le
  refine ⟨segs_E, _, τE, hlE, hME, hM8_le, ?_, ?_, hE4, htwE, hclE, hseq.weaken _ htime⟩
  · rw [hothE 1 (by omega)]
    dsimp only [segs_8]; rw [getD_append_left segs_3 _ [] (by simp only [segs_3, List.length_cons, List.length_nil]; omega)]; rfl
  · intro i
    have h2 : segs_E.getD 2 [] = seg_inp := by
      rw [hothE 2 (by omega)]
      dsimp only [segs_8]; rw [getD_append_left segs_3 _ [] (by simp only [segs_3, List.length_cons, List.length_nil]; omega)]; rfl
    rw [h2]; exact seg_inp_matches_inp n rest hn hinp_len i

abbrev InitWSSuffixQ (R wMul wAdd : ℕ) : Type :=
  Repeat0Q (R + 2) (PushZeroRegQ R wMul wAdd) ⊕
    (GrowOutBufQ R ⊕
      (Repeat0Q 3 (PushZeroRegQ R wMul wAdd) ⊕
        ComputeSegWQ R))

def initWSSuffix (R wMul wAdd : ℕ) : StepFn (InitWSSuffixQ R wMul wAdd) :=
  seq0 (pushZeroRegs R wMul wAdd (R + 2))
    (seq0 (growOutBuf R)
      (seq0 (pushZeroRegs R wMul wAdd 3)
        (computeSegW R)
        (fun _ => computeSegWEntry R))
      (fun _ => Sum.inl (pushZeroRegsEntry R wMul wAdd 3)))
    (fun _ => Sum.inl (Sum.inl (liftBlkEntry 0)))

def initWSSuffixEntry (R wMul wAdd : ℕ) : InitWSSuffixQ R wMul wAdd :=
  Sum.inl (pushZeroRegsEntry R wMul wAdd (R + 2))

theorem initWSSuffix_spec (R wMul wAdd B n L_buf M8 M_blk : ℕ)
    (inp : List Bool) (segs_E : List (List Bool))
    (hlE : segs_E.length = 8)
    (hME : (encodeWorkspace segs_E).length = M8)
    (hM_eq : M8 + (R + 2) * (wMul * n + wAdd + 1) + 1 + L_buf + 3 * (wMul * n + wAdd + 1) = M_blk)
    (hE1 : segs_E.getD 1 [] = List.replicate n false)
    (hE2 : ∀ i, (segs_E.getD 2 []).getD i false = inp.getD i false)
    (hE4 : segs_E.getD 4 [] = natToBitsLE (wMul * n + wAdd) L_buf)
    (hL_pow : L_buf < 2 ^ (wMul * n + wAdd))
    (hW_pow : 3 * M_blk < 2 ^ (wMul * n + wAdd))
    (hB : 3 * M_blk ≤ B)
    {τE : ℕ → Bool}
    (htwE : TapeWS τE (3 * M8) B segs_E)
    (hclE : ∀ p, 3 * M8 ≤ p → τE p = false) :
    let w_reg := wMul * n + wAdd
    ∃ q_end, ∃ τI : ℕ → Bool,
      WSRMInv 8 R w_reg L_buf M_blk B 2 inp τI (3 * M_blk) (fun _ => 0) [] 0 ∧
      (∀ p, 3 * M_blk ≤ p → τI p = false) ∧
      StepExec (initWSSuffix R wMul wAdd) B (initWSSuffixEntry R wMul wAdd)
        (3 * M8) τE 0 q_end (3 * M_blk) τI 0
        ((R + 5) * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) +
          (L_buf + 2) * (60 * M_blk + 40) +
          (R + 20) * ((M_blk + 1) * (100 * M_blk + 60)) + 10) := by
  intro w_reg
  -- Stage F: pushZeroRegs (R + 2)
  rcases pushZeroRegs_spec R wMul wAdd (R + 2) B n segs_E (by omega) hE1
      (by rw [hME]; exact htwE) (by rw [hME]; exact hclE) (by omega)
    with ⟨τF, hMF, htwF, hclF, heF⟩
  let segs_F := segs_E ++ List.replicate (R + 2) (natToBitsLE w_reg 0)
  have hMF_val : (encodeWorkspace segs_F).length = M8 + (R + 2) * (w_reg + 1) := by
    have : (encodeWorkspace segs_F).length = (encodeWorkspace segs_E).length + (R + 2) * (w_reg + 1) := hMF
    omega
  -- Stage G: growOutBuf
  rcases growOutBuf_spec R B w_reg L_buf segs_F (by simp [segs_F, hlE]; omega)
      (by dsimp only [segs_F]; rw [getD_append_left _ _ _ (by omega), hE4])
      hL_pow htwF hclF (by dsimp only [w_reg] at hMF_val ⊢; omega)
    with ⟨τG, hMG, htwG, hclG, heG⟩
  let segs_G := segs_F.set 4 (natToBitsLE w_reg 0) ++ [List.replicate L_buf false]
  have hMG_val : (encodeWorkspace segs_G).length = (encodeWorkspace segs_F).length + 1 + L_buf := hMG
  have hG1 : segs_G.getD 1 [] = List.replicate n false := by
    dsimp only [segs_G, segs_F]
    rw [getD_append_left _ _ _ (by simp [hlE]; omega), getD_set_ne_seg _ (by omega),
        getD_append_left _ _ _ (by omega), hE1]
  -- Stage H: pushZeroRegs 3
  rcases pushZeroRegs_spec R wMul wAdd 3 B n segs_G (by simp [segs_G, segs_F, hlE]; omega) hG1 htwG hclG
      (by dsimp only [w_reg] at hMF_val hMG_val ⊢; omega)
    with ⟨τH, hMH, htwH, hclH, heH⟩
  let segs_H := segs_G ++ List.replicate 3 (natToBitsLE w_reg 0)
  have hMH_val : (encodeWorkspace segs_H).length = (encodeWorkspace segs_G).length + 3 * (w_reg + 1) := hMH
  have hMH_final : (encodeWorkspace segs_H).length = M_blk := by dsimp only [w_reg] at hMF_val hMG_val hMH_val; omega
  have hlen_F : segs_F.length = 8 + R + 2 := by simp [segs_F, hlE]; omega
  have hlen_G : segs_G.length = 8 + R + 3 := by simp [segs_G, hlen_F]
  have hlen_H : segs_H.length = 8 + R + 6 := by simp [segs_H, hlen_G]
  have hH_get_rep : ∀ j < 3, segs_H.getD (8 + R + 3 + j) [] = natToBitsLE w_reg 0 := by
    intro j hj
    dsimp only [segs_H]
    rw [getD_append_right _ _ _ (by omega), show 8 + R + 3 + j - segs_G.length = j by omega,
        List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp only [hj, ↓reduceIte, Option.getD_some]
  -- Stage I: computeSegW
  rcases computeSegW_spec R B w_reg segs_H hlen_H
      (by rw [hH_get_rep 1 (by omega), length_natToBitsLE])
      (by exact hH_get_rep 2 (by omega))
      (by rw [hMH_final]; exact hW_pow) htwH
    with ⟨τI, hMI, htwI, houtI, heI⟩
  rw [hMH_final] at hMI htwI houtI heI heH
  let segs_final := segs_H.set (8 + R + 5) (natToBitsLE w_reg (3 * M_blk))
  have hclI : ∀ p, 3 * M_blk ≤ p → τI p = false := by
    intro p hp; rw [houtI p hp]; exact hclH p (by rw [hMH_final]; exact hp)
  have hget_F : ∀ i < 8 + R + 2, i ≠ 4 → segs_final.getD i [] = segs_F.getD i [] := by
    intro i hi hne4
    have h1 : segs_final.getD i [] = segs_H.getD i [] := getD_set_ne_seg segs_H (by omega) _
    have h2 : segs_H.getD i [] = segs_G.getD i [] := getD_append_left segs_G _ [] (by omega)
    have h3 : segs_G.getD i [] = (segs_F.set 4 (natToBitsLE w_reg 0)).getD i [] :=
      getD_append_left (segs_F.set 4 (natToBitsLE w_reg 0)) _ [] (by rw [List.length_set, hlen_F]; exact hi)
    have h4 : (segs_F.set 4 (natToBitsLE w_reg 0)).getD i [] = segs_F.getD i [] :=
      getD_set_ne_seg segs_F (by omega) _
    exact h1.trans (h2.trans (h3.trans h4))
  have hF_rep : ∀ k < R + 2, segs_F.getD (8 + k) [] = natToBitsLE w_reg 0 := by
    intro k hk
    dsimp only [segs_F]
    rw [getD_append_right segs_E _ [] (by omega), show 8 + k - segs_E.length = k by omega,
        List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp only [hk, ↓reduceIte, Option.getD_some]
  have hinv_final : WSRMInv 8 R w_reg L_buf M_blk B 2 inp τI (3 * M_blk) (fun _ => 0) [] 0 := by
    refine ⟨segs_final, by simp only [segs_final, List.length_set, hlen_H], hMI, htwI,
      ?_, ?_, ?_, ?_, ?_, Nat.zero_le L_buf, ?_, ?_, ?_⟩
    · intro i
      rw [hget_F 2 (by omega) (by omega)]
      dsimp only [segs_F]; rw [getD_append_left segs_E _ [] (by omega)]
      exact hE2 i
    · intro rr
      rw [hget_F (8 + rr.val) (by omega) (by omega), hF_rep rr.val (by omega)]
    · rw [hget_F (8 + R) (by omega) (by omega), hF_rep R (by omega)]; rfl
    · rw [hget_F (8 + R + 1) (by omega) (by omega), show 8 + R + 1 = 8 + (R + 1) by omega,
          hF_rep (R + 1) (by omega)]
    · have h1 : segs_final.getD (8 + R + 2) [] = segs_H.getD (8 + R + 2) [] := getD_set_ne_seg segs_H (by omega) _
      have h2 : segs_H.getD (8 + R + 2) [] = segs_G.getD (8 + R + 2) [] := getD_append_left segs_G _ [] (by omega)
      have h3 : segs_G.getD (8 + R + 2) [] = List.replicate L_buf false := by
        dsimp only [segs_G]
        rw [getD_append_right _ _ [] (by rw [List.length_set, hlen_F]), List.length_set, hlen_F, Nat.sub_self]
        rfl
      rw [h1, h2, h3]; simp
    · rw [getD_set_ne_seg segs_H (by omega), hH_get_rep 0 (by omega), length_natToBitsLE]
    · rw [getD_set_ne_seg segs_H (by omega), hH_get_rep 1 (by omega), length_natToBitsLE]
    · exact getD_set_self_seg segs_H (by omega) _
  let MF := M8 + (R + 2) * (w_reg + 1)
  let MG := MF + 1 + L_buf
  have hMF_eq : (encodeWorkspace segs_F).length = MF := hMF_val
  have hMG_eq : (encodeWorkspace segs_G).length = MG := by clear * - hMG_val hMF_val; omega
  have hposF : 1 ≤ 3 * MF := by have := TapeWS_pos htwF; rw [hMF_eq] at this; exact this
  have hposG : 1 ≤ 3 * MG := by have := TapeWS_pos htwG; rw [hMG_eq] at this; exact this
  have hposH : 1 ≤ 3 * M_blk := by have := TapeWS_pos htwH; rw [hMH_final] at this; exact this
  rw [hME, hMF_eq] at heF
  rw [hMF_eq, hMG_eq] at heG
  rw [hMG_eq] at heH
  have heHI := seq0_spec (f := fun _ => computeSegWEntry R) hposH heH heI
  have heGI := seq0_spec (f := fun _ => Sum.inl (pushZeroRegsEntry R wMul wAdd 3)) hposG heG heHI
  have hseq := seq0_spec (f := fun _ => Sum.inl (Sum.inl (liftBlkEntry 0))) hposF heF heGI
  have hMF_le : MF ≤ M_blk := by clear * - hM_eq; dsimp only [MF, w_reg]; omega
  have hMG_le : MG ≤ M_blk := by clear * - hM_eq; dsimp only [MG, MF, w_reg]; omega
  have htime := initWSSuffix_time_le (R := R) (n := n) (wMul := wMul) (wAdd := wAdd)
    (L_buf := L_buf) (M_blk := M_blk) hMF_le hMG_le
  exact ⟨_, τI, hinv_final, hclI, hseq.weaken _ htime⟩

abbrev InitWSQ (R wMul wAdd K_L d_L : ℕ) : Type :=
  InitWSPrefixQ R wMul wAdd K_L d_L ⊕ InitWSSuffixQ R wMul wAdd

def initWSProg (R wMul wAdd K_L d_L : ℕ) : StepFn (InitWSQ R wMul wAdd K_L d_L) :=
  seq0 (initWSPrefix R wMul wAdd K_L d_L) (initWSSuffix R wMul wAdd)
    (fun _ => initWSSuffixEntry R wMul wAdd)

def initWSProgEntry (R wMul wAdd K_L d_L : ℕ) : InitWSQ R wMul wAdd K_L d_L :=
  Sum.inl (initWSPrefixEntry R wMul wAdd K_L d_L)

theorem initWSProg_spec (R wMul wAdd K_L d_L B n : ℕ) (rest : List Bool)
    (hn : 2 ≤ n)
    (hinp_len : (QCSD_natToUnary n ++ rest).length ≤ 9 * n + 4)
    (hlogK : Nat.log 2 K_L + 1 ≤ wMul * n + wAdd)
    (hn2_pow : n + 2 < 2 ^ (wMul * n + wAdd))
    (hL_pow : K_L * (n + 2) ^ d_L < 2 ^ (wMul * n + wAdd))
    (hW_pow : 3 * initMblk R wMul wAdd K_L d_L n < 2 ^ (wMul * n + wAdd))
    (hB : 3 * initMblk R wMul wAdd K_L d_L n ≤ B) :
    let inp := QCSD_natToUnary n ++ rest
    let w_reg := wMul * n + wAdd
    let L_buf := K_L * (n + 2) ^ d_L
    let M_blk := initMblk R wMul wAdd K_L d_L n
    ∃ q_end, ∃ τ₀ : ℕ → Bool,
      WSRMInv 8 R w_reg L_buf M_blk B 2 inp τ₀ (3 * M_blk) (fun _ => 0) [] 0 ∧
      (∀ p, 3 * M_blk ≤ p → τ₀ p = false) ∧
      StepExec (initWSProg R wMul wAdd K_L d_L) B (initWSProgEntry R wMul wAdd K_L d_L)
        inp.length (fun p => QCSD_tapeRead inp p) 0
        q_end (3 * M_blk) τ₀ 0 (initWSTimeBound R wMul wAdd d_L n L_buf M_blk) := by
  intro inp w_reg L_buf M_blk
  rcases initWSPrefix_spec R wMul wAdd K_L d_L B n rest hn hinp_len hlogK hn2_pow hL_pow hB
    with ⟨segs_E, q_E, τE, hlE, hME, _, hE1, hE2, hE4, htwE, hclE, heP⟩
  have hM_eq : (3 + (18 * ((n - 2) / 2) + 31) + n +
      (n + (if decide ((n - 2) % 2 = 1) then 0 else 1) + 18 * ((n - 2) / 2) + 31) + 1 +
      5 * (w_reg + 1)) + (R + 2) * (w_reg + 1) + 1 + L_buf + 3 * (w_reg + 1) = M_blk := by
    dsimp only [M_blk, initMblk, w_reg, L_buf]
    have hsum : 5 * (wMul * n + wAdd + 1) + (R + 2) * (wMul * n + wAdd + 1) + 3 * (wMul * n + wAdd + 1) =
        (R + 10) * (wMul * n + wAdd) + (R + 10) := by ring
    omega
  rcases initWSSuffix_spec R wMul wAdd B n L_buf _ M_blk inp segs_E hlE hME hM_eq
      hE1 hE2 hE4 hL_pow hW_pow hB htwE hclE
    with ⟨q_S, τI, hinv, hclI, heS⟩
  have he_tot : StepExec (initWSProg R wMul wAdd K_L d_L) B (initWSProgEntry R wMul wAdd K_L d_L)
      inp.length (fun p => QCSD_tapeRead inp p) 0 (Sum.inr q_S) (3 * M_blk) τI 0
      (initWSTimeBound R wMul wAdd d_L n L_buf M_blk) := by
    unfold initWSProg initWSProgEntry
    have hseq := seq0_spec (f := fun _ => initWSSuffixEntry R wMul wAdd) (TapeWS_pos htwE) heP heS
    change StepExec _ B _ _ _ _ _ _ _ _
      ((30000 * (n + 2) ^ 2 +
          (n + 5) * (50 * M_blk + 40) +
          (n + M_blk + 4) * (40 * M_blk + 40) +
          5 * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) +
          (d_L + 2) * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250))) + 10) + 1 +
        ((R + 5) * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) +
          (L_buf + 2) * (60 * M_blk + 40) +
          (R + 20) * ((M_blk + 1) * (100 * M_blk + 60)) + 10)) at hseq
    have h5R : 5 * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) +
        (R + 5) * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) =
        (R + 10) * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) := by ring
    exact hseq.weaken _ (by dsimp only [initWSTimeBound]; rw [← h5R]; omega)
  exact ⟨Sum.inr q_S, τI, hinv, hclI, he_tot⟩

/-! ## Phase 2: Zero-Circularity Padded Output (`shuttlePadTail`, `unpackOutLoop_spec_fixedLen`, `execRMToOutputPadded`) -/

theorem padBits_length (m : ℕ) (c6 : List Bool) (hc6 : c6.length = 6) :
    ((List.range m).flatMap (fun _ => c6)).length = 6 * m := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton, hc6]; omega

theorem padBits_getD (m : ℕ) (c6 : List Bool) (hc6 : c6.length = 6) (i : ℕ) (hi : i < 6 * m) :
    ((List.range m).flatMap (fun _ => c6)).getD i false = c6.getD (i % 6) false := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    by_cases hlt : i < 6 * m
    · rw [getD_append_left _ _ _ (by rw [padBits_length m c6 hc6]; exact hlt)]
      exact ih hlt
    · rw [getD_append_right _ _ _ (by rw [padBits_length m c6 hc6]; omega),
          padBits_length m c6 hc6, show i - 6 * m = i % 6 by omega]

/-! ### `shuttleDecWrite`: decrement `s_pos`, copy to `s_off`, `shuttleWrite b` -/

abbrev ShuttleDecWriteQ (MaxSeg : ℕ) : Type :=
  WsDecJzQ MaxSeg ⊕
    ((SegTriple MaxSeg × WsCopyInnerQ MaxSeg) ⊕
      ((Fin (MaxSeg + 1) × Bool) × ShuttleWriteInnerQ MaxSeg))

def shuttleDecWrite (base R : ℕ) (b : Bool) : StepFn (ShuttleDecWriteQ (base + R + 5)) :=
  let MaxSeg := base + R + 5
  seq0 (wsDecJz MaxSeg)
    (seq0 (wsCopy MaxSeg) (shuttleWrite MaxSeg)
      (fun _ => shuttleWriteEntry MaxSeg ⟨base + R + 1, by omega⟩ b))
    (fun _ => Sum.inl (wsCopyEntry MaxSeg
      (⟨base + R + 1, by omega⟩, ⟨base + R + 4, by omega⟩, ⟨base + R + 3, by omega⟩)))

def shuttleDecWriteEntry (base R : ℕ) : ShuttleDecWriteQ (base + R + 5) :=
  Sum.inl (wsDecJzEntry (base + R + 5) ⟨base + R + 4, by omega⟩)

private lemma shuttleDecWrite_time_le {pos M_blk : ℕ} :
    42 * M_blk + 10 + 1 + ((pos + 2) * (150 * M_blk + 50) + 1 +
      (pos + 2) * (16 * (3 * M_blk) + 2 * pos + 30)) ≤
    (pos + 2) * (250 * M_blk + 2 * pos + 100) := by
  have h1 : 42 * M_blk + 12 ≤ (pos + 2) * (52 * M_blk + 20) := by
    have : 2 * (52 * M_blk + 20) ≤ (pos + 2) * (52 * M_blk + 20) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hexp : (pos + 2) * (250 * M_blk + 2 * pos + 100) =
      (pos + 2) * (150 * M_blk + 50) + (pos + 2) * (16 * (3 * M_blk) + 2 * pos + 30) +
      (pos + 2) * (52 * M_blk + 20) := by ring
  omega

theorem shuttleDecWrite_spec (base R w M_blk B pos : ℕ) (b : Bool) (segs : List (List Bool))
    (hlen_s : segs.length = base + R + 6)
    (hM : (encodeWorkspace segs).length = M_blk)
    (hpos_seg : segs.getD (base + R + 4) [] = natToBitsLE w (pos + 1))
    (hoff_len : (segs.getD (base + R + 1) []).length = w)
    (htmp_len : (segs.getD (base + R + 3) []).length = w)
    (hpos_pow : pos + 1 < 2 ^ w)
    (hB : 3 * M_blk + pos < B)
    {len : ℕ} {τ₀ : ℕ → Bool}
    (htw₀ : TapeWS τ₀ len B segs)
    (hclean : ∀ p, 3 * M_blk ≤ p → p ≤ 3 * M_blk + pos → τ₀ p = false) :
    ∃ q_end segs_end, ∃ τ₁ : ℕ → Bool,
      segs_end.length = base + R + 6 ∧
      (encodeWorkspace segs_end).length = M_blk ∧
      segs_end.getD (base + R + 4) [] = natToBitsLE w pos ∧
      (segs_end.getD (base + R + 1) []).length = w ∧
      (segs_end.getD (base + R + 3) []).length = w ∧
      (∀ i, i ≠ base + R + 1 → i ≠ base + R + 3 → i ≠ base + R + 4 → segs_end.getD i [] = segs.getD i []) ∧
      TapeWS τ₁ (max len (3 * M_blk + pos + 1)) B segs_end ∧
      (∀ p, 3 * M_blk ≤ p → p < 3 * M_blk + pos → τ₁ p = false) ∧
      τ₁ (3 * M_blk + pos) = b ∧
      (∀ p, 3 * M_blk + pos < p → τ₁ p = τ₀ p) ∧
      StepExec (shuttleDecWrite base R b) B (shuttleDecWriteEntry base R) len τ₀ 0
        q_end (max len (3 * M_blk + pos + 1)) τ₁ 0
        ((pos + 2) * (250 * M_blk + 2 * pos + 100)) := by
  let MaxSeg := base + R + 5
  have hlen_pos := TapeWS_pos htw₀
  -- 1) wsDecJz on s_pos = base + R + 4 (`pos + 1 -> pos`)
  rcases wsDecJz_spec MaxSeg B segs (s := base + R + 4) (w := w) (v := pos + 1)
      (by omega) (by omega) hpos_seg hpos_pow htw₀
    with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
  rw [hM] at hout_dz he_dz
  simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at htw_dz
  let s1 := segs.set (base + R + 4) (natToBitsLE w pos)
  have hM1 : (encodeWorkspace s1).length = M_blk :=
    (length_encodeWorkspace_set (by omega) (by rw [hpos_seg, length_natToBitsLE, length_natToBitsLE])).trans hM
  -- 2) wsCopy (`s_off := s_pos`, `tmp := s_tmp`)
  rcases wsCopy_spec MaxSeg B s1 (dst := base + R + 1) (src := base + R + 4) (tmp := base + R + 3)
      (w := w) (v := pos)
      (by simp [s1]; omega) (by simp [s1]; omega) (by simp [s1]; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by dsimp only [s1]; rw [getD_set_ne_seg _ (by omega), hoff_len])
      (by dsimp only [s1]; rw [getD_set_self_seg _ (by omega)])
      (by dsimp only [s1]; rw [getD_set_ne_seg _ (by omega), htmp_len])
      (by omega) htw_dz
    with ⟨q_cp, τ_cp, htw_cp, hout_cp, he_cp⟩
  rw [hM1] at hout_cp he_cp
  let s2_0 := s1.set (base + R + 1) (natToBitsLE w pos)
  let s2 := s2_0.set (base + R + 3) (natToBitsLE w 0)
  have hM2 : (encodeWorkspace s2).length = M_blk := by
    have h1 := length_encodeWorkspace_set (segs := s1) (s := base + R + 1) (newSeg := natToBitsLE w pos)
      (by simp [s1]; omega) (by dsimp only [s1]; rw [getD_set_ne_seg _ (by omega), hoff_len, length_natToBitsLE])
    have h2 := length_encodeWorkspace_set (segs := s2_0) (s := base + R + 3) (newSeg := natToBitsLE w 0)
      (by simp [s2_0, s1]; omega)
      (by dsimp only [s2_0, s1]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), htmp_len, length_natToBitsLE])
    exact h2.trans (h1.trans hM1)
  have hs2_off : s2.getD (base + R + 1) [] = natToBitsLE w pos := by
    dsimp only [s2, s2_0]; rw [getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by simp [s1]; omega)]
  -- 3) shuttleWrite `b` at offset `pos`
  rcases shuttleWrite_spec MaxSeg B s2 (s_off := base + R + 1) (w := w) (offset := pos) b
      (by simp [s2, s2_0, s1]; omega) (by omega) hs2_off (by omega) (by rw [hM2]; exact hB) htw_cp
      (fun p hp1 hp2 => by rw [hM2] at hp1 hp2; rw [hout_cp p hp1, hout_dz p hp1]; exact hclean p hp1 hp2)
    with ⟨q_sw, τ_sw, htw_sw, hpre_sw, hcur_sw, hout_sw, he_sw⟩
  rw [hM2] at htw_sw hpre_sw hcur_sw hout_sw he_sw
  let segs_end := s2.set (base + R + 1) (natToBitsLE w 0)
  have hMend : (encodeWorkspace segs_end).length = M_blk :=
    (length_encodeWorkspace_set (by simp [s2, s2_0, s1]; omega)
      (by rw [hs2_off, length_natToBitsLE, length_natToBitsLE])).trans hM2
  have he23 := seq0_spec (f := fun _ => shuttleWriteEntry MaxSeg ⟨base + R + 1, by omega⟩ b) hlen_pos he_cp he_sw
  have he13 := seq0_spec (f := fun _ => Sum.inl (wsCopyEntry MaxSeg
      (⟨base + R + 1, by omega⟩, ⟨base + R + 4, by omega⟩, ⟨base + R + 3, by omega⟩))) hlen_pos he_dz he23
  refine ⟨_, segs_end, τ_sw, by simp [segs_end, s2, s2_0, s1, hlen_s], hMend, ?_, ?_, ?_, ?_,
    htw_sw, hpre_sw, hcur_sw, ?_, he13.weaken _ shuttleDecWrite_time_le⟩
  · dsimp only [segs_end, s2, s2_0, s1]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
        getD_set_self_seg _ (by omega)]
  · dsimp only [segs_end]; rw [getD_set_self_seg _ (by simp [s2, s2_0, s1]; omega), length_natToBitsLE]
  · dsimp only [segs_end, s2]; rw [getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by simp [s2_0, s1]; omega), length_natToBitsLE]
  · intro i h1 h3 h4
    dsimp only [segs_end, s2, s2_0, s1]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
        getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega)]
  · intro p hp
    rw [hout_sw p hp, hout_cp p (by omega), hout_dz p (by omega)]

/-! ### `shuttlePad6`: write one 6-bit pad circuit `[false, true, false, false, false, true]` right-to-left -/

abbrev ShuttlePad6Q (MaxSeg : ℕ) : Type :=
  ShuttleDecWriteQ MaxSeg ⊕
    (ShuttleDecWriteQ MaxSeg ⊕
      (ShuttleDecWriteQ MaxSeg ⊕
        (ShuttleDecWriteQ MaxSeg ⊕
          (ShuttleDecWriteQ MaxSeg ⊕
            ShuttleDecWriteQ MaxSeg))))

def shuttlePad6 (base R : ℕ) : StepFn (ShuttlePad6Q (base + R + 5)) :=
  seq0 (shuttleDecWrite base R true)
    (seq0 (shuttleDecWrite base R false)
      (seq0 (shuttleDecWrite base R false)
        (seq0 (shuttleDecWrite base R false)
          (seq0 (shuttleDecWrite base R true)
            (shuttleDecWrite base R false)
            (fun _ => shuttleDecWriteEntry base R))
          (fun _ => Sum.inl (shuttleDecWriteEntry base R)))
        (fun _ => Sum.inl (shuttleDecWriteEntry base R)))
      (fun _ => Sum.inl (shuttleDecWriteEntry base R)))
    (fun _ => Sum.inl (shuttleDecWriteEntry base R))

def shuttlePad6Entry (base R : ℕ) : ShuttlePad6Q (base + R + 5) :=
  Sum.inl (shuttleDecWriteEntry base R)

private lemma shuttlePad6_time_le {pos M_blk : ℕ} :
    ((pos + 5 + 2) * (250 * M_blk + 2 * (pos + 5) + 100)) + 1 +
      (((pos + 4 + 2) * (250 * M_blk + 2 * (pos + 4) + 100)) + 1 +
        (((pos + 3 + 2) * (250 * M_blk + 2 * (pos + 3) + 100)) + 1 +
          (((pos + 2 + 2) * (250 * M_blk + 2 * (pos + 2) + 100)) + 1 +
            (((pos + 1 + 2) * (250 * M_blk + 2 * (pos + 1) + 100)) + 1 +
              ((pos + 2) * (250 * M_blk + 2 * pos + 100)))))) ≤
    6 * ((pos + 8) * (250 * M_blk + 2 * (pos + 8) + 100)) + 10 := by
  have h5 : (pos + 5 + 2) * (250 * M_blk + 2 * (pos + 5) + 100) ≤ (pos + 8) * (250 * M_blk + 2 * (pos + 8) + 100) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : (pos + 4 + 2) * (250 * M_blk + 2 * (pos + 4) + 100) ≤ (pos + 8) * (250 * M_blk + 2 * (pos + 8) + 100) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : (pos + 3 + 2) * (250 * M_blk + 2 * (pos + 3) + 100) ≤ (pos + 8) * (250 * M_blk + 2 * (pos + 8) + 100) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (pos + 2 + 2) * (250 * M_blk + 2 * (pos + 2) + 100) ≤ (pos + 8) * (250 * M_blk + 2 * (pos + 8) + 100) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h1 : (pos + 1 + 2) * (250 * M_blk + 2 * (pos + 1) + 100) ≤ (pos + 8) * (250 * M_blk + 2 * (pos + 8) + 100) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h0 : (pos + 2) * (250 * M_blk + 2 * pos + 100) ≤ (pos + 8) * (250 * M_blk + 2 * (pos + 8) + 100) :=
    Nat.mul_le_mul (by omega) (by omega)
  linarith

theorem shuttlePad6_spec (base R w M_blk B pos : ℕ) (segs : List (List Bool))
    (hlen_s : segs.length = base + R + 6)
    (hM : (encodeWorkspace segs).length = M_blk)
    (hpos_seg : segs.getD (base + R + 4) [] = natToBitsLE w (pos + 6))
    (hoff_len : (segs.getD (base + R + 1) []).length = w)
    (htmp_len : (segs.getD (base + R + 3) []).length = w)
    (hpos_pow : pos + 6 < 2 ^ w)
    (hB : 3 * M_blk + pos + 6 ≤ B)
    {len : ℕ} {τ₀ : ℕ → Bool}
    (htw₀ : TapeWS τ₀ len B segs)
    (hclean : ∀ p, 3 * M_blk ≤ p → p < 3 * M_blk + pos + 6 → τ₀ p = false) :
    ∃ q_end segs_end, ∃ τ₆ : ℕ → Bool,
      segs_end.length = base + R + 6 ∧
      (encodeWorkspace segs_end).length = M_blk ∧
      segs_end.getD (base + R + 4) [] = natToBitsLE w pos ∧
      (segs_end.getD (base + R + 1) []).length = w ∧
      (segs_end.getD (base + R + 3) []).length = w ∧
      (∀ i, i ≠ base + R + 1 → i ≠ base + R + 3 → i ≠ base + R + 4 → segs_end.getD i [] = segs.getD i []) ∧
      TapeWS τ₆ (max len (3 * M_blk + pos + 6)) B segs_end ∧
      (∀ p, 3 * M_blk ≤ p → p < 3 * M_blk + pos → τ₆ p = false) ∧
      (∀ d < 6, τ₆ (3 * M_blk + pos + d) = ([false, true, false, false, false, true] : List Bool).getD d false) ∧
      (∀ p, 3 * M_blk + pos + 6 ≤ p → τ₆ p = τ₀ p) ∧
      StepExec (shuttlePad6 base R) B (shuttlePad6Entry base R) len τ₀ 0
        q_end (max len (3 * M_blk + pos + 6)) τ₆ 0
        (6 * ((pos + 8) * (250 * M_blk + 2 * (pos + 8) + 100)) + 10) := by
  let L := max len (3 * M_blk + pos + 6)
  have hmax5 : max len (3 * M_blk + (pos + 5) + 1) = L := by dsimp only [L]; omega
  have hmax4 : max L (3 * M_blk + (pos + 4) + 1) = L := by dsimp only [L]; omega
  have hmax3 : max L (3 * M_blk + (pos + 3) + 1) = L := by dsimp only [L]; omega
  have hmax2 : max L (3 * M_blk + (pos + 2) + 1) = L := by dsimp only [L]; omega
  have hmax1 : max L (3 * M_blk + (pos + 1) + 1) = L := by dsimp only [L]; omega
  have hmax0 : max L (3 * M_blk + pos + 1) = L := by dsimp only [L]; omega
  -- bit 5: true
  rcases shuttleDecWrite_spec base R w M_blk B (pos + 5) true segs hlen_s hM hpos_seg hoff_len htmp_len
      (by omega) (by omega) htw₀ (fun p h1 h2 => hclean p h1 (by omega))
    with ⟨q5, s5, τ5, hl5, hM5, hp5, ho5, ht5, hoth5, htw5, hpre5, hcur5, hout5, he5⟩
  rw [hmax5] at htw5 he5
  -- bit 4: false
  rcases shuttleDecWrite_spec base R w M_blk B (pos + 4) false s5 hl5 hM5 hp5 ho5 ht5
      (by omega) (by omega) htw5 (fun p h1 h2 => hpre5 p h1 (by omega))
    with ⟨q4, s4, τ4, hl4, hM4, hp4, ho4, ht4, hoth4, htw4, hpre4, hcur4, hout4, he4⟩
  rw [hmax4] at htw4 he4
  -- bit 3: false
  rcases shuttleDecWrite_spec base R w M_blk B (pos + 3) false s4 hl4 hM4 hp4 ho4 ht4
      (by omega) (by omega) htw4 (fun p h1 h2 => hpre4 p h1 (by omega))
    with ⟨q3, s3, τ3, hl3, hM3, hp3, ho3, ht3, hoth3, htw3, hpre3, hcur3, hout3, he3⟩
  rw [hmax3] at htw3 he3
  -- bit 2: false
  rcases shuttleDecWrite_spec base R w M_blk B (pos + 2) false s3 hl3 hM3 hp3 ho3 ht3
      (by omega) (by omega) htw3 (fun p h1 h2 => hpre3 p h1 (by omega))
    with ⟨q2, s2, τ2, hl2, hM2, hp2, ho2, ht2, hoth2, htw2, hpre2, hcur2, hout2, he2⟩
  rw [hmax2] at htw2 he2
  -- bit 1: true
  rcases shuttleDecWrite_spec base R w M_blk B (pos + 1) true s2 hl2 hM2 hp2 ho2 ht2
      (by omega) (by omega) htw2 (fun p h1 h2 => hpre2 p h1 (by omega))
    with ⟨q1, s1, τ1, hl1, hM1, hp1, ho1, ht1, hoth1, htw1, hpre1, hcur1, hout1, he1⟩
  rw [hmax1] at htw1 he1
  -- bit 0: false
  rcases shuttleDecWrite_spec base R w M_blk B pos false s1 hl1 hM1 hp1 ho1 ht1
      (by omega) (by omega) htw1 (fun p h1 h2 => hpre1 p h1 (by omega))
    with ⟨q0, s0, τ0, hl0, hM0, hp0, ho0, ht0, hoth0, htw0, hpre0, hcur0, hout0, he0⟩
  rw [hmax0] at htw0 he0
  have hL_pos : 1 ≤ L := TapeWS_pos htw5
  have he10 := seq0_spec (f := fun _ => shuttleDecWriteEntry base R) hL_pos he1 he0
  have he20 := seq0_spec (f := fun _ => Sum.inl (shuttleDecWriteEntry base R)) hL_pos he2 he10
  have he30 := seq0_spec (f := fun _ => Sum.inl (shuttleDecWriteEntry base R)) hL_pos he3 he20
  have he40 := seq0_spec (f := fun _ => Sum.inl (shuttleDecWriteEntry base R)) hL_pos he4 he30
  have he50 := seq0_spec (f := fun _ => Sum.inl (shuttleDecWriteEntry base R)) hL_pos he5 he40
  refine ⟨_, s0, τ0, hl0, hM0, hp0, ho0, ht0, ?_, htw0, hpre0, ?_, ?_, he50.weaken _ shuttlePad6_time_le⟩
  · intro i h1 h3 h4
    exact (hoth0 i h1 h3 h4).trans ((hoth1 i h1 h3 h4).trans ((hoth2 i h1 h3 h4).trans
      ((hoth3 i h1 h3 h4).trans ((hoth4 i h1 h3 h4).trans (hoth5 i h1 h3 h4)))))
  · intro d hd
    have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using hcur0
    · rw [hout0 _ (by omega), show 3 * M_blk + pos + 1 = 3 * M_blk + (pos + 1) by omega, hcur1]; rfl
    · rw [hout0 _ (by omega), hout1 _ (by omega), show 3 * M_blk + pos + 2 = 3 * M_blk + (pos + 2) by omega, hcur2]; rfl
    · rw [hout0 _ (by omega), hout1 _ (by omega), hout2 _ (by omega),
          show 3 * M_blk + pos + 3 = 3 * M_blk + (pos + 3) by omega, hcur3]; rfl
    · rw [hout0 _ (by omega), hout1 _ (by omega), hout2 _ (by omega), hout3 _ (by omega),
          show 3 * M_blk + pos + 4 = 3 * M_blk + (pos + 4) by omega, hcur4]; rfl
    · rw [hout0 _ (by omega), hout1 _ (by omega), hout2 _ (by omega), hout3 _ (by omega), hout4 _ (by omega),
          show 3 * M_blk + pos + 5 = 3 * M_blk + (pos + 5) by omega, hcur5]; rfl
  · intro p hp
    rw [hout0 p (by omega), hout1 p (by omega), hout2 p (by omega),
        hout3 p (by omega), hout4 p (by omega), hout5 p (by omega)]

/-! ### `shuttlePadTail`: write all `3 * M_blk` pad circuits directly to `[3 * M_blk + emitted.length, 3 * M_blk + emitted.length + 18 * M_blk)` -/

abbrev PadAdd6LoopQ (MaxSeg : ℕ) : Type :=
  WsDecJzQ MaxSeg ⊕ (Unit ⊕ Repeat0Q 6 (LiftBlkQ (Fin (MaxSeg + 1) × Bool)))

def padAdd6Body (base R : ℕ) : StepFn (PadAdd6LoopQ (base + R + 5)) :=
  let MaxSeg := base + R + 5
  seq0 (wsDecJz MaxSeg)
    (sumStep (nopStep Unit) (repeat0 6 (wsInc MaxSeg) (wsIncEntry MaxSeg ⟨base + R + 4, by omega⟩)))
    (fun q => if wsDecJzWasZero q then Sum.inl ()
      else Sum.inr (repeat0Entry 6 (wsIncEntry MaxSeg ⟨base + R + 4, by omega⟩)))

def padAdd6Next (base R : ℕ) : PadAdd6LoopQ (base + R + 5) → Option (PadAdd6LoopQ (base + R + 5))
  | Sum.inr (Sum.inr _) => some (Sum.inl (wsDecJzEntry (base + R + 5) ⟨base + R + 1, by omega⟩))
  | _ => none

abbrev ShuttlePadLoopQ (MaxSeg : ℕ) : Type :=
  WsDecJzQ MaxSeg ⊕ (Unit ⊕ ShuttlePad6Q MaxSeg)

def shuttlePadLoopBody (base R : ℕ) : StepFn (ShuttlePadLoopQ (base + R + 5)) :=
  let MaxSeg := base + R + 5
  seq0 (wsDecJz MaxSeg)
    (sumStep (nopStep Unit) (shuttlePad6 base R))
    (fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (shuttlePad6Entry base R))

def shuttlePadLoopNext (base R : ℕ) : ShuttlePadLoopQ (base + R + 5) → Option (ShuttlePadLoopQ (base + R + 5))
  | Sum.inr (Sum.inr _) => some (Sum.inl (wsDecJzEntry (base + R + 5) ⟨base + R + 5, by omega⟩))
  | _ => none

abbrev ShuttlePadTailQ (base R : ℕ) : Type :=
  let MaxSeg := base + R + 5
  (SegTriple MaxSeg × WsCopyInnerQ MaxSeg) ⊕
    ((SegTriple MaxSeg × WsCopyInnerQ MaxSeg) ⊕
      (PadAdd6LoopQ MaxSeg ⊕ ShuttlePadLoopQ MaxSeg))

def shuttlePadTail (base R : ℕ) : StepFn (ShuttlePadTailQ base R) :=
  let MaxSeg := base + R + 5
  seq0 (wsCopy MaxSeg)
    (seq0 (wsCopy MaxSeg)
      (seq0 (loop0 (padAdd6Body base R) (padAdd6Next base R))
        (loop0 (shuttlePadLoopBody base R) (shuttlePadLoopNext base R))
        (fun _ => Sum.inl (wsDecJzEntry MaxSeg ⟨base + R + 5, by omega⟩)))
      (fun _ => Sum.inl (Sum.inl (wsDecJzEntry MaxSeg ⟨base + R + 1, by omega⟩))))
    (fun _ => Sum.inl (wsCopyEntry MaxSeg
      (⟨base + R + 1, by omega⟩, ⟨base + R + 5, by omega⟩, ⟨base + R + 3, by omega⟩)))

def shuttlePadTailEntry (base R : ℕ) : ShuttlePadTailQ base R :=
  let MaxSeg := base + R + 5
  Sum.inl (wsCopyEntry MaxSeg
    (⟨base + R + 4, by omega⟩, ⟨base + R, by omega⟩, ⟨base + R + 3, by omega⟩))

def shuttlePadTailTimeBound (L_buf M_blk : ℕ) : ℕ :=
  let P := L_buf + 18 * M_blk
  (3 * M_blk + 5) * (6 * ((P + 8) * (250 * M_blk + 2 * (P + 8) + 100)) + 450 * M_blk + 200) +
  (L_buf + 2) * (150 * M_blk + 50)

private lemma shuttlePadTail_time_le {emLen L_buf M_blk : ℕ} (hem : emLen ≤ L_buf) :
    let P := L_buf + 18 * M_blk
    let S_p := 6 * ((P + 8) * (250 * M_blk + 2 * (P + 8) + 100)) + 50 * M_blk + 30
    (emLen + 2) * (150 * M_blk + 50) + 1 +
      ((3 * M_blk + 2) * (150 * M_blk + 50) + 1 +
        ((3 * M_blk + 1) * (180 * M_blk + 62) + 1 + (3 * M_blk + 1) * (S_p + 2))) ≤
    shuttlePadTailTimeBound L_buf M_blk := by
  intro P S_p
  unfold shuttlePadTailTimeBound
  dsimp only
  have h1 : (emLen + 2) * (150 * M_blk + 50) ≤ (L_buf + 2) * (150 * M_blk + 50) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (3 * M_blk + 2) * (150 * M_blk + 50) + (3 * M_blk + 1) * (180 * M_blk + 62) + (3 * M_blk + 1) * (S_p + 2) + 3 ≤
      (3 * M_blk + 5) * (6 * ((P + 8) * (250 * M_blk + 2 * (P + 8) + 100)) + 450 * M_blk + 200) := by
    have ha : (3 * M_blk + 2) * (150 * M_blk + 50) ≤ (3 * M_blk + 5) * (150 * M_blk + 50) :=
      Nat.mul_le_mul_right _ (by omega)
    have hb : (3 * M_blk + 1) * (180 * M_blk + 62) ≤ (3 * M_blk + 5) * (180 * M_blk + 62) :=
      Nat.mul_le_mul_right _ (by omega)
    have hc : (3 * M_blk + 1) * (S_p + 2) ≤ (3 * M_blk + 5) * (S_p + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have hsum : (3 * M_blk + 5) * (150 * M_blk + 50) + (3 * M_blk + 5) * (180 * M_blk + 62) +
        (3 * M_blk + 5) * (S_p + 2) + 3 ≤
        (3 * M_blk + 5) * (6 * ((P + 8) * (250 * M_blk + 2 * (P + 8) + 100)) + 450 * M_blk + 200) := by
      have h3 : 3 ≤ (3 * M_blk + 5) * (70 * M_blk + 56) := by
        have : 5 * 56 ≤ (3 * M_blk + 5) * (70 * M_blk + 56) := Nat.mul_le_mul (by omega) (by omega)
        omega
      have hexp : (3 * M_blk + 5) * (6 * ((P + 8) * (250 * M_blk + 2 * (P + 8) + 100)) + 450 * M_blk + 200) =
          (3 * M_blk + 5) * (150 * M_blk + 50) + (3 * M_blk + 5) * (180 * M_blk + 62) +
          (3 * M_blk + 5) * (S_p + 2) + (3 * M_blk + 5) * (70 * M_blk + 56) := by
        dsimp only [S_p]; ring
      omega
    omega
  dsimp only [P] at h2
  omega

theorem shuttlePadTail_spec (base R w L_buf M_blk B seg_inp : ℕ)
    (inp : List Bool) {sys1Val : ℕ} {τ₁ : ℕ → Bool} {reg : RegState R} {emitted : List Bool}
    (hinv : WSRMInv base R w L_buf M_blk B seg_inp inp τ₁ (3 * M_blk) reg emitted sys1Val)
    (hclean : ∀ p, 3 * M_blk ≤ p → τ₁ p = false)
    (hP_pow : L_buf + 18 * M_blk < 2 ^ w)
    (hB : 3 * M_blk + emitted.length + 18 * M_blk ≤ B) :
    let padBits := (List.range (3 * M_blk)).flatMap (fun _ => [false, true, false, false, false, true])
    let len_end := 3 * M_blk + emitted.length + 18 * M_blk
    ∃ q_end, ∃ τ₂ : ℕ → Bool,
      WSUnpackInv base R w L_buf M_blk B emitted τ₂ len_end emitted.length ∧
      (∀ p, 3 * M_blk ≤ p → p < 3 * M_blk + emitted.length → τ₂ p = false) ∧
      (∀ i < 18 * M_blk, τ₂ (3 * M_blk + emitted.length + i) = padBits.getD i false) ∧
      StepExec (shuttlePadTail base R) B (shuttlePadTailEntry base R) (3 * M_blk) τ₁ 0
        q_end len_end τ₂ 0 (shuttlePadTailTimeBound L_buf M_blk) := by
  intro padBits len_end
  let MaxSeg := base + R + 5
  let c6 : List Bool := [false, true, false, false, false, true]
  rcases hinv with ⟨segs, hlen_s, hM, htw, _, _, houtL, hsys1, houtB, hem_le, htmp1, htmp2, hW⟩
  have hM_ge2 : 2 ≤ M_blk := by rw [← hM]; exact encodeWorkspace_len_ge2 segs htw.1
  have hlen0_pos : 1 ≤ 3 * M_blk := by omega
  have hlen0_B : 3 * M_blk ≤ B := htw.2.2.1
  -- Stage 1: wsCopy (s_pos := s_len, tmp := s_tmp)
  rcases wsCopy_spec MaxSeg B segs (dst := base + R + 4) (src := base + R) (tmp := base + R + 3)
      (w := w) (v := emitted.length)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
      htmp2 houtL htmp1 (by omega) htw
    with ⟨q_cp1, τ_cp1, htw_cp1, hout_cp1, he_cp1⟩
  rw [hM] at hout_cp1 he_cp1
  let s1_0 := segs.set (base + R + 4) (natToBitsLE w emitted.length)
  let s1 := s1_0.set (base + R + 3) (natToBitsLE w 0)
  have hM1 : (encodeWorkspace s1).length = M_blk := by
    have h1 := length_encodeWorkspace_set (segs := segs) (s := base + R + 4)
      (newSeg := natToBitsLE w emitted.length) (by omega) (by rw [htmp2, length_natToBitsLE])
    have h2 := length_encodeWorkspace_set (segs := s1_0) (s := base + R + 3) (newSeg := natToBitsLE w 0)
      (by simp [s1_0]; omega) (by dsimp only [s1_0]; rw [getD_set_ne_seg _ (by omega), htmp1, length_natToBitsLE])
    exact h2.trans (h1.trans hM)
  -- Stage 2: wsCopy (s_off := s_W, tmp := s_tmp)
  rcases wsCopy_spec MaxSeg B s1 (dst := base + R + 1) (src := base + R + 5) (tmp := base + R + 3)
      (w := w) (v := 3 * M_blk)
      (by simp [s1, s1_0]; omega) (by simp [s1, s1_0]; omega) (by simp [s1, s1_0]; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by dsimp only [s1, s1_0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), hsys1, length_natToBitsLE])
      (by dsimp only [s1, s1_0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), hW])
      (by dsimp only [s1]; rw [getD_set_self_seg _ (by simp [s1_0]; omega), length_natToBitsLE])
      (by omega) htw_cp1
    with ⟨q_cp2, τ_cp2, htw_cp2, hout_cp2, he_cp2⟩
  rw [hM1] at hout_cp2 he_cp2
  let s2_0 := s1.set (base + R + 1) (natToBitsLE w (3 * M_blk))
  let s2 := s2_0.set (base + R + 3) (natToBitsLE w 0)
  have hM2 : (encodeWorkspace s2).length = M_blk := by
    have h1 := length_encodeWorkspace_set (segs := s1) (s := base + R + 1) (newSeg := natToBitsLE w (3 * M_blk))
      (by simp [s1, s1_0]; omega)
      (by dsimp only [s1, s1_0]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), hsys1, length_natToBitsLE, length_natToBitsLE])
    have h2 := length_encodeWorkspace_set (segs := s2_0) (s := base + R + 3) (newSeg := natToBitsLE w 0)
      (by simp [s2_0, s1, s1_0]; omega)
      (by dsimp only [s2_0, s1]; rw [getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by simp [s1_0]; omega), length_natToBitsLE])
    exact h2.trans (h1.trans hM1)
  have hlen_s2 : s2.length = base + R + 6 := by simp [s2, s2_0, s1, s1_0, hlen_s]
  have hs2_len : s2.getD (base + R) [] = natToBitsLE w emitted.length := by
    dsimp only [s2, s2_0, s1, s1_0]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
        getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), houtL]
  have hs2_off : s2.getD (base + R + 1) [] = natToBitsLE w (3 * M_blk) := by
    dsimp only [s2, s2_0]; rw [getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by simp [s1, s1_0]; omega)]
  have hs2_buf : s2.getD (base + R + 2) [] = emitted ++ List.replicate (L_buf - emitted.length) false := by
    dsimp only [s2, s2_0, s1, s1_0]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
        getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), houtB]
  have hs2_tmp : (s2.getD (base + R + 3) []).length = w := by
    dsimp only [s2]; rw [getD_set_self_seg _ (by simp [s2_0, s1, s1_0]; omega), length_natToBitsLE]
  have hs2_pos : s2.getD (base + R + 4) [] = natToBitsLE w emitted.length := by
    dsimp only [s2, s2_0, s1, s1_0]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
        getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by omega)]
  have hs2_W : s2.getD (base + R + 5) [] = natToBitsLE w (3 * M_blk) := by
    dsimp only [s2, s2_0, s1, s1_0]
    rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
        getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), hW]
  -- Stage 3: loop adding `6 * (3 * M_blk)` to `s_pos`
  have hadd_loop : ∀ rem acc (sx : List (List Bool)) (τx : ℕ → Bool),
      rem + acc = 3 * M_blk →
      sx.length = base + R + 6 →
      (encodeWorkspace sx).length = M_blk →
      sx.getD (base + R) [] = natToBitsLE w emitted.length →
      sx.getD (base + R + 1) [] = natToBitsLE w rem →
      sx.getD (base + R + 2) [] = emitted ++ List.replicate (L_buf - emitted.length) false →
      (sx.getD (base + R + 3) []).length = w →
      sx.getD (base + R + 4) [] = natToBitsLE w (emitted.length + 6 * acc) →
      sx.getD (base + R + 5) [] = natToBitsLE w (3 * M_blk) →
      TapeWS τx (3 * M_blk) B sx →
      ∃ sy, ∃ τy : ℕ → Bool,
        sy.length = base + R + 6 ∧
        (encodeWorkspace sy).length = M_blk ∧
        sy.getD (base + R) [] = natToBitsLE w emitted.length ∧
        (sy.getD (base + R + 1) []).length = w ∧
        sy.getD (base + R + 2) [] = emitted ++ List.replicate (L_buf - emitted.length) false ∧
        (sy.getD (base + R + 3) []).length = w ∧
        sy.getD (base + R + 4) [] = natToBitsLE w (emitted.length + 18 * M_blk) ∧
        sy.getD (base + R + 5) [] = natToBitsLE w (3 * M_blk) ∧
        TapeWS τy (3 * M_blk) B sy ∧
        (∀ p, 3 * M_blk ≤ p → τy p = τx p) ∧
        StepExec (loop0 (padAdd6Body base R) (padAdd6Next base R)) B
          (Sum.inl (wsDecJzEntry MaxSeg ⟨base + R + 1, by omega⟩)) (3 * M_blk) τx 0
          (Sum.inr (Sum.inl ())) (3 * M_blk) τy 0 ((rem + 1) * (180 * M_blk + 62)) := by
    intro rem
    induction rem with
    | zero =>
      intro acc sx τx hsum hlx hMx hxL hx1 hxB hx3 hx4 hx5 htw_x
      have hacc : 6 * acc = 18 * M_blk := by omega
      rw [hacc] at hx4
      rcases wsDecJz_spec MaxSeg B sx (s := base + R + 1) (w := w) (v := 0)
          (by omega) (by omega) hx1 (by omega) htw_x
        with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
      rw [hMx] at hout_dz he_dz
      simp only [decide_true, ↓reduceIte] at hz_dz htw_dz
      have he_nop := sumStep_inl_spec (nopStep Unit)
        (repeat0 6 (wsInc MaxSeg) (wsIncEntry MaxSeg ⟨base + R + 4, by omega⟩))
        (nopStep_spec (B := B) () (3 * M_blk) τ_dz 0 hlen0_B (by omega))
      have he_body : StepExec (padAdd6Body base R) B (Sum.inl (wsDecJzEntry MaxSeg ⟨base + R + 1, by omega⟩))
          (3 * M_blk) τx 0 (Sum.inr (Sum.inl ())) (3 * M_blk) τ_dz 0 (180 * M_blk + 60) := by
        unfold padAdd6Body
        exact (seq0_spec hlen0_pos he_dz (by rw [hz_dz]; exact he_nop)).weaken _ (by omega)
      have hdone := (loop0_done (next := padAdd6Next base R) he_body rfl).weaken
        ((0 + 1) * (180 * M_blk + 62)) (by omega)
      exact ⟨sx, τ_dz, hlx, hMx, hxL, by rw [hx1, length_natToBitsLE], hxB, hx3, hx4, hx5, htw_dz, hout_dz, hdone⟩
    | succ rem ih =>
      intro acc sx τx hsum hlx hMx hxL hx1 hxB hx3 hx4 hx5 htw_x
      rcases wsDecJz_spec MaxSeg B sx (s := base + R + 1) (w := w) (v := rem + 1)
          (by omega) (by omega) hx1 (by omega) htw_x
        with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
      rw [hMx] at hout_dz he_dz
      simp only [Nat.succ_ne_zero, decide_false, ↓reduceIte, Nat.add_sub_cancel] at hz_dz htw_dz
      let sx1 := sx.set (base + R + 1) (natToBitsLE w rem)
      have hMx1 : (encodeWorkspace sx1).length = M_blk :=
        (length_encodeWorkspace_set (by omega) (by rw [hx1, length_natToBitsLE, length_natToBitsLE])).trans hMx
      -- repeat0 6 wsInc on s_pos = base + R + 4
      let Inv6 : ℕ → ℕ → (ℕ → Bool) → Prop := fun j l_cur τ_cur =>
        l_cur = 3 * M_blk ∧
        TapeWS τ_cur (3 * M_blk) B (sx1.set (base + R + 4) (natToBitsLE w (emitted.length + 6 * acc + j))) ∧
        (∀ p, 3 * M_blk ≤ p → τ_cur p = τ_dz p)
      have hstep6 : ∀ j < 6, ∀ l_cur τ_cur, Inv6 j l_cur τ_cur →
          ∃ q_e l' τ', Inv6 (j + 1) l' τ' ∧ 1 ≤ l' ∧
            StepExec (wsInc MaxSeg) B (wsIncEntry MaxSeg ⟨base + R + 4, by omega⟩)
              l_cur τ_cur 0 q_e l' τ' 0 (21 * M_blk + 4) := by
        intro j hj l_cur τ_cur ⟨hl_eq, htw_j, hout_j⟩
        subst l_cur
        let sj := sx1.set (base + R + 4) (natToBitsLE w (emitted.length + 6 * acc + j))
        have hMj : (encodeWorkspace sj).length = M_blk :=
          (length_encodeWorkspace_set (by simp [sx1]; omega)
            (by dsimp only [sx1]; rw [getD_set_ne_seg _ (by omega), hx4, length_natToBitsLE, length_natToBitsLE])).trans hMx1
        rcases wsInc_spec MaxSeg B sj (s := base + R + 4) (w := w) (v := emitted.length + 6 * acc + j)
            (by simp [sj, sx1]; omega) (by omega) (getD_set_self_seg sx1 (by simp [sx1]; omega) _)
            (by omega) htw_j
          with ⟨τ', htw', hout', he'⟩
        rw [hMj] at hout' he'
        simp only [sj, List.set_set] at htw'
        rw [show emitted.length + 6 * acc + j + 1 = emitted.length + 6 * acc + (j + 1) by omega] at htw'
        exact ⟨_, 3 * M_blk, τ', ⟨rfl, htw', fun p hp => (hout' p hp).trans (hout_j p hp)⟩, hlen0_pos, he'⟩
      have hsx1_0 : sx1.set (base + R + 4) (natToBitsLE w (emitted.length + 6 * acc + 0)) = sx1 := by
        simp only [Nat.add_zero]
        apply List.ext_getElem (by simp)
        intro i h1 h2; rw [List.getElem_set]; split_ifs with heq
        · subst heq
          have hget : sx1.getD (base + R + 4) [] = natToBitsLE w (emitted.length + 6 * acc) := by
            dsimp only [sx1]; rw [getD_set_ne_seg _ (by omega), hx4]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at hget
          exact hget.symm
        · rfl
      rcases repeat0_spec 6 (wsInc MaxSeg) (wsIncEntry MaxSeg ⟨base + R + 4, by omega⟩)
          B (21 * M_blk + 4) Inv6 hstep6
          (fun _ _ ⟨hl_eq, _⟩ => ⟨by rw [hl_eq]; exact hlen0_B, by omega⟩)
          ⟨rfl, by rw [hsx1_0]; exact htw_dz, fun _ _ => rfl⟩
        with ⟨len_6, τ_6, ⟨hlen6_eq, htw_6, hout_6⟩, he_6⟩
      subst len_6
      have he_inr := sumStep_inr_spec (nopStep Unit)
        (repeat0 6 (wsInc MaxSeg) (wsIncEntry MaxSeg ⟨base + R + 4, by omega⟩)) he_6
      have he_body : StepExec (padAdd6Body base R) B (Sum.inl (wsDecJzEntry MaxSeg ⟨base + R + 1, by omega⟩))
          (3 * M_blk) τx 0 (Sum.inr (Sum.inr (repeat0Exit 6))) (3 * M_blk) τ_6 0 (180 * M_blk + 60) := by
        unfold padAdd6Body
        exact (seq0_spec hlen0_pos he_dz (by rw [hz_dz]; exact he_inr)).weaken _ (by omega)
      let sx2 := sx1.set (base + R + 4) (natToBitsLE w (emitted.length + 6 * (acc + 1)))
      have h6eq : emitted.length + 6 * acc + 6 = emitted.length + 6 * (acc + 1) := by omega
      rw [h6eq] at htw_6
      have hMx2 : (encodeWorkspace sx2).length = M_blk :=
        (length_encodeWorkspace_set (by simp [sx1]; omega)
          (by dsimp only [sx1]; rw [getD_set_ne_seg _ (by omega), hx4, length_natToBitsLE, length_natToBitsLE])).trans hMx1
      rcases ih (acc + 1) sx2 τ_6 (by omega) (by simp [sx2, sx1, hlx]) hMx2
          (by dsimp only [sx2, sx1]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), hxL])
          (by dsimp only [sx2, sx1]; rw [getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by omega)])
          (by dsimp only [sx2, sx1]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), hxB])
          (by dsimp only [sx2, sx1]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), hx3])
          (by dsimp only [sx2]; rw [getD_set_self_seg _ (by simp [sx1]; omega)])
          (by dsimp only [sx2, sx1]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), hx5])
          htw_6
        with ⟨sy, τy, hly, hMy, hyL, hy1, hyB, hy3, hy4, hy5, htw_y, hout_y, he_rest⟩
      have hcomb := (loop0_step (next := padAdd6Next base R) hlen0_pos he_body rfl he_rest).weaken
        ((rem + 1 + 1) * (180 * M_blk + 62)) (by
          have : (rem + 1 + 1) * (180 * M_blk + 62) = (180 * M_blk + 62) + (rem + 1) * (180 * M_blk + 62) := by ring
          omega)
      exact ⟨sy, τy, hly, hMy, hyL, hy1, hyB, hy3, hy4, hy5, htw_y,
        fun p hp => (hout_y p hp).trans ((hout_6 p hp).trans (hout_dz p hp)), hcomb⟩
  rcases hadd_loop (3 * M_blk) 0 s2 τ_cp2 (Nat.add_zero _) hlen_s2 hM2
      hs2_len hs2_off hs2_buf hs2_tmp (by simpa using hs2_pos) hs2_W htw_cp2
    with ⟨s3, τ3, hlen_s3, hM3, hs3_len, hs3_off, hs3_buf, hs3_tmp, hs3_pos, hs3_W, htw3, hout3, he3⟩
  have hcl3 : ∀ p, 3 * M_blk ≤ p → τ3 p = false := fun p hp =>
    (hout3 p hp).trans ((hout_cp2 p hp).trans ((hout_cp1 p hp).trans (hclean p hp)))
  -- Stage 4: loop writing `3 * M_blk` pad circuits right-to-left via `shuttlePad6`
  let P := L_buf + 18 * M_blk
  let S_p := 6 * ((P + 8) * (250 * M_blk + 2 * (P + 8) + 100)) + 50 * M_blk + 30
  have hpad_loop : ∀ rem (sx : List (List Bool)) (τx : ℕ → Bool),
      rem ≤ 3 * M_blk →
      let len_x := if rem = 3 * M_blk then 3 * M_blk else len_end
      sx.length = base + R + 6 →
      (encodeWorkspace sx).length = M_blk →
      sx.getD (base + R) [] = natToBitsLE w emitted.length →
      (sx.getD (base + R + 1) []).length = w →
      sx.getD (base + R + 2) [] = emitted ++ List.replicate (L_buf - emitted.length) false →
      (sx.getD (base + R + 3) []).length = w →
      sx.getD (base + R + 4) [] = natToBitsLE w (emitted.length + 6 * rem) →
      sx.getD (base + R + 5) [] = natToBitsLE w rem →
      TapeWS τx len_x B sx →
      (∀ p, 3 * M_blk ≤ p → p < 3 * M_blk + emitted.length + 6 * rem → τx p = false) →
      (∀ i, 6 * rem ≤ i → i < 18 * M_blk → τx (3 * M_blk + emitted.length + i) = padBits.getD i false) →
      ∃ τ_end : ℕ → Bool,
        WSUnpackInv base R w L_buf M_blk B emitted τ_end len_end emitted.length ∧
        (∀ p, 3 * M_blk ≤ p → p < 3 * M_blk + emitted.length → τ_end p = false) ∧
        (∀ i < 18 * M_blk, τ_end (3 * M_blk + emitted.length + i) = padBits.getD i false) ∧
        StepExec (loop0 (shuttlePadLoopBody base R) (shuttlePadLoopNext base R)) B
          (Sum.inl (wsDecJzEntry MaxSeg ⟨base + R + 5, by omega⟩)) len_x τx 0
          (Sum.inr (Sum.inl ())) len_end τ_end 0 ((rem + 1) * (S_p + 2)) := by
    intro rem
    induction rem with
    | zero =>
      intro sx τx _ len_x hlx hMx hxL hx1 hxB hx3 hx4 hx5 htw_x hpre_x hwr_x
      have hlen_eq : len_x = len_end := by
        dsimp only [len_x]; simp only [show (0 : ℕ) ≠ 3 * M_blk by omega, ↓reduceIte]
      rw [hlen_eq] at htw_x ⊢
      have hlen_pos := TapeWS_pos htw_x
      rcases wsDecJz_spec MaxSeg B sx (s := base + R + 5) (w := w) (v := 0)
          (by omega) (by omega) hx5 (by omega) htw_x
        with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
      rw [hMx] at hout_dz he_dz
      simp only [decide_true, ↓reduceIte] at hz_dz htw_dz
      have he_nop := sumStep_inl_spec (nopStep Unit) (shuttlePad6 base R)
        (nopStep_spec (B := B) () len_end τ_dz 0 htw_dz.2.2.1 (by omega))
      have he_body : StepExec (shuttlePadLoopBody base R) B
          (Sum.inl (wsDecJzEntry MaxSeg ⟨base + R + 5, by omega⟩)) len_end τx 0
          (Sum.inr (Sum.inl ())) len_end τ_dz 0 S_p := by
        unfold shuttlePadLoopBody
        exact (seq0_spec hlen_pos he_dz (by rw [hz_dz]; exact he_nop)).weaken S_p (by dsimp only [S_p]; omega)
      have hdone := (loop0_done (next := shuttlePadLoopNext base R) he_body rfl).weaken
        ((0 + 1) * (S_p + 2)) (by omega)
      refine ⟨τ_dz, ⟨sx, hlx, hMx, htw_dz, hxL, hx1, hxB, hx3, by rw [hx4, length_natToBitsLE]⟩, ?_, ?_, hdone⟩
      · intro p hp1 hp2; rw [hout_dz p hp1]; exact hpre_x p hp1 (by omega)
      · intro i hi; rw [hout_dz _ (by omega)]; exact hwr_x i (Nat.zero_le i) hi
    | succ rem ih =>
      intro sx τx hrem_le len_x hlx hMx hxL hx1 hxB hx3 hx4 hx5 htw_x hpre_x hwr_x
      have hlen_pos := TapeWS_pos htw_x
      -- a) wsDecJz s_W (`rem + 1 -> rem`)
      rcases wsDecJz_spec MaxSeg B sx (s := base + R + 5) (w := w) (v := rem + 1)
          (by omega) (by omega) hx5 (by omega) htw_x
        with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
      rw [hMx] at hout_dz he_dz
      simp only [Nat.succ_ne_zero, decide_false, ↓reduceIte, Nat.add_sub_cancel] at hz_dz htw_dz
      let sx1 := sx.set (base + R + 5) (natToBitsLE w rem)
      have hMx1 : (encodeWorkspace sx1).length = M_blk :=
        (length_encodeWorkspace_set (by omega) (by rw [hx5, length_natToBitsLE, length_natToBitsLE])).trans hMx
      -- b) shuttlePad6 at `pos = emitted.length + 6 * rem`
      have hpos_eq : emitted.length + 6 * (rem + 1) = (emitted.length + 6 * rem) + 6 := by omega
      rcases shuttlePad6_spec base R w M_blk B (emitted.length + 6 * rem) sx1
          (by simp [sx1, hlx]) hMx1
          (by dsimp only [sx1]; rw [getD_set_ne_seg _ (by omega), hx4, hpos_eq])
          (by dsimp only [sx1]; rw [getD_set_ne_seg _ (by omega), hx1])
          (by dsimp only [sx1]; rw [getD_set_ne_seg _ (by omega), hx3])
          (by omega) (by omega) htw_dz
          (fun p hp1 hp2 => by rw [hout_dz p hp1]; exact hpre_x p hp1 (by omega))
        with ⟨q_p6, sx2, τ_p6, hlx2, hMx2, hx2_pos, hx2_off, hx2_tmp, hx2_oth, htw_p6, hpre_p6, h6_p6, hout_p6, he_p6⟩
      have hlen_next : max len_x (3 * M_blk + (emitted.length + 6 * rem) + 6) =
          (if rem = 3 * M_blk then 3 * M_blk else len_end) := by
        have hne : rem ≠ 3 * M_blk := by omega
        simp only [hne, ↓reduceIte]
        dsimp only [len_x, len_end]
        split_ifs with htop <;> omega
      rw [hlen_next] at htw_p6 he_p6
      have he_inr := sumStep_inr_spec (nopStep Unit) (shuttlePad6 base R) he_p6
      have hbody_t : 42 * M_blk + 10 + 1 +
          (6 * ((emitted.length + 6 * rem + 8) * (250 * M_blk + 2 * (emitted.length + 6 * rem + 8) + 100)) + 10) ≤ S_p := by
        dsimp only [S_p, P]
        have hle1 : (emitted.length + 6 * rem + 8) * (250 * M_blk + 2 * (emitted.length + 6 * rem + 8) + 100) ≤
            (L_buf + 18 * M_blk + 8) * (250 * M_blk + 2 * (L_buf + 18 * M_blk + 8) + 100) :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
      have he_body : StepExec (shuttlePadLoopBody base R) B
          (Sum.inl (wsDecJzEntry MaxSeg ⟨base + R + 5, by omega⟩)) len_x τx 0
          (Sum.inr (Sum.inr q_p6)) (if rem = 3 * M_blk then 3 * M_blk else len_end) τ_p6 0 S_p := by
        unfold shuttlePadLoopBody
        exact (seq0_spec hlen_pos he_dz (by rw [hz_dz]; exact he_inr)).weaken S_p hbody_t
      have hwr_next : ∀ i, 6 * rem ≤ i → i < 18 * M_blk →
          τ_p6 (3 * M_blk + emitted.length + i) = padBits.getD i false := by
        intro i hi1 hi2
        by_cases hlt : i < 6 * rem + 6
        · have hd_lt : i - 6 * rem < 6 := by omega
          have hpos_i : 3 * M_blk + emitted.length + i = 3 * M_blk + (emitted.length + 6 * rem) + (i - 6 * rem) := by omega
          rw [hpos_i, h6_p6 (i - 6 * rem) hd_lt]
          dsimp only [padBits]
          rw [padBits_getD (3 * M_blk) [false, true, false, false, false, true] rfl i (by omega),
              show i % 6 = i - 6 * rem by omega]
        · rw [hout_p6 _ (by omega), hout_dz _ (by omega)]
          exact hwr_x i (by omega) hi2
      rcases ih sx2 τ_p6 (by omega) hlx2 hMx2
          (by rw [hx2_oth _ (by omega) (by omega) (by omega)]; dsimp only [sx1]; rw [getD_set_ne_seg _ (by omega), hxL])
          hx2_off
          (by rw [hx2_oth _ (by omega) (by omega) (by omega)]; dsimp only [sx1]; rw [getD_set_ne_seg _ (by omega), hxB])
          hx2_tmp hx2_pos
          (by rw [hx2_oth _ (by omega) (by omega) (by omega)]; dsimp only [sx1]; rw [getD_set_self_seg _ (by omega)])
          htw_p6 (fun p h1 h2 => hpre_p6 p h1 (by omega)) hwr_next
        with ⟨τ_end, hunp_end, hpre_end, hwr_end, he_rest⟩
      have hcomb := (loop0_step (next := shuttlePadLoopNext base R) (TapeWS_pos htw_p6) he_body rfl he_rest).weaken
        ((rem + 1 + 1) * (S_p + 2)) (by
          have : (rem + 1 + 1) * (S_p + 2) = (S_p + 2) + (rem + 1) * (S_p + 2) := by ring
          omega)
      exact ⟨τ_end, hunp_end, hpre_end, hwr_end, hcomb⟩
  rcases hpad_loop (3 * M_blk) s3 τ3 (Nat.le_refl _) hlen_s3 hM3
      hs3_len hs3_off hs3_buf hs3_tmp (by simpa [show 6 * (3 * M_blk) = 18 * M_blk by omega] using hs3_pos)
      hs3_W (by simpa using htw3) (fun p hp _ => hcl3 p hp) (fun i h1 h2 => by omega)
    with ⟨τ_end, hunp_end, hpre_end, hwr_end, he4⟩
  simp only [↓reduceIte] at he4
  have he34 := seq0_spec (f := fun _ => Sum.inl (wsDecJzEntry MaxSeg ⟨base + R + 5, by omega⟩)) hlen0_pos he3 he4
  have he24 := seq0_spec (f := fun _ => Sum.inl (Sum.inl (wsDecJzEntry MaxSeg ⟨base + R + 1, by omega⟩))) hlen0_pos he_cp2 he34
  have he14 := seq0_spec (f := fun _ => Sum.inl (wsCopyEntry MaxSeg
      (⟨base + R + 1, by omega⟩, ⟨base + R + 5, by omega⟩, ⟨base + R + 3, by omega⟩))) hlen0_pos he_cp1 he24
  exact ⟨_, τ_end, hunp_end, hpre_end, hwr_end, he14.weaken _ (shuttlePadTail_time_le hem_le)⟩

/-! ### `unpackOutLoop_spec_fixedLen`: unpack `emitted` into `[3 * M_blk, 3 * M_blk + emitted.length)` preserving all `p ≥ 3 * M_blk + emitted.length` -/

theorem unpackOutLoop_spec_fixedLen (base R w L_buf M_blk B len_fixed : ℕ) (full_tail : List Bool)
    (htail_le : full_tail.length ≤ L_buf)
    (hL_pow : L_buf < 2 ^ w)
    (hfix_ge : 3 * M_blk + full_tail.length ≤ len_fixed)
    (hfix_B : len_fixed ≤ B)
    {τ₁ : ℕ → Bool}
    (hinv : WSUnpackInv base R w L_buf M_blk B full_tail τ₁ len_fixed full_tail.length)
    (hclean : ∀ p, 3 * M_blk ≤ p → p < 3 * M_blk + full_tail.length → τ₁ p = false) :
    ∃ τ₂ : ℕ → Bool,
      WSUnpackInv base R w L_buf M_blk B full_tail τ₂ len_fixed 0 ∧
      (∀ i < full_tail.length, τ₂ (3 * M_blk + i) = full_tail.getD i false) ∧
      (∀ p, 3 * M_blk + full_tail.length ≤ p → τ₂ p = τ₁ p) ∧
      StepExec (unpackOutLoop base R) B (unpackOutLoopEntry base R) len_fixed τ₁ 0
        (Sum.inr (Sum.inl ())) len_fixed τ₂ 0
        ((L_buf + 1) * ((L_buf + 2) * (450 * M_blk + 2 * L_buf + 200) + 2)) := by
  let MaxSeg := base + R + 5
  let L_tail := full_tail.length
  let S_unp := (L_buf + 2) * (450 * M_blk + 2 * L_buf + 200)
  have haux : ∀ rem (τa : ℕ → Bool),
      rem ≤ L_tail →
      WSUnpackInv base R w L_buf M_blk B full_tail τa len_fixed rem →
      (∀ p, 3 * M_blk ≤ p → p < 3 * M_blk + rem → τa p = false) →
      (∀ i, rem ≤ i → i < L_tail → τa (3 * M_blk + i) = full_tail.getD i false) →
      ∃ τ₂ : ℕ → Bool,
        WSUnpackInv base R w L_buf M_blk B full_tail τ₂ len_fixed 0 ∧
        (∀ i < L_tail, τ₂ (3 * M_blk + i) = full_tail.getD i false) ∧
        (∀ p, 3 * M_blk + L_tail ≤ p → τ₂ p = τa p) ∧
        StepExec (unpackOutLoop base R) B (unpackOutLoopEntry base R) len_fixed τa 0
          (Sum.inr (Sum.inl ())) len_fixed τ₂ 0 ((rem + 1) * (S_unp + 2)) := by
    intro rem
    induction rem with
    | zero =>
      intro τa _ hinv_a _ hwritten
      rcases hinv_a with ⟨sa, hla, hMa, htwa, houtLa, hsys1a, houtBa, htmp1a, htmp2a⟩
      have hlen_pos := TapeWS_pos htwa
      rcases wsDecJz_spec MaxSeg B sa (s := base + R) (w := w) (v := 0)
          (by omega) (by omega) houtLa (by omega) htwa
        with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
      rw [hMa] at hout_dz he_dz
      simp only [decide_true, ↓reduceIte] at hz_dz htw_dz
      have he_nop := sumStep_inl_spec (nopStep Unit) (unpackActive base R)
        (nopStep_spec (B := B) () len_fixed τ_dz 0 hfix_B (by omega))
      have hbody := seq0_spec
        (f := fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (unpackActiveEntry base R))
        hlen_pos he_dz (by rw [hz_dz]; exact he_nop)
      have hdone := (loop0_done (next := unpackNext base R) hbody rfl).weaken
        ((0 + 1) * (S_unp + 2)) (by
          have : 2 * (450 * M_blk + 2 * L_buf + 200) ≤ S_unp := Nat.mul_le_mul_right _ (by omega)
          omega)
      refine ⟨τ_dz, ⟨sa, hla, hMa, htw_dz, houtLa, hsys1a, houtBa, htmp1a, htmp2a⟩, ?_, ?_, hdone⟩
      · intro i hi; rw [hout_dz _ (by omega)]; exact hwritten i (Nat.zero_le i) hi
      · intro p hp; exact hout_dz p (by omega)
    | succ rem ih =>
      intro τa hrem_le hinv_a hpre_a hwritten_a
      rcases hinv_a with ⟨sa, hla, hMa, htwa, houtLa, hsys1a, houtBa, htmp1a, htmp2a⟩
      have hlen_pos := TapeWS_pos htwa
      have hrem_lt_L : rem < L_tail := by omega
      -- 1) wsDecJz on base + R (`rem + 1 -> rem`)
      rcases wsDecJz_spec MaxSeg B sa (s := base + R) (w := w) (v := rem + 1)
          (by omega) (by omega) houtLa (by omega) htwa
        with ⟨q_dz, τ_dz, hz_dz, htw_dz, hout_dz, he_dz⟩
      rw [hMa] at hout_dz he_dz
      simp only [Nat.succ_ne_zero, decide_false, ↓reduceIte, Nat.add_sub_cancel] at hz_dz htw_dz
      let sa₁ := sa.set (base + R) (natToBitsLE w rem)
      have hMa₁ : (encodeWorkspace sa₁).length = M_blk :=
        (length_encodeWorkspace_set (by omega) (by rw [houtLa, length_natToBitsLE, length_natToBitsLE])).trans hMa
      -- 2) wsCopy (`base + R + 1 := base + R`, `tmp := base + R + 3`)
      rcases wsCopy_spec MaxSeg B sa₁ (dst := base + R + 1) (src := base + R) (tmp := base + R + 3)
          (w := w) (v := rem)
          (by simp [sa₁]; omega) (by simp [sa₁]; omega) (by simp [sa₁]; omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by dsimp only [sa₁]; rw [getD_set_ne_seg _ (by omega), hsys1a])
          (by dsimp only [sa₁]; rw [getD_set_self_seg _ (by omega)])
          (by dsimp only [sa₁]; rw [getD_set_ne_seg _ (by omega), htmp1a])
          (by omega) htw_dz
        with ⟨q_cp, τ_cp, htw_cp, hout_cp, he_cp⟩
      rw [hMa₁] at hout_cp he_cp
      let sa₂_0 := sa₁.set (base + R + 1) (natToBitsLE w rem)
      let sa₂ := sa₂_0.set (base + R + 3) (natToBitsLE w 0)
      have hMa₂ : (encodeWorkspace sa₂).length = M_blk := by
        have h1 := length_encodeWorkspace_set (segs := sa₁) (s := base + R + 1) (newSeg := natToBitsLE w rem)
          (by simp [sa₁]; omega) (by dsimp only [sa₁]; rw [getD_set_ne_seg _ (by omega), hsys1a, length_natToBitsLE])
        have h2 := length_encodeWorkspace_set (segs := sa₂_0) (s := base + R + 3) (newSeg := natToBitsLE w 0)
          (by simp [sa₂_0, sa₁]; omega)
          (by dsimp only [sa₂_0, sa₁]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), htmp1a, length_natToBitsLE])
        exact h2.trans (h1.trans hMa₁)
      -- 3) wsReadBit
      rcases wsReadBit_spec MaxSeg B sa₂ (arr := base + R + 2) (idx := base + R)
          (tmp := base + R + 3) (tmp2 := base + R + 4) (w := w) (v := rem)
          (by simp [sa₂, sa₂_0, sa₁]; omega) (by simp [sa₂, sa₂_0, sa₁]; omega)
          (by simp [sa₂, sa₂_0, sa₁]; omega) (by simp [sa₂, sa₂_0, sa₁]; omega)
          (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by dsimp only [sa₂, sa₂_0, sa₁]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by omega)])
          (by dsimp only [sa₂, sa₂_0, sa₁]; rw [getD_set_self_seg _ (by simp; omega), length_natToBitsLE])
          (by dsimp only [sa₂, sa₂_0, sa₁]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), htmp2a])
          (by omega) htw_cp
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
        have h1 := length_encodeWorkspace_set (segs := sa₂) (s := base + R + 3) (newSeg := natToBitsLE w 0)
          (by simp [sa₂, sa₂_0, sa₁]; omega) (by dsimp only [sa₂, sa₂_0, sa₁]; rw [getD_set_self_seg _ (by simp; omega)])
        have h2 := length_encodeWorkspace_set (segs := sa₃_0) (s := base + R + 4) (newSeg := natToBitsLE w 0)
          (by simp [sa₃_0, sa₂, sa₂_0, sa₁]; omega)
          (by dsimp only [sa₃_0, sa₂, sa₂_0, sa₁]; rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega), htmp2a, length_natToBitsLE])
        exact h2.trans (h1.trans hMa₂)
      -- 4) shuttleWrite
      have hsys1₃ : sa₃.getD (base + R + 1) [] = natToBitsLE w rem := by
        dsimp only [sa₃, sa₃_0, sa₂, sa₂_0, sa₁]
        rw [getD_set_ne_seg _ (by omega), getD_set_ne_seg _ (by omega),
            getD_set_ne_seg _ (by omega), getD_set_self_seg _ (by simp; omega)]
      rcases shuttleWrite_spec MaxSeg B sa₃ (s_off := base + R + 1) (w := w) (offset := rem) (wsReadBitResult q_rb)
          (by simp [sa₃, sa₃_0, sa₂, sa₂_0, sa₁]; omega) (by omega) hsys1₃ (by omega)
          (by rw [hMa₃]; omega) htw_rb
          (fun p hp1 hp2 => by rw [hMa₃] at hp1 hp2; rw [hout_rb p hp1, hout_cp p hp1, hout_dz p hp1]; exact hpre_a p hp1 (by omega))
        with ⟨q_sw, τ_sw, htw_sw, hpre_sw, hcur_sw, hout_sw, he_sw⟩
      rw [hMa₃] at htw_sw hpre_sw hcur_sw hout_sw he_sw
      have hlen_max : max len_fixed (3 * M_blk + rem + 1) = len_fixed := by omega
      rw [hlen_max] at htw_sw he_sw
      let sa₄ := sa₃.set (base + R + 1) (natToBitsLE w 0)
      have hMa₄ : (encodeWorkspace sa₄).length = M_blk :=
        (length_encodeWorkspace_set (by simp [sa₃, sa₃_0, sa₂, sa₂_0, sa₁]; omega)
          (by rw [hsys1₃, length_natToBitsLE, length_natToBitsLE])).trans hMa₃
      let qd : SegQuad MaxSeg :=
        (⟨base + R + 2, by omega⟩, ⟨base + R, by omega⟩, ⟨base + R + 3, by omega⟩, ⟨base + R + 4, by omega⟩)
      have he_rbsw := seq0_spec (f := fun q => shuttleWriteEntry MaxSeg ⟨base + R + 1, by omega⟩ (wsReadBitResult q))
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
              have : 2 * (32 * M_blk + 40) ≤ (L_buf + 2) * (32 * M_blk + 40) := Nat.mul_le_mul_right _ (by omega)
              omega
      have hbody := (seq0_spec
        (f := fun q => if wsDecJzWasZero q then Sum.inl () else Sum.inr (unpackActiveEntry base R))
        hlen_pos he_dz (by rw [hz_dz]; exact he_right)).weaken S_unp htime_body
      have hinv_sw : WSUnpackInv base R w L_buf M_blk B full_tail τ_sw len_fixed rem := by
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
        · rw [hout_sw _ (by omega), hout_rb _ (by omega), hout_cp _ (by omega), hout_dz _ (by omega)]
          exact hwritten_a i (by omega) hi2
      rcases ih τ_sw (by omega) hinv_sw hpre_sw hwritten_sw with ⟨τ_end, hinv_end, hwr_end, hout_end, he_rest⟩
      have hstep := (loop0_step (next := unpackNext base R) hlen_pos hbody rfl he_rest).weaken
        ((rem + 1 + 1) * (S_unp + 2)) (by
          have : (rem + 1 + 1) * (S_unp + 2) = (S_unp + 2) + (rem + 1) * (S_unp + 2) := by ring
          omega)
      refine ⟨τ_end, hinv_end, hwr_end, ?_, hstep⟩
      intro p hp
      rw [hout_end p hp, hout_sw p (by omega), hout_rb p (by omega), hout_cp p (by omega), hout_dz p (by omega)]
  rcases haux L_tail τ₁ (Nat.le_refl _) hinv hclean (fun i h1 h2 => by omega)
    with ⟨τ₂, hinv₂, hwr₂, hout₂, he_tot⟩
  exact ⟨τ₂, hinv₂, hwr₂, hout₂, he_tot.weaken _ (Nat.mul_le_mul_right (S_unp + 2) (by omega))⟩

/-! ### `execRMToOutputPadded`: zero-circularity RM simulator + direct padded output -/

abbrev ExecRMOutPaddedQ (base R : ℕ) (Q : Type) : Type :=
  (Q × RMSubQ base R) ⊕
    (ShuttlePadTailQ base R ⊕
      (UnpackLoopQ base R ⊕ LiftBlkQ Bool))

def execRMToOutputPadded (base R seg_inp : ℕ) {Q : Type} (M : RMProg R Q) :
    StepFn (ExecRMOutPaddedQ base R Q) :=
  seq0 (simRMLoop base R seg_inp M)
    (seq0 (shuttlePadTail base R)
      (seq0 (unpackOutLoop base R) (liftBlockStep blkSweepTrue)
        (fun _ => liftBlkEntry false))
      (fun _ => Sum.inl (unpackOutLoopEntry base R)))
    (fun _ => Sum.inl (shuttlePadTailEntry base R))

def execRMToOutputPaddedEntry (base R seg_inp : ℕ) {Q : Type} (M : RMProg R Q) (q₀ : Q) :
    ExecRMOutPaddedQ base R Q :=
  Sum.inl (q₀, rmSubEntry base R seg_inp M q₀)

def execRMPaddedTimeBound (steps Vmax L_buf M_blk : ℕ) : ℕ :=
  (steps + 1) * ((max Vmax L_buf + 2) * (250 * M_blk + 100) + 2) +
  shuttlePadTailTimeBound L_buf M_blk +
  (L_buf + 1) * ((L_buf + 2) * (450 * M_blk + 2 * L_buf + 200) + 2) +
  14 * M_blk + 20

theorem execRMToOutputPadded_spec (base R w L_buf M_blk B seg_inp Vmax : ℕ)
    (h_inp : seg_inp < base) (hV_pow : Vmax < 2 ^ w) (hP_pow : L_buf + 18 * M_blk < 2 ^ w)
    {Q : Type} (M : RMProg R Q) (inp : List Bool)
    {q₀ q₁ : Q} {reg₀ reg₁ : RegState R} {emitted : List Bool} {steps sys1Val : ℕ}
    (hexec : RMExec M Vmax inp q₀ reg₀ q₁ reg₁ emitted steps)
    (hem_le : emitted.length ≤ L_buf)
    (hout_B : 3 * M_blk + emitted.length + 18 * M_blk ≤ B)
    {τ₀ : ℕ → Bool}
    (hinv₀ : WSRMInv base R w L_buf M_blk B seg_inp inp τ₀ (3 * M_blk) reg₀ [] sys1Val)
    (hclean₀ : ∀ p, 3 * M_blk ≤ p → τ₀ p = false) :
    let padBits := (List.range (3 * M_blk)).flatMap (fun _ => [false, true, false, false, false, true])
    let out := List.replicate (3 * M_blk) true ++ emitted ++ padBits
    ∃ q_end, ∃ τ_final : ℕ → Bool,
      1 ≤ out.length ∧
      (∀ j < out.length, τ_final j = QCSD_tapeRead out j) ∧
      StepExec (execRMToOutputPadded base R seg_inp M) B
        (execRMToOutputPaddedEntry base R seg_inp M q₀) (3 * M_blk) τ₀ 0
        q_end out.length τ_final 0 (execRMPaddedTimeBound steps Vmax L_buf M_blk) := by
  intro padBits out
  have hlen0_pos : 1 ≤ 3 * M_blk := by rcases hinv₀ with ⟨_, _, _, htw₀, _⟩; exact TapeWS_pos htw₀
  have hL_pow : L_buf < 2 ^ w := by omega
  have hpad_len : padBits.length = 18 * M_blk := by
    have := padBits_length (3 * M_blk) [false, true, false, false, false, true] rfl
    dsimp only [padBits]; omega
  have hout_len : out.length = 3 * M_blk + emitted.length + 18 * M_blk := by
    simp only [out, List.length_append, List.length_replicate, hpad_len]
  -- Stage 1: simRMLoop
  rcases simRMLoop_spec base R w L_buf M_blk B seg_inp Vmax h_inp hV_pow hL_pow M inp hexec hem_le hinv₀
    with ⟨τ₁, hinv₁, hout₁, he_sim⟩
  have hclean₁ : ∀ p, 3 * M_blk ≤ p → τ₁ p = false := fun p hp => (hout₁ p hp).trans (hclean₀ p hp)
  -- Stage 2: shuttlePadTail
  rcases shuttlePadTail_spec base R w L_buf M_blk B seg_inp inp hinv₁ hclean₁ hP_pow hout_B
    with ⟨q_pad, τ₂, hunp₂, hpre₂, hwr_pad, he_pad⟩
  -- Stage 3: unpackOutLoop_spec_fixedLen
  rcases unpackOutLoop_spec_fixedLen base R w L_buf M_blk B (3 * M_blk + emitted.length + 18 * M_blk) emitted
      hem_le hL_pow (by omega) hout_B hunp₂ hpre₂
    with ⟨τ₃, hunp₃, hwr_em, hout₃, he_unp⟩
  -- Stage 4: blkSweepTrue
  rcases hunp₃ with ⟨s3, hl3, hM3, htw3, _⟩
  rcases htw3 with ⟨hs3_ne, hW_le3, hlen_B3, hws3⟩
  rw [hM3] at hW_le3
  rcases blkSweepTrue_spec s3 hs3_ne (readBlk τ₃) hws3 with ⟨σ_end, hall_home, hblk_sw⟩
  rw [hM3] at hall_home hblk_sw
  rcases liftBlockStep_spec blkSweepTrue B M_blk (3 * M_blk + emitted.length + 18 * M_blk) τ₃
      false true σ_end 0 0 (2 * M_blk) hW_le3 hlen_B3 hblk_sw
    with ⟨τ_final, hread_fin, hout_fin, he_sw⟩
  simp only [Nat.mul_zero] at he_sw
  have he34 := seq0_spec (f := fun _ => liftBlkEntry false) (by omega) he_unp he_sw
  have he24 := seq0_spec (f := fun _ => Sum.inl (unpackOutLoopEntry base R)) (by omega) he_pad he34
  have he14 := (seq0_spec (f := fun _ => Sum.inl (shuttlePadTailEntry base R)) hlen0_pos he_sim he24).weaken
    (execRMPaddedTimeBound steps Vmax L_buf M_blk) (by dsimp only [execRMPaddedTimeBound]; omega)
  rw [← hout_len] at he14
  refine ⟨_, τ_final, by omega, ?_, he14⟩
  intro j hj
  rw [hout_len] at hj
  simp only [QCSD_tapeRead, out]
  by_cases hjW : j < 3 * M_blk
  · rw [List.append_assoc, getD_append_left _ _ _ (by simpa using hjW)]
    have hrep : (List.replicate (3 * M_blk) true).getD j false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; simp [hjW]
    rw [hrep]
    have hdiv : j / 3 < M_blk := by omega
    have hblk := (congrFun hread_fin (j / 3)).trans (hall_home (j / 3) hdiv)
    dsimp only [readBlk, blkHome] at hblk
    have h0 : τ_final (3 * (j / 3)) = true := (Prod.mk.inj hblk).1
    have h1 : τ_final (3 * (j / 3) + 1) = true := (Prod.mk.inj (Prod.mk.inj hblk).2).1
    have h2 : τ_final (3 * (j / 3) + 2) = true := (Prod.mk.inj (Prod.mk.inj hblk).2).2
    have hmod : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hmod with hm | hm | hm
    · rw [show j = 3 * (j / 3) by omega, h0]
    · rw [show j = 3 * (j / 3) + 1 by omega, h1]
    · rw [show j = 3 * (j / 3) + 2 by omega, h2]
  · by_cases hjE : j < 3 * M_blk + emitted.length
    · rw [getD_append_left _ _ _ (by simp; omega), getD_append_right _ _ _ (by simp; omega)]
      simp only [List.length_replicate]
      calc τ_final j = τ_final (3 * M_blk + (j - 3 * M_blk)) := by congr 1; omega
        _ = τ₃ (3 * M_blk + (j - 3 * M_blk)) := hout_fin _ (by omega)
        _ = emitted.getD (j - 3 * M_blk) false := hwr_em (j - 3 * M_blk) (by omega)
    · rw [getD_append_right _ _ _ (by simp; omega)]
      simp only [List.length_append, List.length_replicate]
      calc τ_final j = τ_final (3 * M_blk + emitted.length + (j - (3 * M_blk + emitted.length))) := by congr 1; omega
        _ = τ₃ (3 * M_blk + emitted.length + (j - (3 * M_blk + emitted.length))) := hout_fin _ (by omega)
        _ = τ₂ (3 * M_blk + emitted.length + (j - (3 * M_blk + emitted.length))) := hout₃ _ (by omega)
        _ = padBits.getD (j - (3 * M_blk + emitted.length)) false := hwr_pad (j - (3 * M_blk + emitted.length)) (by omega)

/-! ## Phase 3: Compact Register Width, Explicit `Fintype`/`DecidableEq`, and End-to-End TM Compilation Theorems -/

/-! ### Explicit `Fintype` / `DecidableEq` Witnesses (Zero `instance` Declarations) -/

private abbrev ftSum {α β : Type} (hα : Fintype α) (hβ : Fintype β) : Fintype (α ⊕ β) :=
  @instFintypeSum α β hα hβ

private def deSum {α β : Type} (hα : DecidableEq α) (hβ : DecidableEq β) : DecidableEq (α ⊕ β) :=
  @instDecidableEqSum α β hα hβ

private abbrev ftProd {α β : Type} (hα : Fintype α) (hβ : Fintype β) : Fintype (α × β) :=
  @instFintypeProd α β hα hβ

private def deProd {α β : Type} (hα : DecidableEq α) (hβ : DecidableEq β) : DecidableEq (α × β) :=
  @instDecidableEqProd α β hα hβ

private abbrev ftRepeat0Q (N : ℕ) {Q : Type} (hQ : Fintype Q) : Fintype (Repeat0Q N Q) :=
  ftProd inferInstance (ftSum inferInstance hQ)

private def deRepeat0Q (N : ℕ) {Q : Type} (hQ : DecidableEq Q) : DecidableEq (Repeat0Q N Q) :=
  deProd inferInstance (deSum inferInstance hQ)

private abbrev ftRepeatAtQ (N : ℕ) {Q : Type} (hQ : Fintype Q) : Fintype (RepeatAtQ N Q) :=
  ftProd inferInstance (ftProd inferInstance (ftSum inferInstance hQ))

private def deRepeatAtQ (N : ℕ) {Q : Type} (hQ : DecidableEq Q) : DecidableEq (RepeatAtQ N Q) :=
  deProd inferInstance (deProd inferInstance (deSum inferInstance hQ))

private abbrev ftRawInitWinQ : Fintype RawInitWinQ :=
  ftSum inferInstance inferInstance

private def deRawInitWinQ : DecidableEq RawInitWinQ :=
  deSum inferInstance inferInstance

private abbrev ftRawSlideRight1Q : Fintype RawSlideRight1Q :=
  ftSum inferInstance (ftProd inferInstance (ftSum inferInstance inferInstance))

private def deRawSlideRight1Q : DecidableEq RawSlideRight1Q :=
  deSum inferInstance (deProd inferInstance (deSum inferInstance inferInstance))

private abbrev ftRawDecWinMarkQ : Fintype RawDecWinMarkQ :=
  ftSum inferInstance (ftProd inferInstance (ftSum inferInstance (ftProd inferInstance (ftSum inferInstance inferInstance))))

private def deRawDecWinMarkQ : DecidableEq RawDecWinMarkQ :=
  deSum inferInstance (deProd inferInstance (deSum inferInstance (deProd inferInstance (deSum inferInstance inferInstance))))

private abbrev ftRawSlideWBodyQ : Fintype RawSlideWBodyQ :=
  ftSum ftRawDecWinMarkQ (ftProd inferInstance (ftSum inferInstance ftRawSlideRight1Q))

private def deRawSlideWBodyQ : DecidableEq RawSlideWBodyQ :=
  deSum deRawDecWinMarkQ (deProd inferInstance (deSum inferInstance deRawSlideRight1Q))

private abbrev ftRawSlide16w28Q : Fintype RawSlide16w28Q :=
  ftSum (ftRepeatAtQ 16 (ftProd inferInstance ftRawSlideWBodyQ))
    (ftProd inferInstance (ftRepeatAtQ 28 ftRawSlideRight1Q))

private def deRawSlide16w28Q : DecidableEq RawSlide16w28Q :=
  deSum (deRepeatAtQ 16 (deProd inferInstance deRawSlideWBodyQ))
    (deProd inferInstance (deRepeatAtQ 28 deRawSlideRight1Q))

private abbrev ftExpandBodyQ : Fintype ExpandBodyQ :=
  ftSum inferInstance (ftProd inferInstance (ftSum inferInstance (ftSum inferInstance inferInstance)))

private def deExpandBodyQ : DecidableEq ExpandBodyQ :=
  deSum inferInstance (deProd inferInstance (deSum inferInstance (deSum inferInstance inferInstance)))

private abbrev ftRawExpandTouchQ : Fintype RawExpandTouchQ :=
  ftSum
    (ftSum ftRawInitWinQ
      (ftProd inferInstance
        (ftProd inferInstance
          (ftSum ftRawSlide16w28Q
            (ftProd inferInstance
              (ftSum inferInstance (ftProd inferInstance (ftProd inferInstance ftExpandBodyQ))))))))
    (ftProd inferInstance inferInstance)

private def deRawExpandTouchQ : DecidableEq RawExpandTouchQ :=
  deSum
    (deSum deRawInitWinQ
      (deProd inferInstance
        (deProd inferInstance
          (deSum deRawSlide16w28Q
            (deProd inferInstance
              (deSum inferInstance (deProd inferInstance (deProd inferInstance deExpandBodyQ))))))))
    (deProd inferInstance inferInstance)

private abbrev ftExtract2wLoopQ : Fintype Extract2wLoopQ :=
  ftSum inferInstance (ftSum inferInstance inferInstance)

private def deExtract2wLoopQ : DecidableEq Extract2wLoopQ :=
  deSum inferInstance (deSum inferInstance inferInstance)

private abbrev ftExtractSegNQ : Fintype ExtractSegNQ :=
  ftProd inferInstance
    (ftSum inferInstance
      (ftSum inferInstance
        (ftSum inferInstance
          (ftSum (ftSum inferInstance inferInstance) ftExtract2wLoopQ))))

private def deExtractSegNQ : DecidableEq ExtractSegNQ :=
  deProd inferInstance
    (deSum inferInstance
      (deSum inferInstance
        (deSum inferInstance
          (deSum (deSum inferInstance inferInstance) deExtract2wLoopQ))))

private abbrev ftWsCopyLastQ (MaxSeg : ℕ) : Fintype (WsCopyLastQ MaxSeg) :=
  ftSum inferInstance (ftSum inferInstance (ftSum inferInstance inferInstance))

private def deWsCopyLastQ (MaxSeg : ℕ) : DecidableEq (WsCopyLastQ MaxSeg) :=
  deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance))

private abbrev ftBuildSegInpQ (R : ℕ) : Fintype (BuildSegInpQ R) :=
  ftProd inferInstance
    (ftSum inferInstance
      (ftSum (ftWsCopyLastQ (8 + R + 5))
        (ftSum (ftSum inferInstance inferInstance) (ftWsCopyLastQ (8 + R + 5)))))

private def deBuildSegInpQ (R : ℕ) : DecidableEq (BuildSegInpQ R) :=
  deProd inferInstance
    (deSum inferInstance
      (deSum (deWsCopyLastQ (8 + R + 5))
        (deSum (deSum inferInstance inferInstance) (deWsCopyLastQ (8 + R + 5)))))

private abbrev ftPushZeroRegQ (R wMul wAdd : ℕ) : Fintype (PushZeroRegQ R wMul wAdd) :=
  ftSum inferInstance
    (ftSum (ftRepeat0Q wAdd inferInstance)
      (ftRepeat0Q wMul (ftWsCopyLastQ (8 + R + 5))))

private def dePushZeroRegQ (R wMul wAdd : ℕ) : DecidableEq (PushZeroRegQ R wMul wAdd) :=
  deSum inferInstance
    (deSum (deRepeat0Q wAdd inferInstance)
      (deRepeat0Q wMul (deWsCopyLastQ (8 + R + 5))))

private abbrev ftWsAddLoopQ (MaxSeg : ℕ) : Fintype (WsAddLoopQ MaxSeg) :=
  ftSum inferInstance (ftSum inferInstance inferInstance)

private def deWsAddLoopQ (MaxSeg : ℕ) : DecidableEq (WsAddLoopQ MaxSeg) :=
  deSum inferInstance (deSum inferInstance inferInstance)

private abbrev ftWsMulLoopQ (MaxSeg : ℕ) : Fintype (WsMulLoopQ MaxSeg) :=
  ftSum inferInstance (ftSum inferInstance (ftSum inferInstance (ftWsAddLoopQ MaxSeg)))

private def deWsMulLoopQ (MaxSeg : ℕ) : DecidableEq (WsMulLoopQ MaxSeg) :=
  deSum inferInstance (deSum inferInstance (deSum inferInstance (deWsAddLoopQ MaxSeg)))

private abbrev ftWsMulIntoQ (MaxSeg : ℕ) : Fintype (WsMulIntoQ MaxSeg) :=
  ftSum inferInstance (ftSum (ftWsMulLoopQ MaxSeg) (ftSum inferInstance inferInstance))

private def deWsMulIntoQ (MaxSeg : ℕ) : DecidableEq (WsMulIntoQ MaxSeg) :=
  deSum inferInstance (deSum (deWsMulLoopQ MaxSeg) (deSum inferInstance inferInstance))

private abbrev ftWsAddSegLenQ (MaxSeg mult : ℕ) : Fintype (WsAddSegLenQ MaxSeg mult) :=
  ftSum inferInstance (ftSum inferInstance (ftRepeat0Q mult inferInstance))

private def deWsAddSegLenQ (MaxSeg mult : ℕ) : DecidableEq (WsAddSegLenQ MaxSeg mult) :=
  deSum inferInstance (deSum inferInstance (deRepeat0Q mult inferInstance))

private abbrev ftComputeLbufQ (R K_L d_L : ℕ) : Fintype (ComputeLbufQ R K_L d_L) :=
  ftSum (ftWsAddSegLenQ (8 + R + 5) 1)
    (ftSum inferInstance
      (ftSum inferInstance
        (ftSum inferInstance (ftRepeat0Q d_L (ftWsMulIntoQ (8 + R + 5))))))

private def deComputeLbufQ (R K_L d_L : ℕ) : DecidableEq (ComputeLbufQ R K_L d_L) :=
  deSum (deWsAddSegLenQ (8 + R + 5) 1)
    (deSum inferInstance
      (deSum inferInstance
        (deSum inferInstance (deRepeat0Q d_L (deWsMulIntoQ (8 + R + 5))))))

private abbrev ftInitWSPrefixQ (R wMul wAdd K_L d_L : ℕ) : Fintype (InitWSPrefixQ R wMul wAdd K_L d_L) :=
  ftSum ftRawExpandTouchQ
    (ftSum ftExtractSegNQ
      (ftSum (ftBuildSegInpQ R)
        (ftSum (ftRepeat0Q 5 (ftPushZeroRegQ R wMul wAdd))
          (ftComputeLbufQ R K_L d_L))))

private def deInitWSPrefixQ (R wMul wAdd K_L d_L : ℕ) : DecidableEq (InitWSPrefixQ R wMul wAdd K_L d_L) :=
  deSum deRawExpandTouchQ
    (deSum deExtractSegNQ
      (deSum (deBuildSegInpQ R)
        (deSum (deRepeat0Q 5 (dePushZeroRegQ R wMul wAdd))
          (deComputeLbufQ R K_L d_L))))

private abbrev ftGrowOutBufQ (R : ℕ) : Fintype (GrowOutBufQ R) :=
  ftSum inferInstance (ftSum inferInstance (ftSum inferInstance inferInstance))

private def deGrowOutBufQ (R : ℕ) : DecidableEq (GrowOutBufQ R) :=
  deSum inferInstance (deSum inferInstance (deSum inferInstance inferInstance))

private abbrev ftComputeSegWQ (R : ℕ) : Fintype (ComputeSegWQ R) :=
  ftSum (ftProd inferInstance (ftWsAddSegLenQ (8 + R + 5) 3))
    (ftSum (ftWsAddSegLenQ (8 + R + 5) 3)
      (ftRepeat0Q (3 * (8 + R + 7)) inferInstance))

private def deComputeSegWQ (R : ℕ) : DecidableEq (ComputeSegWQ R) :=
  deSum (deProd inferInstance (deWsAddSegLenQ (8 + R + 5) 3))
    (deSum (deWsAddSegLenQ (8 + R + 5) 3)
      (deRepeat0Q (3 * (8 + R + 7)) inferInstance))

private abbrev ftInitWSSuffixQ (R wMul wAdd : ℕ) : Fintype (InitWSSuffixQ R wMul wAdd) :=
  ftSum (ftRepeat0Q (R + 2) (ftPushZeroRegQ R wMul wAdd))
    (ftSum (ftGrowOutBufQ R)
      (ftSum (ftRepeat0Q 3 (ftPushZeroRegQ R wMul wAdd))
        (ftComputeSegWQ R)))

private def deInitWSSuffixQ (R wMul wAdd : ℕ) : DecidableEq (InitWSSuffixQ R wMul wAdd) :=
  deSum (deRepeat0Q (R + 2) (dePushZeroRegQ R wMul wAdd))
    (deSum (deGrowOutBufQ R)
      (deSum (deRepeat0Q 3 (dePushZeroRegQ R wMul wAdd))
        (deComputeSegWQ R)))

private abbrev ftInitWSQ (R wMul wAdd K_L d_L : ℕ) : Fintype (InitWSQ R wMul wAdd K_L d_L) :=
  ftSum (ftInitWSPrefixQ R wMul wAdd K_L d_L) (ftInitWSSuffixQ R wMul wAdd)

private def deInitWSQ (R wMul wAdd K_L d_L : ℕ) : DecidableEq (InitWSQ R wMul wAdd K_L d_L) :=
  deSum (deInitWSPrefixQ R wMul wAdd K_L d_L) (deInitWSSuffixQ R wMul wAdd)

private abbrev ftShuttleDecWriteQ (MaxSeg : ℕ) : Fintype (ShuttleDecWriteQ MaxSeg) := by
  unfold ShuttleDecWriteQ
  infer_instance

private def deShuttleDecWriteQ (MaxSeg : ℕ) : DecidableEq (ShuttleDecWriteQ MaxSeg) := by
  unfold ShuttleDecWriteQ
  infer_instance

private abbrev ftShuttlePad6Q (MaxSeg : ℕ) : Fintype (ShuttlePad6Q MaxSeg) :=
  let h := ftShuttleDecWriteQ MaxSeg
  ftSum h (ftSum h (ftSum h (ftSum h (ftSum h h))))

private def deShuttlePad6Q (MaxSeg : ℕ) : DecidableEq (ShuttlePad6Q MaxSeg) :=
  let h := deShuttleDecWriteQ MaxSeg
  deSum h (deSum h (deSum h (deSum h (deSum h h))))

private abbrev ftPadAdd6LoopQ (MaxSeg : ℕ) : Fintype (PadAdd6LoopQ MaxSeg) := by
  unfold PadAdd6LoopQ Repeat0Q
  infer_instance

private def dePadAdd6LoopQ (MaxSeg : ℕ) : DecidableEq (PadAdd6LoopQ MaxSeg) := by
  unfold PadAdd6LoopQ Repeat0Q
  infer_instance

private abbrev ftShuttlePadLoopQ (MaxSeg : ℕ) : Fintype (ShuttlePadLoopQ MaxSeg) :=
  ftSum inferInstance (ftSum inferInstance (ftShuttlePad6Q MaxSeg))

private def deShuttlePadLoopQ (MaxSeg : ℕ) : DecidableEq (ShuttlePadLoopQ MaxSeg) :=
  deSum inferInstance (deSum inferInstance (deShuttlePad6Q MaxSeg))

private abbrev ftShuttlePadTailQ (base R : ℕ) : Fintype (ShuttlePadTailQ base R) :=
  ftSum inferInstance
    (ftSum inferInstance
      (ftSum (ftPadAdd6LoopQ (base + R + 5)) (ftShuttlePadLoopQ (base + R + 5))))

private def deShuttlePadTailQ (base R : ℕ) : DecidableEq (ShuttlePadTailQ base R) :=
  deSum inferInstance
    (deSum inferInstance
      (deSum (dePadAdd6LoopQ (base + R + 5)) (deShuttlePadLoopQ (base + R + 5))))

private abbrev ftExecRMOutPaddedQ (base R : ℕ) (Q : Type) [Fintype Q] :
    Fintype (ExecRMOutPaddedQ base R Q) :=
  ftSum inferInstance (ftSum (ftShuttlePadTailQ base R) inferInstance)

private def deExecRMOutPaddedQ (base R : ℕ) (Q : Type) [DecidableEq Q] :
    DecidableEq (ExecRMOutPaddedQ base R Q) :=
  deSum inferInstance (deSum (deShuttlePadTailQ base R) inferInstance)

private abbrev ftCompileQ (R wMul wAdd K_L d_L : ℕ) (Q : Type) [Fintype Q] :
    Fintype (InitWSQ R wMul wAdd K_L d_L ⊕ ExecRMOutPaddedQ 8 R Q) :=
  ftSum (ftInitWSQ R wMul wAdd K_L d_L) (ftExecRMOutPaddedQ 8 R Q)

private def deCompileQ (R wMul wAdd K_L d_L : ℕ) (Q : Type) [DecidableEq Q] :
    DecidableEq (InitWSQ R wMul wAdd K_L d_L ⊕ ExecRMOutPaddedQ 8 R Q) :=
  deSum (deInitWSQ R wMul wAdd K_L d_L) (deExecRMOutPaddedQ 8 R Q)

/-! ### Compact Register Width (`O(n)` bits, logarithmic in `K_V, K_L, R`) and Polynomial Space/Time Bridges -/

def chosenWMul (d_V d_L : ℕ) : ℕ := max (max d_V d_L) 1

def chosenWAdd (R K_V d_V K_L d_L : ℕ) : ℕ :=
  let D := chosenWMul d_V d_L
  let a := Nat.log 2 (R + 20) + 6
  max (Nat.log 2 (K_V + 1) + 1) (Nat.log 2 (K_L + 1) + 8) + 2 * D + 2 * a + 10

private lemma two_mul_lt_two_pow (u : ℕ) (hu : 3 ≤ u) : 2 * u < 2 ^ u := by
  induction u with
  | zero => omega
  | succ u ih =>
    by_cases hu3 : 3 ≤ u
    · have hih := ih hu3
      have hge8 : 8 ≤ 2 ^ u := by
        calc 8 = 2 ^ 3 := by decide
          _ ≤ 2 ^ u := Nat.pow_le_pow_right (by decide) hu3
      rw [Nat.pow_succ]
      omega
    · have hu2 : u = 2 := by omega
      subst hu2; decide

private lemma add_two_pow_le_two_pow (d n : ℕ) : (n + 2) ^ d ≤ 2 ^ (d * (n + 2)) := by
  calc (n + 2) ^ d ≤ (2 ^ (n + 2)) ^ d :=
        Nat.pow_le_pow_left (Nat.le_of_lt (nat_lt_two_pow_self (n + 2))) d
    _ = 2 ^ ((n + 2) * d) := (Nat.pow_mul 2 (n + 2) d).symm
    _ = 2 ^ (d * (n + 2)) := by rw [Nat.mul_comm]

private lemma K_mul_pow_lt_two_pow (K d n : ℕ) :
    K * (n + 2) ^ d < 2 ^ (Nat.log 2 (K + 1) + 1 + d * (n + 2)) := by
  have hK : K < 2 ^ (Nat.log 2 (K + 1) + 1) :=
    Nat.lt_trans (Nat.lt_succ_self K) (lt_two_pow_log_succ (K + 1))
  have hpos : 0 < 2 ^ (d * (n + 2)) := Nat.pos_of_ne_zero (by positivity)
  calc K * (n + 2) ^ d
      ≤ K * 2 ^ (d * (n + 2)) := Nat.mul_le_mul_left K (add_two_pow_le_two_pow d n)
    _ < 2 ^ (Nat.log 2 (K + 1) + 1) * 2 ^ (d * (n + 2)) := Nat.mul_lt_mul_of_pos_right hK hpos
    _ = 2 ^ (Nat.log 2 (K + 1) + 1 + d * (n + 2)) := (Nat.pow_add 2 _ _).symm

private lemma initMblk_le_poly (R K_V d_V K_L d_L n : ℕ) :
    let wMul := chosenWMul d_V d_L
    let wAdd := chosenWAdd R K_V d_V K_L d_L
    let C_M := (R + 110) + (R + 10) * (wMul + wAdd) + K_L
    initMblk R wMul wAdd K_L d_L n ≤ C_M * (n + 2) ^ wMul := by
  intro wMul wAdd C_M
  unfold initMblk
  dsimp only
  have hD1 : 1 ≤ wMul := le_max_right _ _
  have hdL : d_L ≤ wMul := le_trans (le_max_right d_V d_L) (le_max_left _ _)
  have hn2_ge1 : 1 ≤ n + 2 := by omega
  have h1_le_pow : 1 ≤ (n + 2) ^ wMul := Nat.one_le_pow _ _ hn2_ge1
  have hn2_le_pow : n + 2 ≤ (n + 2) ^ wMul := by
    calc n + 2 = (n + 2) ^ 1 := (Nat.pow_one _).symm
      _ ≤ (n + 2) ^ wMul := Nat.pow_le_pow_right hn2_ge1 hD1
  have hw_le : (n - 2) / 2 * 2 ≤ n := by omega
  have hif_le : (if decide ((n - 2) % 2 = 1) then 0 else 1) ≤ 1 := by split_ifs <;> omega
  have hlin1 : (8 + R + 7) + (18 * ((n - 2) / 2) + 31) + n +
      (n + (if decide ((n - 2) % 2 = 1) then 0 else 1) + 18 * ((n - 2) / 2) + 31) ≤ (R + 110) * (n + 2) ^ wMul := by
    have ha : (8 + R + 7) + (18 * ((n - 2) / 2) + 31) + n +
        (n + (if decide ((n - 2) % 2 = 1) then 0 else 1) + 18 * ((n - 2) / 2) + 31) ≤ (R + 110) * (n + 2) := by
      have : R * 1 ≤ R * (n + 2) := Nat.mul_le_mul_left R (by omega)
      have hexp : (R + 110) * (n + 2) = R * (n + 2) + 110 * (n + 2) := by ring
      omega
    exact le_trans ha (Nat.mul_le_mul_left _ hn2_le_pow)
  have hlin2 : (R + 10) * (wMul * n + wAdd) ≤ (R + 10) * (wMul + wAdd) * (n + 2) ^ wMul := by
    have ha : wMul * n + wAdd ≤ (wMul + wAdd) * (n + 2) := by
      have h1 : wMul * n ≤ wMul * (n + 2) := Nat.mul_le_mul_left _ (by omega)
      have h2 : wAdd ≤ wAdd * (n + 2) := Nat.le_mul_of_pos_right _ (by omega)
      have hexp : (wMul + wAdd) * (n + 2) = wMul * (n + 2) + wAdd * (n + 2) := by ring
      omega
    calc (R + 10) * (wMul * n + wAdd)
        ≤ (R + 10) * ((wMul + wAdd) * (n + 2)) := Nat.mul_le_mul_left _ ha
      _ = (R + 10) * (wMul + wAdd) * (n + 2) := by ring
      _ ≤ (R + 10) * (wMul + wAdd) * (n + 2) ^ wMul := Nat.mul_le_mul_left _ hn2_le_pow
  have hlin3 : K_L * (n + 2) ^ d_L ≤ K_L * (n + 2) ^ wMul :=
    Nat.mul_le_mul_left K_L (Nat.pow_le_pow_right hn2_ge1 hdL)
  have hexp : C_M * (n + 2) ^ wMul =
      (R + 110) * (n + 2) ^ wMul + (R + 10) * (wMul + wAdd) * (n + 2) ^ wMul + K_L * (n + 2) ^ wMul := by
    dsimp only [C_M]; ring
  omega

private lemma chosenW_P_core (R n w_reg L_buf M_blk a K_L d_L : ℕ)
    (hw_ge22 : 22 ≤ w_reg)
    (hL_def : L_buf = K_L * (n + 2) ^ d_L)
    (ha_def : a = Nat.log 2 (R + 20) + 6)
    (hM_split : L_buf + 18 * M_blk ≤ 19 * L_buf + 18 * (R + 10) * w_reg + 18 * (R + 20 * n + 100))
    (hexp1 : 5 + (Nat.log 2 (K_L + 1) + 1 + d_L * (n + 2)) ≤ w_reg - 2)
    (ha_le : 2 * a + 7 ≤ w_reg)
    (hexp3 : a + (n + 8) ≤ w_reg - 2) :
    L_buf + 18 * M_blk < 2 ^ w_reg := by
  have h4pow : 2 ^ w_reg = 4 * 2 ^ (w_reg - 2) := by
    have h1 : 2 ^ w_reg = 2 ^ (2 + (w_reg - 2)) := by congr 1; omega
    rw [h1, Nat.pow_add]
  -- Piece 1: `19 * L_buf < 2 ^ (w_reg - 2)`
  have hp1 : 19 * L_buf < 2 ^ (w_reg - 2) := by
    have hL1 : L_buf < 2 ^ (Nat.log 2 (K_L + 1) + 1 + d_L * (n + 2)) := by
      rw [hL_def]; exact K_mul_pow_lt_two_pow K_L d_L n
    have h19 : 19 * L_buf < 2 ^ 5 * 2 ^ (Nat.log 2 (K_L + 1) + 1 + d_L * (n + 2)) := by
      calc 19 * L_buf ≤ 2 ^ 5 * L_buf := Nat.mul_le_mul_right L_buf (by omega)
        _ < 2 ^ 5 * 2 ^ (Nat.log 2 (K_L + 1) + 1 + d_L * (n + 2)) :=
          Nat.mul_lt_mul_of_pos_left hL1 (by omega)
    rw [← Nat.pow_add] at h19
    exact Nat.lt_of_lt_of_le h19 (Nat.pow_le_pow_right (by omega) hexp1)
  -- Piece 2: `18 * (R + 10) * w_reg < 2 ^ (w_reg - 2)`
  have h18R : 18 * (R + 20) < 2 ^ a := by
    have hlogR := lt_two_pow_log_succ (R + 20)
    calc 18 * (R + 20) ≤ 2 ^ 5 * (R + 20) := Nat.mul_le_mul_right _ (by omega)
      _ < 2 ^ 5 * 2 ^ (Nat.log 2 (R + 20) + 1) := Nat.mul_lt_mul_of_pos_left hlogR (by omega)
      _ = 2 ^ (5 + (Nat.log 2 (R + 20) + 1)) := (Nat.pow_add 2 _ _).symm
      _ = 2 ^ a := by congr 1; omega
  have hp2 : 18 * (R + 10) * w_reg < 2 ^ (w_reg - 2) := by
    have hu3 : 3 ≤ w_reg - a - 2 := by omega
    have hw_lt_2u : w_reg ≤ 2 * (w_reg - a - 2) := by omega
    have hw_lt_pow : w_reg < 2 ^ (w_reg - a - 2) :=
      Nat.lt_of_le_of_lt hw_lt_2u (two_mul_lt_two_pow (w_reg - a - 2) hu3)
    have h18_lt : 18 * (R + 10) < 2 ^ a := Nat.lt_of_le_of_lt (by omega) h18R
    calc 18 * (R + 10) * w_reg
        < 2 ^ a * w_reg := Nat.mul_lt_mul_of_pos_right h18_lt (by omega)
      _ < 2 ^ a * 2 ^ (w_reg - a - 2) :=
        Nat.mul_lt_mul_of_pos_left hw_lt_pow (Nat.pow_pos (by omega : 0 < 2))
      _ = 2 ^ (a + (w_reg - a - 2)) := (Nat.pow_add 2 a (w_reg - a - 2)).symm
      _ = 2 ^ (w_reg - 2) := by congr 1; omega
  -- Piece 3: `18 * (R + 20 * n + 100) < 2 ^ (w_reg - 2)`
  have hp3 : 18 * (R + 20 * n + 100) < 2 ^ (w_reg - 2) := by
    have hadd_mul : R + 20 * n + 100 ≤ (R + 20) * (20 * n + 100) := by
      have h1 : R * 1 ≤ R * (20 * n + 100) := Nat.mul_le_mul_left R (by omega)
      have hexp : (R + 20) * (20 * n + 100) = R * (20 * n + 100) + 20 * (20 * n + 100) := by ring
      omega
    have h20n : 20 * n + 100 < 2 ^ (n + 8) := by
      have hn1 : n + 2 ≤ 2 ^ (n + 1) := by
        have := nat_lt_two_pow_self (n + 1)
        omega
      calc 20 * n + 100 ≤ 100 * (n + 2) := by omega
        _ < 2 ^ 7 * (n + 2) := by omega
        _ ≤ 2 ^ 7 * 2 ^ (n + 1) := Nat.mul_le_mul_left (2 ^ 7) hn1
        _ = 2 ^ (7 + (n + 1)) := (Nat.pow_add 2 7 (n + 1)).symm
        _ = 2 ^ (n + 8) := by congr 1; omega
    calc 18 * (R + 20 * n + 100)
        ≤ 18 * ((R + 20) * (20 * n + 100)) := Nat.mul_le_mul_left 18 hadd_mul
      _ = (18 * (R + 20)) * (20 * n + 100) := by ring
      _ < 2 ^ a * 2 ^ (n + 8) := Nat.mul_lt_mul'' h18R h20n
      _ = 2 ^ (a + (n + 8)) := (Nat.pow_add 2 a (n + 8)).symm
      _ ≤ 2 ^ (w_reg - 2) := Nat.pow_le_pow_right (by omega) hexp3
  omega

private lemma chosenW_bounds (R K_V d_V K_L d_L n : ℕ) (hn : 2 ≤ n) :
    let wMul := chosenWMul d_V d_L
    let wAdd := chosenWAdd R K_V d_V K_L d_L
    let w_reg := wMul * n + wAdd
    let L_buf := K_L * (n + 2) ^ d_L
    let M_blk := initMblk R wMul wAdd K_L d_L n
    Nat.log 2 K_L + 1 ≤ w_reg ∧
    n + 2 < 2 ^ w_reg ∧
    K_V * (n + 2) ^ d_V < 2 ^ w_reg ∧
    L_buf + 18 * M_blk < 2 ^ w_reg := by
  intro wMul wAdd w_reg L_buf M_blk
  have hD1 : 1 ≤ wMul := le_max_right _ _
  have hdV : d_V ≤ wMul := le_trans (le_max_left d_V d_L) (le_max_left _ _)
  have hdL : d_L ≤ wMul := le_trans (le_max_right d_V d_L) (le_max_left _ _)
  have hwAdd_def : wAdd = max (Nat.log 2 (K_V + 1) + 1) (Nat.log 2 (K_L + 1) + 8) + 2 * wMul +
      2 * (Nat.log 2 (R + 20) + 6) + 10 := rfl
  have hw_def : w_reg = wMul * n + wAdd := rfl
  have hlogK_le : Nat.log 2 K_L + 1 ≤ w_reg := by
    have h1 : Nat.log 2 K_L ≤ Nat.log 2 (K_L + 1) := Nat.log_mono_right (by omega)
    have h2 : Nat.log 2 (K_L + 1) + 8 ≤ max (Nat.log 2 (K_V + 1) + 1) (Nat.log 2 (K_L + 1) + 8) :=
      le_max_right _ _
    omega
  have hn2_lt : n + 2 < 2 ^ w_reg := by
    have h1 : 1 * n ≤ wMul * n := Nat.mul_le_mul_right n hD1
    exact Nat.lt_of_le_of_lt (by omega) (nat_lt_two_pow_self w_reg)
  have hV_lt : K_V * (n + 2) ^ d_V < 2 ^ w_reg := by
    have h1 := K_mul_pow_lt_two_pow K_V d_V n
    have hexp : Nat.log 2 (K_V + 1) + 1 + d_V * (n + 2) ≤ w_reg := by
      have hmax := le_max_left (Nat.log 2 (K_V + 1) + 1) (Nat.log 2 (K_L + 1) + 8)
      have hdn : d_V * n ≤ wMul * n := Nat.mul_le_mul_right n hdV
      have hmul : d_V * (n + 2) = d_V * n + 2 * d_V := by ring
      omega
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) hexp)
  have hM_split : L_buf + 18 * M_blk ≤ 19 * L_buf + 18 * (R + 10) * w_reg + 18 * (R + 20 * n + 100) := by
    have hif : (if decide ((n - 2) % 2 = 1) then 0 else 1) ≤ 1 := by split_ifs <;> omega
    have hdiv : 2 * ((n - 2) / 2) ≤ n := by omega
    have hmul_assoc : 18 * ((R + 10) * w_reg) = 18 * (R + 10) * w_reg := by ring
    have hM_eq : M_blk = (8 + R + 7) + (18 * ((n - 2) / 2) + 31) + n +
        (n + (if decide ((n - 2) % 2 = 1) then 0 else 1) + 18 * ((n - 2) / 2) + 31) +
        (R + 10) * w_reg + L_buf := rfl
    omega
  have hexp1 : 5 + (Nat.log 2 (K_L + 1) + 1 + d_L * (n + 2)) ≤ w_reg - 2 := by
    have hmax := le_max_right (Nat.log 2 (K_V + 1) + 1) (Nat.log 2 (K_L + 1) + 8)
    have hdn : d_L * n ≤ wMul * n := Nat.mul_le_mul_right n hdL
    have hmul : d_L * (n + 2) = d_L * n + 2 * d_L := by ring
    omega
  have hexp3 : (Nat.log 2 (R + 20) + 6) + (n + 8) ≤ w_reg - 2 := by
    have : 1 * n ≤ wMul * n := Nat.mul_le_mul_right n hD1
    omega
  have hP_lt : L_buf + 18 * M_blk < 2 ^ w_reg :=
    chosenW_P_core R n w_reg L_buf M_blk (Nat.log 2 (R + 20) + 6) K_L d_L
      (by omega) rfl rfl hM_split hexp1 (by omega) hexp3
  exact ⟨hlogK_le, hn2_lt, hV_lt, hP_lt⟩

theorem poly_le_spaceBound (K d : ℕ) :
    ∃ kst : ℕ, ∀ n : ℕ, 2 ≤ n → K * (n + 2) ^ d ≤ QCSD_spaceBound kst n := by
  refine ⟨Nat.log 2 (K + 1) + 1 + 2 * d, fun n hn => ?_⟩
  unfold QCSD_spaceBound
  have hK : K ≤ n ^ (Nat.log 2 (K + 1) + 1) := by
    calc K ≤ 2 ^ (Nat.log 2 (K + 1) + 1) :=
          Nat.le_of_lt (Nat.lt_trans (Nat.lt_succ_self K) (lt_two_pow_log_succ (K + 1)))
      _ ≤ n ^ (Nat.log 2 (K + 1) + 1) := Nat.pow_le_pow_left hn _
  have hn2 : n + 2 ≤ n ^ 2 := by nlinarith
  have hpow : (n + 2) ^ d ≤ n ^ (2 * d) := by
    calc (n + 2) ^ d ≤ (n ^ 2) ^ d := Nat.pow_le_pow_left hn2 d
      _ = n ^ (2 * d) := (Nat.pow_mul n 2 d).symm
  calc K * (n + 2) ^ d
      ≤ n ^ (Nat.log 2 (K + 1) + 1) * n ^ (2 * d) := Nat.mul_le_mul hK hpow
    _ = n ^ (Nat.log 2 (K + 1) + 1 + 2 * d) := (Nat.pow_add n _ _).symm

private lemma hmul_le_X2 (a b X : ℕ) {u v : ℕ} (hu : u ≤ a * X) (hv : v ≤ b * X) :
    u * v ≤ (a * b) * X ^ 2 := by
  calc u * v ≤ (a * X) * (b * X) := Nat.mul_le_mul hu hv
    _ = (a * b) * X ^ 2 := by ring

private lemma hmul_le_X3 (a b X : ℕ) {u v : ℕ} (hu : u ≤ a * X) (hv : v ≤ b * X ^ 2) :
    u * v ≤ (a * b) * X ^ 3 := by
  calc u * v ≤ (a * X) * (b * X ^ 2) := Nat.mul_le_mul hu hv
    _ = (a * b) * X ^ 3 := by ring

private lemma hmul_le_X4 (a b X : ℕ) {u v : ℕ} (hu : u ≤ a * X) (hv : v ≤ b * X ^ 3) :
    u * v ≤ (a * b) * X ^ 4 := by
  calc u * v ≤ (a * X) * (b * X ^ 3) := Nat.mul_le_mul hu hv
    _ = (a * b) * X ^ 4 := by ring

private lemma hX2_le_X4_mul (c X : ℕ) (hX : 1 ≤ X) : c * X ^ 2 ≤ c * X ^ 4 := by
  have h1 : X ^ 2 ≤ X ^ 4 := by
    calc X ^ 2 = X ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ X ^ 2 * X ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_pow 2 X hX)
      _ = X ^ 4 := by ring
  exact Nat.mul_le_mul_left c h1

private lemma hX3_le_X4_mul (c X : ℕ) (hX : 1 ≤ X) : c * X ^ 3 ≤ c * X ^ 4 := by
  have h1 : X ^ 3 ≤ X ^ 4 := by
    calc X ^ 3 = X ^ 3 * 1 := (Nat.mul_one _).symm
      _ ≤ X ^ 3 * X := Nat.mul_le_mul_left _ hX
      _ = X ^ 4 := by ring
  exact Nat.mul_le_mul_left c h1

private lemma totalTime_core_le (R wMul wAdd d_L n Vmax L_buf M_blk steps X : ℕ)
    (hX40 : 40 ≤ X)
    (hn5 : n + 5 ≤ X)
    (hV : Vmax ≤ X)
    (hL : L_buf ≤ X)
    (hM : M_blk ≤ X)
    (hT : steps ≤ X)
    (hwn1 : wMul * (n + 1) ≤ X)
    (hR : R ≤ X)
    (hwAdd : wAdd ≤ X)
    (hdL : d_L ≤ X) :
    initWSTimeBound R wMul wAdd d_L n L_buf M_blk +
      execRMPaddedTimeBound steps Vmax L_buf M_blk + 3 ≤
    300000 * X ^ 4 := by
  have hX1 : 1 ≤ X := by omega
  have h1_X2 : 1 ≤ X ^ 2 := Nat.one_le_pow 2 X hX1
  have hX_X4 : X ≤ X ^ 4 := by
    calc X = X ^ 1 := (Nat.pow_one X).symm
      _ ≤ X ^ 4 := Nat.pow_le_pow_right hX1 (by omega)
  have ht1 : 30000 * (n + 2) ^ 2 ≤ 30000 * X ^ 4 :=
    le_trans (Nat.mul_le_mul_left 30000 (Nat.pow_le_pow_left (by omega) 2)) (hX2_le_X4_mul 30000 X hX1)
  have ht2 : (n + 5) * (50 * M_blk + 40) ≤ 90 * X ^ 4 :=
    le_trans (hmul_le_X2 1 90 X (by omega) (by omega)) (hX2_le_X4_mul 90 X hX1)
  have ht3 : (n + M_blk + 4) * (40 * M_blk + 40) ≤ 240 * X ^ 4 :=
    le_trans (hmul_le_X2 3 80 X (by omega) (by omega)) (hX2_le_X4_mul 240 X hX1)
  have ht4 : (R + 10) * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) ≤ 500 * X ^ 4 := by
    have h1 : (wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) ≤ 240 * X ^ 2 :=
      hmul_le_X2 3 80 X (by omega) (by omega)
    have h_in : (wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2 ≤ 242 * X ^ 2 := by
      linarith only [h1, h1_X2]
    have h2 : (R + 10) * ((wMul * (n + 1) + wAdd + 2) * (40 * M_blk + 40) + 2) ≤ 484 * X ^ 3 :=
      hmul_le_X3 2 242 X (by omega) h_in
    exact le_trans h2 (le_trans (hX3_le_X4_mul 484 X hX1) (Nat.mul_le_mul_right (X ^ 4) (by omega)))
  have ht5 : (d_L + 2) * ((L_buf + 2) * ((n + 5) * (500 * M_blk + 250))) ≤ 3000 * X ^ 4 := by
    have h_in : (n + 5) * (500 * M_blk + 250) ≤ 750 * X ^ 2 :=
      hmul_le_X2 1 750 X (by omega) (by omega)
    have h_mid : (L_buf + 2) * ((n + 5) * (500 * M_blk + 250)) ≤ 1500 * X ^ 3 :=
      hmul_le_X3 2 750 X (by omega) h_in
    exact hmul_le_X4 2 1500 X (by omega) h_mid
  have ht6 : (L_buf + 2) * (60 * M_blk + 40) ≤ 200 * X ^ 4 :=
    le_trans (hmul_le_X2 2 100 X (by omega) (by omega)) (hX2_le_X4_mul 200 X hX1)
  have ht7 : (R + 20) * ((M_blk + 1) * (100 * M_blk + 60)) ≤ 960 * X ^ 4 := by
    have h_in : (M_blk + 1) * (100 * M_blk + 60) ≤ 320 * X ^ 2 :=
      hmul_le_X2 2 160 X (by omega) (by omega)
    exact le_trans (hmul_le_X3 3 320 X (by omega) h_in) (hX3_le_X4_mul 960 X hX1)
  have ht8 : (steps + 1) * ((max Vmax L_buf + 2) * (250 * M_blk + 100) + 2) ≤ 2200 * X ^ 4 := by
    have h1 : (max Vmax L_buf + 2) * (250 * M_blk + 100) ≤ 1050 * X ^ 2 :=
      hmul_le_X2 3 350 X (by omega) (by omega)
    have h_in : (max Vmax L_buf + 2) * (250 * M_blk + 100) + 2 ≤ 1060 * X ^ 2 := by
      linarith only [h1, h1_X2]
    have h2 : (steps + 1) * ((max Vmax L_buf + 2) * (250 * M_blk + 100) + 2) ≤ 2120 * X ^ 3 :=
      hmul_le_X3 2 1060 X (by omega) h_in
    exact le_trans h2 (le_trans (hX3_le_X4_mul 2120 X hX1) (Nat.mul_le_mul_right (X ^ 4) (by omega)))
  have ht9 : shuttlePadTailTimeBound L_buf M_blk ≤ 200000 * X ^ 4 := by
    unfold shuttlePadTailTimeBound
    dsimp only
    have hP1 : (L_buf + 18 * M_blk + 8) * (250 * M_blk + 2 * (L_buf + 18 * M_blk + 8) + 100) ≤ 7800 * X ^ 2 :=
      hmul_le_X2 20 390 X (by omega) (by omega)
    have hM_X2 : 450 * M_blk + 200 ≤ 500 * X ^ 2 := by
      have hM1 : 450 * M_blk + 200 ≤ 500 * X := by omega
      have hX_X2 : X ≤ X ^ 2 := by
        calc X = X ^ 1 := (Nat.pow_one X).symm
          _ ≤ X ^ 2 := Nat.pow_le_pow_right hX1 (by omega)
      exact le_trans hM1 (Nat.mul_le_mul_left 500 hX_X2)
    have hP_in : 6 * ((L_buf + 18 * M_blk + 8) * (250 * M_blk + 2 * (L_buf + 18 * M_blk + 8) + 100)) +
        450 * M_blk + 200 ≤ 48000 * X ^ 2 := by
      linarith only [hP1, hM_X2]
    have h1 : (3 * M_blk + 5) * (6 * ((L_buf + 18 * M_blk + 8) * (250 * M_blk + 2 * (L_buf + 18 * M_blk + 8) + 100)) +
        450 * M_blk + 200) ≤ 192000 * X ^ 4 :=
      le_trans (hmul_le_X3 4 48000 X (by omega) hP_in) (hX3_le_X4_mul 192000 X hX1)
    have h2 : (L_buf + 2) * (150 * M_blk + 50) ≤ 400 * X ^ 4 :=
      le_trans (hmul_le_X2 2 200 X (by omega) (by omega)) (hX2_le_X4_mul 400 X hX1)
    exact le_trans (Nat.add_le_add h1 h2) (by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right (X ^ 4) (by decide))
  have ht10 : (L_buf + 1) * ((L_buf + 2) * (450 * M_blk + 2 * L_buf + 200) + 2) ≤ 3000 * X ^ 4 := by
    have h1 : (L_buf + 2) * (450 * M_blk + 2 * L_buf + 200) ≤ 1304 * X ^ 2 :=
      hmul_le_X2 2 652 X (by omega) (by omega)
    have h_in : (L_buf + 2) * (450 * M_blk + 2 * L_buf + 200) + 2 ≤ 1400 * X ^ 2 := by
      linarith only [h1, h1_X2]
    have h2 : (L_buf + 1) * ((L_buf + 2) * (450 * M_blk + 2 * L_buf + 200) + 2) ≤ 2800 * X ^ 3 :=
      hmul_le_X3 2 1400 X (by omega) h_in
    exact le_trans h2 (le_trans (hX3_le_X4_mul 2800 X hX1) (Nat.mul_le_mul_right (X ^ 4) (by omega)))
  have ht11 : 14 * M_blk + 53 ≤ 100 * X ^ 4 := by
    have : 14 * M_blk + 53 ≤ 100 * X := by omega
    exact le_trans this (Nat.mul_le_mul_left 100 hX_X4)
  have h1_X4 : 1 ≤ X ^ 4 := le_trans hX1 hX_X4
  unfold initWSTimeBound execRMPaddedTimeBound
  linarith only [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11, h1_X4]

private lemma totalTime_le_poly (R K_V d_V K_L d_L K_T d_T n : ℕ) (hn : 2 ≤ n) :
    let wMul := chosenWMul d_V d_L
    let wAdd := chosenWAdd R K_V d_V K_L d_L
    let C_M := (R + 110) + (R + 10) * (wMul + wAdd) + K_L
    let E := max wMul (max d_T 1)
    let A := max (max K_V K_L) (max C_M K_T) + R + wMul + wAdd + d_L + 10
    let Vmax := K_V * (n + 2) ^ d_V
    let L_buf := K_L * (n + 2) ^ d_L
    let M_blk := initMblk R wMul wAdd K_L d_L n
    let steps := K_T * (n + 2) ^ d_T
    initWSTimeBound R wMul wAdd d_L n L_buf M_blk +
      execRMPaddedTimeBound steps Vmax L_buf M_blk + 3 ≤
    (300000 * A ^ 4) * (n + 2) ^ (4 * E) := by
  intro wMul wAdd C_M E A Vmax L_buf M_blk steps
  have hE1 : 1 ≤ E := le_trans (le_max_right d_T 1) (le_max_right _ _)
  have hED : wMul ≤ E := le_max_left _ _
  have hEdV : d_V ≤ E := le_trans (le_trans (le_max_left d_V d_L) (le_max_left _ _)) hED
  have hEdL : d_L ≤ E := le_trans (le_trans (le_max_right d_V d_L) (le_max_left _ _)) hED
  have hEdT : d_T ≤ E := le_trans (le_max_left d_T 1) (le_max_right _ _)
  have hn2_le_U : n + 2 ≤ (n + 2) ^ E := by
    calc n + 2 = (n + 2) ^ 1 := (Nat.pow_one _).symm
      _ ≤ (n + 2) ^ E := Nat.pow_le_pow_right (by omega) hE1
  have hU_ge4 : 4 ≤ (n + 2) ^ E := le_trans (by omega) hn2_le_U
  have hA_def : A = max (max K_V K_L) (max C_M K_T) + R + wMul + wAdd + d_L + 10 := rfl
  have hA_ge10 : 10 ≤ A := by omega
  have hX_ge40 : 40 ≤ A * (n + 2) ^ E := le_trans (by decide : 40 ≤ 10 * 4) (Nat.mul_le_mul hA_ge10 hU_ge4)
  have hA_le_X : A ≤ A * (n + 2) ^ E := Nat.le_mul_of_pos_right A (by omega)
  have hmax_le_A : max (max K_V K_L) (max C_M K_T) ≤ A := by omega
  have hKV_le_A : K_V ≤ A := le_trans (le_trans (le_max_left K_V K_L) (le_max_left _ _)) hmax_le_A
  have hKL_le_A : K_L ≤ A := le_trans (le_trans (le_max_right K_V K_L) (le_max_left _ _)) hmax_le_A
  have hCM_le_A : C_M ≤ A := le_trans (le_trans (le_max_left C_M K_T) (le_max_right _ _)) hmax_le_A
  have hKT_le_A : K_T ≤ A := le_trans (le_trans (le_max_right C_M K_T) (le_max_right _ _)) hmax_le_A
  have hV_le_X : Vmax ≤ A * (n + 2) ^ E :=
    Nat.mul_le_mul hKV_le_A (Nat.pow_le_pow_right (by omega) hEdV)
  have hL_le_X : L_buf ≤ A * (n + 2) ^ E :=
    Nat.mul_le_mul hKL_le_A (Nat.pow_le_pow_right (by omega) hEdL)
  have hM_le_X : M_blk ≤ A * (n + 2) ^ E :=
    le_trans (initMblk_le_poly R K_V d_V K_L d_L n)
      (Nat.mul_le_mul hCM_le_A (Nat.pow_le_pow_right (by omega) hED))
  have hT_le_X : steps ≤ A * (n + 2) ^ E :=
    Nat.mul_le_mul hKT_le_A (Nat.pow_le_pow_right (by omega) hEdT)
  have hn5_le_X : n + 5 ≤ A * (n + 2) ^ E := by
    calc n + 5 ≤ 2 * (n + 2) := by omega
      _ ≤ A * (n + 2) ^ E := Nat.mul_le_mul (by omega) hn2_le_U
  have hwMul_n1 : wMul * (n + 1) ≤ A * (n + 2) ^ E :=
    Nat.mul_le_mul (by omega) (le_trans (by omega) hn2_le_U)
  have hR_le_X : R ≤ A * (n + 2) ^ E := le_trans (by omega) hA_le_X
  have hwAdd_le_X : wAdd ≤ A * (n + 2) ^ E := le_trans (by omega) hA_le_X
  have hdL_le_X : d_L ≤ A * (n + 2) ^ E := le_trans (by omega) hA_le_X
  have hcore := totalTime_core_le R wMul wAdd d_L n Vmax L_buf M_blk steps (A * (n + 2) ^ E)
    hX_ge40 hn5_le_X hV_le_X hL_le_X hM_le_X hT_le_X hwMul_n1 hR_le_X hwAdd_le_X hdL_le_X
  have hX4_eq : (A * (n + 2) ^ E) ^ 4 = A ^ 4 * (n + 2) ^ (4 * E) := by
    rw [mul_pow, ← Nat.pow_mul, Nat.mul_comm E 4]
  rw [hX4_eq, ← Nat.mul_assoc] at hcore
  exact hcore

/-! ### Master Compiler Theorem (`compileRMProg_unaryPrefix_spec`) + Standard & Separated Exports -/

def compileRMProgPadded (R wMul wAdd K_L d_L : ℕ) {Q : Type} [Fintype Q] [DecidableEq Q]
    (M : RMProg R Q) (q₀ : Q) : QCSD_DetTM :=
  @toDetTM _ (ftCompileQ R wMul wAdd K_L d_L Q) (deCompileQ R wMul wAdd K_L d_L Q)
    (Sum.inl (initWSProgEntry R wMul wAdd K_L d_L))
    (seq0 (initWSProg R wMul wAdd K_L d_L) (execRMToOutputPadded 8 R 2 M)
      (fun _ => execRMToOutputPaddedEntry 8 R 2 M q₀))

theorem compileRMProg_unaryPrefix_spec (R : ℕ) {Q : Type} [Fintype Q] [DecidableEq Q]
    (M : RMProg R Q) (q₀ : Q) (K_V d_V K_L d_L K_T d_T : ℕ) :
    ∃ (M_tm : QCSD_DetTM) (Ctm : ℝ) (kst C_W d_W : ℕ) (padW : ℕ → ℕ),
      0 ≤ Ctm ∧
      (∀ n : ℕ, 2 ≤ n → padW n ≤ C_W * (n + 1) ^ d_W) ∧
      (∀ (n : ℕ) (rest : List Bool) (q₁ : Q) (reg₁ : RegState R) (emitted : List Bool),
        2 ≤ n →
        (QCSD_natToUnary n ++ rest).length ≤ 9 * n + 4 →
        RMExec M (K_V * (n + 2) ^ d_V) (QCSD_natToUnary n ++ rest) q₀ (fun _ => 0) q₁ reg₁
          emitted (K_T * (n + 2) ^ d_T) →
        emitted.length ≤ K_L * (n + 2) ^ d_L →
        ∃ k ≤ QCSD_timeBound Ctm n,
          (QCSD_configAt2 M_tm (QCSD_natToUnary n ++ rest) k).state = M_tm.qhalt ∧
          (QCSD_configAt2 M_tm (QCSD_natToUnary n ++ rest) k).tape =
            List.replicate (padW n) true ++ emitted ++
              (List.range (padW n)).flatMap (fun _ => [false, true, false, false, false, true]) ∧
          (∀ j ≤ k, QCSD_spaceUse2 (QCSD_configAt2 M_tm (QCSD_natToUnary n ++ rest) j) ≤
            QCSD_spaceBound kst n)) := by
  let wMul := chosenWMul d_V d_L
  let wAdd := chosenWAdd R K_V d_V K_L d_L
  let C_M := (R + 110) + (R + 10) * (wMul + wAdd) + K_L
  let E := max wMul (max d_T 1)
  let A := max (max K_V K_L) (max C_M K_T) + R + wMul + wAdd + d_L + 10
  let M_tm := compileRMProgPadded R wMul wAdd K_L d_L M q₀
  let padW : ℕ → ℕ := fun n => 3 * initMblk R wMul wAdd K_L d_L n
  rcases exists_Ctm_poly_le_timeBound (300000 * A ^ 4) (4 * E) with ⟨Ctm, hCtm1, hCtm_le⟩
  rcases poly_le_spaceBound (21 * C_M + K_L + 1) wMul with ⟨kst, hkst_le⟩
  refine ⟨M_tm, Ctm, kst, 3 * C_M * 2 ^ wMul, wMul, padW, le_trans zero_le_one hCtm1, ?_, ?_⟩
  · intro n _
    have hM := initMblk_le_poly R K_V d_V K_L d_L n
    have hn2_le : n + 2 ≤ 2 * (n + 1) := by omega
    calc padW n = 3 * initMblk R wMul wAdd K_L d_L n := rfl
      _ ≤ 3 * (C_M * (n + 2) ^ wMul) := Nat.mul_le_mul_left 3 hM
      _ ≤ 3 * (C_M * (2 * (n + 1)) ^ wMul) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left C_M (Nat.pow_le_pow_left hn2_le wMul))
      _ = 3 * C_M * 2 ^ wMul * (n + 1) ^ wMul := by rw [mul_pow]; ring
  · intro n rest q₁ reg₁ emitted hn hinp_len hexec hem_le
    let inp := QCSD_natToUnary n ++ rest
    let w_reg := wMul * n + wAdd
    let L_buf := K_L * (n + 2) ^ d_L
    let M_blk := initMblk R wMul wAdd K_L d_L n
    let B := (21 * C_M + K_L + 1) * (n + 2) ^ wMul
    have hM_poly : M_blk ≤ C_M * (n + 2) ^ wMul := initMblk_le_poly R K_V d_V K_L d_L n
    have hL_poly : L_buf ≤ K_L * (n + 2) ^ wMul :=
      Nat.mul_le_mul_left K_L (Nat.pow_le_pow_right (by omega) (le_trans (le_max_right d_V d_L) (le_max_left _ _)))
    have hB_ge : 3 * M_blk + L_buf + 18 * M_blk ≤ B := by
      have : (21 * C_M + K_L + 1) * (n + 2) ^ wMul =
          21 * (C_M * (n + 2) ^ wMul) + K_L * (n + 2) ^ wMul + (n + 2) ^ wMul := by ring
      dsimp only [B]; omega
    rcases chosenW_bounds R K_V d_V K_L d_L n hn with ⟨hlogK, hn2_pow, hV_pow, hP_pow⟩
    change L_buf + 18 * M_blk < 2 ^ w_reg at hP_pow
    have hL_pow : L_buf < 2 ^ w_reg := by omega
    have hW_pow : 3 * M_blk < 2 ^ w_reg := by omega
    -- Phase 1: initWSProg
    rcases initWSProg_spec R wMul wAdd K_L d_L B n rest hn hinp_len hlogK hn2_pow hL_pow hW_pow (by omega)
      with ⟨q_init_end, τ₀, hinv₀, hclean₀, he_init⟩
    -- Phase 2: execRMToOutputPadded
    rcases execRMToOutputPadded_spec 8 R w_reg L_buf M_blk B 2 (K_V * (n + 2) ^ d_V)
        (by omega) hV_pow hP_pow M inp hexec hem_le (by omega) hinv₀ hclean₀
      with ⟨q_end, τ_final, hout_pos, hmatch, he_exec⟩
    have hlen0_pos : 1 ≤ 3 * M_blk := by rcases hinv₀ with ⟨_, _, _, htw₀, _⟩; exact TapeWS_pos htw₀
    have he_tot := seq0_spec (f := fun _ => execRMToOutputPaddedEntry 8 R 2 M q₀) hlen0_pos he_init he_exec
    let out := List.replicate (3 * M_blk) true ++ emitted ++
      (List.range (3 * M_blk)).flatMap (fun _ => [false, true, false, false, false, true])
    have hout_le_B : out.length ≤ B := by
      have hp := padBits_length (3 * M_blk) [false, true, false, false, false, true] rfl
      simp only [out, List.length_append, List.length_replicate, hp]; omega
    rcases @toDetTM_spec _ (ftCompileQ R wMul wAdd K_L d_L Q) (deCompileQ R wMul wAdd K_L d_L Q)
        (Sum.inl (initWSProgEntry R wMul wAdd K_L d_L))
        (seq0 (initWSProg R wMul wAdd K_L d_L) (execRMToOutputPadded 8 R 2 M)
          (fun _ => execRMToOutputPaddedEntry 8 R 2 M q₀))
        inp out B _ _ _ hout_pos hout_le_B he_tot hmatch
      with ⟨k, hk, hcfg, hsp⟩
    have hk_le : k ≤ QCSD_timeBound Ctm n := by
      have h1 := totalTime_le_poly R K_V d_V K_L d_L K_T d_T n hn
      change k ≤ initWSTimeBound R wMul wAdd d_L n L_buf M_blk + 1 +
        execRMPaddedTimeBound (K_T * (n + 2) ^ d_T) (K_V * (n + 2) ^ d_V) L_buf M_blk + 1 at hk
      change initWSTimeBound R wMul wAdd d_L n L_buf M_blk +
        execRMPaddedTimeBound (K_T * (n + 2) ^ d_T) (K_V * (n + 2) ^ d_V) L_buf M_blk + 3 ≤
        (300000 * A ^ 4) * (n + 2) ^ (4 * E) at h1
      have h2 := hCtm_le n hn
      omega
    refine ⟨k, hk_le, ?_, ?_, fun j hj => le_trans (hsp j hj) (hkst_le n hn)⟩
    · dsimp only [M_tm, compileRMProgPadded]
      rw [hcfg]
    · dsimp only [M_tm, compileRMProgPadded]
      rw [hcfg]

theorem QCSD_encodeInstance_withPre_split (x : QCSD_Instance) (pre : List Bool)
    (ht : x.t ≤ 2 * x.n) (hpre : pre.length ≤ 2 * x.n) :
    ∃ rest : List Bool,
      QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre = QCSD_natToUnary x.n ++ rest ∧
      (QCSD_natToUnary x.n ++ rest).length ≤ 9 * x.n + 4 := by
  refine ⟨QCSD_vecToBits x.h ++ QCSD_vecToBits x.s ++ QCSD_natToUnary x.t ++ QCSD_natToUnary pre.length ++ pre,
    by unfold QCSD_encodeInstance; simp only [List.append_assoc], ?_⟩
  simp only [List.length_append, QCSD_natToUnary, QCSD_vecToBits, List.length_replicate,
    List.length_singleton, List.length_map, List.length_finRange]
  omega

theorem QCSD_encodeInstanceSep_withPre_split (x : QCSD_InstanceSep) (pre : List Bool)
    (ht0 : x.t₀ ≤ x.n) (ht1 : x.t₁ ≤ x.n) (hpre : pre.length ≤ 2 * x.n) :
    ∃ rest : List Bool,
      QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre = QCSD_natToUnary x.n ++ rest ∧
      (QCSD_natToUnary x.n ++ rest).length ≤ 9 * x.n + 4 := by
  refine ⟨QCSD_vecToBits x.h ++ QCSD_vecToBits x.s ++ QCSD_natToUnary x.t₀ ++ QCSD_natToUnary x.t₁ ++
      QCSD_natToUnary pre.length ++ pre,
    by unfold QCSD_encodeInstanceSep; simp only [List.append_assoc], ?_⟩
  simp only [List.length_append, QCSD_natToUnary, QCSD_vecToBits, List.length_replicate,
    List.length_singleton, List.length_map, List.length_finRange]
  omega

/-- End-to-end compilation theorem for Standard (`Exact`/`Le`) `QCSD_Instance` + prefix inputs. -/
theorem compileRMProg_std_spec (R : ℕ) {Q : Type} [Fintype Q] [DecidableEq Q]
    (M : RMProg R Q) (q₀ : Q) (K_V d_V K_L d_L K_T d_T : ℕ)
    (emitted : QCSD_Instance → List Bool → List Bool)
    (hExec : ∀ (x : QCSD_Instance) (pre : List Bool),
      2 ≤ x.n → x.t ≤ 2 * x.n → pre.length ≤ 2 * x.n →
      ∃ q₁ reg₁, RMExec M (K_V * (x.n + 2) ^ d_V)
        (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) q₀ (fun _ => 0) q₁ reg₁
        (emitted x pre) (K_T * (x.n + 2) ^ d_T))
    (hLen : ∀ (x : QCSD_Instance) (pre : List Bool),
      2 ≤ x.n → x.t ≤ 2 * x.n → pre.length ≤ 2 * x.n →
      (emitted x pre).length ≤ K_L * (x.n + 2) ^ d_L) :
    ∃ (M_tm : QCSD_DetTM) (Ctm : ℝ) (kst C_W d_W : ℕ) (padW : QCSD_Instance → List Bool → ℕ),
      0 ≤ Ctm ∧
      ∀ (x : QCSD_Instance) (pre : List Bool),
        2 ≤ x.n → x.t ≤ 2 * x.n → pre.length ≤ 2 * x.n →
        padW x pre ≤ C_W * (x.n + 1) ^ d_W ∧
        ∃ k ≤ QCSD_timeBound Ctm x.n,
          (QCSD_configAt2 M_tm (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) k).state = M_tm.qhalt ∧
          (QCSD_configAt2 M_tm (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) k).tape =
            List.replicate (padW x pre) true ++ emitted x pre ++
              (List.range (padW x pre)).flatMap (fun _ => [false, true, false, false, false, true]) ∧
          (∀ j ≤ k, QCSD_spaceUse2
            (QCSD_configAt2 M_tm (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) j) ≤
            QCSD_spaceBound kst x.n) := by
  rcases compileRMProg_unaryPrefix_spec R M q₀ K_V d_V K_L d_L K_T d_T
    with ⟨M_tm, Ctm, kst, C_W, d_W, padW_n, hCtm, hpad_le, hrun⟩
  refine ⟨M_tm, Ctm, kst, C_W, d_W, fun x _ => padW_n x.n, hCtm, fun x pre hn ht hpre => ?_⟩
  rcases QCSD_encodeInstance_withPre_split x pre ht hpre with ⟨rest, hinp_eq, hlen_le⟩
  rcases hExec x pre hn ht hpre with ⟨q₁, reg₁, hexec⟩
  have hlen := hLen x pre hn ht hpre
  rw [hinp_eq] at hexec ⊢
  exact ⟨hpad_le x.n hn, hrun x.n rest q₁ reg₁ (emitted x pre) hn hlen_le hexec hlen⟩

/-- End-to-end compilation theorem for Separated (`Sep`) `QCSD_InstanceSep` + prefix inputs. -/
theorem compileRMProg_sep_spec (R : ℕ) {Q : Type} [Fintype Q] [DecidableEq Q]
    (M : RMProg R Q) (q₀ : Q) (K_V d_V K_L d_L K_T d_T : ℕ)
    (emitted : QCSD_InstanceSep → List Bool → List Bool)
    (hExec : ∀ (x : QCSD_InstanceSep) (pre : List Bool),
      2 ≤ x.n → x.t₀ ≤ x.n → x.t₁ ≤ x.n → pre.length ≤ 2 * x.n →
      ∃ q₁ reg₁, RMExec M (K_V * (x.n + 2) ^ d_V)
        (QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre) q₀ (fun _ => 0) q₁ reg₁
        (emitted x pre) (K_T * (x.n + 2) ^ d_T))
    (hLen : ∀ (x : QCSD_InstanceSep) (pre : List Bool),
      2 ≤ x.n → x.t₀ ≤ x.n → x.t₁ ≤ x.n → pre.length ≤ 2 * x.n →
      (emitted x pre).length ≤ K_L * (x.n + 2) ^ d_L) :
    ∃ (M_tm : QCSD_DetTM) (Ctm : ℝ) (kst C_W d_W : ℕ) (padW : QCSD_InstanceSep → List Bool → ℕ),
      0 ≤ Ctm ∧
      ∀ (x : QCSD_InstanceSep) (pre : List Bool),
        2 ≤ x.n → x.t₀ ≤ x.n → x.t₁ ≤ x.n → pre.length ≤ 2 * x.n →
        padW x pre ≤ C_W * (x.n + 1) ^ d_W ∧
        ∃ k ≤ QCSD_timeBound Ctm x.n,
          (QCSD_configAt2 M_tm (QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre) k).state = M_tm.qhalt ∧
          (QCSD_configAt2 M_tm (QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre) k).tape =
            List.replicate (padW x pre) true ++ emitted x pre ++
              (List.range (padW x pre)).flatMap (fun _ => [false, true, false, false, false, true]) ∧
          (∀ j ≤ k, QCSD_spaceUse2
            (QCSD_configAt2 M_tm (QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre) j) ≤
            QCSD_spaceBound kst x.n) := by
  rcases compileRMProg_unaryPrefix_spec R M q₀ K_V d_V K_L d_L K_T d_T
    with ⟨M_tm, Ctm, kst, C_W, d_W, padW_n, hCtm, hpad_le, hrun⟩
  refine ⟨M_tm, Ctm, kst, C_W, d_W, fun x _ => padW_n x.n, hCtm, fun x pre hn ht0 ht1 hpre => ?_⟩
  rcases QCSD_encodeInstanceSep_withPre_split x pre ht0 ht1 hpre with ⟨rest, hinp_eq, hlen_le⟩
  rcases hExec x pre hn ht0 ht1 hpre with ⟨q₁, reg₁, hexec⟩
  have hlen := hLen x pre hn ht0 ht1 hpre
  rw [hinp_eq] at hexec ⊢
  exact ⟨hpad_le x.n hn, hrun x.n rest q₁ reg₁ (emitted x pre) hn hlen_le hexec hlen⟩

end Branch4Phase1Dev
