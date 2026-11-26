import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Finset.Card
import QCSD.Defs

namespace Branch1Recovery

open QCSD.Defs

/-! ### Section 1: Tape Equivalence & `QCSD_bitsToNat` Laws -/

def tapeEq (t₁ t₂ : List Bool) : Prop :=
  ∀ i : ℕ, QCSD_tapeRead t₁ i = QCSD_tapeRead t₂ i

lemma tapeEq_refl (t : List Bool) : tapeEq t t := fun _ => rfl

lemma tapeEq_symm {t₁ t₂ : List Bool} (h : tapeEq t₁ t₂) : tapeEq t₂ t₁ :=
  fun i => (h i).symm

lemma tapeEq_trans {t₁ t₂ t₃ : List Bool} (h₁ : tapeEq t₁ t₂) (h₂ : tapeEq t₂ t₃) :
    tapeEq t₁ t₃ :=
  fun i => (h₁ i).trans (h₂ i)

lemma tapeRead_replicate_false (m i : ℕ) :
    QCSD_tapeRead (List.replicate m false) i = false := by
  unfold QCSD_tapeRead
  by_cases hi : i < m
  · simp [List.getD_eq_getElem?_getD, hi]
  · have hlen : (List.replicate m false).length ≤ i := by simpa using hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]

lemma tapeRead_append_replicate_false (t : List Bool) (m i : ℕ) :
    QCSD_tapeRead (t ++ List.replicate m false) i = QCSD_tapeRead t i := by
  unfold QCSD_tapeRead
  by_cases hi : i < t.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, hi]
  · have hge : t.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge,
        List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    have hr := tapeRead_replicate_false m (i - t.length)
    unfold QCSD_tapeRead at hr
    rw [List.getD_eq_getElem?_getD] at hr
    exact hr

lemma tapeWrite2_length (t : List Bool) (i : ℕ) (b : Bool) :
    (QCSD_tapeWrite2 t i b).length = Nat.max t.length (i + 1) := by
  rw [Nat.max_eq_max]
  unfold QCSD_tapeWrite2
  split_ifs with h
  · simp; omega
  · simp; omega

lemma tapeRead_set (t : List Bool) (i j : ℕ) (b : Bool) (hi : i < t.length) :
    QCSD_tapeRead (t.set i b) j = if j = i then b else QCSD_tapeRead t j := by
  unfold QCSD_tapeRead
  by_cases hji : j = i
  · subst hji
    simp [List.getD_eq_getElem?_getD, hi]
  · have hij : i ≠ j := fun h => hji h.symm
    simp [List.getD_eq_getElem?_getD, hji, hij]

lemma tapeRead_tapeWrite2 (t : List Bool) (i j : ℕ) (b : Bool) :
    QCSD_tapeRead (QCSD_tapeWrite2 t i b) j = if j = i then b else QCSD_tapeRead t j := by
  unfold QCSD_tapeWrite2
  by_cases hi : i < t.length
  · rw [ite_eq_left hi]
    exact tapeRead_set t i j b hi
  · rw [ite_eq_right hi]
    have hi' : i < (t ++ List.replicate (i + 1 - t.length) false).length := by
      simp; omega
    rw [tapeRead_set _ i j b hi']
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji, ↓reduceIte]
      exact tapeRead_append_replicate_false t (i + 1 - t.length) j

lemma tapeEq_tapeWrite2 {t₁ t₂ : List Bool} (h : tapeEq t₁ t₂) (i : ℕ) (b : Bool) :
    tapeEq (QCSD_tapeWrite2 t₁ i b) (QCSD_tapeWrite2 t₂ i b) := by
  intro j
  rw [tapeRead_tapeWrite2, tapeRead_tapeWrite2, h j]

def stepHead (h : ℕ) (d : QCSD_HeadDir) : ℕ :=
  match d with
  | QCSD_HeadDir.left => h - 1
  | QCSD_HeadDir.right => h + 1

noncomputable def stepOrStay (M : QCSD_DetTM) (c : QCSD_Config M) : QCSD_Config M :=
  match QCSD_stepConfig2 M c with
  | none => c
  | some c' => c'

lemma configAt2_eq_iterate (M : QCSD_DetTM) (x : List Bool) (k : ℕ) :
    QCSD_configAt2 M x k = (stepOrStay M)^[k] ⟨M.q0, x, 0⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

lemma stepOrStay_of_qhalt (M : QCSD_DetTM) (c : QCSD_Config M) (h : c.state = M.qhalt) :
    stepOrStay M c = c := by
  unfold stepOrStay QCSD_stepConfig2
  have hd : @decide (c.state = M.qhalt) (M.decEqQ c.state M.qhalt) = true := by
    let _ := M.decEqQ
    exact decide_eq_true h
  rw [hd]
  rfl

lemma stepOrStay_of_ne_qhalt (M : QCSD_DetTM) (c : QCSD_Config M) (h : c.state ≠ M.qhalt) :
    let r := M.step c.state (QCSD_tapeRead c.tape c.head)
    stepOrStay M c = ⟨r.1, QCSD_tapeWrite2 c.tape c.head r.2.1, stepHead c.head r.2.2⟩ := by
  unfold stepOrStay QCSD_stepConfig2 stepHead
  have hd : @decide (c.state = M.qhalt) (M.decEqQ c.state M.qhalt) = false := by
    let _ := M.decEqQ
    exact decide_eq_false h
  rw [hd]
  dsimp only [Bool.false_eq_true, ↓reduceIte]
  cases (M.step c.state (QCSD_tapeRead c.tape c.head)).2.2 <;> rfl

lemma iterate_stepOrStay_tapeEq (M : QCSD_DetTM) :
    ∀ (k : ℕ) {c₁ c₂ : QCSD_Config M},
      c₁.state = c₂.state → c₁.head = c₂.head → tapeEq c₁.tape c₂.tape →
      ((stepOrStay M)^[k] c₁).state = ((stepOrStay M)^[k] c₂).state ∧
      ((stepOrStay M)^[k] c₁).head = ((stepOrStay M)^[k] c₂).head ∧
      tapeEq ((stepOrStay M)^[k] c₁).tape ((stepOrStay M)^[k] c₂).tape ∧
      ((stepOrStay M)^[k] c₂).tape.length ≤
        Nat.max ((stepOrStay M)^[k] c₁).tape.length c₂.tape.length := by
  intro k
  induction k with
  | zero =>
    intro c₁ c₂ hq hh ht
    exact ⟨hq, hh, ht, Nat.le_max_right _ _⟩
  | succ k ih =>
    intro c₁ c₂ hq hh ht
    obtain ⟨hqk, hhk, htk, hlenk⟩ := ih hq hh ht
    simp only [Function.iterate_succ_apply']
    set d₁ := (stepOrStay M)^[k] c₁
    set d₂ := (stepOrStay M)^[k] c₂
    let _ := M.decEqQ
    by_cases hhalt : d₁.state = M.qhalt
    · have hhalt2 : d₂.state = M.qhalt := hqk.symm.trans hhalt
      rw [stepOrStay_of_qhalt M d₁ hhalt, stepOrStay_of_qhalt M d₂ hhalt2]
      exact ⟨hqk, hhk, htk, hlenk⟩
    · have hhalt2 : d₂.state ≠ M.qhalt := by intro h2; exact hhalt (hqk.trans h2)
      rw [stepOrStay_of_ne_qhalt M d₁ hhalt, stepOrStay_of_ne_qhalt M d₂ hhalt2]
      dsimp only
      have hread : QCSD_tapeRead d₁.tape d₁.head = QCSD_tapeRead d₂.tape d₂.head := by
        rw [hhk]; exact htk d₂.head
      rw [hqk, hread]
      refine ⟨rfl, by rw [hhk], ?_, ?_⟩
      · rw [hhk]
        exact tapeEq_tapeWrite2 htk d₂.head _
      · rw [tapeWrite2_length, tapeWrite2_length, hhk]
        simp only [Nat.max_eq_max] at hlenk ⊢
        omega

lemma bitsToNat_nil : QCSD_bitsToNat [] = 0 := rfl

lemma bitsToNat_cons (b : Bool) (bs : List Bool) :
    QCSD_bitsToNat (b :: bs) = 2 * QCSD_bitsToNat bs + (if b then 1 else 0) := rfl

lemma bitsToNat_append (l₁ l₂ : List Bool) :
    QCSD_bitsToNat (l₁ ++ l₂) = QCSD_bitsToNat l₁ + 2 ^ l₁.length * QCSD_bitsToNat l₂ := by
  induction l₁ with
  | nil => simp [QCSD_bitsToNat]
  | cons b bs ih =>
    simp only [List.cons_append, bitsToNat_cons, List.length_cons, ih, Nat.pow_succ]
    ring

lemma bitsToNat_replicate_false (m : ℕ) :
    QCSD_bitsToNat (List.replicate m false) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, bitsToNat_cons, ih]

lemma bitsToNat_lt_two_pow (l : List Bool) :
    QCSD_bitsToNat l < 2 ^ l.length := by
  induction l with
  | nil => simp [QCSD_bitsToNat]
  | cons b bs ih =>
    rw [bitsToNat_cons, List.length_cons]
    have hp : 2 ^ (bs.length + 1) = 2 * 2 ^ bs.length := by ring
    rw [hp]
    cases b <;> simp <;> omega

lemma ofFn_tapeRead_eq_append (t : List Bool) (M : ℕ) (hM : t.length ≤ M) :
    List.ofFn (fun i : Fin M => QCSD_tapeRead t i.val) =
      t ++ List.replicate (M - t.length) false := by
  apply List.ext_getElem
  · simp [hM]
  · intro i hi1 hi2
    simp only [List.getElem_ofFn]
    rw [← tapeRead_append_replicate_false t (M - t.length) i]
    unfold QCSD_tapeRead
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2, Option.getD_some]

lemma bitsToNat_of_tapeEq {t₁ t₂ : List Bool} (h : tapeEq t₁ t₂) :
    QCSD_bitsToNat t₁ = QCSD_bitsToNat t₂ := by
  let M := Nat.max t₁.length t₂.length
  have h1 : List.ofFn (fun i : Fin M => QCSD_tapeRead t₁ i.val) =
      t₁ ++ List.replicate (M - t₁.length) false :=
    ofFn_tapeRead_eq_append t₁ M (Nat.le_max_left _ _)
  have h2 : List.ofFn (fun i : Fin M => QCSD_tapeRead t₂ i.val) =
      t₂ ++ List.replicate (M - t₂.length) false :=
    ofFn_tapeRead_eq_append t₂ M (Nat.le_max_right _ _)
  have heq : List.ofFn (fun i : Fin M => QCSD_tapeRead t₁ i.val) =
      List.ofFn (fun i : Fin M => QCSD_tapeRead t₂ i.val) := by
    congr 1; ext i; exact h i.val
  have hb1 : QCSD_bitsToNat (t₁ ++ List.replicate (M - t₁.length) false) = QCSD_bitsToNat t₁ := by
    rw [bitsToNat_append, bitsToNat_replicate_false]; omega
  have hb2 : QCSD_bitsToNat (t₂ ++ List.replicate (M - t₂.length) false) = QCSD_bitsToNat t₂ := by
    rw [bitsToNat_append, bitsToNat_replicate_false]; omega
  rw [← hb1, ← h1, heq, h2, hb2]

lemma bitsToNat_ofFn_take_of_lt (t : List Bool) (m : ℕ) (hlt : QCSD_bitsToNat t < 2 ^ m) :
    QCSD_bitsToNat (List.ofFn (fun i : Fin m => QCSD_tapeRead t i.val)) = QCSD_bitsToNat t := by
  let M := Nat.max t.length m
  let u := List.ofFn (fun i : Fin M => QCSD_tapeRead t i.val)
  have hu : u = t ++ List.replicate (M - t.length) false :=
    ofFn_tapeRead_eq_append t M (Nat.le_max_left _ _)
  have hbu : QCSD_bitsToNat u = QCSD_bitsToNat t := by
    rw [hu, bitsToNat_append, bitsToNat_replicate_false]; omega
  have hmM : m ≤ M := Nat.le_max_right _ _
  have htake : u.take m = List.ofFn (fun i : Fin m => QCSD_tapeRead t i.val) := by
    apply List.ext_getElem
    · simp [u, hmM]
    · intro i hi1 hi2
      simp [u]
  have hsplit : u = u.take m ++ u.drop m := (List.take_append_drop m u).symm
  have hbu2 : QCSD_bitsToNat u = QCSD_bitsToNat (u.take m) + 2 ^ m * QCSD_bitsToNat (u.drop m) := by
    conv_lhs => rw [hsplit]
    rw [bitsToNat_append]
    have htl : (u.take m).length = m := by simp [u, hmM]
    rw [htl]
  have hdrop0 : QCSD_bitsToNat (u.drop m) = 0 := by
    by_contra hne
    have hge1 : 1 ≤ QCSD_bitsToNat (u.drop m) := Nat.pos_of_ne_zero hne
    have hge : 2 ^ m ≤ 2 ^ m * QCSD_bitsToNat (u.drop m) := Nat.le_mul_of_pos_right _ hge1
    omega
  rw [hdrop0, Nat.mul_zero, Nat.add_zero, htake] at hbu2
  exact hbu2.symm.trans hbu

lemma bitsToNat_ofFn_pos_iff (t : List Bool) (m : ℕ) (hlt : QCSD_bitsToNat t < 2 ^ m) :
    0 < QCSD_bitsToNat t ↔ ∃ i : Fin m, QCSD_tapeRead t i.val = true := by
  rw [← bitsToNat_ofFn_take_of_lt t m hlt]
  generalize hl : List.ofFn (fun i : Fin m => QCSD_tapeRead t i.val) = l
  have hex : (∃ i : Fin m, QCSD_tapeRead t i.val = true) ↔ true ∈ l := by
    rw [← hl]
    simp
  rw [hex]
  clear hl hlt hex
  induction l with
  | nil => simp [QCSD_bitsToNat]
  | cons b bs ih =>
    rw [bitsToNat_cons, List.mem_cons]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      constructor
      · intro h
        exact Or.inr (ih.mp (by omega))
      · intro h
        rcases h with h | h
        · cases h
        · have hb := ih.mpr h
          omega
    · simp only [↓reduceIte, true_or, iff_true]
      omega

/-! ### Section 2: Combinatorial Solution Bounds, Prefix-Count Laws & Witness Decoding -/

def qcsdIface (n : ℕ) (e₀ e₁ : Fin n → ZMod 2) : List Bool :=
  (List.ofFn fun i : Fin n => decide (e₀ i = 1)) ++
  (List.ofFn fun i : Fin n => decide (e₁ i = 1))

lemma qcsdIface_length (n : ℕ) (e₀ e₁ : Fin n → ZMod 2) :
    (qcsdIface n e₀ e₁).length = 2 * n := by
  simp [qcsdIface, Nat.two_mul]

lemma zmod2_recover_bit (x : ZMod 2) :
    (if decide (x = 1) then (1 : ZMod 2) else 0) = x := by
  fin_cases x <;> rfl

lemma decodeSolPair_qcsdIface (n : ℕ) (e₀ e₁ : Fin n → ZMod 2) :
    QCSD_decodeSolPair n (qcsdIface n e₀ e₁) = some (e₀, e₁) := by
  unfold QCSD_decodeSolPair
  rw [ite_eq_left (qcsdIface_length n e₀ e₁)]
  congr 1
  ext i
  · have hi : i.val < (List.ofFn fun j : Fin n => decide (e₀ j = 1)).length := by simp
    simp only [qcsdIface, List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
      List.length_ofFn, i.isLt, List.getElem?_eq_getElem, Option.getD_some, List.getElem_ofFn]
    exact zmod2_recover_bit (e₀ i)
  · have hge : (List.ofFn fun j : Fin n => decide (e₀ j = 1)).length ≤ n + i.val := by simp
    have hi2 : (n + i.val) - n < n := by omega
    simp only [qcsdIface, List.getD_eq_getElem?_getD, List.getElem?_append_right hge,
      List.length_ofFn, hi2, List.getElem?_eq_getElem, Option.getD_some, List.getElem_ofFn]
    have hsub : (⟨n + i.val - n, hi2⟩ : Fin n) = i := by ext; simp
    rw [hsub]
    exact zmod2_recover_bit (e₁ i)

lemma card_sols_lt_two_pow_two_mul
    (n : ℕ) (hn : 2 ≤ n) (h s : Fin n → ZMod 2)
    (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hLin : ∀ p ∈ sols, ∀ k : Fin n, p.1 k + QCSD_cycMul n h p.2 k = s k) :
    sols.card < 2 ^ (2 * n) := by
  have hinj : Set.InjOn Prod.snd (sols : Set ((Fin n → ZMod 2) × (Fin n → ZMod 2))) := by
    intro p hp q hq hsnd
    have hp' := hLin p hp
    have hq' := hLin q hq
    ext k
    · have hk1 := hp' k
      have hk2 := hq' k
      rw [hsnd] at hk1
      exact add_right_cancel (hk1.trans hk2.symm)
    · exact congrFun hsnd k
  have hle : sols.card ≤ (Finset.univ : Finset (Fin n → ZMod 2)).card :=
    Finset.card_le_card_of_injOn Prod.snd (fun _ _ => Finset.mem_univ _) hinj
  have hcard : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2 ^ n := by
    simp [ZMod.card]
  have hpow : 2 ^ n < 2 ^ (2 * n) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

lemma prefix_count_split
    (n : ℕ) (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (pre : List Bool) (hp : pre.length < 2 * n) :
    (sols.filter (fun q => (qcsdIface n q.1 q.2).take pre.length = pre)).card =
      (sols.filter (fun q => (qcsdIface n q.1 q.2).take (pre.length + 1) = pre ++ [false])).card +
      (sols.filter (fun q => (qcsdIface n q.1 q.2).take (pre.length + 1) = pre ++ [true])).card := by
  classical
  have split (l : List Bool) (hl : pre.length < l.length) :
      l.take pre.length = pre ↔
        l.take (pre.length + 1) = pre ++ [false] ∨
        l.take (pre.length + 1) = pre ++ [true] := by
    constructor
    · intro h
      have hnext := (List.take_concat_get' l pre.length hl).symm
      rw [h] at hnext
      cases hb : l[pre.length] with
      | false => exact Or.inl (by simpa [hb] using hnext)
      | true => exact Or.inr (by simpa [hb] using hnext)
    · intro h
      rcases h with h | h
      · have htake := congrArg (fun z : List Bool => z.take pre.length) h
        simpa [List.take_take, Nat.min_eq_left (show pre.length ≤ pre.length + 1 by omega)] using htake
      · have htake := congrArg (fun z : List Bool => z.take pre.length) h
        simpa [List.take_take, Nat.min_eq_left (show pre.length ≤ pre.length + 1 by omega)] using htake
  have hlen (q : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
      pre.length < (qcsdIface n q.1 q.2).length := by
    rw [qcsdIface_length]; exact hp
  have hunion :
      sols.filter (fun q => (qcsdIface n q.1 q.2).take pre.length = pre) =
        sols.filter (fun q => (qcsdIface n q.1 q.2).take (pre.length + 1) = pre ++ [false]) ∪
        sols.filter (fun q => (qcsdIface n q.1 q.2).take (pre.length + 1) = pre ++ [true]) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    rw [split _ (hlen q)]
    tauto
  have hdisj : Disjoint
      (sols.filter (fun q => (qcsdIface n q.1 q.2).take (pre.length + 1) = pre ++ [false]))
      (sols.filter (fun q => (qcsdIface n q.1 q.2).take (pre.length + 1) = pre ++ [true])) := by
    apply Finset.disjoint_left.mpr
    intro q hf ht
    have hbad := (Finset.mem_filter.mp hf).2.symm.trans (Finset.mem_filter.mp ht).2
    simp at hbad
  rw [hunion, Finset.card_union_of_disjoint hdisj]

lemma greedy_bit_step
    (n : ℕ) (sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (pre : List Bool) (hp : pre.length < 2 * n)
    (hpos : 0 < (sols.filter (fun q => (qcsdIface n q.1 q.2).take pre.length = pre)).card) :
    let c0 := (sols.filter (fun q => (qcsdIface n q.1 q.2).take (pre.length + 1) = pre ++ [false])).card
    let b := if 0 < c0 then false else true
    0 < (sols.filter (fun q => (qcsdIface n q.1 q.2).take (pre.length + 1) = pre ++ [b])).card := by
  classical
  have hs := prefix_count_split n sols pre hp
  dsimp only
  split_ifs with hc0
  · exact hc0
  · omega

/-! ### Section 3: Composable Monadic TM Programs (`ReachesWithin` & `Prog`) -/

def ReachesWithin (M : QCSD_DetTM) (Sp T : ℕ) (c₁ c₂ : QCSD_Config M) : Prop :=
  ∃ k ≤ T, (stepOrStay M)^[k] c₁ = c₂ ∧
    ∀ j ≤ k, QCSD_spaceUse2 ((stepOrStay M)^[j] c₁) ≤ Sp

lemma ReachesWithin.refl {M : QCSD_DetTM} {Sp : ℕ} {c : QCSD_Config M}
    (hsp : QCSD_spaceUse2 c ≤ Sp) : ReachesWithin M Sp 0 c c := by
  refine ⟨0, Nat.le_refl 0, rfl, fun j hj => ?_⟩
  obtain rfl : j = 0 := by omega
  exact hsp

lemma ReachesWithin.mono {M : QCSD_DetTM} {Sp₁ Sp₂ T₁ T₂ : ℕ} {c₁ c₂ : QCSD_Config M}
    (hSp : Sp₁ ≤ Sp₂) (hT : T₁ ≤ T₂) (h : ReachesWithin M Sp₁ T₁ c₁ c₂) :
    ReachesWithin M Sp₂ T₂ c₁ c₂ := by
  obtain ⟨k, hk, heq, hsp⟩ := h
  exact ⟨k, hk.trans hT, heq, fun j hj => (hsp j hj).trans hSp⟩

lemma ReachesWithin.trans {M : QCSD_DetTM} {Sp T₁ T₂ : ℕ} {c₁ c₂ c₃ : QCSD_Config M}
    (h₁ : ReachesWithin M Sp T₁ c₁ c₂) (h₂ : ReachesWithin M Sp T₂ c₂ c₃) :
    ReachesWithin M Sp (T₁ + T₂) c₁ c₃ := by
  obtain ⟨k₁, hk₁, heq₁, hsp₁⟩ := h₁
  obtain ⟨k₂, hk₂, heq₂, hsp₂⟩ := h₂
  refine ⟨k₁ + k₂, Nat.add_le_add hk₁ hk₂, ?_, ?_⟩
  · rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, heq₁, heq₂]
  · intro j hj
    by_cases hj1 : j ≤ k₁
    · exact hsp₁ j hj1
    · have hsub : j = (j - k₁) + k₁ := by omega
      rw [hsub, Function.iterate_add_apply, heq₁]
      exact hsp₂ (j - k₁) (by omega)

lemma ReachesWithin.step {M : QCSD_DetTM} {Sp : ℕ} {c c' : QCSD_Config M}
    (hne : c.state ≠ M.qhalt)
    (hstep : let r := M.step c.state (QCSD_tapeRead c.tape c.head)
             c' = ⟨r.1, QCSD_tapeWrite2 c.tape c.head r.2.1, stepHead c.head r.2.2⟩)
    (hsp₁ : QCSD_spaceUse2 c ≤ Sp)
    (hsp₂ : QCSD_spaceUse2 c' ≤ Sp) :
    ReachesWithin M Sp 1 c c' := by
  refine ⟨1, Nat.le_refl 1, ?_, ?_⟩
  · simp only [Function.iterate_one]
    rw [stepOrStay_of_ne_qhalt M c hne, ← hstep]
  · intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact hsp₁
    · simp only [Function.iterate_one]
      rw [stepOrStay_of_ne_qhalt M c hne, ← hstep]
      exact hsp₂

abbrev Prog (Q E : Type) :=
  Q × (Q → Bool → (Q ⊕ E) × Bool × QCSD_HeadDir)

def EmbedsProg (M : QCSD_DetTM) {Q E : Type} (p : Prog Q E)
    (emb : Q → M.Q) (onExit : E → M.Q) : Prop :=
  (∀ q, emb q ≠ M.qhalt) ∧
  (∀ q b, M.step (emb q) b =
    match p.2 q b with
    | (Sum.inl q', b', d) => (emb q', b', d)
    | (Sum.inr e, b', d) => (onExit e, b', d))

def ProgRuns {Q E : Type} (p : Prog Q E) (Sp T : ℕ)
    (th₁ : List Bool × ℕ) (e : E) (th₂ : List Bool × ℕ) : Prop :=
  ∀ (M : QCSD_DetTM) (emb : Q → M.Q) (onExit : E → M.Q),
    EmbedsProg M p emb onExit →
    ReachesWithin M Sp T ⟨emb p.1, th₁.1, th₁.2⟩ ⟨onExit e, th₂.1, th₂.2⟩

def progToTM {Q : Type} [Fintype Q] [DecidableEq Q] (p : Prog Q Unit) : QCSD_DetTM where
  Q := Q ⊕ Unit
  q0 := Sum.inl p.1
  qhalt := Sum.inr ()
  step := fun s b =>
    match s with
    | Sum.inl q => p.2 q b
    | Sum.inr () => (Sum.inr (), b, QCSD_HeadDir.right)

lemma progToTM_reaches {Q : Type} [Fintype Q] [DecidableEq Q] (p : Prog Q Unit)
    {Sp T : ℕ} {inp out : List Bool} {hout : ℕ}
    (h : ProgRuns p Sp T (inp, 0) () (out, hout)) :
    ReachesWithin (progToTM p) Sp T ⟨(progToTM p).q0, inp, 0⟩ ⟨(progToTM p).qhalt, out, hout⟩ := by
  apply h (progToTM p) Sum.inl Sum.inr
  refine ⟨fun q hbad => ?_, fun q b => ?_⟩
  · change Sum.inl q = Sum.inr () at hbad
    cases hbad
  · change p.2 q b = _
    rcases p.2 q b with ⟨q' | e, b', d⟩ <;> rfl

lemma ProgRuns.mono {Q E : Type} {p : Prog Q E} {Sp₁ Sp₂ T₁ T₂ : ℕ}
    {th₁ th₂ : List Bool × ℕ} {e : E}
    (hSp : Sp₁ ≤ Sp₂) (hT : T₁ ≤ T₂)
    (h : ProgRuns p Sp₁ T₁ th₁ e th₂) :
    ProgRuns p Sp₂ T₂ th₁ e th₂ :=
  fun M emb onExit hemb => (h M emb onExit hemb).mono hSp hT

def primProg {E : Type} (f : Bool → E × Bool × QCSD_HeadDir) : Prog Unit E :=
  ((), fun _ b => let r := f b; (Sum.inr r.1, r.2.1, r.2.2))

lemma ProgRuns_prim {E : Type} (f : Bool → E × Bool × QCSD_HeadDir)
    {Sp : ℕ} {t : List Bool} {h : ℕ}
    (hsp₁ : Nat.max t.length (h + 1) ≤ Sp)
    (hsp₂ : Nat.max (QCSD_tapeWrite2 t h (f (QCSD_tapeRead t h)).2.1).length
              (stepHead h (f (QCSD_tapeRead t h)).2.2 + 1) ≤ Sp) :
    ProgRuns (primProg f) Sp 1 (t, h) (f (QCSD_tapeRead t h)).1
      (QCSD_tapeWrite2 t h (f (QCSD_tapeRead t h)).2.1,
       stepHead h (f (QCSD_tapeRead t h)).2.2) := by
  unfold ProgRuns
  intro M emb onExit hemb
  obtain ⟨hne, hstep⟩ := hemb
  apply ReachesWithin.step (hne ())
  · rw [hstep () (QCSD_tapeRead t h)]
    rfl
  · exact hsp₁
  · exact hsp₂

def seqProg {Q₁ Q₂ E : Type} (p₁ : Prog Q₁ Unit) (p₂ : Prog Q₂ E) : Prog (Q₁ ⊕ Q₂) E :=
  (Sum.inl p₁.1, fun s b =>
    match s with
    | Sum.inl q₁ =>
      match p₁.2 q₁ b with
      | (Sum.inl q₁', b', d) => (Sum.inl (Sum.inl q₁'), b', d)
      | (Sum.inr (), b', d) => (Sum.inl (Sum.inr p₂.1), b', d)
    | Sum.inr q₂ =>
      match p₂.2 q₂ b with
      | (Sum.inl q₂', b', d) => (Sum.inl (Sum.inr q₂'), b', d)
      | (Sum.inr e, b', d) => (Sum.inr e, b', d))

lemma ProgRuns_seq {Q₁ Q₂ E : Type} {p₁ : Prog Q₁ Unit} {p₂ : Prog Q₂ E}
    {Sp T₁ T₂ : ℕ} {th₀ th₁ th₂ : List Bool × ℕ} {e : E}
    (h₁ : ProgRuns p₁ Sp T₁ th₀ () th₁)
    (h₂ : ProgRuns p₂ Sp T₂ th₁ e th₂) :
    ProgRuns (seqProg p₁ p₂) Sp (T₁ + T₂) th₀ e th₂ := by
  intro M emb onExit ⟨hne, hstep⟩
  have hemb₁ : EmbedsProg M p₁ (emb ∘ Sum.inl) (fun _ => emb (Sum.inr p₂.1)) := by
    refine ⟨fun q => hne (Sum.inl q), fun q b => ?_⟩
    rw [Function.comp_apply, hstep (Sum.inl q) b]
    dsimp [seqProg]
    rcases p₁.2 q b with ⟨q' | ⟨⟩, b', d⟩ <;> rfl
  have hemb₂ : EmbedsProg M p₂ (emb ∘ Sum.inr) onExit := by
    refine ⟨fun q => hne (Sum.inr q), fun q b => ?_⟩
    rw [Function.comp_apply, hstep (Sum.inr q) b]
    dsimp [seqProg]
    rcases p₂.2 q b with ⟨q' | e', b', d⟩ <;> rfl
  exact (h₁ M _ _ hemb₁).trans (h₂ M _ _ hemb₂)

def bindProg {Q₁ E₁ Q₂ E₂ : Type} (p₁ : Prog Q₁ E₁) (k : E₁ → Prog Q₂ E₂) :
    Prog (Q₁ ⊕ (E₁ × Q₂)) E₂ :=
  (Sum.inl p₁.1, fun s b =>
    match s with
    | Sum.inl q₁ =>
      match p₁.2 q₁ b with
      | (Sum.inl q₁', b', d) => (Sum.inl (Sum.inl q₁'), b', d)
      | (Sum.inr e₁, b', d) => (Sum.inl (Sum.inr (e₁, (k e₁).1)), b', d)
    | Sum.inr (e₁, q₂) =>
      match (k e₁).2 q₂ b with
      | (Sum.inl q₂', b', d) => (Sum.inl (Sum.inr (e₁, q₂')), b', d)
      | (Sum.inr e₂, b', d) => (Sum.inr e₂, b', d))

lemma ProgRuns_bind {Q₁ E₁ Q₂ E₂ : Type} {p₁ : Prog Q₁ E₁} {k : E₁ → Prog Q₂ E₂}
    {Sp T₁ T₂ : ℕ} {th₀ th₁ th₂ : List Bool × ℕ} {e₁ : E₁} {e₂ : E₂}
    (h₁ : ProgRuns p₁ Sp T₁ th₀ e₁ th₁)
    (h₂ : ProgRuns (k e₁) Sp T₂ th₁ e₂ th₂) :
    ProgRuns (bindProg p₁ k) Sp (T₁ + T₂) th₀ e₂ th₂ := by
  intro M emb onExit ⟨hne, hstep⟩
  have hemb₁ : EmbedsProg M p₁ (emb ∘ Sum.inl) (fun x => emb (Sum.inr (x, (k x).1))) := by
    refine ⟨fun q => hne (Sum.inl q), fun q b => ?_⟩
    rw [Function.comp_apply, hstep (Sum.inl q) b]
    dsimp [bindProg]
    rcases p₁.2 q b with ⟨q' | x, b', d⟩ <;> rfl
  have hemb₂ : EmbedsProg M (k e₁) (fun q₂ => emb (Sum.inr (e₁, q₂))) onExit := by
    refine ⟨fun q₂ => hne (Sum.inr (e₁, q₂)), fun q₂ b => ?_⟩
    rw [hstep (Sum.inr (e₁, q₂)) b]
    dsimp [bindProg]
    rcases (k e₁).2 q₂ b with ⟨q₂' | y, b', d⟩ <;> rfl
  exact (h₁ M _ _ hemb₁).trans (h₂ M _ _ hemb₂)

def whileProg {Q : Type} (body : Prog Q Bool) : Prog Q Unit :=
  (body.1, fun q b =>
    match body.2 q b with
    | (Sum.inl q', b', d) => (Sum.inl q', b', d)
    | (Sum.inr true, b', d) => (Sum.inl body.1, b', d)
    | (Sum.inr false, b', d) => (Sum.inr (), b', d))

lemma ProgRuns_while_false {Q : Type} {body : Prog Q Bool}
    {Sp T : ℕ} {th₀ th₁ : List Bool × ℕ}
    (h : ProgRuns body Sp T th₀ false th₁) :
    ProgRuns (whileProg body) Sp T th₀ () th₁ := by
  intro M emb onExit ⟨hne, hstep⟩
  have hemb : EmbedsProg M body emb (fun c => if c then emb body.1 else onExit ()) := by
    refine ⟨hne, fun q b => ?_⟩
    rw [hstep q b]
    dsimp [whileProg]
    rcases body.2 q b with ⟨q' | (_ | _), b', d⟩ <;> rfl
  exact h M emb _ hemb

lemma ProgRuns_while_true {Q : Type} {body : Prog Q Bool}
    {Sp T₁ T₂ : ℕ} {th₀ th₁ th₂ : List Bool × ℕ}
    (h₁ : ProgRuns body Sp T₁ th₀ true th₁)
    (h₂ : ProgRuns (whileProg body) Sp T₂ th₁ () th₂) :
    ProgRuns (whileProg body) Sp (T₁ + T₂) th₀ () th₂ := by
  intro M emb onExit hemb
  obtain ⟨hne, hstep⟩ := hemb
  have hembB : EmbedsProg M body emb (fun c => if c then emb body.1 else onExit ()) := by
    refine ⟨hne, fun q b => ?_⟩
    rw [hstep q b]
    dsimp [whileProg]
    rcases body.2 q b with ⟨q' | (_ | _), b', d⟩ <;> rfl
  exact (h₁ M emb _ hembB).trans (h₂ M emb onExit ⟨hne, hstep⟩)

/-! ### Section 4: Explicit Polynomial & Subexponential Asymptotic Absorption -/

lemma nat_const_mul_pow_le_spaceBound (K d n : ℕ) (hn : 2 ≤ n) :
    K * n ^ d ≤ QCSD_spaceBound (K + d) n := by
  unfold QCSD_spaceBound
  have hK2 : K ≤ 2 ^ K := Nat.le_of_lt Nat.lt_two_pow_self
  have h2n : 2 ^ K ≤ n ^ K := Nat.pow_le_pow_left hn K
  calc K * n ^ d ≤ n ^ K * n ^ d := Nat.mul_le_mul_right (n ^ d) (hK2.trans h2n)
    _ = n ^ (K + d) := (Nat.pow_add n K d).symm

lemma qcsd_log2_ge_one {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ QCSD_log2 (n : ℝ) := by
  unfold QCSD_log2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2, one_mul]
  exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)

lemma qcsd_log2_le_div_log2 {n : ℕ} (hn : 2 ≤ n) :
    QCSD_log2 (n : ℝ) ≤ (n : ℝ) / Real.log 2 := by
  unfold QCSD_log2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have h1 := Real.add_one_le_exp (Real.log (n : ℝ))
  rw [Real.exp_log hn_pos] at h1
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hlog2)

lemma qcsd_timeBound_pos (C : ℝ) (hC : 0 ≤ C) {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ QCSD_timeBound C n := by
  unfold QCSD_timeBound
  have hsq : 0 ≤ Real.sqrt (QCSD_log2 (n : ℝ)) := Real.sqrt_nonneg _
  have hexp : 0 ≤ C * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ)) :=
    div_nonneg (mul_nonneg hC (by positivity)) hsq
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (C * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ))) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  have hc := Nat.ceil_mono hpow
  rwa [Nat.ceil_one] at hc

lemma qcsd_timeBound_mono_C {C₁ C₂ : ℝ} (hC : C₁ ≤ C₂) {n : ℕ} :
    QCSD_timeBound C₁ n ≤ QCSD_timeBound C₂ n := by
  unfold QCSD_timeBound
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right hC (by positivity)

lemma qcsd_timeBound_edge_scale {Ct : ℝ} (hCt : 0 ≤ Ct) {Cl n S : ℕ}
    (hn : 2 ≤ n) (hLow : n ≤ S) (hHigh : S ≤ Cl * n) :
    QCSD_timeBound Ct S ≤ QCSD_timeBound (Ct * (Cl : ℝ)) n := by
  unfold QCSD_timeBound
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hlog_ge1 : 1 ≤ QCSD_log2 (n : ℝ) := qcsd_log2_ge_one hn
  have hsq_pos : 0 < Real.sqrt (QCSD_log2 (n : ℝ)) :=
    Real.sqrt_pos_of_pos (by linarith)
  have hlog_mono : QCSD_log2 (n : ℝ) ≤ QCSD_log2 (S : ℝ) := by
    unfold QCSD_log2
    apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num)))
    exact Real.log_le_log (by positivity) (by exact_mod_cast hLow)
  have hsq_mono : Real.sqrt (QCSD_log2 (n : ℝ)) ≤ Real.sqrt (QCSD_log2 (S : ℝ)) :=
    Real.sqrt_le_sqrt hlog_mono
  have hnum : Ct * (S : ℝ) ≤ Ct * (Cl : ℝ) * (n : ℝ) := by
    have hS : (S : ℝ) ≤ (Cl : ℝ) * (n : ℝ) := by exact_mod_cast hHigh
    calc Ct * (S : ℝ) ≤ Ct * ((Cl : ℝ) * (n : ℝ)) := mul_le_mul_of_nonneg_left hS hCt
      _ = Ct * (Cl : ℝ) * (n : ℝ) := (mul_assoc _ _ _).symm
  calc Ct * (S : ℝ) / Real.sqrt (QCSD_log2 (S : ℝ))
      ≤ Ct * (S : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ)) :=
        div_le_div_of_nonneg_left (mul_nonneg hCt (by positivity)) hsq_pos hsq_mono
    _ ≤ Ct * (Cl : ℝ) * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ)) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hsq_pos)

lemma nat_pow_le_two_rpow_subexp (D : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, 2 ≤ n →
      ((n : ℝ) ^ D) ≤ (2 : ℝ) ^ (c * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqlog2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos_of_pos hlog2
  let c₁ : ℝ := 2 / (Real.log 2 * Real.sqrt (Real.log 2))
  refine ⟨(D : ℝ) * c₁, by positivity, fun n hn => ?_⟩
  have hsqn_le : Real.sqrt (n : ℝ) ≤
      (1 / Real.sqrt (Real.log 2)) * ((n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ))) := by
    have hq_pos : 0 < Real.sqrt (QCSD_log2 (n : ℝ)) :=
      Real.sqrt_pos_of_pos (by linarith [qcsd_log2_ge_one hn])
    have hq_le : Real.sqrt (QCSD_log2 (n : ℝ)) ≤ Real.sqrt (n : ℝ) / Real.sqrt (Real.log 2) := by
      rw [← Real.sqrt_div (by positivity)]
      exact Real.sqrt_le_sqrt (qcsd_log2_le_div_log2 hn)
    rw [one_div_mul_eq_div, div_div, le_div_iff₀ (mul_pos hq_pos hsqlog2)]
    have hmul := mul_le_mul_of_nonneg_left hq_le (Real.sqrt_nonneg (n : ℝ))
    rw [← mul_div_assoc, Real.mul_self_sqrt (by positivity), le_div_iff₀ hsqlog2] at hmul
    linarith
  have hn_exp : (n : ℝ) ≤ (2 : ℝ) ^ (c₁ * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ))) := by
    have h1 : Real.sqrt (n : ℝ) ≤ Real.exp (Real.sqrt (n : ℝ)) := by
      linarith [Real.add_one_le_exp (Real.sqrt (n : ℝ))]
    have h2 : (n : ℝ) ≤ Real.exp (2 * Real.sqrt (n : ℝ)) := by
      calc (n : ℝ) = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
            (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ Real.exp (Real.sqrt (n : ℝ)) * Real.exp (Real.sqrt (n : ℝ)) :=
            mul_le_mul h1 h1 (Real.sqrt_nonneg _) (le_of_lt (Real.exp_pos _))
        _ = Real.exp (Real.sqrt (n : ℝ) + Real.sqrt (n : ℝ)) := (Real.exp_add _ _).symm
        _ = Real.exp (2 * Real.sqrt (n : ℝ)) := by ring_nf
    have h3 : Real.exp (2 * Real.sqrt (n : ℝ)) =
        (2 : ℝ) ^ ((2 * Real.sqrt (n : ℝ)) / Real.log 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
          mul_div_cancel₀ _ (ne_of_gt hlog2)]
    have hexp_le : (2 * Real.sqrt (n : ℝ)) / Real.log 2 ≤
        c₁ * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hsqn_le (by positivity : (0 : ℝ) ≤ 2 / Real.log 2)
      calc (2 * Real.sqrt (n : ℝ)) / Real.log 2
          = (2 / Real.log 2) * Real.sqrt (n : ℝ) := by ring
        _ ≤ (2 / Real.log 2) * ((1 / Real.sqrt (Real.log 2)) *
              ((n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ)))) := hmul
        _ = c₁ * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ)) := by dsimp [c₁]; ring
    exact h2.trans (h3.le.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le))
  calc ((n : ℝ) ^ D)
      ≤ ((2 : ℝ) ^ (c₁ * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ)))) ^ D :=
        pow_le_pow_left₀ (by positivity) hn_exp D
    _ = (2 : ℝ) ^ ((c₁ * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ))) * (D : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    _ = (2 : ℝ) ^ (((D : ℝ) * c₁) * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ))) := by
        congr 1; ring

lemma poly_mul_timeBound_le (K d : ℕ) (Ctm CtA : ℝ) (hCtm : 0 ≤ Ctm)
    (Cl : ℕ) :
    ∃ Ct' : ℝ, 0 ≤ Ct' ∧ ∀ (n : ℕ), 2 ≤ n →
      K * n ^ d * (QCSD_timeBound Ctm n + QCSD_timeBound (CtA * (Cl : ℝ)) n + 1) ≤
        QCSD_timeBound Ct' n := by
  let C₀ : ℝ := max Ctm (CtA * (Cl : ℝ))
  have hC₀ : 0 ≤ C₀ := le_max_of_le_left hCtm
  obtain ⟨cPoly, hcPoly, hPoly⟩ := nat_pow_le_two_rpow_subexp (3 * K + d + 2)
  refine ⟨cPoly + C₀, by positivity, fun n hn => ?_⟩
  have ht1 : QCSD_timeBound Ctm n ≤ QCSD_timeBound C₀ n :=
    qcsd_timeBound_mono_C (le_max_left _ _)
  have ht2 : QCSD_timeBound (CtA * (Cl : ℝ)) n ≤ QCSD_timeBound C₀ n :=
    qcsd_timeBound_mono_C (le_max_right _ _)
  have htpos : 1 ≤ QCSD_timeBound C₀ n := qcsd_timeBound_pos C₀ hC₀ hn
  have hsum : QCSD_timeBound Ctm n + QCSD_timeBound (CtA * (Cl : ℝ)) n + 1 ≤
      3 * QCSD_timeBound C₀ n := by omega
  have h3K : 3 * K ≤ n ^ (3 * K + 1) := by
    have h1 : 3 * K + 1 ≤ 2 ^ (3 * K + 1) := Nat.le_of_lt Nat.lt_two_pow_self
    have h2 : 2 ^ (3 * K + 1) ≤ n ^ (3 * K + 1) := Nat.pow_le_pow_left hn _
    omega
  have hnat : K * n ^ d * (QCSD_timeBound Ctm n + QCSD_timeBound (CtA * (Cl : ℝ)) n + 1) ≤
      n ^ (3 * K + d + 1) * QCSD_timeBound C₀ n := by
    calc K * n ^ d * (QCSD_timeBound Ctm n + QCSD_timeBound (CtA * (Cl : ℝ)) n + 1)
        ≤ K * n ^ d * (3 * QCSD_timeBound C₀ n) := Nat.mul_le_mul_left _ hsum
      _ = (3 * K) * n ^ d * QCSD_timeBound C₀ n := by ring
      _ ≤ n ^ (3 * K + 1) * n ^ d * QCSD_timeBound C₀ n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3K)
      _ = n ^ (3 * K + d + 1) * QCSD_timeBound C₀ n := by rw [← Nat.pow_add]; ring_nf
  set f : ℝ := (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ))
  have hf_nonneg : 0 ≤ f := div_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hceil_le : (QCSD_timeBound C₀ n : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ (C₀ * f) := by
    unfold QCSD_timeBound
    rw [show C₀ * (n : ℝ) / Real.sqrt (QCSD_log2 (n : ℝ)) = C₀ * f from mul_div_assoc _ _ _]
    have hexp_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (C₀ * f) := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (mul_nonneg hC₀ hf_nonneg)
    have hlt := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (C₀ * f))).le
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc (Nat.ceil ((2 : ℝ) ^ (C₀ * f)) : ℝ)
        ≤ (2 : ℝ) ^ (C₀ * f) + 1 := hlt
      _ ≤ 2 * (2 : ℝ) ^ (C₀ * f) := by linarith
      _ ≤ (n : ℝ) * (2 : ℝ) ^ (C₀ * f) :=
          mul_le_mul_of_nonneg_right hn2 (by positivity)
  have hreal : ((K * n ^ d * (QCSD_timeBound Ctm n + QCSD_timeBound (CtA * (Cl : ℝ)) n + 1) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((cPoly + C₀) * f) := by
    calc ((K * n ^ d * (QCSD_timeBound Ctm n + QCSD_timeBound (CtA * (Cl : ℝ)) n + 1) : ℕ) : ℝ)
        ≤ ((n ^ (3 * K + d + 1) * QCSD_timeBound C₀ n : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = ((n : ℝ) ^ (3 * K + d + 1)) * (QCSD_timeBound C₀ n : ℝ) := by push_cast; ring
      _ ≤ ((n : ℝ) ^ (3 * K + d + 1)) * ((n : ℝ) * (2 : ℝ) ^ (C₀ * f)) :=
          mul_le_mul_of_nonneg_left hceil_le (by positivity)
      _ = ((n : ℝ) ^ (3 * K + d + 2)) * (2 : ℝ) ^ (C₀ * f) := by ring
      _ ≤ (2 : ℝ) ^ (cPoly * f) * (2 : ℝ) ^ (C₀ * f) := by
          have hp := hPoly n hn
          rw [mul_div_assoc] at hp
          exact mul_le_mul_of_nonneg_right hp (by positivity)
      _ = (2 : ℝ) ^ (cPoly * f + C₀ * f) := (Real.rpow_add (by norm_num) _ _).symm
      _ = (2 : ℝ) ^ ((cPoly + C₀) * f) := by congr 1; ring
  have hceil := Nat.ceil_mono hreal
  rw [Nat.ceil_natCast] at hceil
  simpa [QCSD_timeBound, f, mul_div_assoc] using hceil

/-! ### Section 5: Stateful Loop Combinators, `BlockTape` Workspace & `simTMProg` -/

def mapExitProg {Q E₁ E₂ : Type} (f : E₁ → E₂) (p : Prog Q E₁) : Prog Q E₂ :=
  (p.1, fun q b =>
    match p.2 q b with
    | (Sum.inl q', b', d) => (Sum.inl q', b', d)
    | (Sum.inr e₁, b', d) => (Sum.inr (f e₁), b', d))

lemma ProgRuns_mapExit {Q E₁ E₂ : Type} (f : E₁ → E₂) {p : Prog Q E₁}
    {Sp T : ℕ} {th₁ th₂ : List Bool × ℕ} {e₁ : E₁}
    (h : ProgRuns p Sp T th₁ e₁ th₂) :
    ProgRuns (mapExitProg f p) Sp T th₁ (f e₁) th₂ := by
  intro M emb onExit ⟨hne, hstep⟩
  apply h M emb (onExit ∘ f)
  refine ⟨hne, fun q b => ?_⟩
  rw [hstep q b]
  dsimp [mapExitProg]
  rcases p.2 q b with ⟨q' | e, b', d⟩ <;> rfl

def ifProg {Q₁ Q₂ E : Type} (cond : Bool) (pT : Prog Q₁ E) (pF : Prog Q₂ E) :
    Prog (Q₁ ⊕ Q₂) E :=
  (if cond then Sum.inl pT.1 else Sum.inr pF.1,
   fun s b =>
     match s with
     | Sum.inl q₁ =>
       match pT.2 q₁ b with
       | (Sum.inl q₁', b', d) => (Sum.inl (Sum.inl q₁'), b', d)
       | (Sum.inr e, b', d) => (Sum.inr e, b', d)
     | Sum.inr q₂ =>
       match pF.2 q₂ b with
       | (Sum.inl q₂', b', d) => (Sum.inl (Sum.inr q₂'), b', d)
       | (Sum.inr e, b', d) => (Sum.inr e, b', d))

lemma ProgRuns_if_true {Q₁ Q₂ E : Type} {pT : Prog Q₁ E} {pF : Prog Q₂ E}
    {Sp T : ℕ} {th₁ th₂ : List Bool × ℕ} {e : E}
    (h : ProgRuns pT Sp T th₁ e th₂) :
    ProgRuns (ifProg true pT pF) Sp T th₁ e th₂ := by
  intro M emb onExit ⟨hne, hstep⟩
  change ReachesWithin M Sp T ⟨emb (Sum.inl pT.1), th₁.1, th₁.2⟩ ⟨onExit e, th₂.1, th₂.2⟩
  apply h M (emb ∘ Sum.inl) onExit
  refine ⟨fun q => hne (Sum.inl q), fun q b => ?_⟩
  rw [Function.comp_apply, hstep (Sum.inl q) b]
  dsimp [ifProg]
  rcases pT.2 q b with ⟨q' | e', b', d⟩ <;> rfl

lemma ProgRuns_if_false {Q₁ Q₂ E : Type} {pT : Prog Q₁ E} {pF : Prog Q₂ E}
    {Sp T : ℕ} {th₁ th₂ : List Bool × ℕ} {e : E}
    (h : ProgRuns pF Sp T th₁ e th₂) :
    ProgRuns (ifProg false pT pF) Sp T th₁ e th₂ := by
  intro M emb onExit ⟨hne, hstep⟩
  change ReachesWithin M Sp T ⟨emb (Sum.inr pF.1), th₁.1, th₁.2⟩ ⟨onExit e, th₂.1, th₂.2⟩
  apply h M (emb ∘ Sum.inr) onExit
  refine ⟨fun q => hne (Sum.inr q), fun q b => ?_⟩
  rw [Function.comp_apply, hstep (Sum.inr q) b]
  dsimp [ifProg]
  rcases pF.2 q b with ⟨q' | e', b', d⟩ <;> rfl

def loopStateProg {S Q E : Type} (s₀ : S) (body : S → Prog Q (S ⊕ E)) : Prog (S × Q) E :=
  ((s₀, (body s₀).1), fun sq b =>
    match (body sq.1).2 sq.2 b with
    | (Sum.inl q', b', d) => (Sum.inl (sq.1, q'), b', d)
    | (Sum.inr (Sum.inl s'), b', d) => (Sum.inl (s', (body s').1), b', d)
    | (Sum.inr (Sum.inr e), b', d) => (Sum.inr e, b', d))

lemma ProgRuns_loopState_exit {S Q E : Type} {s₀ : S} {body : S → Prog Q (S ⊕ E)}
    {Sp T : ℕ} {th₁ th₂ : List Bool × ℕ} {e : E}
    (h : ProgRuns (body s₀) Sp T th₁ (Sum.inr e) th₂) :
    ProgRuns (loopStateProg s₀ body) Sp T th₁ e th₂ := by
  intro M emb onExit ⟨hne, hstep⟩
  apply h M (fun q => emb (s₀, q)) (fun r =>
    match r with
    | Sum.inl s' => emb (s', (body s').1)
    | Sum.inr e' => onExit e')
  refine ⟨fun q => hne (s₀, q), fun q b => ?_⟩
  rw [hstep (s₀, q) b]
  dsimp [loopStateProg]
  rcases (body s₀).2 q b with ⟨q' | (s' | e'), b', d⟩ <;> rfl

lemma ProgRuns_loopState_cont {S Q E : Type} {s₀ s₁ : S} {body : S → Prog Q (S ⊕ E)}
    {Sp T₁ T₂ : ℕ} {th₀ th₁ th₂ : List Bool × ℕ} {e : E}
    (h₁ : ProgRuns (body s₀) Sp T₁ th₀ (Sum.inl s₁) th₁)
    (h₂ : ProgRuns (loopStateProg s₁ body) Sp T₂ th₁ e th₂) :
    ProgRuns (loopStateProg s₀ body) Sp (T₁ + T₂) th₀ e th₂ := by
  intro M emb onExit ⟨hne, hstep⟩
  have hemb₁ : EmbedsProg M (body s₀) (fun q => emb (s₀, q)) (fun r =>
      match r with
      | Sum.inl s' => emb (s', (body s').1)
      | Sum.inr e' => onExit e') := by
    refine ⟨fun q => hne (s₀, q), fun q b => ?_⟩
    rw [hstep (s₀, q) b]
    dsimp [loopStateProg]
    rcases (body s₀).2 q b with ⟨q' | (s' | e'), b', d⟩ <;> rfl
  have hemb₂ : EmbedsProg M (loopStateProg s₁ body) emb onExit := by
    refine ⟨hne, fun sq b => ?_⟩
    rw [hstep sq b]
    rfl
  exact (h₁ M _ _ hemb₁).trans (h₂ M emb onExit hemb₂)

lemma tapeEq_write_self (t : List Bool) (h : ℕ) :
    tapeEq (QCSD_tapeWrite2 t h (QCSD_tapeRead t h)) t := by
  intro j
  rw [tapeRead_tapeWrite2]
  split_ifs with hj
  · rw [hj]
  · rfl

def stepDirProg (d : QCSD_HeadDir) : Prog Unit Unit :=
  primProg (fun b => ((), b, d))

lemma ProgRuns_stepRight {Sp : ℕ} {t : List Bool} {h : ℕ}
    (hsp : Nat.max t.length (h + 2) ≤ Sp) :
    ∃ t' : List Bool,
      tapeEq t' t ∧ t'.length = Nat.max t.length (h + 1) ∧
      ProgRuns (stepDirProg QCSD_HeadDir.right) Sp 1 (t, h) () (t', h + 1) := by
  refine ⟨QCSD_tapeWrite2 t h (QCSD_tapeRead t h), tapeEq_write_self t h,
    tapeWrite2_length t h _, ?_⟩
  apply ProgRuns_prim (fun b => ((), b, QCSD_HeadDir.right))
  · simp only [Nat.max_eq_max] at hsp ⊢; omega
  · rw [tapeWrite2_length]; simp only [stepHead, Nat.max_eq_max] at hsp ⊢; omega

lemma ProgRuns_stepLeft {Sp : ℕ} {t : List Bool} {h : ℕ}
    (hsp : Nat.max t.length (h + 1) ≤ Sp) :
    ∃ t' : List Bool,
      tapeEq t' t ∧ t'.length = Nat.max t.length (h + 1) ∧
      ProgRuns (stepDirProg QCSD_HeadDir.left) Sp 1 (t, h) () (t', h - 1) := by
  refine ⟨QCSD_tapeWrite2 t h (QCSD_tapeRead t h), tapeEq_write_self t h,
    tapeWrite2_length t h _, ?_⟩
  apply ProgRuns_prim (fun b => ((), b, QCSD_HeadDir.left))
  · exact hsp
  · rw [tapeWrite2_length]; simp only [stepHead, Nat.max_eq_max] at hsp ⊢; omega

def nopProg : Prog (Unit ⊕ Unit) Unit :=
  seqProg (stepDirProg QCSD_HeadDir.right) (stepDirProg QCSD_HeadDir.left)

lemma ProgRuns_nop {Sp : ℕ} {t : List Bool} {h : ℕ}
    (hsp : Nat.max t.length (h + 2) ≤ Sp) :
    ∃ t' : List Bool,
      tapeEq t' t ∧ t'.length ≤ Nat.max t.length (h + 2) ∧
      ProgRuns nopProg Sp 2 (t, h) () (t', h) := by
  obtain ⟨t₁, ht₁, hlen₁, hr₁⟩ := ProgRuns_stepRight (t := t) (h := h) hsp
  have hsp₂ : Nat.max t₁.length ((h + 1) + 1) ≤ Sp := by
    rw [hlen₁]; simp only [Nat.max_eq_max] at hsp ⊢; omega
  obtain ⟨t₂, ht₂, hlen₂, hr₂⟩ := ProgRuns_stepLeft (t := t₁) (h := h + 1) hsp₂
  refine ⟨t₂, tapeEq_trans ht₂ ht₁, ?_, ?_⟩
  · rw [hlen₂, hlen₁]; simp only [Nat.max_eq_max]; omega
  · have hsub : (h + 1) - 1 = h := by omega
    rw [hsub] at hr₂
    exact ProgRuns_seq hr₁ hr₂

def moveDirPosProg (d : QCSD_HeadDir) (k : ℕ) : Prog (Fin (k + 1)) Unit :=
  (⟨0, Nat.zero_lt_succ k⟩, fun idx b =>
    if hlt : idx.val + 1 < k + 1 then
      (Sum.inl ⟨idx.val + 1, hlt⟩, b, d)
    else
      (Sum.inr (), b, d))

lemma ProgRuns_moveRightPos (k : ℕ) {Sp : ℕ} {t : List Bool} {h : ℕ}
    (hsp : Nat.max t.length (h + k + 2) ≤ Sp) :
    ∃ t' : List Bool,
      tapeEq t' t ∧ t'.length ≤ Nat.max t.length (h + k + 1) ∧
      ProgRuns (moveDirPosProg QCSD_HeadDir.right k) Sp (k + 1) (t, h) () (t', h + k + 1) := by
  have gen : ∀ (r : ℕ) (hr : r ≤ k) (t₀ : List Bool),
      tapeEq t₀ t →
      t₀.length ≤ Nat.max t.length (h + (k - r)) →
      ∃ t' : List Bool,
        tapeEq t' t ∧ t'.length ≤ Nat.max t.length (h + k + 1) ∧
        ∀ (M : QCSD_DetTM) (emb : Fin (k + 1) → M.Q) (onExit : Unit → M.Q),
          EmbedsProg M (moveDirPosProg QCSD_HeadDir.right k) emb onExit →
          ReachesWithin M Sp (r + 1)
            ⟨emb ⟨k - r, by omega⟩, t₀, h + (k - r)⟩
            ⟨onExit (), t', h + k + 1⟩ := by
    intro r
    induction r with
    | zero =>
      intro _ t₀ ht₀ hlen₀
      let t' := QCSD_tapeWrite2 t₀ (h + k) (QCSD_tapeRead t₀ (h + k))
      refine ⟨t', tapeEq_trans (tapeEq_write_self t₀ (h + k)) ht₀, ?_, ?_⟩
      · rw [tapeWrite2_length]; simp only [Nat.max_eq_max, Nat.sub_zero] at hlen₀ ⊢; omega
      · intro M emb onExit ⟨hne, hstep⟩
        simp only [Nat.sub_zero, Nat.zero_add]
        apply ReachesWithin.step (hne ⟨k, by omega⟩)
        · rw [hstep ⟨k, by omega⟩ (QCSD_tapeRead t₀ (h + k))]
          simp [moveDirPosProg, t', stepHead]
        · simp only [QCSD_spaceUse2, Nat.max_eq_max, Nat.sub_zero] at hlen₀ hsp ⊢; omega
        · simp only [QCSD_spaceUse2, t', tapeWrite2_length, Nat.max_eq_max] at hlen₀ hsp ⊢; omega
    | succ r ih =>
      intro hr t₀ ht₀ hlen₀
      let pos := h + (k - (r + 1))
      let t₁ := QCSD_tapeWrite2 t₀ pos (QCSD_tapeRead t₀ pos)
      have ht₁ : tapeEq t₁ t := tapeEq_trans (tapeEq_write_self t₀ pos) ht₀
      have hpos_eq : pos + 1 = h + (k - r) := by dsimp [pos]; omega
      have hlen₁ : t₁.length ≤ Nat.max t.length (h + (k - r)) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, pos] at hlen₀ ⊢; omega
      obtain ⟨t', ht', hlen', hreach⟩ := ih (by omega) t₁ ht₁ hlen₁
      refine ⟨t', ht', hlen', fun M emb onExit hemb => ?_⟩
      obtain ⟨hne, hstep⟩ := hemb
      have h1 : ReachesWithin M Sp 1
          ⟨emb ⟨k - (r + 1), by omega⟩, t₀, pos⟩
          ⟨emb ⟨k - r, by omega⟩, t₁, h + (k - r)⟩ := by
        apply ReachesWithin.step (hne ⟨k - (r + 1), by omega⟩)
        · rw [hstep ⟨k - (r + 1), by omega⟩ (QCSD_tapeRead t₀ pos)]
          have hlt : (k - (r + 1)) + 1 < k + 1 := by omega
          have hidx : (⟨(k - (r + 1)) + 1, hlt⟩ : Fin (k + 1)) = ⟨k - r, by omega⟩ := by
            ext; dsimp; omega
          simp only [moveDirPosProg, hlt, ↓reduceDIte, hidx, t₁, stepHead, hpos_eq]
        · simp only [QCSD_spaceUse2, Nat.max_eq_max, pos] at hlen₀ hsp ⊢; omega
        · simp only [QCSD_spaceUse2, Nat.max_eq_max] at hlen₁ hsp ⊢; omega
      have h2 := hreach M emb onExit ⟨hne, hstep⟩
      have h12 := h1.trans h2
      rwa [Nat.add_comm 1 (r + 1)] at h12
  obtain ⟨t', ht', hlen', hreach⟩ := gen k (Nat.le_refl k) t (tapeEq_refl t) (by
    simp only [Nat.sub_self, Nat.add_zero, Nat.max_eq_max]; omega)
  refine ⟨t', ht', hlen', fun M emb onExit hemb => ?_⟩
  have hr := hreach M emb onExit hemb
  have hz : (⟨k - k, by omega⟩ : Fin (k + 1)) = ⟨0, Nat.zero_lt_succ k⟩ := by ext; simp
  have hh : h + (k - k) = h := by omega
  rw [hz, hh] at hr
  exact hr

lemma ProgRuns_moveLeftPos (k : ℕ) {Sp : ℕ} {t : List Bool} {h : ℕ}
    (hsp : Nat.max t.length (h + 1) ≤ Sp) :
    ∃ t' : List Bool,
      tapeEq t' t ∧ t'.length ≤ Nat.max t.length (h + 1) ∧
      ProgRuns (moveDirPosProg QCSD_HeadDir.left k) Sp (k + 1) (t, h) () (t', h - (k + 1)) := by
  have gen : ∀ (r : ℕ) (hr : r ≤ k) (t₀ : List Bool),
      tapeEq t₀ t →
      t₀.length ≤ Nat.max t.length (h + 1) →
      ∃ t' : List Bool,
        tapeEq t' t ∧ t'.length ≤ Nat.max t.length (h + 1) ∧
        ∀ (M : QCSD_DetTM) (emb : Fin (k + 1) → M.Q) (onExit : Unit → M.Q),
          EmbedsProg M (moveDirPosProg QCSD_HeadDir.left k) emb onExit →
          ReachesWithin M Sp (r + 1)
            ⟨emb ⟨k - r, by omega⟩, t₀, h - (k - r)⟩
            ⟨onExit (), t', h - (k + 1)⟩ := by
    intro r
    induction r with
    | zero =>
      intro _ t₀ ht₀ hlen₀
      let pos := h - k
      let t' := QCSD_tapeWrite2 t₀ pos (QCSD_tapeRead t₀ pos)
      refine ⟨t', tapeEq_trans (tapeEq_write_self t₀ pos) ht₀, ?_, ?_⟩
      · rw [tapeWrite2_length]; simp only [Nat.max_eq_max, pos] at hlen₀ ⊢; omega
      · intro M emb onExit ⟨hne, hstep⟩
        simp only [Nat.sub_zero, Nat.zero_add]
        apply ReachesWithin.step (hne ⟨k, by omega⟩)
        · rw [hstep ⟨k, by omega⟩ (QCSD_tapeRead t₀ pos)]
          have hsub : pos - 1 = h - (k + 1) := by dsimp [pos]; omega
          simp [moveDirPosProg, t', pos, stepHead, hsub]
        · simp only [QCSD_spaceUse2, Nat.max_eq_max] at hlen₀ hsp ⊢; omega
        · simp only [QCSD_spaceUse2, t', tapeWrite2_length, Nat.max_eq_max, pos] at hlen₀ hsp ⊢; omega
    | succ r ih =>
      intro hr t₀ ht₀ hlen₀
      let pos := h - (k - (r + 1))
      let t₁ := QCSD_tapeWrite2 t₀ pos (QCSD_tapeRead t₀ pos)
      have ht₁ : tapeEq t₁ t := tapeEq_trans (tapeEq_write_self t₀ pos) ht₀
      have hpos_eq : pos - 1 = h - (k - r) := by dsimp [pos]; omega
      have hlen₁ : t₁.length ≤ Nat.max t.length (h + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, pos] at hlen₀ ⊢; omega
      obtain ⟨t', ht', hlen', hreach⟩ := ih (by omega) t₁ ht₁ hlen₁
      refine ⟨t', ht', hlen', fun M emb onExit hemb => ?_⟩
      obtain ⟨hne, hstep⟩ := hemb
      have h1 : ReachesWithin M Sp 1
          ⟨emb ⟨k - (r + 1), by omega⟩, t₀, pos⟩
          ⟨emb ⟨k - r, by omega⟩, t₁, h - (k - r)⟩ := by
        apply ReachesWithin.step (hne ⟨k - (r + 1), by omega⟩)
        · rw [hstep ⟨k - (r + 1), by omega⟩ (QCSD_tapeRead t₀ pos)]
          have hlt : (k - (r + 1)) + 1 < k + 1 := by omega
          have hidx : (⟨(k - (r + 1)) + 1, hlt⟩ : Fin (k + 1)) = ⟨k - r, by omega⟩ := by
            ext; dsimp; omega
          simp only [moveDirPosProg, hlt, ↓reduceDIte, hidx, t₁, stepHead, hpos_eq]
        · simp only [QCSD_spaceUse2, Nat.max_eq_max, pos] at hlen₀ hsp ⊢; omega
        · simp only [QCSD_spaceUse2, Nat.max_eq_max] at hlen₁ hsp ⊢; omega
      have h2 := hreach M emb onExit ⟨hne, hstep⟩
      have h12 := h1.trans h2
      rwa [Nat.add_comm 1 (r + 1)] at h12
  obtain ⟨t', ht', hlen', hreach⟩ := gen k (Nat.le_refl k) t (tapeEq_refl t) (Nat.le_max_left _ _)
  refine ⟨t', ht', hlen', fun M emb onExit hemb => ?_⟩
  have hr := hreach M emb onExit hemb
  have hz : (⟨k - k, by omega⟩ : Fin (k + 1)) = ⟨0, Nat.zero_lt_succ k⟩ := by ext; simp
  have hh : h - (k - k) = h := by omega
  rw [hz, hh] at hr
  exact hr

def slotVal (allocLen : ℕ) (inBits : List Bool) (nLen : ℕ)
    (cBits preBits vSub : List Bool) (rMark wMark : Option ℕ) (i s : ℕ) : Bool :=
  if i < allocLen then
    match s with
    | 0 => true
    | 1 => decide (i = 0)
    | 2 => decide (i < inBits.length)
    | 3 => QCSD_tapeRead inBits i
    | 4 => decide (i < nLen)
    | 5 => QCSD_tapeRead cBits i
    | 6 => decide (i < preBits.length)
    | 7 => QCSD_tapeRead preBits i
    | 8 => QCSD_tapeRead vSub i
    | 9 => decide (rMark = some i)
    | 10 => decide (wMark = some i)
    | _ => false
  else false

def BlockTape (base allocLen : ℕ) (inBits : List Bool) (nLen : ℕ)
    (cBits preBits vSub : List Bool) (rMark wMark : Option ℕ) (tape : List Bool) : Prop :=
  1 ≤ allocLen ∧
  inBits.length ≤ allocLen ∧
  nLen ≤ allocLen ∧
  cBits.length ≤ nLen ∧
  preBits.length ≤ nLen ∧
  vSub.length ≤ allocLen ∧
  (∀ r, rMark = some r → r < allocLen) ∧
  (∀ w, wMark = some w → w < allocLen) ∧
  tape.length ≤ base + 11 * allocLen ∧
  (∀ p < base, QCSD_tapeRead tape p = false) ∧
  (∀ p, base ≤ p →
    QCSD_tapeRead tape p =
      slotVal allocLen inBits nLen cBits preBits vSub rMark wMark
        ((p - base) / 11) ((p - base) % 11))

lemma BlockTape_of_tapeEq {base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark wMark : Option ℕ} {t₁ t₂ : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark t₁)
    (heq : tapeEq t₂ t₁) (hlen : t₂.length ≤ base + 11 * allocLen) :
    BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark t₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, hlow, hhigh⟩ := hbt
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, hlen,
    fun p hp => (heq p).trans (hlow p hp),
    fun p hp => (heq p).trans (hhigh p hp)⟩

lemma BlockTape_read_slot {base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark wMark : Option ℕ} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape)
    (i : ℕ) (s : Fin 11) :
    QCSD_tapeRead tape (base + 11 * i + s.val) =
      slotVal allocLen inBits nLen cBits preBits vSub rMark wMark i s.val := by
  have hp : base ≤ base + 11 * i + s.val := by omega
  rw [hbt.2.2.2.2.2.2.2.2.2.2 _ hp]
  have hdiv : (base + 11 * i + s.val - base) / 11 = i := by
    have hs := s.isLt; omega
  have hmod : (base + 11 * i + s.val - base) % 11 = s.val := by
    have hs := s.isLt; omega
  rw [hdiv, hmod]

def accessSlotStep {E : Type} (s : Fin 11) (upd : Bool → E × Bool)
    (st : Fin 20 × E) (b : Bool) : ((Fin 20 × E) ⊕ E) × Bool × QCSD_HeadDir :=
  if h10 : st.1.val < 10 then
    let res : E × Bool := if st.1.val = s.val then upd b else (st.2, b)
    (Sum.inl (⟨st.1.val + 1, by omega⟩, res.1), res.2, QCSD_HeadDir.right)
  else if st.1.val = 10 then
    let res : E × Bool := if 10 = s.val then upd b else (st.2, b)
    (Sum.inl (⟨11, by decide⟩, res.1), res.2, QCSD_HeadDir.left)
  else if hlt : st.1.val < 19 then
    (Sum.inl (⟨st.1.val + 1, by omega⟩, st.2), b, QCSD_HeadDir.left)
  else
    (Sum.inr st.2, b, QCSD_HeadDir.left)

def accessSlotProg {E : Type} (defaultE : E) (s : Fin 11) (upd : Bool → E × Bool) :
    Prog (Fin 20 × E) E :=
  ((⟨0, by decide⟩, defaultE), accessSlotStep s upd)

lemma ProgRuns_accessSlot {E : Type} (defaultE : E) (s : Fin 11) (upd : Bool → E × Bool)
    {Sp : ℕ} {t : List Bool} {base : ℕ}
    (hsp : Nat.max t.length (base + 11) ≤ Sp) :
    let pos := base + s.val
    let res := upd (QCSD_tapeRead t pos)
    ∃ t' : List Bool,
      (∀ p, QCSD_tapeRead t' p = if p = pos then res.2 else QCSD_tapeRead t p) ∧
      t'.length ≤ Nat.max t.length (base + 11) ∧
      ProgRuns (accessSlotProg defaultE s upd) Sp 20 (t, base) res.1 (t', base) := by
  let pos := base + s.val
  let res := upd (QCSD_tapeRead t pos)
  let targetRead (p : ℕ) : Bool := if p = pos then res.2 else QCSD_tapeRead t p
  -- Phase A: steps 0..9 moving right from base + 0 to base + 10
  have phaseA : ∀ (r : ℕ) (hr : r ≤ 10) (t₀ : List Bool) (acc : E),
      t₀.length ≤ Nat.max t.length (base + 11) →
      (∀ p, QCSD_tapeRead t₀ p = if p < base + r then targetRead p else QCSD_tapeRead t p) →
      (s.val < r → acc = res.1) →
      ∃ t₁ : List Bool, ∃ acc₁ : E,
        t₁.length ≤ Nat.max t.length (base + 11) ∧
        (∀ p, QCSD_tapeRead t₁ p = if p < base + 10 then targetRead p else QCSD_tapeRead t p) ∧
        (s.val < 10 → acc₁ = res.1) ∧
        ∀ (M : QCSD_DetTM) (emb : Fin 20 × E → M.Q) (onExit : E → M.Q),
          EmbedsProg M (accessSlotProg defaultE s upd) emb onExit →
          ReachesWithin M Sp (10 - r)
            ⟨emb (⟨r, by omega⟩, acc), t₀, base + r⟩
            ⟨emb (⟨10, by decide⟩, acc₁), t₁, base + 10⟩ := by
    intro r hr
    induction hrem : 10 - r generalizing r with
    | zero =>
      obtain rfl : r = 10 := by omega
      intro t₀ acc hlen hread hacc
      refine ⟨t₀, acc, hlen, hread, hacc, fun M emb _ _ => ReachesWithin.refl ?_⟩
      simp only [QCSD_spaceUse2, Nat.max_eq_max] at hsp hlen ⊢; omega
    | succ d ih =>
      have hr10 : r < 10 := by omega
      intro t₀ acc hlen hread hacc
      let cur := base + r
      have hcur_read : QCSD_tapeRead t₀ cur = QCSD_tapeRead t cur := by
        rw [hread cur]; simp [cur]
      let stepRes : E × Bool := if r = s.val then upd (QCSD_tapeRead t₀ cur) else (acc, QCSD_tapeRead t₀ cur)
      let t_next := QCSD_tapeWrite2 t₀ cur stepRes.2
      have hlen_next : t_next.length ≤ Nat.max t.length (base + 11) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, cur] at hlen ⊢; omega
      have hread_next : ∀ p, QCSD_tapeRead t_next p =
          if p < base + (r + 1) then targetRead p else QCSD_tapeRead t p := by
        intro p
        rw [tapeRead_tapeWrite2, hread p]
        by_cases hp : p = cur
        · subst hp
          have hlt : cur < base + (r + 1) := by dsimp [cur]; omega
          rw [ite_eq_left rfl, ite_eq_left hlt]
          dsimp [stepRes, targetRead, pos, res, cur]
          rw [hcur_read]
          by_cases hrs : r = s.val
          · subst hrs
            rw [ite_eq_left rfl, ite_eq_left (show cur = pos from rfl)]
          · have hne : cur ≠ pos := by dsimp [cur, pos]; omega
            rw [ite_eq_right hrs, ite_eq_right hne]
        · simp only [hp, ↓reduceIte]
          by_cases hlt1 : p < base + r
          · have hlt2 : p < base + (r + 1) := by omega
            simp [hlt1, hlt2]
          · have hlt2 : ¬ p < base + (r + 1) := by dsimp [cur] at hp; omega
            simp [hlt1, hlt2]
      have hacc_next : s.val < r + 1 → stepRes.1 = res.1 := by
        intro hs_lt
        dsimp [stepRes]
        by_cases hrs : r = s.val
        · subst hrs; rw [ite_eq_left rfl, hcur_read]
        · rw [ite_eq_right hrs]; exact hacc (by omega)
      obtain ⟨t₁, acc₁, hlen₁, hread₁, hacc₁, hreach₁⟩ :=
        ih (r + 1) (by omega) (by omega) t_next stepRes.1 hlen_next hread_next hacc_next
      refine ⟨t₁, acc₁, hlen₁, hread₁, hacc₁, fun M emb onExit hemb => ?_⟩
      obtain ⟨hne, hstep⟩ := hemb
      have h1 : ReachesWithin M Sp 1
          ⟨emb (⟨r, by omega⟩, acc), t₀, base + r⟩
          ⟨emb (⟨r + 1, by omega⟩, stepRes.1), t_next, base + (r + 1)⟩ := by
        apply ReachesWithin.step (hne _)
        · rw [hstep (⟨r, by omega⟩, acc) (QCSD_tapeRead t₀ cur)]
          dsimp [accessSlotProg, accessSlotStep]
          rw [dite_eq_left hr10]
          dsimp [stepRes, t_next, stepHead, cur]
          rw [Nat.add_assoc]
        · simp only [QCSD_spaceUse2, Nat.max_eq_max] at hlen hsp ⊢; omega
        · simp only [QCSD_spaceUse2, Nat.max_eq_max] at hlen_next hsp ⊢; omega
      have h2 := hreach₁ M emb onExit ⟨hne, hstep⟩
      have h12 := h1.trans h2
      rwa [show 1 + d = d + 1 by omega] at h12
  -- Phase B: steps 11..19 moving left from base + 9 down to base + 0
  have phaseB : ∀ (r : ℕ) (hr11 : 11 ≤ r) (hr19 : r ≤ 19) (t₀ : List Bool),
      t₀.length ≤ Nat.max t.length (base + 11) →
      (∀ p, QCSD_tapeRead t₀ p = targetRead p) →
      ∃ t₂ : List Bool,
        t₂.length ≤ Nat.max t.length (base + 11) ∧
        (∀ p, QCSD_tapeRead t₂ p = targetRead p) ∧
        ∀ (M : QCSD_DetTM) (emb : Fin 20 × E → M.Q) (onExit : E → M.Q),
          EmbedsProg M (accessSlotProg defaultE s upd) emb onExit →
          ReachesWithin M Sp (20 - r)
            ⟨emb (⟨r, by omega⟩, res.1), t₀, base + (20 - r)⟩
            ⟨onExit res.1, t₂, base⟩ := by
    intro r hr11 hr19
    induction hrem : 19 - r generalizing r with
    | zero =>
      obtain rfl : r = 19 := by omega
      intro t₀ hlen hread
      let cur := base + 1
      let t₂ := QCSD_tapeWrite2 t₀ cur (QCSD_tapeRead t₀ cur)
      refine ⟨t₂, ?_, ?_, fun M emb onExit ⟨hne, hstep⟩ => ?_⟩
      · rw [tapeWrite2_length]; simp only [Nat.max_eq_max, cur] at hlen ⊢; omega
      · intro p; rw [tapeEq_write_self t₀ cur p, hread p]
      · simp only [show 20 - 19 = 1 by decide]
        apply ReachesWithin.step (hne _)
        · rw [hstep (⟨19, by decide⟩, res.1) (QCSD_tapeRead t₀ cur)]
          simp [accessSlotProg, accessSlotStep, t₂, cur, stepHead]
        · simp only [QCSD_spaceUse2, Nat.max_eq_max] at hlen hsp ⊢; omega
        · simp only [QCSD_spaceUse2, t₂, tapeWrite2_length, Nat.max_eq_max, cur] at hlen hsp ⊢; omega
    | succ d ih =>
      have hrlt : r < 19 := by omega
      intro t₀ hlen hread
      let cur := base + (20 - r)
      let t_next := QCSD_tapeWrite2 t₀ cur (QCSD_tapeRead t₀ cur)
      have hlen_next : t_next.length ≤ Nat.max t.length (base + 11) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, cur] at hlen ⊢; omega
      have hread_next : ∀ p, QCSD_tapeRead t_next p = targetRead p :=
        fun p => (tapeEq_write_self t₀ cur p).trans (hread p)
      obtain ⟨t₂, hlen₂, hread₂, hreach₂⟩ :=
        ih (r + 1) (by omega) (by omega) (by omega) t_next hlen_next hread_next
      refine ⟨t₂, hlen₂, hread₂, fun M emb onExit hemb => ?_⟩
      obtain ⟨hne, hstep⟩ := hemb
      have h1 : ReachesWithin M Sp 1
          ⟨emb (⟨r, by omega⟩, res.1), t₀, cur⟩
          ⟨emb (⟨r + 1, by omega⟩, res.1), t_next, base + (20 - (r + 1))⟩ := by
        apply ReachesWithin.step (hne _)
        · rw [hstep (⟨r, by omega⟩, res.1) (QCSD_tapeRead t₀ cur)]
          have hn10 : ¬ r < 10 := by omega
          have hne10 : r ≠ 10 := by omega
          simp only [accessSlotProg, accessSlotStep, hn10, hne10, hrlt, ↓reduceIte, ↓reduceDIte,
            t_next, stepHead, cur]
          congr 2; omega
        · simp only [QCSD_spaceUse2, Nat.max_eq_max, cur] at hlen hsp ⊢; omega
        · simp only [QCSD_spaceUse2, Nat.max_eq_max] at hlen_next hsp ⊢; omega
      have h2 := hreach₂ M emb onExit ⟨hne, hstep⟩
      have h12 := h1.trans h2
      rwa [show 1 + (20 - (r + 1)) = 20 - r by omega] at h12
  -- Stitch Phase A (0..10), step 10, and Phase B (11..19)
  obtain ⟨t₁, acc₁, hlen₁, hread₁, hacc₁, hreachA⟩ :=
    phaseA 0 (by decide) t defaultE (Nat.le_max_left _ _)
      (fun p => by
        simp only [Nat.add_zero]
        split_ifs with hp
        · have hne : p ≠ pos := by dsimp [pos]; omega
          simp [targetRead, hne]
        · rfl) (fun h => by omega)
  let cur10 := base + 10
  have hcur10 : QCSD_tapeRead t₁ cur10 = QCSD_tapeRead t cur10 := by
    rw [hread₁ cur10]; simp [cur10]
  let res10 : E × Bool := if 10 = s.val then upd (QCSD_tapeRead t₁ cur10) else (acc₁, QCSD_tapeRead t₁ cur10)
  have hres10_fst : res10.1 = res.1 := by
    dsimp [res10]
    by_cases h10 : 10 = s.val
    · rw [ite_eq_left h10, hcur10]
      dsimp [res, pos, cur10]; rw [← h10]
    · rw [ite_eq_right h10]
      exact hacc₁ (by have := s.isLt; omega)
  let t₁₀ := QCSD_tapeWrite2 t₁ cur10 res10.2
  have hlen₁₀ : t₁₀.length ≤ Nat.max t.length (base + 11) := by
    rw [tapeWrite2_length]; simp only [Nat.max_eq_max, cur10] at hlen₁ ⊢; omega
  have hread₁₀ : ∀ p, QCSD_tapeRead t₁₀ p = targetRead p := by
    intro p
    rw [tapeRead_tapeWrite2, hread₁ p]
    by_cases hp : p = cur10
    · subst hp
      rw [ite_eq_left rfl]
      dsimp [res10, targetRead, pos, res, cur10]
      rw [hcur10]
      by_cases h10 : 10 = s.val
      · have hcp : cur10 = pos := by dsimp [cur10, pos]; omega
        rw [ite_eq_left h10, ite_eq_left hcp, hcp]
      · have hcp : cur10 ≠ pos := by dsimp [cur10, pos]; omega
        rw [ite_eq_right h10, ite_eq_right hcp]
    · simp only [hp, ↓reduceIte]
      by_cases hlt : p < base + 10
      · simp [hlt]
      · have hne : p ≠ pos := by
          have hs := s.isLt
          dsimp [pos, cur10] at hp ⊢
          omega
        simp [hlt, targetRead, hne]
  obtain ⟨t₂, hlen₂, hread₂, hreachB⟩ :=
    phaseB 11 (by decide) (by decide) t₁₀ hlen₁₀ hread₁₀
  refine ⟨t₂, hread₂, hlen₂, fun M emb onExit hemb => ?_⟩
  obtain ⟨hne, hstep⟩ := hemb
  have hA := hreachA M emb onExit ⟨hne, hstep⟩
  rw [Nat.sub_zero, Nat.add_zero] at hA
  have hStep10 : ReachesWithin M Sp 1
      ⟨emb (⟨10, by decide⟩, acc₁), t₁, cur10⟩
      ⟨emb (⟨11, by decide⟩, res.1), t₁₀, base + 9⟩ := by
    apply ReachesWithin.step (hne _)
    · rw [hstep (⟨10, by decide⟩, acc₁) (QCSD_tapeRead t₁ cur10)]
      dsimp [accessSlotProg, accessSlotStep]
      rw [hres10_fst]
      dsimp [t₁₀, res10, stepHead, cur10]
    · simp only [QCSD_spaceUse2, Nat.max_eq_max, cur10] at hlen₁ hsp ⊢; omega
    · simp only [QCSD_spaceUse2, Nat.max_eq_max] at hlen₁₀ hsp ⊢; omega
  have hB := hreachB M emb onExit ⟨hne, hstep⟩
  have hAll := (hA.trans hStep10).trans hB
  dsimp [accessSlotProg]
  exact hAll

def readSlotProg (s : Fin 11) : Prog (Fin 20 × Bool) Bool :=
  accessSlotProg false s (fun b => (b, b))

def writeSlotProg (s : Fin 11) (val : Bool) : Prog (Fin 20 × Unit) Unit :=
  accessSlotProg () s (fun _ => ((), val))

lemma ProgRuns_readSlot (s : Fin 11) {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark wMark : Option ℕ} {tape : List Bool} {i : ℕ}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape)
    (hi : i < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape' ∧
      ProgRuns (readSlotProg s) Sp 20 (tape, base + 11 * i)
        (slotVal allocLen inBits nLen cBits preBits vSub rMark wMark i s.val)
        (tape', base + 11 * i) := by
  have hlen : tape.length ≤ base + 11 * allocLen := hbt.2.2.2.2.2.2.2.2.1
  have hsp' : Nat.max tape.length ((base + 11 * i) + 11) ≤ Sp := by
    simp only [Nat.max_eq_max]; omega
  obtain ⟨t', hread', hlen', hrun⟩ :=
    ProgRuns_accessSlot false s (fun b => (b, b)) (t := tape) (base := base + 11 * i) hsp'
  have heq : tapeEq t' tape := by
    intro p; rw [hread']; split_ifs with hp <;> simp [hp]
  have hlen2 : t'.length ≤ base + 11 * allocLen := by
    simp only [Nat.max_eq_max] at hlen' ⊢; omega
  refine ⟨t', BlockTape_of_tapeEq hbt heq hlen2, ?_⟩
  have hval := BlockTape_read_slot hbt i s
  simpa [readSlotProg, hval] using hrun

def moveBlockLeftProg : Prog ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ Fin 11))) Unit :=
  bindProg (readSlotProg ⟨1, by decide⟩) (fun isOrig =>
    ifProg isOrig nopProg (moveDirPosProg QCSD_HeadDir.left 10))

lemma ProgRuns_moveBlockLeft {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark wMark : Option ℕ} {tape : List Bool} {i : ℕ}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape)
    (hi : i < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape' ∧
      ProgRuns moveBlockLeftProg Sp 31 (tape, base + 11 * i) () (tape', base + 11 * (i - 1)) := by
  obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨1, by decide⟩ hbt hi hsp
  have hsv : slotVal allocLen inBits nLen cBits preBits vSub rMark wMark i 1 = decide (i = 0) := by
    simp [slotVal, hi]
  rw [hsv] at hr₁
  have hlen₁ : t₁.length ≤ base + 11 * allocLen := hbt₁.2.2.2.2.2.2.2.2.1
  by_cases hi0 : i = 0
  · subst hi0
    simp only [decide_true] at hr₁
    have hsp_nop : Nat.max t₁.length (base + 11 * 0 + 2) ≤ Sp := by
      simp only [Nat.max_eq_max]; omega
    obtain ⟨t₂, heq₂, hlen₂, hr₂⟩ := ProgRuns_nop (t := t₁) (h := base + 11 * 0) hsp_nop
    have hbt₂ : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark t₂ :=
      BlockTape_of_tapeEq hbt₁ heq₂ (by simp only [Nat.max_eq_max] at hlen₂ ⊢; omega)
    refine ⟨t₂, hbt₂, ?_⟩
    exact (ProgRuns_bind hr₁ (ProgRuns_if_true hr₂)).mono (Nat.le_refl Sp) (by decide)
  · have hd : decide (i = 0) = false := decide_eq_false hi0
    rw [hd] at hr₁
    have hsp_l : Nat.max t₁.length (base + 11 * i + 1) ≤ Sp := by
      simp only [Nat.max_eq_max]; omega
    obtain ⟨t₂, heq₂, hlen₂, hr₂⟩ := ProgRuns_moveLeftPos 10 (t := t₁) (h := base + 11 * i) hsp_l
    have hbt₂ : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark t₂ :=
      BlockTape_of_tapeEq hbt₁ heq₂ (by simp only [Nat.max_eq_max] at hlen₂ ⊢; omega)
    have hpos : base + 11 * i - (10 + 1) = base + 11 * (i - 1) := by omega
    rw [hpos] at hr₂
    refine ⟨t₂, hbt₂, ?_⟩
    exact ProgRuns_bind (k := fun isOrig => ifProg isOrig nopProg (moveDirPosProg QCSD_HeadDir.left 10))
      hr₁ (ProgRuns_if_false hr₂)

def moveBlockRightProg :
    Prog (Fin 11 ⊕ ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ (Fin 20 × Unit))))) Unit :=
  seqProg (moveDirPosProg QCSD_HeadDir.right 10)
    (bindProg (accessSlotProg false ⟨0, by decide⟩ (fun b => (b, b)))
      (fun isInit =>
        ifProg isInit nopProg (accessSlotProg () ⟨0, by decide⟩ (fun _ => ((), true)))))

lemma ProgRuns_moveBlockRight {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark wMark : Option ℕ} {tape : List Bool} {i : ℕ}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape)
    (hi : i < allocLen)
    (hsp : base + 11 * Nat.max allocLen (i + 2) ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base (Nat.max allocLen (i + 2)) inBits nLen cBits preBits vSub rMark wMark tape' ∧
      ProgRuns moveBlockRightProg Sp 51 (tape, base + 11 * i) () (tape', base + 11 * (i + 1)) := by
  have hlen : tape.length ≤ base + 11 * allocLen := hbt.2.2.2.2.2.2.2.2.1
  have hsp₁ : Nat.max tape.length (base + 11 * i + 10 + 2) ≤ Sp := by
    simp only [Nat.max_eq_max] at hsp ⊢; omega
  obtain ⟨t₁, heq₁, hlen₁, hr₁⟩ := ProgRuns_moveRightPos 10 (t := tape) (h := base + 11 * i) hsp₁
  have hpos : base + 11 * i + 10 + 1 = base + 11 * (i + 1) := by omega
  rw [hpos] at hr₁ hlen₁
  have hsp₂ : Nat.max t₁.length (base + 11 * (i + 1) + 11) ≤ Sp := by
    simp only [Nat.max_eq_max] at hsp hlen₁ ⊢; omega
  obtain ⟨t₂, hread₂, hlen₂, hr₂⟩ :=
    ProgRuns_accessSlot false ⟨0, by decide⟩ (fun b => (b, b))
      (t := t₁) (base := base + 11 * (i + 1)) hsp₂
  have heq₂ : tapeEq t₂ tape := by
    intro p; rw [hread₂]; split_ifs with hp <;> [subst hp; skip] <;> exact heq₁ _
  have hb0_eq : QCSD_tapeRead t₁ (base + 11 * (i + 1) + 0) = decide (i + 1 < allocLen) := by
    rw [heq₁, BlockTape_read_slot hbt (i + 1) ⟨0, by decide⟩]
    unfold slotVal
    split_ifs with hlt <;> simp [hlt]
  dsimp only at hr₂
  rw [hb0_eq] at hr₂
  by_cases hlt : i + 1 < allocLen
  · have hmax : Nat.max allocLen (i + 2) = allocLen := by simp only [Nat.max_eq_max]; omega
    rw [decide_eq_true hlt] at hr₂
    have hsp₃ : Nat.max t₂.length (base + 11 * (i + 1) + 2) ≤ Sp := by
      simp only [Nat.max_eq_max] at hsp hlen hlen₁ hlen₂ ⊢; omega
    obtain ⟨t₃, heq₃, hlen₃, hr₃⟩ := ProgRuns_nop (t := t₂) (h := base + 11 * (i + 1)) hsp₃
    have hbt₃ : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark t₃ :=
      BlockTape_of_tapeEq hbt (tapeEq_trans heq₃ heq₂) (by
        simp only [Nat.max_eq_max] at hlen hlen₃ hlen₂ hlen₁ ⊢; omega)
    rw [hmax]
    refine ⟨t₃, hbt₃, ?_⟩
    exact (ProgRuns_seq hr₁ (ProgRuns_bind hr₂ (ProgRuns_if_true hr₃))).mono
      (Nat.le_refl Sp) (by decide)
  · have hi_eq : i + 1 = allocLen := by omega
    have hmax : Nat.max allocLen (i + 2) = allocLen + 1 := by simp only [Nat.max_eq_max]; omega
    rw [decide_eq_false hlt] at hr₂
    have hsp₃ : Nat.max t₂.length (base + 11 * (i + 1) + 11) ≤ Sp := by
      simp only [Nat.max_eq_max] at hsp hlen hlen₁ hlen₂ ⊢; omega
    obtain ⟨t₃, hread₃, hlen₃, hr₃⟩ :=
      ProgRuns_accessSlot () ⟨0, by decide⟩ (fun _ => ((), true))
        (t := t₂) (base := base + 11 * (i + 1)) hsp₃
    rw [hmax]
    refine ⟨t₃, ?_, ?_⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, hlow, hhigh⟩ := hbt
      refine ⟨by omega, by omega, by omega, h4, h5, by omega,
        fun r hr => Nat.lt_succ_of_lt (h7 r hr),
        fun w hw => Nat.lt_succ_of_lt (h8 w hw),
        by simp only [Nat.max_eq_max] at hlen hlen₃ hlen₂ hlen₁ ⊢; omega,
        fun p hp => ?_, fun p hp => ?_⟩
      · rw [hread₃ p]
        have hne : p ≠ base + 11 * (i + 1) + 0 := by omega
        rw [ite_eq_right hne, heq₂ p, hlow p hp]
      · rw [hread₃ p]
        set bi := (p - base) / 11
        set bs := (p - base) % 11
        by_cases hp_eq : p = base + 11 * (i + 1) + 0
        · rw [ite_eq_left hp_eq]
          have hbi : bi = allocLen := by dsimp [bi]; omega
          have hbs : bs = 0 := by dsimp [bs]; omega
          change true = slotVal (allocLen + 1) inBits nLen cBits preBits vSub rMark wMark bi bs
          rw [hbi, hbs]
          simp [slotVal]
        · rw [ite_eq_right hp_eq, heq₂ p, hhigh p hp]
          change slotVal allocLen inBits nLen cBits preBits vSub rMark wMark bi bs =
            slotVal (allocLen + 1) inBits nLen cBits preBits vSub rMark wMark bi bs
          by_cases hbi_lt : bi < allocLen
          · have hbi_lt' : bi < allocLen + 1 := by omega
            unfold slotVal
            rw [ite_eq_left hbi_lt, ite_eq_left hbi_lt']
          · by_cases hbi_eq : bi = allocLen
            · have hbs_ne0 : bs ≠ 0 := by
                intro hbs0
                apply hp_eq
                have hdiv_mod := Nat.div_add_mod (p - base) 11
                change 11 * bi + bs = p - base at hdiv_mod
                omega
              have h1_pos : allocLen ≠ 0 := by omega
              have hin : ¬ allocLen < inBits.length := by omega
              have hn : ¬ allocLen < nLen := by omega
              have hpre : ¬ allocLen < preBits.length := by omega
              have hsub_f : QCSD_tapeRead vSub allocLen = false := by
                unfold QCSD_tapeRead
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h6]; rfl
              have hin_f : QCSD_tapeRead inBits allocLen = false := by
                unfold QCSD_tapeRead
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h2]; rfl
              have hc_f : QCSD_tapeRead cBits allocLen = false := by
                unfold QCSD_tapeRead
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (h4.trans h3)]; rfl
              have hpre_f : QCSD_tapeRead preBits allocLen = false := by
                unfold QCSD_tapeRead
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (h5.trans h3)]; rfl
              have hrm : rMark ≠ some allocLen := fun h => Nat.lt_irrefl _ (h7 _ h)
              have hwm : wMark ≠ some allocLen := fun h => Nat.lt_irrefl _ (h8 _ h)
              rw [hbi_eq]
              have hlt11 : bs < 11 := Nat.mod_lt _ (by decide)
              unfold slotVal
              rw [ite_eq_right (Nat.lt_irrefl allocLen), ite_eq_left (Nat.lt_succ_self allocLen)]
              rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                           bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs
              · exact absurd hbs hbs_ne0
              · rw [hbs]; simp [h1_pos]
              · rw [hbs]; simp [hin]
              · rw [hbs]; simp [hin_f]
              · rw [hbs]; simp [hn]
              · rw [hbs]; simp [hc_f]
              · rw [hbs]; simp [hpre]
              · rw [hbs]; simp [hpre_f]
              · rw [hbs]; simp [hsub_f]
              · rw [hbs]; simp [hrm]
              · rw [hbs]; simp [hwm]
            · have hbi_gt : ¬ bi < allocLen + 1 := by omega
              simp [slotVal, hbi_lt, hbi_gt]
    · exact ProgRuns_seq hr₁
        (ProgRuns_bind (k := fun isInit =>
          ifProg isInit nopProg (accessSlotProg () ⟨0, by decide⟩ (fun _ => ((), true))))
          hr₂ (ProgRuns_if_false hr₃))

lemma ProgRuns_writeSubTape (val : Bool) {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark wMark : Option ℕ} {tape : List Bool} {i : ℕ}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape)
    (hi : i < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits (QCSD_tapeWrite2 vSub i val) rMark wMark tape' ∧
      ProgRuns (writeSlotProg ⟨8, by decide⟩ val) Sp 20 (tape, base + 11 * i) ()
        (tape', base + 11 * i) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hlen, hlow, hhigh⟩ := hbt
  have hsp' : Nat.max tape.length ((base + 11 * i) + 11) ≤ Sp := by
    simp only [Nat.max_eq_max]; omega
  obtain ⟨t', hread', hlen', hrun⟩ :=
    ProgRuns_accessSlot () ⟨8, by decide⟩ (fun _ => ((), val))
      (t := tape) (base := base + 11 * i) hsp'
  refine ⟨t', ⟨h1, h2, h3, h4, h5, ?_, h7, h8, ?_, ?_, ?_⟩, hrun⟩
  · rw [tapeWrite2_length]; simp only [Nat.max_eq_max]; omega
  · simp only [Nat.max_eq_max] at hlen' ⊢; omega
  · intro p hp
    rw [hread' p, ite_eq_right (by omega)]
    exact hlow p hp
  · intro p hp
    rw [hread' p]
    set bi := (p - base) / 11
    set bs := (p - base) % 11
    by_cases hp_eq : p = base + 11 * i + 8
    · rw [ite_eq_left hp_eq]
      have hbi : bi = i := by dsimp [bi]; omega
      have hbs : bs = 8 := by dsimp [bs]; omega
      change val = slotVal allocLen inBits nLen cBits preBits (QCSD_tapeWrite2 vSub i val) rMark wMark bi bs
      rw [hbi, hbs]
      simp [slotVal, hi, tapeRead_tapeWrite2]
    · rw [ite_eq_right hp_eq, hhigh p hp]
      change slotVal allocLen inBits nLen cBits preBits vSub rMark wMark bi bs =
        slotVal allocLen inBits nLen cBits preBits (QCSD_tapeWrite2 vSub i val) rMark wMark bi bs
      by_cases hbi_lt : bi < allocLen
      · by_cases hbs8 : bs = 8
        · have hbi_ne : bi ≠ i := by
            intro hbi_i
            apply hp_eq
            have hdm := Nat.div_add_mod (p - base) 11
            change 11 * bi + bs = p - base at hdm
            omega
          rw [hbs8]
          simp [slotVal, hbi_lt, tapeRead_tapeWrite2, hbi_ne]
        · have hlt11 : bs < 11 := Nat.mod_lt _ (by decide)
          unfold slotVal
          rw [ite_eq_left hbi_lt, ite_eq_left hbi_lt]
          rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                       bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
            hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs <;>
            (rw [hbs] at hbs8 ⊢; simp at hbs8 ⊢)
      · simp [slotVal, hbi_lt]

def simTMStepBody (M : QCSD_DetTM) (q : M.Q) :
    Prog (((Unit ⊕ Unit) ⊕
      ((Fin 20 × Bool) ⊕ (Bool × ((Fin 20 × Unit) ⊕
        (((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ Fin 11))) ⊕
         (Fin 11 ⊕ ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ (Fin 20 × Unit)))))))))) )
      (M.Q ⊕ Unit) :=
  ifProg (@decide (q = M.qhalt) (M.decEqQ q M.qhalt))
    (mapExitProg Sum.inr nopProg)
    (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
      let r := M.step q b
      seqProg (writeSlotProg ⟨8, by decide⟩ r.2.1)
        (mapExitProg (fun _ => Sum.inl r.1)
          (match r.2.2 with
           | QCSD_HeadDir.left => ifProg true moveBlockLeftProg moveBlockRightProg
           | QCSD_HeadDir.right => ifProg false moveBlockLeftProg moveBlockRightProg))))

def simTMProg (M : QCSD_DetTM) :
    Prog (M.Q × (((Unit ⊕ Unit) ⊕
      ((Fin 20 × Bool) ⊕ (Bool × ((Fin 20 × Unit) ⊕
        (((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ Fin 11))) ⊕
         (Fin 11 ⊕ ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ (Fin 20 × Unit)))))))))))) Unit :=
  loopStateProg M.q0 (simTMStepBody M)

lemma ProgRuns_simTM (M : QCSD_DetTM) {Sp SpM k base allocLen : ℕ}
    {inBits : List Bool} {nLen : ℕ} {cBits preBits vSub : List Bool}
    {rMark wMark : Option ℕ} {tape : List Bool} {inpM : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape)
    (heq : tapeEq inpM vSub)
    (hhalt : (QCSD_configAt2 M inpM k).state = M.qhalt)
    (hspM : ∀ j ≤ k, QCSD_spaceUse2 (QCSD_configAt2 M inpM j) ≤ SpM)
    (hsp : base + 11 * Nat.max allocLen (SpM + 1) ≤ Sp) :
    ∃ allocLen' vSub' tape' hout,
      (allocLen ≤ allocLen' ∧ allocLen' ≤ Nat.max allocLen (SpM + 1)) ∧
      hout < allocLen' ∧
      tapeEq (QCSD_configAt2 M inpM k).tape vSub' ∧
      BlockTape base allocLen' inBits nLen cBits preBits vSub' rMark wMark tape' ∧
      ProgRuns (simTMProg M) Sp (91 * k + 2) (tape, base) () (tape', base + 11 * hout) := by
  let _ := M.decEqQ
  have hgen : ∀ (rem : ℕ) (j : ℕ), j + rem = k →
      ∀ (aL : ℕ) (vS t₀ : List Bool),
        (allocLen ≤ aL ∧ aL ≤ Nat.max allocLen (SpM + 1)) →
        ((stepOrStay M)^[j] ⟨M.q0, inpM, 0⟩).head < aL →
        tapeEq ((stepOrStay M)^[j] ⟨M.q0, inpM, 0⟩).tape vS →
        BlockTape base aL inBits nLen cBits preBits vS rMark wMark t₀ →
        ∃ allocLen' vSub' tape' hout,
          (allocLen ≤ allocLen' ∧ allocLen' ≤ Nat.max allocLen (SpM + 1)) ∧
          hout < allocLen' ∧
          tapeEq ((stepOrStay M)^[k] ⟨M.q0, inpM, 0⟩).tape vSub' ∧
          BlockTape base allocLen' inBits nLen cBits preBits vSub' rMark wMark tape' ∧
          ProgRuns (loopStateProg ((stepOrStay M)^[j] ⟨M.q0, inpM, 0⟩).state (simTMStepBody M))
            Sp (91 * rem + 2)
            (t₀, base + 11 * ((stepOrStay M)^[j] ⟨M.q0, inpM, 0⟩).head) ()
            (tape', base + 11 * hout) := by
    intro rem
    induction rem with
    | zero =>
      intro j hj aL vS t₀ haL hhead heq_j hbt_j
      have hjk : j = k := by omega
      subst hjk
      set ck := (stepOrStay M)^[j] ⟨M.q0, inpM, 0⟩
      have hstate : ck.state = M.qhalt := by
        simpa [ck, configAt2_eq_iterate] using hhalt
      have hlen₀ : t₀.length ≤ base + 11 * aL := hbt_j.2.2.2.2.2.2.2.2.1
      have hsp_nop : Nat.max t₀.length (base + 11 * ck.head + 2) ≤ Sp := by
        simp only [Nat.max_eq_max] at haL hsp ⊢; omega
      obtain ⟨t₁, heq₁, hlen₁, hr₁⟩ := ProgRuns_nop (t := t₀) (h := base + 11 * ck.head) hsp_nop
      have hbt₁ : BlockTape base aL inBits nLen cBits preBits vS rMark wMark t₁ :=
        BlockTape_of_tapeEq hbt_j heq₁ (by simp only [Nat.max_eq_max] at hlen₁ ⊢; omega)
      refine ⟨aL, vS, t₁, ck.head, haL, hhead, heq_j, hbt₁, ?_⟩
      apply ProgRuns_loopState_exit
      unfold simTMStepBody
      have hd_halt : @decide (ck.state = M.qhalt) (M.decEqQ ck.state M.qhalt) = true := by
        let _ := M.decEqQ; exact decide_eq_true hstate
      rw [hd_halt]
      exact ProgRuns_if_true (ProgRuns_mapExit Sum.inr hr₁)
    | succ rem ih =>
      intro j hj aL vS t₀ haL hhead heq_j hbt_j
      set cj := (stepOrStay M)^[j] ⟨M.q0, inpM, 0⟩
      by_cases hqj : cj.state = M.qhalt
      · have hfix : ∀ r, (stepOrStay M)^[j + r] ⟨M.q0, inpM, 0⟩ = cj := by
          intro r
          induction r with
          | zero => rfl
          | succ r ihr =>
            rw [← Nat.add_assoc, Nat.add_comm _ 1, Function.iterate_add_apply,
                Function.iterate_one, ihr, stepOrStay_of_qhalt M cj hqj]
        have hck : (stepOrStay M)^[k] ⟨M.q0, inpM, 0⟩ = cj := by
          rw [← hj]; exact hfix (rem + 1)
        have hlen₀ : t₀.length ≤ base + 11 * aL := hbt_j.2.2.2.2.2.2.2.2.1
        have hsp_nop : Nat.max t₀.length (base + 11 * cj.head + 2) ≤ Sp := by
          simp only [Nat.max_eq_max] at haL hsp ⊢; omega
        obtain ⟨t₁, heq₁, hlen₁, hr₁⟩ := ProgRuns_nop (t := t₀) (h := base + 11 * cj.head) hsp_nop
        have hbt₁ : BlockTape base aL inBits nLen cBits preBits vS rMark wMark t₁ :=
          BlockTape_of_tapeEq hbt_j heq₁ (by simp only [Nat.max_eq_max] at hlen₁ ⊢; omega)
        refine ⟨aL, vS, t₁, cj.head, haL, hhead, by rw [hck]; exact heq_j, hbt₁, ?_⟩
        apply (ProgRuns_loopState_exit (T := 2) ?_).mono (Nat.le_refl Sp) (by omega)
        unfold simTMStepBody
        have hd_halt : @decide (cj.state = M.qhalt) (M.decEqQ cj.state M.qhalt) = true := by
          let _ := M.decEqQ; exact decide_eq_true hqj
        rw [hd_halt]
        exact ProgRuns_if_true (ProgRuns_mapExit Sum.inr hr₁)
      · have hd_nhalt : @decide (cj.state = M.qhalt) (M.decEqQ cj.state M.qhalt) = false := by
          let _ := M.decEqQ; exact decide_eq_false hqj
        have hsp_aL : base + 11 * aL ≤ Sp := by
          simp only [Nat.max_eq_max] at haL hsp ⊢; omega
        obtain ⟨t₁, hbt₁, hrRead⟩ :=
          ProgRuns_readSlot ⟨8, by decide⟩ hbt_j hhead hsp_aL
        have hsv : slotVal aL inBits nLen cBits preBits vS rMark wMark cj.head 8 =
            QCSD_tapeRead cj.tape cj.head := by
          simp [slotVal, hhead, heq_j cj.head]
        rw [hsv] at hrRead
        let r := M.step cj.state (QCSD_tapeRead cj.tape cj.head)
        obtain ⟨t₂, hbt₂, hrWrite⟩ :=
          ProgRuns_writeSubTape r.2.1 hbt₁ hhead hsp_aL
        have hnext_cfg : (stepOrStay M)^[j + 1] ⟨M.q0, inpM, 0⟩ =
            ⟨r.1, QCSD_tapeWrite2 cj.tape cj.head r.2.1, stepHead cj.head r.2.2⟩ := by
          rw [Nat.add_comm j 1, Function.iterate_add_apply, Function.iterate_one]
          exact stepOrStay_of_ne_qhalt M cj hqj
        have hsp_j1 : QCSD_spaceUse2 ((stepOrStay M)^[j + 1] ⟨M.q0, inpM, 0⟩) ≤ SpM := by
          rw [← configAt2_eq_iterate]
          exact hspM (j + 1) (by omega)
        rw [hnext_cfg] at hsp_j1
        have hhead_le_SpM : stepHead cj.head r.2.2 < SpM + 1 := by
          simp only [QCSD_spaceUse2, Nat.max_eq_max] at hsp_j1; omega
        have heq_next : tapeEq (QCSD_tapeWrite2 cj.tape cj.head r.2.1)
            (QCSD_tapeWrite2 vS cj.head r.2.1) :=
          tapeEq_tapeWrite2 heq_j cj.head r.2.1
        cases hdir : r.2.2 with
        | left =>
          obtain ⟨t₃, hbt₃, hrMove⟩ := ProgRuns_moveBlockLeft hbt₂ hhead hsp_aL
          have hstep1 : ProgRuns (simTMStepBody M cj.state) Sp 91
              (t₀, base + 11 * cj.head) (Sum.inl r.1) (t₃, base + 11 * (cj.head - 1)) := by
            unfold simTMStepBody
            rw [hd_nhalt]
            apply ProgRuns_if_false
            refine (ProgRuns_bind (T₂ := 71) hrRead ?_)
            change ProgRuns (seqProg (writeSlotProg ⟨8, by decide⟩ r.2.1)
              (mapExitProg (fun _ => Sum.inl r.1)
                (match r.2.2 with
                 | QCSD_HeadDir.left => ifProg true moveBlockLeftProg moveBlockRightProg
                 | QCSD_HeadDir.right => ifProg false moveBlockLeftProg moveBlockRightProg)))
              Sp 71 _ _ _
            rw [hdir]
            exact (ProgRuns_seq hrWrite
              (ProgRuns_mapExit (fun _ => Sum.inl r.1) (ProgRuns_if_true hrMove))).mono
              (Nat.le_refl Sp) (by decide)
          have hsh : stepHead cj.head r.2.2 = cj.head - 1 := by simp [stepHead, hdir]
          obtain ⟨aL', vS', t', hout, haL', hhout, heq', hbt', hrLoop⟩ :=
            ih (j + 1) (by omega) aL (QCSD_tapeWrite2 vS cj.head r.2.1) t₃
              haL (by rw [hnext_cfg]; dsimp only; rw [hsh]; omega)
              (by rw [hnext_cfg]; exact heq_next) hbt₃
          rw [hnext_cfg] at hrLoop
          dsimp only at hrLoop
          rw [hsh] at hrLoop
          refine ⟨aL', vS', t', hout, haL', hhout, heq', hbt', ?_⟩
          simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ProgRuns_loopState_cont hstep1 hrLoop
        | right =>
          have hsp_r : base + 11 * Nat.max aL (cj.head + 2) ≤ Sp := by
            have hsh : stepHead cj.head r.2.2 = cj.head + 1 := by simp [stepHead, hdir]
            simp only [Nat.max_eq_max] at haL hhead_le_SpM hsp ⊢; omega
          obtain ⟨t₃, hbt₃, hrMove⟩ := ProgRuns_moveBlockRight hbt₂ hhead hsp_r
          have hstep1 : ProgRuns (simTMStepBody M cj.state) Sp 91
              (t₀, base + 11 * cj.head) (Sum.inl r.1) (t₃, base + 11 * (cj.head + 1)) := by
            unfold simTMStepBody
            rw [hd_nhalt]
            apply ProgRuns_if_false
            refine (ProgRuns_bind (T₂ := 71) hrRead ?_)
            change ProgRuns (seqProg (writeSlotProg ⟨8, by decide⟩ r.2.1)
              (mapExitProg (fun _ => Sum.inl r.1)
                (match r.2.2 with
                 | QCSD_HeadDir.left => ifProg true moveBlockLeftProg moveBlockRightProg
                 | QCSD_HeadDir.right => ifProg false moveBlockLeftProg moveBlockRightProg)))
              Sp 71 _ _ _
            rw [hdir]
            exact ProgRuns_seq hrWrite
              (ProgRuns_mapExit (fun _ => Sum.inl r.1) (ProgRuns_if_false hrMove))
          have hsh : stepHead cj.head r.2.2 = cj.head + 1 := by simp [stepHead, hdir]
          have haL2 : allocLen ≤ Nat.max aL (cj.head + 2) ∧
              Nat.max aL (cj.head + 2) ≤ Nat.max allocLen (SpM + 1) := by
            simp only [Nat.max_eq_max] at haL hhead_le_SpM hsh ⊢; omega
          obtain ⟨aL', vS', t', hout, haL', hhout, heq', hbt', hrLoop⟩ :=
            ih (j + 1) (by omega) (Nat.max aL (cj.head + 2))
              (QCSD_tapeWrite2 vS cj.head r.2.1) t₃
              haL2 (by rw [hnext_cfg]; dsimp only; rw [hsh]; simp only [Nat.max_eq_max]; omega)
              (by rw [hnext_cfg]; exact heq_next) hbt₃
          rw [hnext_cfg] at hrLoop
          dsimp only at hrLoop
          rw [hsh] at hrLoop
          refine ⟨aL', vS', t', hout, haL', hhout, heq', hbt', ?_⟩
          simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ProgRuns_loopState_cont hstep1 hrLoop
  obtain ⟨aL', vS', t', hout, haL', hhout, heq', hbt', hr⟩ :=
    hgen k 0 (Nat.zero_add k) allocLen vSub tape
      ⟨Nat.le_refl _, Nat.le_max_left _ _⟩ hbt.1 heq hbt
  rw [← configAt2_eq_iterate] at heq'
  exact ⟨aL', vS', t', hout, haL', hhout, heq', hbt', hr⟩

/-! ### Section 6a: Master Slot Write, Rewind, Mark Seek, Clear & Sub-Input Preparation -/

lemma ProgRuns_writeSlot_spec (s : Fin 11) (val : Bool)
    {Sp base allocLen : ℕ}
    {inBits inBits' : List Bool} {nLen nLen' : ℕ}
    {cBits cBits' preBits preBits' vSub vSub' : List Bool}
    {rMark rMark' wMark wMark' : Option ℕ} {tape : List Bool} {i : ℕ}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape)
    (hi : i < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp)
    (hb2 : inBits'.length ≤ allocLen)
    (hb3 : nLen' ≤ allocLen)
    (hb4 : cBits'.length ≤ nLen')
    (hb5 : preBits'.length ≤ nLen')
    (hb6 : vSub'.length ≤ allocLen)
    (hb7 : ∀ r, rMark' = some r → r < allocLen)
    (hb8 : ∀ w, wMark' = some w → w < allocLen)
    (hTarget : slotVal allocLen inBits' nLen' cBits' preBits' vSub' rMark' wMark' i s.val = val)
    (hOther : ∀ bi < allocLen, ∀ bs < 11, (bi ≠ i ∨ bs ≠ s.val) →
      slotVal allocLen inBits' nLen' cBits' preBits' vSub' rMark' wMark' bi bs =
      slotVal allocLen inBits nLen cBits preBits vSub rMark wMark bi bs) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits' nLen' cBits' preBits' vSub' rMark' wMark' tape' ∧
      ProgRuns (writeSlotProg s val) Sp 20 (tape, base + 11 * i) () (tape', base + 11 * i) := by
  obtain ⟨h1, _, _, _, _, _, _, _, hlen, hlow, hhigh⟩ := hbt
  have hsp' : Nat.max tape.length ((base + 11 * i) + 11) ≤ Sp := by
    have hs := s.isLt; simp only [Nat.max_eq_max]; omega
  obtain ⟨t', hread', hlen', hrun⟩ :=
    ProgRuns_accessSlot () s (fun _ => ((), val)) (t := tape) (base := base + 11 * i) hsp'
  refine ⟨t', ⟨h1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, ?_, ?_, ?_⟩, hrun⟩
  · simp only [Nat.max_eq_max] at hlen' ⊢; omega
  · intro p hp
    have hs := s.isLt
    rw [hread' p, ite_eq_right (by omega)]
    exact hlow p hp
  · intro p hp
    have hs := s.isLt
    rw [hread' p]
    set bi := (p - base) / 11
    set bs := (p - base) % 11
    by_cases hp_eq : p = base + 11 * i + s.val
    · rw [ite_eq_left hp_eq]
      have hbi : bi = i := by dsimp [bi]; omega
      have hbs : bs = s.val := by dsimp [bs]; omega
      change val = slotVal allocLen inBits' nLen' cBits' preBits' vSub' rMark' wMark' bi bs
      rw [hbi, hbs, hTarget]
    · rw [ite_eq_right hp_eq, hhigh p hp]
      change slotVal allocLen inBits nLen cBits preBits vSub rMark wMark bi bs =
        slotVal allocLen inBits' nLen' cBits' preBits' vSub' rMark' wMark' bi bs
      by_cases hbi_lt : bi < allocLen
      · have hbs_lt : bs < 11 := Nat.mod_lt _ (by decide)
        have hne : bi ≠ i ∨ bs ≠ s.val := by
          by_cases hbi_i : bi = i
          · right
            intro hbs_s
            apply hp_eq
            have hdm := Nat.div_add_mod (p - base) 11
            change 11 * bi + bs = p - base at hdm
            omega
          · exact Or.inl hbi_i
        exact (hOther bi hbi_lt bs hbs_lt hne).symm
      · simp [slotVal, hbi_lt]

def rewindToBlock0Prog :
    Prog ((Fin 20 × Bool) ⊕ (Bool × ((((Unit ⊕ Unit) ⊕
      ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ Fin 11)))))))) Unit :=
  whileProg
    (bindProg (readSlotProg ⟨1, by decide⟩) (fun isOrig =>
      ifProg isOrig
        (mapExitProg (fun _ => false) nopProg)
        (mapExitProg (fun _ => true) moveBlockLeftProg)))

lemma ProgRuns_rewindToBlock0 {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark wMark : Option ℕ} {tape : List Bool} {i : ℕ}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape)
    (hi : i < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape' ∧
      ProgRuns rewindToBlock0Prog Sp (51 * i + 22) (tape, base + 11 * i) () (tape', base) := by
  induction i generalizing tape with
  | zero =>
    obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨1, by decide⟩ hbt hi hsp
    have hsv : slotVal allocLen inBits nLen cBits preBits vSub rMark wMark 0 1 = true := by
      simp [slotVal, hi]
    rw [hsv] at hr₁
    have hlen₁ : t₁.length ≤ base + 11 * allocLen := hbt₁.2.2.2.2.2.2.2.2.1
    have hsp_nop : Nat.max t₁.length (base + 11 * 0 + 2) ≤ Sp := by
      simp only [Nat.max_eq_max]; omega
    obtain ⟨t₂, heq₂, hlen₂, hr₂⟩ := ProgRuns_nop (t := t₁) (h := base + 11 * 0) hsp_nop
    have hbt₂ : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark t₂ :=
      BlockTape_of_tapeEq hbt₁ heq₂ (by simp only [Nat.max_eq_max] at hlen₂ ⊢; omega)
    refine ⟨t₂, hbt₂, ?_⟩
    rw [Nat.mul_zero, Nat.add_zero] at hr₁ hr₂
    rw [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    apply ProgRuns_while_false
    exact ProgRuns_bind (k := fun isOrig =>
      ifProg isOrig (mapExitProg (fun _ => false) nopProg)
        (mapExitProg (fun _ => true) moveBlockLeftProg))
      hr₁ (ProgRuns_if_true (ProgRuns_mapExit (fun _ => false) hr₂))
  | succ i ih =>
    obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨1, by decide⟩ hbt hi hsp
    have hsv : slotVal allocLen inBits nLen cBits preBits vSub rMark wMark (i + 1) 1 = false := by
      simp [slotVal, hi]
    rw [hsv] at hr₁
    obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_moveBlockLeft hbt₁ hi hsp
    rw [Nat.add_sub_cancel] at hr₂
    obtain ⟨t₃, hbt₃, hr₃⟩ := ih hbt₂ (by omega)
    refine ⟨t₃, hbt₃, ?_⟩
    have hbody : ProgRuns
        (bindProg (readSlotProg ⟨1, by decide⟩) (fun isOrig =>
          ifProg isOrig (mapExitProg (fun _ => false) nopProg)
            (mapExitProg (fun _ => true) moveBlockLeftProg)))
        Sp 51 (tape, base + 11 * (i + 1)) true (t₂, base + 11 * i) :=
      ProgRuns_bind (k := fun isOrig =>
        ifProg isOrig (mapExitProg (fun _ => false) nopProg)
          (mapExitProg (fun _ => true) moveBlockLeftProg))
        hr₁ (ProgRuns_if_false (ProgRuns_mapExit (fun _ => true) hr₂))
    simpa [rewindToBlock0Prog, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ProgRuns_while_true hbody hr₃

def seekMarkProg (s : Fin 11) :
    Prog ((Fin 20 × Bool) ⊕ (Bool × (((Unit ⊕ Unit) ⊕
      (Fin 11 ⊕ ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ (Fin 20 × Unit))))))))) Unit :=
  whileProg
    (bindProg (readSlotProg s) (fun found =>
      ifProg found
        (mapExitProg (fun _ => false) nopProg)
        (mapExitProg (fun _ => true) moveBlockRightProg)))

lemma ProgRuns_seekRMark {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {target : ℕ} {wMark : Option ℕ} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub (some target) wMark tape)
    (htarget : target < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub (some target) wMark tape' ∧
      ProgRuns (seekMarkProg ⟨9, by decide⟩) Sp (71 * target + 22)
        (tape, base) () (tape', base + 11 * target) := by
  have hgen : ∀ (rem i : ℕ), i + rem = target → ∀ t₀ : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub (some target) wMark t₀ →
      ∃ tape' : List Bool,
        BlockTape base allocLen inBits nLen cBits preBits vSub (some target) wMark tape' ∧
        ProgRuns (seekMarkProg ⟨9, by decide⟩) Sp (71 * rem + 22)
          (t₀, base + 11 * i) () (tape', base + 11 * target) := by
    intro rem
    induction rem with
    | zero =>
      intro i hi_eq t₀ hbt₀
      have hit : i = target := by omega
      subst hit
      obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨9, by decide⟩ hbt₀ htarget hsp
      have hsv : slotVal allocLen inBits nLen cBits preBits vSub (some i) wMark i 9 = true := by
        simp [slotVal, htarget]
      rw [hsv] at hr₁
      have hlen₁ : t₁.length ≤ base + 11 * allocLen := hbt₁.2.2.2.2.2.2.2.2.1
      have hsp_nop : Nat.max t₁.length (base + 11 * i + 2) ≤ Sp := by
        simp only [Nat.max_eq_max]; omega
      obtain ⟨t₂, heq₂, hlen₂, hr₂⟩ := ProgRuns_nop (t := t₁) (h := base + 11 * i) hsp_nop
      have hbt₂ := BlockTape_of_tapeEq hbt₁ heq₂ (by simp only [Nat.max_eq_max] at hlen₂ ⊢; omega)
      refine ⟨t₂, hbt₂, ?_⟩
      rw [Nat.mul_zero, Nat.zero_add]
      apply ProgRuns_while_false
      exact ProgRuns_bind (k := fun found =>
        ifProg found (mapExitProg (fun _ => false) nopProg)
          (mapExitProg (fun _ => true) moveBlockRightProg))
        hr₁ (ProgRuns_if_true (ProgRuns_mapExit (fun _ => false) hr₂))
    | succ rem ih =>
      intro i hi_eq t₀ hbt₀
      have hi_lt : i < allocLen := by omega
      have hne_t : target ≠ i := by omega
      obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨9, by decide⟩ hbt₀ hi_lt hsp
      have hsv : slotVal allocLen inBits nLen cBits preBits vSub (some target) wMark i 9 = false := by
        simp [slotVal, hi_lt, hne_t]
      rw [hsv] at hr₁
      have hmax : Nat.max allocLen (i + 2) = allocLen := by simp only [Nat.max_eq_max]; omega
      have hsp_r : base + 11 * Nat.max allocLen (i + 2) ≤ Sp := by rw [hmax]; exact hsp
      obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_moveBlockRight hbt₁ hi_lt hsp_r
      rw [hmax] at hbt₂
      obtain ⟨t₃, hbt₃, hr₃⟩ := ih (i + 1) (by omega) t₂ hbt₂
      refine ⟨t₃, hbt₃, ?_⟩
      have hbody : ProgRuns
          (bindProg (readSlotProg ⟨9, by decide⟩) (fun found =>
            ifProg found (mapExitProg (fun _ => false) nopProg)
              (mapExitProg (fun _ => true) moveBlockRightProg)))
          Sp 71 (t₀, base + 11 * i) true (t₂, base + 11 * (i + 1)) :=
        ProgRuns_bind (k := fun found =>
          ifProg found (mapExitProg (fun _ => false) nopProg)
            (mapExitProg (fun _ => true) moveBlockRightProg))
          hr₁ (ProgRuns_if_false (ProgRuns_mapExit (fun _ => true) hr₂))
      simpa [seekMarkProg, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ProgRuns_while_true hbody hr₃
  obtain ⟨t', hbt', hr⟩ := hgen target 0 (Nat.zero_add target) tape hbt
  rw [Nat.mul_zero, Nat.add_zero] at hr
  exact ⟨t', hbt', hr⟩

lemma ProgRuns_seekWMark {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark : Option ℕ} {target : ℕ} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark (some target) tape)
    (htarget : target < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub rMark (some target) tape' ∧
      ProgRuns (seekMarkProg ⟨10, by decide⟩) Sp (71 * target + 22)
        (tape, base) () (tape', base + 11 * target) := by
  have hgen : ∀ (rem i : ℕ), i + rem = target → ∀ t₀ : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub rMark (some target) t₀ →
      ∃ tape' : List Bool,
        BlockTape base allocLen inBits nLen cBits preBits vSub rMark (some target) tape' ∧
        ProgRuns (seekMarkProg ⟨10, by decide⟩) Sp (71 * rem + 22)
          (t₀, base + 11 * i) () (tape', base + 11 * target) := by
    intro rem
    induction rem with
    | zero =>
      intro i hi_eq t₀ hbt₀
      have hit : i = target := by omega
      subst hit
      obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨10, by decide⟩ hbt₀ htarget hsp
      have hsv : slotVal allocLen inBits nLen cBits preBits vSub rMark (some i) i 10 = true := by
        simp [slotVal, htarget]
      rw [hsv] at hr₁
      have hlen₁ : t₁.length ≤ base + 11 * allocLen := hbt₁.2.2.2.2.2.2.2.2.1
      have hsp_nop : Nat.max t₁.length (base + 11 * i + 2) ≤ Sp := by
        simp only [Nat.max_eq_max]; omega
      obtain ⟨t₂, heq₂, hlen₂, hr₂⟩ := ProgRuns_nop (t := t₁) (h := base + 11 * i) hsp_nop
      have hbt₂ := BlockTape_of_tapeEq hbt₁ heq₂ (by simp only [Nat.max_eq_max] at hlen₂ ⊢; omega)
      refine ⟨t₂, hbt₂, ?_⟩
      rw [Nat.mul_zero, Nat.zero_add]
      apply ProgRuns_while_false
      exact ProgRuns_bind (k := fun found =>
        ifProg found (mapExitProg (fun _ => false) nopProg)
          (mapExitProg (fun _ => true) moveBlockRightProg))
        hr₁ (ProgRuns_if_true (ProgRuns_mapExit (fun _ => false) hr₂))
    | succ rem ih =>
      intro i hi_eq t₀ hbt₀
      have hi_lt : i < allocLen := by omega
      have hne_t : target ≠ i := by omega
      obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨10, by decide⟩ hbt₀ hi_lt hsp
      have hsv : slotVal allocLen inBits nLen cBits preBits vSub rMark (some target) i 10 = false := by
        simp [slotVal, hi_lt, hne_t]
      rw [hsv] at hr₁
      have hmax : Nat.max allocLen (i + 2) = allocLen := by simp only [Nat.max_eq_max]; omega
      have hsp_r : base + 11 * Nat.max allocLen (i + 2) ≤ Sp := by rw [hmax]; exact hsp
      obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_moveBlockRight hbt₁ hi_lt hsp_r
      rw [hmax] at hbt₂
      obtain ⟨t₃, hbt₃, hr₃⟩ := ih (i + 1) (by omega) t₂ hbt₂
      refine ⟨t₃, hbt₃, ?_⟩
      have hbody : ProgRuns
          (bindProg (readSlotProg ⟨10, by decide⟩) (fun found =>
            ifProg found (mapExitProg (fun _ => false) nopProg)
              (mapExitProg (fun _ => true) moveBlockRightProg)))
          Sp 71 (t₀, base + 11 * i) true (t₂, base + 11 * (i + 1)) :=
        ProgRuns_bind (k := fun found =>
          ifProg found (mapExitProg (fun _ => false) nopProg)
            (mapExitProg (fun _ => true) moveBlockRightProg))
          hr₁ (ProgRuns_if_false (ProgRuns_mapExit (fun _ => true) hr₂))
      simpa [seekMarkProg, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ProgRuns_while_true hbody hr₃
  obtain ⟨t', hbt', hr⟩ := hgen target 0 (Nat.zero_add target) tape hbt
  rw [Nat.mul_zero, Nat.add_zero] at hr
  exact ⟨t', hbt', hr⟩

def clearSubTapeProg :
    Prog (((Fin 20 × Unit) ⊕ (Fin 11 ⊕ ((Fin 20 × Bool) ⊕
      (Bool × (Unit ⊕ Unit))))) ⊕
      ((Fin 20 × Bool) ⊕ (Bool × (((Unit ⊕ Unit) ⊕
        ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ Fin 11)))))))) Unit :=
  seqProg
    (whileProg
      (seqProg (writeSlotProg ⟨8, by decide⟩ false)
        (seqProg (moveDirPosProg QCSD_HeadDir.right 10)
          (bindProg (accessSlotProg false ⟨0, by decide⟩ (fun b => (b, true)))
            (fun wasInit => mapExitProg (fun _ => wasInit) nopProg)))))
    rewindToBlock0Prog

lemma ProgRuns_clearSubTape {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark wMark : Option ℕ} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape)
    (hsp : base + 11 * (allocLen + 1) ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base (allocLen + 1) inBits nLen cBits preBits [] rMark wMark tape' ∧
      ProgRuns clearSubTapeProg Sp (110 * allocLen + 90) (tape, base) () (tape', base) := by
  let vCleared (k : ℕ) : List Bool :=
    List.ofFn (fun j : Fin allocLen => if j.val < k then false else QCSD_tapeRead vSub j.val)
  have hv0 : ∀ j < allocLen, QCSD_tapeRead (vCleared 0) j = QCSD_tapeRead vSub j := by
    intro j hj
    dsimp only [vCleared]
    unfold QCSD_tapeRead
    simp only [List.getD_eq_getElem?_getD, List.length_ofFn, hj,
      List.getElem?_eq_getElem, Option.getD_some, List.getElem_ofFn, Nat.not_lt_zero, ↓reduceIte]
  have hbt0 : BlockTape base allocLen inBits nLen cBits preBits (vCleared 0) rMark wMark tape := by
    obtain ⟨h1, h2, h3, h4, h5, _, h7, h8, hlen, hlow, hhigh⟩ := hbt
    refine ⟨h1, h2, h3, h4, h5, by simp [vCleared], h7, h8, hlen, hlow, fun p hp => ?_⟩
    rw [hhigh p hp]
    set bi := (p - base) / 11
    set bs := (p - base) % 11
    by_cases hbi : bi < allocLen
    · by_cases hbs8 : bs = 8
      · rw [hbs8]; simp [slotVal, hbi, hv0 bi hbi]
      · have hbs_lt : bs < 11 := Nat.mod_lt _ (by decide)
        unfold slotVal
        rw [ite_eq_left hbi, ite_eq_left hbi]
        rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                     bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
          h | h | h | h | h | h | h | h | h | h | h <;> (rw [h] at hbs8 ⊢; simp at hbs8 ⊢)
    · simp [slotVal, hbi]
  have hclearStep : ∀ (i : ℕ) (hi_lt : i < allocLen) (t₀ : List Bool),
      BlockTape base allocLen inBits nLen cBits preBits (vCleared i) rMark wMark t₀ →
      ∃ t₁ : List Bool,
        BlockTape base allocLen inBits nLen cBits preBits (vCleared (i + 1)) rMark wMark t₁ ∧
        ProgRuns (writeSlotProg ⟨8, by decide⟩ false) Sp 20
          (t₀, base + 11 * i) () (t₁, base + 11 * i) := by
    intro i hi_lt t₀ hbt₀
    exact ProgRuns_writeSlot_spec ⟨8, by decide⟩ false hbt₀ hi_lt (by omega)
      hbt₀.2.1 hbt₀.2.2.1 hbt₀.2.2.2.1 hbt₀.2.2.2.2.1
      (by simp [vCleared]) hbt₀.2.2.2.2.2.2.1 hbt₀.2.2.2.2.2.2.2.1
      (by
        unfold slotVal; rw [ite_eq_left hi_lt]
        dsimp only [vCleared]; unfold QCSD_tapeRead
        simp [List.getD_eq_getElem?_getD, hi_lt])
      (fun bi hbi bs _ hne => by
        by_cases hbs8 : bs = 8
        · have hbi_ne : bi ≠ i := hne.resolve_right (fun h => h hbs8)
          rw [hbs8]; unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
          dsimp only [vCleared]; unfold QCSD_tapeRead
          simp only [List.getD_eq_getElem?_getD, List.length_ofFn, hbi,
            List.getElem?_eq_getElem, Option.getD_some, List.getElem_ofFn]
          have hiff : (bi < i + 1) ↔ (bi < i) := by omega
          simp [hiff]
        · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                       bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact absurd rfl hbs8 | simp only [slotVal, hbi, ↓reduceIte])
  let clearBody :=
    seqProg (writeSlotProg ⟨8, by decide⟩ false)
      (seqProg (moveDirPosProg QCSD_HeadDir.right 10)
        (bindProg (accessSlotProg false ⟨0, by decide⟩ (fun b => (b, true)))
          (fun wasInit => mapExitProg (fun _ => wasInit) nopProg)))
  have hloop : ∀ (rem i : ℕ), i + 1 + rem = allocLen → ∀ t₀ : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits (vCleared i) rMark wMark t₀ →
      ∃ t₁ : List Bool,
        BlockTape base (allocLen + 1) inBits nLen cBits preBits [] rMark wMark t₁ ∧
        ProgRuns (whileProg clearBody) Sp (53 * rem + 53)
          (t₀, base + 11 * i) () (t₁, base + 11 * allocLen) := by
    intro rem
    induction rem with
    | zero =>
      intro i hi_eq t₀ hbt₀
      have hi_lt : i < allocLen := by omega
      have hi1 : i + 1 = allocLen := by omega
      obtain ⟨t₁, hbt₁, hrW⟩ := hclearStep i hi_lt t₀ hbt₀
      have hlen₁ : t₁.length ≤ base + 11 * allocLen := hbt₁.2.2.2.2.2.2.2.2.1
      have hspR : Nat.max t₁.length (base + 11 * i + 10 + 2) ≤ Sp := by
        simp only [Nat.max_eq_max]; omega
      obtain ⟨t₂, heq₂, hlen₂, hrR⟩ := ProgRuns_moveRightPos 10 (t := t₁) (h := base + 11 * i) hspR
      have hpos : base + 11 * i + 10 + 1 = base + 11 * allocLen := by omega
      rw [hpos] at hrR hlen₂
      have hspA : Nat.max t₂.length (base + 11 * allocLen + 11) ≤ Sp := by
        simp only [Nat.max_eq_max] at hlen₂ ⊢; omega
      obtain ⟨t₃, hread₃, hlen₃, hrA⟩ :=
        ProgRuns_accessSlot false ⟨0, by decide⟩ (fun b => (b, true))
          (t := t₂) (base := base + 11 * allocLen) hspA
      have hb0_f : QCSD_tapeRead t₂ (base + 11 * allocLen + 0) = false := by
        rw [heq₂, BlockTape_read_slot hbt₁ allocLen ⟨0, by decide⟩]
        simp [slotVal]
      dsimp only at hrA
      rw [hb0_f] at hrA
      have hspN : Nat.max t₃.length (base + 11 * allocLen + 2) ≤ Sp := by
        simp only [Nat.max_eq_max] at hlen₃ hlen₂ ⊢; omega
      obtain ⟨t₄, heq₄, hlen₄, hrN⟩ := ProgRuns_nop (t := t₃) (h := base + 11 * allocLen) hspN
      refine ⟨t₄, ?_, ?_⟩
      · obtain ⟨h1, h2, h3, h4, h5, _, h7, h8, _, hlow, hhigh⟩ := hbt₁
        refine ⟨by omega, by omega, by omega, h4, h5, by simp,
          fun r hr => Nat.lt_succ_of_lt (h7 r hr),
          fun w hw => Nat.lt_succ_of_lt (h8 w hw),
          by simp only [Nat.max_eq_max] at hlen₄ hlen₃ hlen₂ ⊢; omega,
          fun p hp => ?_, fun p hp => ?_⟩
        · rw [heq₄ p, hread₃ p, ite_eq_right (by omega), heq₂ p, hlow p hp]
        · rw [heq₄ p, hread₃ p]
          set bi := (p - base) / 11
          set bs := (p - base) % 11
          by_cases hp_eq : p = base + 11 * allocLen + 0
          · rw [ite_eq_left hp_eq]
            have hbi : bi = allocLen := by dsimp [bi]; omega
            have hbs : bs = 0 := by dsimp [bs]; omega
            change true = slotVal (allocLen + 1) inBits nLen cBits preBits [] rMark wMark bi bs
            rw [hbi, hbs]; simp [slotVal]
          · rw [ite_eq_right hp_eq, heq₂ p, hhigh p hp]
            change slotVal allocLen inBits nLen cBits preBits (vCleared (i + 1)) rMark wMark bi bs =
              slotVal (allocLen + 1) inBits nLen cBits preBits [] rMark wMark bi bs
            rw [hi1]
            by_cases hbi_lt : bi < allocLen
            · have hbi_lt' : bi < allocLen + 1 := by omega
              by_cases hbs8 : bs = 8
              · rw [hbs8]
                unfold slotVal
                rw [ite_eq_left hbi_lt, ite_eq_left hbi_lt']
                dsimp only [vCleared]
                unfold QCSD_tapeRead
                simp [List.getD_eq_getElem?_getD, hbi_lt]
              · unfold slotVal
                rw [ite_eq_left hbi_lt, ite_eq_left hbi_lt']
                rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                             bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                  h | h | h | h | h | h | h | h | h | h | h <;> (rw [h] at hbs8 ⊢; simp at hbs8 ⊢)
            · by_cases hbi_eq : bi = allocLen
              · have hbs_ne0 : bs ≠ 0 := by
                  intro hbs0; apply hp_eq
                  have hdm := Nat.div_add_mod (p - base) 11
                  change 11 * bi + bs = p - base at hdm; omega
                have h1_pos : allocLen ≠ 0 := by omega
                have hin : ¬ allocLen < inBits.length := by omega
                have hn : ¬ allocLen < nLen := by omega
                have hpre : ¬ allocLen < preBits.length := by omega
                have hin_f : QCSD_tapeRead inBits allocLen = false := by
                  unfold QCSD_tapeRead; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h2]; rfl
                have hc_f : QCSD_tapeRead cBits allocLen = false := by
                  unfold QCSD_tapeRead; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (h4.trans h3)]; rfl
                have hpre_f : QCSD_tapeRead preBits allocLen = false := by
                  unfold QCSD_tapeRead; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (h5.trans h3)]; rfl
                have hrm : rMark ≠ some allocLen := fun h => Nat.lt_irrefl _ (h7 _ h)
                have hwm : wMark ≠ some allocLen := fun h => Nat.lt_irrefl _ (h8 _ h)
                rw [hbi_eq]
                unfold slotVal
                rw [ite_eq_right (Nat.lt_irrefl allocLen), ite_eq_left (Nat.lt_succ_self allocLen)]
                rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                             bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                  hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs
                · exact absurd hbs hbs_ne0
                · rw [hbs]; simp [h1_pos]
                · rw [hbs]; simp [hin]
                · rw [hbs]; simp [hin_f]
                · rw [hbs]; simp [hn]
                · rw [hbs]; simp [hc_f]
                · rw [hbs]; simp [hpre]
                · rw [hbs]; simp [hpre_f]
                · rw [hbs]; simp [QCSD_tapeRead]
                · rw [hbs]; simp [hrm]
                · rw [hbs]; simp [hwm]
              · have hbi_gt : ¬ bi < allocLen + 1 := by omega
                simp [slotVal, hbi_lt, hbi_gt]
      · rw [Nat.mul_zero, Nat.zero_add]
        apply ProgRuns_while_false
        exact ProgRuns_seq hrW (ProgRuns_seq hrR
          (ProgRuns_bind (k := fun wasInit => mapExitProg (fun _ => wasInit) nopProg)
            hrA (ProgRuns_mapExit (fun _ => false) hrN)))
    | succ rem ih =>
      intro i hi_eq t₀ hbt₀
      have hi_lt : i < allocLen := by omega
      have hi1_lt : i + 1 < allocLen := by omega
      obtain ⟨t₁, hbt₁, hrW⟩ := hclearStep i hi_lt t₀ hbt₀
      have hlen₁ : t₁.length ≤ base + 11 * allocLen := hbt₁.2.2.2.2.2.2.2.2.1
      have hspR : Nat.max t₁.length (base + 11 * i + 10 + 2) ≤ Sp := by
        simp only [Nat.max_eq_max]; omega
      obtain ⟨t₂, heq₂, hlen₂, hrR⟩ := ProgRuns_moveRightPos 10 (t := t₁) (h := base + 11 * i) hspR
      have hpos : base + 11 * i + 10 + 1 = base + 11 * (i + 1) := by omega
      rw [hpos] at hrR hlen₂
      have hspA : Nat.max t₂.length (base + 11 * (i + 1) + 11) ≤ Sp := by
        simp only [Nat.max_eq_max] at hlen₂ ⊢; omega
      obtain ⟨t₃, hread₃, hlen₃, hrA⟩ :=
        ProgRuns_accessSlot false ⟨0, by decide⟩ (fun b => (b, true))
          (t := t₂) (base := base + 11 * (i + 1)) hspA
      have hb0_t : QCSD_tapeRead t₂ (base + 11 * (i + 1) + 0) = true := by
        rw [heq₂, BlockTape_read_slot hbt₁ (i + 1) ⟨0, by decide⟩]
        simp [slotVal, hi1_lt]
      dsimp only at hrA
      rw [hb0_t] at hrA
      have heq₃ : tapeEq t₃ t₁ := by
        intro p; rw [hread₃]; split_ifs with hp
        · subst hp; dsimp only; rw [← hb0_t, heq₂]
        · exact heq₂ p
      have hspN : Nat.max t₃.length (base + 11 * (i + 1) + 2) ≤ Sp := by
        simp only [Nat.max_eq_max] at hlen₃ hlen₂ ⊢; omega
      obtain ⟨t₄, heq₄, hlen₄, hrN⟩ := ProgRuns_nop (t := t₃) (h := base + 11 * (i + 1)) hspN
      have hbt₄ : BlockTape base allocLen inBits nLen cBits preBits (vCleared (i + 1)) rMark wMark t₄ :=
        BlockTape_of_tapeEq hbt₁ (tapeEq_trans heq₄ heq₃)
          (by simp only [Nat.max_eq_max] at hlen₄ hlen₃ hlen₂ ⊢; omega)
      obtain ⟨t₅, hbt₅, hrRest⟩ := ih (i + 1) (by omega) t₄ hbt₄
      refine ⟨t₅, hbt₅, ?_⟩
      have hbody : ProgRuns clearBody Sp 53 (t₀, base + 11 * i) true (t₄, base + 11 * (i + 1)) :=
        ProgRuns_seq hrW (ProgRuns_seq hrR
          (ProgRuns_bind (k := fun wasInit => mapExitProg (fun _ => wasInit) nopProg)
            hrA (ProgRuns_mapExit (fun _ => true) hrN)))
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ProgRuns_while_true hbody hrRest
  have halloc_pos : 1 ≤ allocLen := hbt.1
  obtain ⟨t₁, hbt₁, hrLoop⟩ := hloop (allocLen - 1) 0 (by omega) tape hbt0
  have hbz : base + 11 * 0 = base := by omega
  rw [hbz] at hrLoop
  obtain ⟨t₂, hbt₂, hrRew⟩ :=
    ProgRuns_rewindToBlock0 hbt₁ (Nat.lt_succ_self allocLen) hsp
  refine ⟨t₂, hbt₂, ?_⟩
  exact (ProgRuns_seq hrLoop hrRew).mono (Nat.le_refl Sp) (by omega)

def advanceMarkProg (s : Fin 11) :
    Prog ((Fin 20 × Unit) ⊕ ((Fin 11 ⊕ ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ (Fin 20 × Unit))))) ⊕
      ((Fin 20 × Unit) ⊕ ((Fin 20 × Bool) ⊕ (Bool × (((Unit ⊕ Unit) ⊕
        ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ Fin 11)))))))))) Unit :=
  seqProg (writeSlotProg s false)
    (seqProg moveBlockRightProg
      (seqProg (writeSlotProg s true) rewindToBlock0Prog))

lemma ProgRuns_advanceRMark {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {r : ℕ} {wMark : Option ℕ} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub (some r) wMark tape)
    (hr1 : r + 1 < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub (some (r + 1)) wMark tape' ∧
      ProgRuns (advanceMarkProg ⟨9, by decide⟩) Sp (51 * (r + 1) + 113)
        (tape, base + 11 * r) () (tape', base) := by
  have hr_lt : r < allocLen := by omega
  obtain ⟨t₁, hbt₁, hr₁⟩ :=
    ProgRuns_writeSlot_spec ⟨9, by decide⟩ false
      (inBits' := inBits) (nLen' := nLen) (cBits' := cBits) (preBits' := preBits)
      (vSub' := vSub) (rMark' := none) (wMark' := wMark)
      hbt hr_lt hsp hbt.2.1 hbt.2.2.1 hbt.2.2.2.1 hbt.2.2.2.2.1 hbt.2.2.2.2.2.1
      (fun _ h => by cases h) hbt.2.2.2.2.2.2.2.1
      (by simp [slotVal, hr_lt])
      (fun bi hbi bs _ hne => by
        by_cases hbs9 : bs = 9
        · have hbi_ne : bi ≠ r := hne.resolve_right (fun h => h hbs9)
          rw [hbs9]; simp [slotVal, hbi, hbi_ne.symm]
        · unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
          rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                       bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
            h | h | h | h | h | h | h | h | h | h | h <;> (rw [h] at hbs9 ⊢; simp at hbs9 ⊢))
  have hmax : Nat.max allocLen (r + 2) = allocLen := by simp only [Nat.max_eq_max]; omega
  obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_moveBlockRight (Sp := Sp) hbt₁ hr_lt (by rw [hmax]; exact hsp)
  rw [hmax] at hbt₂
  obtain ⟨t₃, hbt₃, hr₃⟩ :=
    ProgRuns_writeSlot_spec ⟨9, by decide⟩ true
      (inBits' := inBits) (nLen' := nLen) (cBits' := cBits) (preBits' := preBits)
      (vSub' := vSub) (rMark' := some (r + 1)) (wMark' := wMark)
      hbt₂ hr1 hsp hbt₂.2.1 hbt₂.2.2.1 hbt₂.2.2.2.1 hbt₂.2.2.2.2.1 hbt₂.2.2.2.2.2.1
      (fun r' hr' => by cases hr'; exact hr1) hbt₂.2.2.2.2.2.2.2.1
      (by simp [slotVal, hr1])
      (fun bi hbi bs _ hne => by
        by_cases hbs9 : bs = 9
        · have hbi_ne : bi ≠ r + 1 := hne.resolve_right (fun h => h hbs9)
          rw [hbs9]; simp [slotVal, hbi, hbi_ne.symm]
        · unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
          rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                       bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
            h | h | h | h | h | h | h | h | h | h | h <;> (rw [h] at hbs9 ⊢; simp at hbs9 ⊢))
  obtain ⟨t₄, hbt₄, hr₄⟩ := ProgRuns_rewindToBlock0 hbt₃ hr1 hsp
  refine ⟨t₄, hbt₄, ?_⟩
  exact (ProgRuns_seq hr₁ (ProgRuns_seq hr₂ (ProgRuns_seq hr₃ hr₄))).mono
    (Nat.le_refl Sp) (by omega)

lemma ProgRuns_advanceWMark {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark : Option ℕ} {w : ℕ} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark (some w) tape)
    (hw1 : w + 1 < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub rMark (some (w + 1)) tape' ∧
      ProgRuns (advanceMarkProg ⟨10, by decide⟩) Sp (51 * (w + 1) + 113)
        (tape, base + 11 * w) () (tape', base) := by
  have hw_lt : w < allocLen := by omega
  obtain ⟨t₁, hbt₁, hr₁⟩ :=
    ProgRuns_writeSlot_spec ⟨10, by decide⟩ false
      (inBits' := inBits) (nLen' := nLen) (cBits' := cBits) (preBits' := preBits)
      (vSub' := vSub) (rMark' := rMark) (wMark' := none)
      hbt hw_lt hsp hbt.2.1 hbt.2.2.1 hbt.2.2.2.1 hbt.2.2.2.2.1 hbt.2.2.2.2.2.1
      hbt.2.2.2.2.2.2.1 (fun _ h => by cases h)
      (by simp [slotVal, hw_lt])
      (fun bi hbi bs _ hne => by
        by_cases hbs10 : bs = 10
        · have hbi_ne : bi ≠ w := hne.resolve_right (fun h => h hbs10)
          rw [hbs10]; simp [slotVal, hbi, hbi_ne.symm]
        · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                       bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact absurd rfl hbs10 | simp only [slotVal, hbi, ↓reduceIte])
  have hmax : Nat.max allocLen (w + 2) = allocLen := by simp only [Nat.max_eq_max]; omega
  obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_moveBlockRight (Sp := Sp) hbt₁ hw_lt (by rw [hmax]; exact hsp)
  rw [hmax] at hbt₂
  obtain ⟨t₃, hbt₃, hr₃⟩ :=
    ProgRuns_writeSlot_spec ⟨10, by decide⟩ true
      (inBits' := inBits) (nLen' := nLen) (cBits' := cBits) (preBits' := preBits)
      (vSub' := vSub) (rMark' := rMark) (wMark' := some (w + 1))
      hbt₂ hw1 hsp hbt₂.2.1 hbt₂.2.2.1 hbt₂.2.2.2.1 hbt₂.2.2.2.2.1 hbt₂.2.2.2.2.2.1
      hbt₂.2.2.2.2.2.2.1 (fun w' hw' => by cases hw'; exact hw1)
      (by simp [slotVal, hw1])
      (fun bi hbi bs _ hne => by
        by_cases hbs10 : bs = 10
        · have hbi_ne : bi ≠ w + 1 := hne.resolve_right (fun h => h hbs10)
          rw [hbs10]; simp [slotVal, hbi, hbi_ne.symm]
        · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                       bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact absurd rfl hbs10 | simp only [slotVal, hbi, ↓reduceIte])
  obtain ⟨t₄, hbt₄, hr₄⟩ := ProgRuns_rewindToBlock0 hbt₃ hw1 hsp
  refine ⟨t₄, hbt₄, ?_⟩
  exact (ProgRuns_seq hr₁ (ProgRuns_seq hr₂ (ProgRuns_seq hr₃ hr₄))).mono
    (Nat.le_refl Sp) (by omega)

lemma tapeWrite2_append_self (l : List Bool) (b : Bool) :
    QCSD_tapeWrite2 l l.length b = l ++ [b] := by
  unfold QCSD_tapeWrite2
  rw [ite_eq_right (Nat.lt_irrefl l.length)]
  have hsub : l.length + 1 - l.length = 1 := by omega
  rw [hsub]
  simp

def emitSubBitProg (b : Bool) :=
  seqProg (seekMarkProg ⟨10, by decide⟩)
    (seqProg (writeSlotProg ⟨8, by decide⟩ b)
      (advanceMarkProg ⟨10, by decide⟩))

lemma ProgRuns_emitSubBit (b : Bool) {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark : Option ℕ} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark (some vSub.length) tape)
    (hw1 : vSub.length + 1 < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits (vSub ++ [b]) rMark
        (some (vSub.length + 1)) tape' ∧
      ProgRuns (emitSubBitProg b) Sp (122 * allocLen + 200) (tape, base) () (tape', base) := by
  have hw_lt : vSub.length < allocLen := by omega
  obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_seekWMark hbt hw_lt hsp
  obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_writeSubTape b hbt₁ hw_lt hsp
  rw [tapeWrite2_append_self] at hbt₂
  obtain ⟨t₃, hbt₃, hr₃⟩ := ProgRuns_advanceWMark hbt₂ hw1 hsp
  refine ⟨t₃, hbt₃, ?_⟩
  exact (ProgRuns_seq hr₁ (ProgRuns_seq hr₂ hr₃)).mono (Nat.le_refl Sp) (by omega)

lemma ProgRuns_setRMark0 {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {wMark : Option ℕ} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub none wMark tape)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub (some 0) wMark tape' ∧
      ProgRuns (writeSlotProg ⟨9, by decide⟩ true) Sp 20 (tape, base) () (tape', base) := by
  have h0 : 0 < allocLen := hbt.1
  obtain ⟨t', hbt', hr⟩ :=
    ProgRuns_writeSlot_spec ⟨9, by decide⟩ true
      (inBits' := inBits) (nLen' := nLen) (cBits' := cBits) (preBits' := preBits)
      (vSub' := vSub) (rMark' := some 0) (wMark' := wMark)
      hbt h0 hsp hbt.2.1 hbt.2.2.1 hbt.2.2.2.1 hbt.2.2.2.2.1 hbt.2.2.2.2.2.1
      (fun r hr => by cases hr; exact h0) hbt.2.2.2.2.2.2.2.1
      (by simp [slotVal, h0])
      (fun bi hbi bs _ hne => by
        by_cases hbs9 : bs = 9
        · have hbi_ne : bi ≠ 0 := hne.resolve_right (fun h => h hbs9)
          rw [hbs9]; simp [slotVal, hbi, hbi_ne.symm]
        · unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
          rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                       bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
            h | h | h | h | h | h | h | h | h | h | h <;> (rw [h] at hbs9 ⊢; simp at hbs9 ⊢))
  have hbz : base + 11 * 0 = base := by omega
  rw [hbz] at hr
  exact ⟨t', hbt', hr⟩

lemma ProgRuns_setWMark0 {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark : Option ℕ} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark none tape)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub rMark (some 0) tape' ∧
      ProgRuns (writeSlotProg ⟨10, by decide⟩ true) Sp 20 (tape, base) () (tape', base) := by
  have h0 : 0 < allocLen := hbt.1
  obtain ⟨t', hbt', hr⟩ :=
    ProgRuns_writeSlot_spec ⟨10, by decide⟩ true
      (inBits' := inBits) (nLen' := nLen) (cBits' := cBits) (preBits' := preBits)
      (vSub' := vSub) (rMark' := rMark) (wMark' := some 0)
      hbt h0 hsp hbt.2.1 hbt.2.2.1 hbt.2.2.2.1 hbt.2.2.2.2.1 hbt.2.2.2.2.2.1
      hbt.2.2.2.2.2.2.1 (fun w hw => by cases hw; exact h0)
      (by simp [slotVal, h0])
      (fun bi hbi bs _ hne => by
        by_cases hbs10 : bs = 10
        · have hbi_ne : bi ≠ 0 := hne.resolve_right (fun h => h hbs10)
          rw [hbs10]; simp [slotVal, hbi, hbi_ne.symm]
        · unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
          rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                       bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
            h | h | h | h | h | h | h | h | h | h | h <;> (rw [h] at hbs10 ⊢; simp at hbs10 ⊢))
  have hbz : base + 11 * 0 = base := by omega
  rw [hbz] at hr
  exact ⟨t', hbt', hr⟩

lemma ProgRuns_clearRMarkAndRewind {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {r : ℕ} {wMark : Option ℕ} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub (some r) wMark tape)
    (hr_lt : r < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub none wMark tape' ∧
      ProgRuns (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog)
        Sp (51 * allocLen + 50) (tape, base + 11 * r) () (tape', base) := by
  obtain ⟨t₁, hbt₁, hr₁⟩ :=
    ProgRuns_writeSlot_spec ⟨9, by decide⟩ false
      (inBits' := inBits) (nLen' := nLen) (cBits' := cBits) (preBits' := preBits)
      (vSub' := vSub) (rMark' := none) (wMark' := wMark)
      hbt hr_lt hsp hbt.2.1 hbt.2.2.1 hbt.2.2.2.1 hbt.2.2.2.2.1 hbt.2.2.2.2.2.1
      (fun _ h => by cases h) hbt.2.2.2.2.2.2.2.1
      (by simp [slotVal, hr_lt])
      (fun bi hbi bs _ hne => by
        by_cases hbs9 : bs = 9
        · have hbi_ne : bi ≠ r := hne.resolve_right (fun h => h hbs9)
          rw [hbs9]; simp [slotVal, hbi, hbi_ne.symm]
        · unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
          rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                       bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
            h | h | h | h | h | h | h | h | h | h | h <;> (rw [h] at hbs9 ⊢; simp at hbs9 ⊢))
  obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_rewindToBlock0 hbt₁ hr_lt hsp
  exact ⟨t₂, hbt₂, (ProgRuns_seq hr₁ hr₂).mono (Nat.le_refl Sp) (by omega)⟩

def copyRangeToSubProg (validSlot valSlot : Fin 11) :=
  seqProg (writeSlotProg ⟨9, by decide⟩ true)
    (whileProg
      (seqProg (seekMarkProg ⟨9, by decide⟩)
        (bindProg (readSlotProg validSlot) (fun isValid =>
          ifProg isValid
            (bindProg (readSlotProg valSlot) (fun b =>
              seqProg (advanceMarkProg ⟨9, by decide⟩)
                (mapExitProg (fun _ => true) (emitSubBitProg b))))
            (mapExitProg (fun _ => false)
              (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog))))))

lemma ProgRuns_copyRangeToSub (validSlot valSlot : Fin 11) (src : List Bool)
    {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub none (some vSub.length) tape)
    (hcap : vSub.length + src.length + 1 < allocLen)
    (hsrc_lt : src.length < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp)
    (hValid : ∀ (r : ℕ) (vS : List Bool) (wM : Option ℕ), r < allocLen →
      slotVal allocLen inBits nLen cBits preBits vS (some r) wM r validSlot.val =
        decide (r < src.length))
    (hVal : ∀ (r : ℕ) (hr : r < src.length) (vS : List Bool) (wM : Option ℕ),
      slotVal allocLen inBits nLen cBits preBits vS (some r) wM r valSlot.val = src[r]) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits (vSub ++ src) none
        (some (vSub.length + src.length)) tape' ∧
      ProgRuns (copyRangeToSubProg validSlot valSlot) Sp
        ((300 * allocLen + 500) * (src.length + 1)) (tape, base) () (tape', base) := by
  obtain ⟨t₀, hbt₀, hrSet⟩ := ProgRuns_setRMark0 hbt hsp
  let loopBody :=
    seqProg (seekMarkProg ⟨9, by decide⟩)
      (bindProg (readSlotProg validSlot) (fun isValid =>
        ifProg isValid
          (bindProg (readSlotProg valSlot) (fun b =>
            seqProg (advanceMarkProg ⟨9, by decide⟩)
              (mapExitProg (fun _ => true) (emitSubBitProg b))))
          (mapExitProg (fun _ => false)
            (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog))))
  have hloop : ∀ (rem r : ℕ), r + rem = src.length → ∀ t_cur : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits (vSub ++ src.take r)
        (some r) (some (vSub.length + r)) t_cur →
      ∃ t_end : List Bool,
        BlockTape base allocLen inBits nLen cBits preBits (vSub ++ src)
          none (some (vSub.length + src.length)) t_end ∧
        ProgRuns (whileProg loopBody) Sp
          ((300 * allocLen + 500) * rem + (150 * allocLen + 200))
          (t_cur, base) () (t_end, base) := by
    intro rem
    induction rem with
    | zero =>
      intro r hr_eq t_cur hbt_c
      have hr_s : r = src.length := by omega
      subst hr_s
      rw [List.take_length] at hbt_c
      obtain ⟨t₁, hbt₁, hrSeek⟩ := ProgRuns_seekRMark hbt_c hsrc_lt hsp
      obtain ⟨t₂, hbt₂, hrReadV⟩ := ProgRuns_readSlot validSlot hbt₁ hsrc_lt hsp
      rw [hValid src.length _ _ hsrc_lt, decide_eq_false (Nat.lt_irrefl _)] at hrReadV
      obtain ⟨t₃, hbt₃, hrClr⟩ := ProgRuns_clearRMarkAndRewind hbt₂ hsrc_lt hsp
      refine ⟨t₃, hbt₃, ?_⟩
      rw [Nat.mul_zero, Nat.zero_add]
      have hExit := ProgRuns_seq hrSeek
        (ProgRuns_bind (k := fun isValid =>
          ifProg isValid
            (bindProg (readSlotProg valSlot) (fun b =>
              seqProg (advanceMarkProg ⟨9, by decide⟩)
                (mapExitProg (fun _ => true) (emitSubBitProg b))))
            (mapExitProg (fun _ => false)
              (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog)))
          hrReadV (ProgRuns_if_false (ProgRuns_mapExit (fun _ => false) hrClr)))
      exact (ProgRuns_while_false hExit).mono (Nat.le_refl Sp) (by omega)
    | succ rem ih =>
      intro r hr_eq t_cur hbt_c
      have hr_lt_src : r < src.length := by omega
      have hr_lt : r < allocLen := by omega
      have hr1_lt : r + 1 < allocLen := by omega
      obtain ⟨t₁, hbt₁, hrSeek⟩ := ProgRuns_seekRMark hbt_c hr_lt hsp
      obtain ⟨t₂, hbt₂, hrReadV⟩ := ProgRuns_readSlot validSlot hbt₁ hr_lt hsp
      rw [hValid r _ _ hr_lt, decide_eq_true hr_lt_src] at hrReadV
      obtain ⟨t₃, hbt₃, hrReadB⟩ := ProgRuns_readSlot valSlot hbt₂ hr_lt hsp
      rw [hVal r hr_lt_src _ _] at hrReadB
      obtain ⟨t₄, hbt₄, hrAdvR⟩ := ProgRuns_advanceRMark hbt₃ hr1_lt hsp
      have hvlen : (vSub ++ src.take r).length = vSub.length + r := by
        simp [Nat.min_eq_left (Nat.le_of_lt hr_lt_src)]
      rw [← hvlen] at hbt₄
      obtain ⟨t₅, hbt₅, hrEmit⟩ :=
        ProgRuns_emitSubBit src[r] hbt₄ (by rw [hvlen]; omega) hsp
      have htake_succ : (vSub ++ src.take r) ++ [src[r]] = vSub ++ src.take (r + 1) := by
        rw [List.append_assoc, List.take_concat_get' src r hr_lt_src]
      rw [hvlen, htake_succ] at hbt₅
      obtain ⟨t_end, hbt_end, hrRest⟩ := ih (r + 1) (by omega) t₅ hbt₅
      refine ⟨t_end, hbt_end, ?_⟩
      have hbody : ProgRuns loopBody Sp (300 * allocLen + 500) (t_cur, base) true (t₅, base) := by
        refine (ProgRuns_seq hrSeek
          (ProgRuns_bind (k := fun isValid =>
            ifProg isValid
              (bindProg (readSlotProg valSlot) (fun b =>
                seqProg (advanceMarkProg ⟨9, by decide⟩)
                  (mapExitProg (fun _ => true) (emitSubBitProg b))))
              (mapExitProg (fun _ => false)
                (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog)))
            hrReadV (ProgRuns_if_true
              (ProgRuns_bind (k := fun b =>
                seqProg (advanceMarkProg ⟨9, by decide⟩)
                  (mapExitProg (fun _ => true) (emitSubBitProg b)))
                hrReadB (ProgRuns_seq hrAdvR (ProgRuns_mapExit (fun _ => true) hrEmit)))))).mono
          (Nat.le_refl Sp) (by omega)
      exact (ProgRuns_while_true hbody hrRest).mono (Nat.le_refl Sp) (by
        rw [Nat.mul_succ]; omega)
  have hbt₀' : BlockTape base allocLen inBits nLen cBits preBits (vSub ++ src.take 0)
      (some 0) (some (vSub.length + 0)) t₀ := by simpa using hbt₀
  obtain ⟨t_end, hbt_end, hrL⟩ := hloop src.length 0 (Nat.zero_add _) t₀ hbt₀'
  refine ⟨t_end, hbt_end, ?_⟩
  exact (ProgRuns_seq hrSet hrL).mono (Nat.le_refl Sp) (by rw [Nat.mul_add, Nat.mul_one]; omega)

def prepareSubInputProg :=
  seqProg (writeSlotProg ⟨10, by decide⟩ true)
    (seqProg (copyRangeToSubProg ⟨2, by decide⟩ ⟨3, by decide⟩)
      (seqProg (copyRangeToSubProg ⟨6, by decide⟩ ⟨0, by decide⟩)
        (seqProg (emitSubBitProg false)
          (seqProg (copyRangeToSubProg ⟨6, by decide⟩ ⟨7, by decide⟩)
            (seqProg (seekMarkProg ⟨10, by decide⟩)
              (seqProg (writeSlotProg ⟨10, by decide⟩ false)
                rewindToBlock0Prog))))))

lemma ProgRuns_prepareSubInput {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits : List Bool} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits [] none none tape)
    (hcap : inBits.length + 2 * preBits.length + 2 < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits
        (inBits ++ QCSD_natToUnary preBits.length ++ preBits) none none tape' ∧
      ProgRuns prepareSubInputProg Sp ((1200 * allocLen + 2500) * (allocLen + 1))
        (tape, base) () (tape', base) := by
  obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_setWMark0 hbt hsp
  have h0len : ([] : List Bool).length = 0 := rfl
  rw [← h0len] at hbt₁
  obtain ⟨t₂, hbt₂, hr₂⟩ :=
    ProgRuns_copyRangeToSub ⟨2, by decide⟩ ⟨3, by decide⟩ inBits hbt₁
      (by simp; omega) (by omega) hsp
      (fun r _ _ hr => by simp [slotVal, hr])
      (fun r hr _ _ => by
        have hr_lt : r < allocLen := by omega
        simp [slotVal, hr_lt, QCSD_tapeRead, List.getD_eq_getElem?_getD, hr])
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hbt₂
  let uOnes := List.replicate preBits.length true
  obtain ⟨t₃, hbt₃, hr₃⟩ :=
    ProgRuns_copyRangeToSub ⟨6, by decide⟩ ⟨0, by decide⟩ uOnes hbt₂
      (by simp [uOnes]; omega) (by simp [uOnes]; omega) hsp
      (fun r _ _ hr => by simp [slotVal, hr, uOnes])
      (fun r hr _ _ => by
        have hr_lt : r < allocLen := by simp [uOnes] at hr; omega
        simp [slotVal, hr_lt, uOnes])
  have hlen2 : (inBits ++ uOnes).length = inBits.length + uOnes.length := List.length_append
  rw [← hlen2] at hbt₃
  obtain ⟨t₄, hbt₄, hr₄⟩ :=
    ProgRuns_emitSubBit false hbt₃ (by simp [uOnes]; omega) hsp
  have hunary : (inBits ++ uOnes) ++ [false] = inBits ++ QCSD_natToUnary preBits.length := by
    simp [uOnes, QCSD_natToUnary, List.append_assoc]
  have hlen3 : (inBits ++ uOnes).length + 1 = (inBits ++ QCSD_natToUnary preBits.length).length := by
    rw [← hunary]; simp; omega
  rw [hlen3, hunary] at hbt₄
  obtain ⟨t₅, hbt₅, hr₅⟩ :=
    ProgRuns_copyRangeToSub ⟨6, by decide⟩ ⟨7, by decide⟩ preBits hbt₄
      (by simp [QCSD_natToUnary]; omega) (by omega) hsp
      (fun r _ _ hr => by simp [slotVal, hr])
      (fun r hr _ _ => by
        have hr_lt : r < allocLen := by omega
        simp [slotVal, hr_lt, QCSD_tapeRead, List.getD_eq_getElem?_getD, hr])
  let fullSub := inBits ++ QCSD_natToUnary preBits.length ++ preBits
  have hlen5 : (inBits ++ QCSD_natToUnary preBits.length).length + preBits.length = fullSub.length :=
    List.length_append.symm
  rw [hlen5] at hbt₅
  have hfull_lt : fullSub.length < allocLen := by
    dsimp [fullSub, QCSD_natToUnary]; simp; omega
  obtain ⟨t₆, hbt₆, hr₆⟩ := ProgRuns_seekWMark hbt₅ hfull_lt hsp
  obtain ⟨t₇, hbt₇, hr₇⟩ :=
    ProgRuns_writeSlot_spec ⟨10, by decide⟩ false
      (inBits' := inBits) (nLen' := nLen) (cBits' := cBits) (preBits' := preBits)
      (vSub' := fullSub) (rMark' := none) (wMark' := none)
      hbt₆ hfull_lt hsp hbt₆.2.1 hbt₆.2.2.1 hbt₆.2.2.2.1 hbt₆.2.2.2.2.1 hbt₆.2.2.2.2.2.1
      hbt₆.2.2.2.2.2.2.1 (fun _ h => by cases h)
      (by simp [slotVal, hfull_lt])
      (fun bi hbi bs _ hne => by
        by_cases hbs10 : bs = 10
        · have hbi_ne : bi ≠ fullSub.length := hne.resolve_right (fun h => h hbs10)
          rw [hbs10]; simp [slotVal, hbi, hbi_ne.symm]
        · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                       bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact absurd rfl hbs10 | simp only [slotVal, hbi, ↓reduceIte, fullSub])
  obtain ⟨t₈, hbt₈, hr₈⟩ := ProgRuns_rewindToBlock0 hbt₇ hfull_lt hsp
  refine ⟨t₈, hbt₈, ?_⟩
  have hbound :
      20 + ((300 * allocLen + 500) * (inBits.length + 1) +
        ((300 * allocLen + 500) * (uOnes.length + 1) +
          ((122 * allocLen + 200) +
            ((300 * allocLen + 500) * (preBits.length + 1) +
              ((71 * fullSub.length + 22) + (20 + (51 * fullSub.length + 22))))))) ≤
        (1200 * allocLen + 2500) * (allocLen + 1) := by
    have hu : uOnes.length ≤ allocLen := by simp [uOnes]; omega
    have hin : inBits.length ≤ allocLen := by omega
    have hpr : preBits.length ≤ allocLen := by omega
    have hf : fullSub.length ≤ allocLen := by omega
    nlinarith
  exact (ProgRuns_seq hr₁ (ProgRuns_seq hr₂ (ProgRuns_seq hr₃
    (ProgRuns_seq hr₄ (ProgRuns_seq hr₅ (ProgRuns_seq hr₆ (ProgRuns_seq hr₇ hr₈))))))).mono
    (Nat.le_refl Sp) hbound

/-! ### Section 6b: `evalPrefixProg`, Count Scanners, `greedyLoopProg` & `unpackOutputProg` -/

def ProgState {Q E : Type} (_ : Prog Q E) : Type := Q

@[instance_reducible]
def sumFintype {α β : Type} (hα : Fintype α) (hβ : Fintype β) : Fintype (α ⊕ β) :=
  let _ := hα; let _ := hβ; inferInstance
@[instance_reducible]
def prodFintype {α β : Type} (hα : Fintype α) (hβ : Fintype β) : Fintype (α × β) :=
  let _ := hα; let _ := hβ; inferInstance

def sumDecEq {α β : Type} (hα : DecidableEq α) (hβ : DecidableEq β) : DecidableEq (α ⊕ β) :=
  let _ := hα; let _ := hβ; inferInstance
def prodDecEq {α β : Type} (hα : DecidableEq α) (hβ : DecidableEq β) : DecidableEq (α × β) :=
  let _ := hα; let _ := hβ; inferInstance

def EvalPrefixRaw (M_net A : QCSD_DetTM) :=
  seqProg clearSubTapeProg
    (seqProg prepareSubInputProg
      (seqProg (simTMProg M_net)
        (seqProg rewindToBlock0Prog
          (seqProg (simTMProg A) rewindToBlock0Prog))))

def EvalPrefixQ (M_net A : QCSD_DetTM) : Type := ProgState (EvalPrefixRaw M_net A)

instance (M_net A : QCSD_DetTM) : Fintype (EvalPrefixQ M_net A) := by
  unfold EvalPrefixQ ProgState
  repeat first
    | apply sumFintype
    | apply prodFintype
    | exact M_net.fintypeQ
    | exact A.fintypeQ
    | infer_instance

instance (M_net A : QCSD_DetTM) : DecidableEq (EvalPrefixQ M_net A) := by
  unfold EvalPrefixQ ProgState
  repeat first
    | apply sumDecEq
    | apply prodDecEq
    | exact M_net.decEqQ
    | exact A.decEqQ
    | infer_instance

def evalPrefixProg (M_net A : QCSD_DetTM) : Prog (EvalPrefixQ M_net A) Unit :=
  EvalPrefixRaw M_net A

lemma ProgRuns_evalPrefix (M_net A : QCSD_DetTM)
    {Sp SpM SpA TM TA base allocLen : ℕ}
    {inBits : List Bool} {nLen : ℕ} {cBits preBits vSub : List Bool}
    {tape encNet : List Bool} {cntVal : ℕ}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub none none tape)
    (hcap : inBits.length + 2 * preBits.length + 2 < allocLen + 1)
    (hM : ∃ k₁ ≤ TM,
      (QCSD_configAt2 M_net (inBits ++ QCSD_natToUnary preBits.length ++ preBits) k₁).state = M_net.qhalt ∧
      tapeEq (QCSD_configAt2 M_net (inBits ++ QCSD_natToUnary preBits.length ++ preBits) k₁).tape encNet ∧
      (∀ j ≤ k₁, QCSD_spaceUse2 (QCSD_configAt2 M_net (inBits ++ QCSD_natToUnary preBits.length ++ preBits) j) ≤ SpM))
    (hA : ∃ k₂ ≤ TA,
      (QCSD_configAt2 A encNet k₂).state = A.qhalt ∧
      QCSD_bitsToNat (QCSD_configAt2 A encNet k₂).tape = cntVal ∧
      (∀ j ≤ k₂, QCSD_spaceUse2 (QCSD_configAt2 A encNet j) ≤ SpA))
    (hsp : base + 11 * (Nat.max (Nat.max (allocLen + 1) (SpM + 1)) (SpA + 1) + 1) ≤ Sp) :
    let aMax := Nat.max (Nat.max (allocLen + 1) (SpM + 1)) (SpA + 1)
    ∃ allocLen' vSub' tape',
      allocLen + 1 ≤ allocLen' ∧
      allocLen' ≤ aMax ∧
      QCSD_bitsToNat vSub' = cntVal ∧
      BlockTape base allocLen' inBits nLen cBits preBits vSub' none none tape' ∧
      ProgRuns (evalPrefixProg M_net A) Sp
        ((1500 * aMax + 3000) * (aMax + 1) + 92 * TM + 92 * TA)
        (tape, base) () (tape', base) := by
  let aMax := Nat.max (Nat.max (allocLen + 1) (SpM + 1)) (SpA + 1)
  have ha1 : allocLen + 1 ≤ aMax :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_clearSubTape (Sp := Sp) hbt (by omega)
  obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_prepareSubInput (Sp := Sp) hbt₁ hcap (by omega)
  obtain ⟨k₁, hk₁, hhalt₁, heq₁, hspM₁⟩ := hM
  obtain ⟨aL₃, vS₃, t₃, hout₃, ⟨haL₃_ge, haL₃⟩, hhout₃, heqM, hbt₃, hr₃⟩ :=
    ProgRuns_simTM M_net (Sp := Sp) (SpM := SpM) (k := k₁)
      hbt₂ (tapeEq_refl _) hhalt₁ hspM₁ (by simp only [Nat.max_eq_max] at hsp ⊢; omega)
  have haL₃_le : aL₃ ≤ aMax := by
    simp only [aMax, Nat.max_eq_max] at haL₃ ⊢; omega
  obtain ⟨t₄, hbt₄, hr₄⟩ := ProgRuns_rewindToBlock0 (Sp := Sp) hbt₃ hhout₃ (by omega)
  obtain ⟨k₂, hk₂, hhalt₂, hbits₂, hspA₂⟩ := hA
  have heq_enc_vS₃ : tapeEq encNet vS₃ := tapeEq_trans (tapeEq_symm heq₁) heqM
  obtain ⟨aL₅, vS₅, t₅, hout₅, ⟨haL₅_ge, haL₅⟩, hhout₅, heqA, hbt₅, hr₅⟩ :=
    ProgRuns_simTM A (Sp := Sp) (SpM := SpA) (k := k₂)
      hbt₄ heq_enc_vS₃ hhalt₂ hspA₂ (by
        simp only [aMax, Nat.max_eq_max] at haL₃_le hsp ⊢; omega)
  have haL₅_le : aL₅ ≤ aMax := by
    simp only [aMax, Nat.max_eq_max] at haL₃_le haL₅ ⊢; omega
  obtain ⟨t₆, hbt₆, hr₆⟩ := ProgRuns_rewindToBlock0 (Sp := Sp) hbt₅ hhout₅ (by omega)
  have hbits_eq : QCSD_bitsToNat vS₅ = cntVal :=
    (bitsToNat_of_tapeEq (tapeEq_symm heqA)).trans hbits₂
  refine ⟨aL₅, vS₅, t₆, haL₃_ge.trans haL₅_ge, haL₅_le, hbits_eq, hbt₆, ?_⟩
  have hT :
      (110 * allocLen + 90) +
        (((1200 * (allocLen + 1) + 2500) * ((allocLen + 1) + 1)) +
          ((91 * k₁ + 2) + ((51 * hout₃ + 22) + ((91 * k₂ + 2) + (51 * hout₅ + 22))))) ≤
        (1500 * aMax + 3000) * (aMax + 1) + 92 * TM + 92 * TA := by
    have ho3 : hout₃ ≤ aMax := by omega
    have ho5 : hout₅ ≤ aMax := by omega
    nlinarith
  exact (ProgRuns_seq hr₁ (ProgRuns_seq hr₂ (ProgRuns_seq hr₃
    (ProgRuns_seq hr₄ (ProgRuns_seq hr₅ hr₆))))).mono (Nat.le_refl Sp) hT

def scanCountPosProg :
    Prog (Bool × ((Fin 20 × Bool) ⊕ (Bool × (((Fin 20 × Bool) ⊕
      (Bool × (Fin 11 ⊕ ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ (Fin 20 × Unit))))))) ⊕
      ((Fin 20 × Bool) ⊕ (Bool × (((Unit ⊕ Unit) ⊕
        ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ Fin 11))))))))))) Bool :=
  loopStateProg false (fun acc =>
    bindProg (readSlotProg ⟨4, by decide⟩) (fun isN =>
      ifProg isN
        (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
          mapExitProg (fun _ => Sum.inl (acc || b)) moveBlockRightProg))
        (mapExitProg (fun _ => Sum.inr acc) rewindToBlock0Prog)))

lemma ProgRuns_scanCountPos {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub none none tape)
    (hnLen : nLen < allocLen)
    (hlt : QCSD_bitsToNat vSub < 2 ^ nLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub none none tape' ∧
      ProgRuns scanCountPosProg Sp (150 * nLen + 100)
        (tape, base) (decide (0 < QCSD_bitsToNat vSub)) (tape', base) := by
  let stepFn (acc : Bool) :=
    bindProg (readSlotProg ⟨4, by decide⟩) (fun isN =>
      ifProg isN
        (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
          mapExitProg (fun _ => Sum.inl (acc || b)) moveBlockRightProg))
        (mapExitProg (fun _ => Sum.inr acc) rewindToBlock0Prog))
  have hloop : ∀ (rem i : ℕ), i + rem = nLen → ∀ (acc : Bool) (t₀ : List Bool),
      (acc = true ↔ ∃ j < i, QCSD_tapeRead vSub j = true) →
      BlockTape base allocLen inBits nLen cBits preBits vSub none none t₀ →
      ∃ tape' : List Bool,
        BlockTape base allocLen inBits nLen cBits preBits vSub none none tape' ∧
        ProgRuns (loopStateProg acc stepFn) Sp (91 * rem + (51 * nLen + 50))
          (t₀, base + 11 * i) (decide (0 < QCSD_bitsToNat vSub)) (tape', base) := by
    intro rem
    induction rem with
    | zero =>
      intro i hi_eq acc t₀ hacc hbt₀
      have hi_n : i = nLen := by omega
      subst hi_n
      obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨4, by decide⟩ hbt₀ hnLen hsp
      have hsv : slotVal allocLen inBits i cBits preBits vSub none none i 4 = false := by
        simp [slotVal, hnLen]
      rw [hsv] at hr₁
      obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_rewindToBlock0 hbt₁ hnLen hsp
      have hacc_eq : acc = decide (0 < QCSD_bitsToNat vSub) := by
        cases acc with
        | true =>
          have hex : ∃ j : Fin i, QCSD_tapeRead vSub j.val = true := by
            obtain ⟨j, hj, hb⟩ := hacc.mp rfl
            exact ⟨⟨j, hj⟩, hb⟩
          exact (decide_eq_true ((bitsToNat_ofFn_pos_iff vSub i hlt).mpr hex)).symm
        | false =>
          apply (decide_eq_false ?_).symm
          intro hpos
          obtain ⟨j, hb⟩ := (bitsToNat_ofFn_pos_iff vSub i hlt).mp hpos
          exact Bool.false_ne_true (hacc.mpr ⟨j.val, j.isLt, hb⟩)
      refine ⟨t₂, hbt₂, ?_⟩
      rw [← hacc_eq, Nat.mul_zero, Nat.zero_add]
      have hExit := ProgRuns_bind (k := fun isN =>
        ifProg isN
          (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
            mapExitProg (fun _ => Sum.inl (acc || b)) moveBlockRightProg))
          (mapExitProg (fun _ => Sum.inr acc) rewindToBlock0Prog))
        hr₁ (ProgRuns_if_false (ProgRuns_mapExit (fun _ => Sum.inr acc) hr₂))
      exact (ProgRuns_loopState_exit hExit).mono (Nat.le_refl Sp) (by omega)
    | succ rem ih =>
      intro i hi_eq acc t₀ hacc hbt₀
      have hi_lt_n : i < nLen := by omega
      have hi_lt : i < allocLen := by omega
      obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨4, by decide⟩ hbt₀ hi_lt hsp
      have hsv4 : slotVal allocLen inBits nLen cBits preBits vSub none none i 4 = true := by
        simp [slotVal, hi_lt, hi_lt_n]
      rw [hsv4] at hr₁
      obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_readSlot ⟨8, by decide⟩ hbt₁ hi_lt hsp
      have hsv8 : slotVal allocLen inBits nLen cBits preBits vSub none none i 8 =
          QCSD_tapeRead vSub i := by
        simp [slotVal, hi_lt]
      rw [hsv8] at hr₂
      have hmax : Nat.max allocLen (i + 2) = allocLen := by simp only [Nat.max_eq_max]; omega
      obtain ⟨t₃, hbt₃, hr₃⟩ :=
        ProgRuns_moveBlockRight (Sp := Sp) hbt₂ hi_lt (by rw [hmax]; exact hsp)
      rw [hmax] at hbt₃
      let acc' := acc || QCSD_tapeRead vSub i
      have hacc' : acc' = true ↔ ∃ j < i + 1, QCSD_tapeRead vSub j = true := by
        dsimp [acc']
        rw [Bool.or_eq_true, hacc]
        constructor
        · rintro (⟨j, hj, hb⟩ | hb)
          · exact ⟨j, by omega, hb⟩
          · exact ⟨i, by omega, hb⟩
        · rintro ⟨j, hj, hb⟩
          by_cases hji : j < i
          · exact Or.inl ⟨j, hji, hb⟩
          · have : j = i := by omega
            subst this; exact Or.inr hb
      obtain ⟨t₄, hbt₄, hrRest⟩ := ih (i + 1) (by omega) acc' t₃ hacc' hbt₃
      refine ⟨t₄, hbt₄, ?_⟩
      have hStep := ProgRuns_bind (k := fun isN =>
        ifProg isN
          (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
            mapExitProg (fun _ => Sum.inl (acc || b)) moveBlockRightProg))
          (mapExitProg (fun _ => Sum.inr acc) rewindToBlock0Prog))
        hr₁ (ProgRuns_if_true
          (ProgRuns_bind (k := fun b =>
            mapExitProg (fun _ => Sum.inl (acc || b)) moveBlockRightProg)
            hr₂ (ProgRuns_mapExit (fun _ => Sum.inl acc') hr₃)))
      exact (ProgRuns_loopState_cont hStep hrRest).mono (Nat.le_refl Sp) (by
        rw [Nat.mul_succ]; omega)
  obtain ⟨t', hbt', hr⟩ := hloop nLen 0 (Nat.zero_add nLen) false tape
    (by simp) hbt
  have hbz : base + 11 * 0 = base := by omega
  rw [hbz] at hr
  exact ⟨t', hbt', hr.mono (Nat.le_refl Sp) (by omega)⟩

def scanAndSaveCountProg :
    Prog (Bool × ((Fin 20 × Bool) ⊕ (Bool × (((Fin 20 × Bool) ⊕
      (Bool × ((Fin 20 × Unit) ⊕
        (Fin 11 ⊕ ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ (Fin 20 × Unit)))))))) ⊕
      ((Fin 20 × Bool) ⊕ (Bool × (((Unit ⊕ Unit) ⊕
        ((Fin 20 × Bool) ⊕ (Bool × ((Unit ⊕ Unit) ⊕ Fin 11))))))))))) Bool :=
  loopStateProg false (fun acc =>
    bindProg (readSlotProg ⟨4, by decide⟩) (fun isN =>
      ifProg isN
        (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
          seqProg (writeSlotProg ⟨5, by decide⟩ b)
            (mapExitProg (fun _ => Sum.inl (acc || b)) moveBlockRightProg)))
        (mapExitProg (fun _ => Sum.inr acc) rewindToBlock0Prog)))

lemma ProgRuns_scanAndSaveCount {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {preBits vSub : List Bool} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen [] preBits vSub none none tape)
    (hnLen : nLen < allocLen)
    (hlt : QCSD_bitsToNat vSub < 2 ^ nLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    let cOut := List.ofFn (fun j : Fin nLen => QCSD_tapeRead vSub j.val)
    ∃ tape' : List Bool,
      cOut.length = nLen ∧
      QCSD_bitsToNat cOut = QCSD_bitsToNat vSub ∧
      BlockTape base allocLen inBits nLen cOut preBits vSub none none tape' ∧
      ProgRuns scanAndSaveCountProg Sp (180 * nLen + 100)
        (tape, base) (decide (0 < QCSD_bitsToNat vSub)) (tape', base) := by
  let cOut := List.ofFn (fun j : Fin nLen => QCSD_tapeRead vSub j.val)
  let stepFn (acc : Bool) :=
    bindProg (readSlotProg ⟨4, by decide⟩) (fun isN =>
      ifProg isN
        (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
          seqProg (writeSlotProg ⟨5, by decide⟩ b)
            (mapExitProg (fun _ => Sum.inl (acc || b)) moveBlockRightProg)))
        (mapExitProg (fun _ => Sum.inr acc) rewindToBlock0Prog))
  have hloop : ∀ (rem i : ℕ), i + rem = nLen → ∀ (acc : Bool) (t₀ : List Bool),
      (acc = true ↔ ∃ j < i, QCSD_tapeRead vSub j = true) →
      BlockTape base allocLen inBits nLen (cOut.take i) preBits vSub none none t₀ →
      ∃ tape' : List Bool,
        BlockTape base allocLen inBits nLen cOut preBits vSub none none tape' ∧
        ProgRuns (loopStateProg acc stepFn) Sp (111 * rem + (51 * nLen + 50))
          (t₀, base + 11 * i) (decide (0 < QCSD_bitsToNat vSub)) (tape', base) := by
    intro rem
    induction rem with
    | zero =>
      intro i hi_eq acc t₀ hacc hbt₀
      have hi_n : i = nLen := by omega
      subst hi_n
      have htake_full : cOut.take i = cOut := List.take_of_length_le (by simp [cOut])
      rw [htake_full] at hbt₀
      obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨4, by decide⟩ hbt₀ hnLen hsp
      have hsv : slotVal allocLen inBits i cOut preBits vSub none none i 4 = false := by
        simp [slotVal, hnLen]
      rw [hsv] at hr₁
      obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_rewindToBlock0 hbt₁ hnLen hsp
      have hacc_eq : acc = decide (0 < QCSD_bitsToNat vSub) := by
        cases acc with
        | true =>
          have hex : ∃ j : Fin i, QCSD_tapeRead vSub j.val = true := by
            obtain ⟨j, hj, hb⟩ := hacc.mp rfl
            exact ⟨⟨j, hj⟩, hb⟩
          exact (decide_eq_true ((bitsToNat_ofFn_pos_iff vSub i hlt).mpr hex)).symm
        | false =>
          apply (decide_eq_false ?_).symm
          intro hpos
          obtain ⟨j, hb⟩ := (bitsToNat_ofFn_pos_iff vSub i hlt).mp hpos
          exact Bool.false_ne_true (hacc.mpr ⟨j.val, j.isLt, hb⟩)
      refine ⟨t₂, hbt₂, ?_⟩
      rw [← hacc_eq, Nat.mul_zero, Nat.zero_add]
      have hExit := ProgRuns_bind (k := fun isN =>
        ifProg isN
          (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
            seqProg (writeSlotProg ⟨5, by decide⟩ b)
              (mapExitProg (fun _ => Sum.inl (acc || b)) moveBlockRightProg)))
          (mapExitProg (fun _ => Sum.inr acc) rewindToBlock0Prog))
        hr₁ (ProgRuns_if_false (ProgRuns_mapExit (fun _ => Sum.inr acc) hr₂))
      exact (ProgRuns_loopState_exit hExit).mono (Nat.le_refl Sp) (by omega)
    | succ rem ih =>
      intro i hi_eq acc t₀ hacc hbt₀
      have hi_lt_n : i < nLen := by omega
      have hi_lt : i < allocLen := by omega
      obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨4, by decide⟩ hbt₀ hi_lt hsp
      have hsv4 : slotVal allocLen inBits nLen (cOut.take i) preBits vSub none none i 4 = true := by
        simp [slotVal, hi_lt, hi_lt_n]
      rw [hsv4] at hr₁
      obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_readSlot ⟨8, by decide⟩ hbt₁ hi_lt hsp
      have hsv8 : slotVal allocLen inBits nLen (cOut.take i) preBits vSub none none i 8 =
          QCSD_tapeRead vSub i := by
        simp [slotVal, hi_lt]
      rw [hsv8] at hr₂
      have hc_take_succ : cOut.take (i + 1) = cOut.take i ++ [QCSD_tapeRead vSub i] := by
        have hlt_c : i < cOut.length := by simp [cOut, hi_lt_n]
        rw [(List.take_concat_get' cOut i hlt_c).symm]
        simp [cOut]
      obtain ⟨t₃, hbt₃, hr₃⟩ :=
        ProgRuns_writeSlot_spec ⟨5, by decide⟩ (QCSD_tapeRead vSub i)
          (inBits' := inBits) (nLen' := nLen) (cBits' := cOut.take (i + 1))
          (preBits' := preBits) (vSub' := vSub) (rMark' := none) (wMark' := none)
          hbt₂ hi_lt hsp hbt₂.2.1 hbt₂.2.2.1
          (by simp [cOut]) hbt₂.2.2.2.2.1 hbt₂.2.2.2.2.2.1
          (fun _ h => by cases h) (fun _ h => by cases h)
          (by
            rw [hc_take_succ]
            have htl : (cOut.take i).length = i := by simp [cOut, Nat.min_eq_left (Nat.le_of_lt hi_lt_n)]
            simp only [slotVal, hi_lt, ↓reduceIte, QCSD_tapeRead, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by omega : (cOut.take i).length ≤ i), htl, Nat.sub_self,
              List.getElem?_cons_zero, Option.getD_some])
          (fun bi hbi bs _ hne => by
            by_cases hbs5 : bs = 5
            · have hbi_ne : bi ≠ i := hne.resolve_right (fun h => h hbs5)
              rw [hbs5, hc_take_succ]
              have htl : (cOut.take i).length = i := by simp [cOut, Nat.min_eq_left (Nat.le_of_lt hi_lt_n)]
              simp only [slotVal, hbi, ↓reduceIte, QCSD_tapeRead]
              by_cases hbi_i : bi < i
              · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
                    List.getD_eq_getElem?_getD]
              · have hge1 : (cOut.take i ++ [QCSD_tapeRead vSub i]).length ≤ bi := by simp [htl]; omega
                have hge2 : (cOut.take i).length ≤ bi := by omega
                unfold QCSD_tapeRead at hge1
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
                    List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
            · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                           bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                first | exact absurd rfl hbs5 | simp only [slotVal, hbi, ↓reduceIte])
      have hmax : Nat.max allocLen (i + 2) = allocLen := by simp only [Nat.max_eq_max]; omega
      obtain ⟨t₄, hbt₄, hr₄⟩ :=
        ProgRuns_moveBlockRight (Sp := Sp) hbt₃ hi_lt (by rw [hmax]; exact hsp)
      rw [hmax] at hbt₄
      let acc' := acc || QCSD_tapeRead vSub i
      have hacc' : acc' = true ↔ ∃ j < i + 1, QCSD_tapeRead vSub j = true := by
        dsimp [acc']
        rw [Bool.or_eq_true, hacc]
        constructor
        · rintro (⟨j, hj, hb⟩ | hb)
          · exact ⟨j, by omega, hb⟩
          · exact ⟨i, by omega, hb⟩
        · rintro ⟨j, hj, hb⟩
          by_cases hji : j < i
          · exact Or.inl ⟨j, hji, hb⟩
          · have : j = i := by omega
            subst this; exact Or.inr hb
      obtain ⟨t₅, hbt₅, hrRest⟩ := ih (i + 1) (by omega) acc' t₄ hacc' hbt₄
      refine ⟨t₅, hbt₅, ?_⟩
      have hStep := ProgRuns_bind (k := fun isN =>
        ifProg isN
          (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
            seqProg (writeSlotProg ⟨5, by decide⟩ b)
              (mapExitProg (fun _ => Sum.inl (acc || b)) moveBlockRightProg)))
          (mapExitProg (fun _ => Sum.inr acc) rewindToBlock0Prog))
        hr₁ (ProgRuns_if_true
          (ProgRuns_bind (k := fun b =>
            seqProg (writeSlotProg ⟨5, by decide⟩ b)
              (mapExitProg (fun _ => Sum.inl (acc || b)) moveBlockRightProg))
            hr₂ (ProgRuns_seq hr₃ (ProgRuns_mapExit (fun _ => Sum.inl acc') hr₄))))
      exact (ProgRuns_loopState_cont hStep hrRest).mono (Nat.le_refl Sp) (by
        rw [Nat.mul_succ]; omega)
  have hbt₀ : BlockTape base allocLen inBits nLen (cOut.take 0) preBits vSub none none tape := by
    simpa using hbt
  obtain ⟨t', hbt', hr⟩ := hloop nLen 0 (Nat.zero_add nLen) false tape (by simp) hbt₀
  have hbz : base + 11 * 0 = base := by omega
  rw [hbz] at hr
  exact ⟨t', by simp, bitsToNat_ofFn_take_of_lt vSub nLen hlt, hbt',
    hr.mono (Nat.le_refl Sp) (by omega)⟩

attribute [irreducible]
  rewindToBlock0Prog seekMarkProg clearSubTapeProg advanceMarkProg
  emitSubBitProg copyRangeToSubProg prepareSubInputProg simTMProg
  EvalPrefixQ evalPrefixProg scanCountPosProg scanAndSaveCountProg

def seekPreEndProg :=
  whileProg
    (bindProg (readSlotProg ⟨6, by decide⟩) (fun pv =>
      ifProg pv
        (mapExitProg (fun _ => true) moveBlockRightProg)
        (mapExitProg (fun _ => false) nopProg)))

lemma ProgRuns_seekPreEnd {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {rMark wMark : Option ℕ} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape)
    (hpre_lt : preBits.length < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape' ∧
      ProgRuns seekPreEndProg Sp (71 * preBits.length + 22)
        (tape, base) () (tape', base + 11 * preBits.length) := by
  have hgen : ∀ (rem i : ℕ), i + rem = preBits.length → ∀ t₀ : List Bool,
      BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark t₀ →
      ∃ tape' : List Bool,
        BlockTape base allocLen inBits nLen cBits preBits vSub rMark wMark tape' ∧
        ProgRuns seekPreEndProg Sp (71 * rem + 22)
          (t₀, base + 11 * i) () (tape', base + 11 * preBits.length) := by
    intro rem
    induction rem with
    | zero =>
      intro i hi_eq t₀ hbt₀
      have hip : i = preBits.length := by omega
      subst hip
      obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨6, by decide⟩ hbt₀ hpre_lt hsp
      have hsv : slotVal allocLen inBits nLen cBits preBits vSub rMark wMark preBits.length 6 = false := by
        simp [slotVal, hpre_lt]
      rw [hsv] at hr₁
      have hlen₁ : t₁.length ≤ base + 11 * allocLen := hbt₁.2.2.2.2.2.2.2.2.1
      have hsp_nop : Nat.max t₁.length (base + 11 * preBits.length + 2) ≤ Sp := by
        simp only [Nat.max_eq_max]; omega
      obtain ⟨t₂, heq₂, hlen₂, hr₂⟩ := ProgRuns_nop (t := t₁) (h := base + 11 * preBits.length) hsp_nop
      have hbt₂ := BlockTape_of_tapeEq hbt₁ heq₂ (by simp only [Nat.max_eq_max] at hlen₂ ⊢; omega)
      refine ⟨t₂, hbt₂, ?_⟩
      rw [Nat.mul_zero, Nat.zero_add]
      apply ProgRuns_while_false
      exact ProgRuns_bind (k := fun pv =>
        ifProg pv (mapExitProg (fun _ => true) moveBlockRightProg)
          (mapExitProg (fun _ => false) nopProg))
        hr₁ (ProgRuns_if_false (ProgRuns_mapExit (fun _ => false) hr₂))
    | succ rem ih =>
      intro i hi_eq t₀ hbt₀
      have hi_pre : i < preBits.length := by omega
      have hi_lt : i < allocLen := by omega
      obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_readSlot ⟨6, by decide⟩ hbt₀ hi_lt hsp
      have hsv : slotVal allocLen inBits nLen cBits preBits vSub rMark wMark i 6 = true := by
        simp [slotVal, hi_lt, hi_pre]
      rw [hsv] at hr₁
      have hmax : Nat.max allocLen (i + 2) = allocLen := by simp only [Nat.max_eq_max]; omega
      obtain ⟨t₂, hbt₂, hr₂⟩ :=
        ProgRuns_moveBlockRight (Sp := Sp) hbt₁ hi_lt (by rw [hmax]; exact hsp)
      rw [hmax] at hbt₂
      obtain ⟨t₃, hbt₃, hr₃⟩ := ih (i + 1) (by omega) t₂ hbt₂
      refine ⟨t₃, hbt₃, ?_⟩
      have hbody := ProgRuns_bind (k := fun pv =>
        ifProg pv (mapExitProg (fun _ => true) moveBlockRightProg)
          (mapExitProg (fun _ => false) nopProg))
        hr₁ (ProgRuns_if_true (ProgRuns_mapExit (fun _ => true) hr₂))
      simpa [seekPreEndProg, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ProgRuns_while_true hbody hr₃
  obtain ⟨t', hbt', hr⟩ := hgen preBits.length 0 (Nat.zero_add _) tape hbt
  have hbz : base + 11 * 0 = base := by omega
  rw [hbz] at hr
  exact ⟨t', hbt', hr⟩

def appendPreFalseProg :=
  seqProg (writeSlotProg ⟨6, by decide⟩ true) rewindToBlock0Prog

lemma ProgRuns_appendPreFalse {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits preBits vSub : List Bool} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits vSub none none tape)
    (hpre_n : preBits.length < nLen)
    (hnLen : nLen < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits (preBits ++ [false]) vSub none none tape' ∧
      ProgRuns appendPreFalseProg Sp (51 * allocLen + 50)
        (tape, base + 11 * preBits.length) () (tape', base) := by
  have hi_lt : preBits.length < allocLen := by omega
  obtain ⟨t₁, hbt₁, hr₁⟩ :=
    ProgRuns_writeSlot_spec ⟨6, by decide⟩ true
      (inBits' := inBits) (nLen' := nLen) (cBits' := cBits)
      (preBits' := preBits ++ [false]) (vSub' := vSub) (rMark' := none) (wMark' := none)
      hbt hi_lt hsp hbt.2.1 hbt.2.2.1 hbt.2.2.2.1
      (by simp; omega) hbt.2.2.2.2.2.1
      (fun _ h => by cases h) (fun _ h => by cases h)
      (by simp [slotVal, hi_lt])
      (fun bi hbi bs _ hne => by
        by_cases hbs6 : bs = 6
        · have hbi_ne : bi ≠ preBits.length := hne.resolve_right (fun h => h hbs6)
          rw [hbs6]
          simp only [slotVal, hbi, ↓reduceIte, List.length_append, List.length_singleton]
          have hiff : (bi < preBits.length + 1) ↔ (bi < preBits.length) := by omega
          simp [hiff]
        · by_cases hbs7 : bs = 7
          · rw [hbs7]
            simp only [slotVal, hbi, ↓reduceIte]
            exact tapeRead_append_replicate_false preBits 1 bi
          · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                         bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              first | exact absurd rfl hbs6 | exact absurd rfl hbs7 | simp only [slotVal, hbi, ↓reduceIte])
  obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_rewindToBlock0 hbt₁ hi_lt hsp
  exact ⟨t₂, hbt₂, (ProgRuns_seq hr₁ hr₂).mono (Nat.le_refl Sp) (by omega)⟩

def flipLastPreTrueProg :=
  seqProg seekPreEndProg
    (seqProg moveBlockLeftProg
      (seqProg (writeSlotProg ⟨7, by decide⟩ true) rewindToBlock0Prog))

lemma ProgRuns_flipLastPreTrue {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits pre vSub : List Bool} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits (pre ++ [false]) vSub none none tape)
    (hpre_n : pre.length < nLen)
    (hnLen : nLen < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits (pre ++ [true]) vSub none none tape' ∧
      ProgRuns flipLastPreTrueProg Sp (150 * allocLen + 120) (tape, base) () (tape', base) := by
  have hp1_lt : (pre ++ [false]).length < allocLen := by simp; omega
  obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_seekPreEnd hbt hp1_lt hsp
  obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_moveBlockLeft hbt₁ hp1_lt hsp
  have hlen_pf : (pre ++ [false]).length = pre.length + 1 := by simp
  have hsub1 : (pre ++ [false]).length - 1 = pre.length := by simp
  rw [hsub1] at hr₂
  have hp_lt : pre.length < allocLen := by omega
  obtain ⟨t₃, hbt₃, hr₃⟩ :=
    ProgRuns_writeSlot_spec ⟨7, by decide⟩ true
      (inBits' := inBits) (nLen' := nLen) (cBits' := cBits)
      (preBits' := pre ++ [true]) (vSub' := vSub) (rMark' := none) (wMark' := none)
      hbt₂ hp_lt hsp hbt₂.2.1 hbt₂.2.2.1 hbt₂.2.2.2.1
      (by simp; omega) hbt₂.2.2.2.2.2.1
      (fun _ h => by cases h) (fun _ h => by cases h)
      (by
        simp only [slotVal, hp_lt, ↓reduceIte, QCSD_tapeRead, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_refl pre.length), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some])
      (fun bi hbi bs _ hne => by
        by_cases hbs7 : bs = 7
        · have hbi_ne : bi ≠ pre.length := hne.resolve_right (fun h => h hbs7)
          rw [hbs7]
          simp only [slotVal, hbi, ↓reduceIte, QCSD_tapeRead]
          by_cases hbi_lt_p : bi < pre.length
          · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hbi_lt_p,
                List.getD_eq_getElem?_getD, List.getElem?_append_left hbi_lt_p]
          · have hge1 : (pre ++ [true]).length ≤ bi := by simp; omega
            have hge2 : (pre ++ [false]).length ≤ bi := by simp; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
                List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
        · by_cases hbs6 : bs = 6
          · rw [hbs6]; simp [slotVal, hbi]
          · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                         bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              first | exact absurd rfl hbs6 | exact absurd rfl hbs7 | simp only [slotVal, hbi, ↓reduceIte])
  obtain ⟨t₄, hbt₄, hr₄⟩ := ProgRuns_rewindToBlock0 hbt₃ hp_lt hsp
  refine ⟨t₄, hbt₄, ?_⟩
  exact (ProgRuns_seq hr₁ (ProgRuns_seq hr₂ (ProgRuns_seq hr₃ hr₄))).mono
    (Nat.le_refl Sp) (by rw [hlen_pf] at *; omega)

def FlipLastPreQ : Type := ProgState flipLastPreTrueProg
instance : Fintype FlipLastPreQ := by
  unfold FlipLastPreQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance : DecidableEq FlipLastPreQ := by
  unfold FlipLastPreQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance
def flipLastPreSealedProg : Prog FlipLastPreQ Unit := flipLastPreTrueProg

lemma ProgRuns_flipLastPreSealed {Sp base allocLen : ℕ} {inBits : List Bool} {nLen : ℕ}
    {cBits pre vSub : List Bool} {tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits (pre ++ [false]) vSub none none tape)
    (hpre_n : pre.length < nLen)
    (hnLen : nLen < allocLen)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ tape' : List Bool,
      BlockTape base allocLen inBits nLen cBits (pre ++ [true]) vSub none none tape' ∧
      ProgRuns flipLastPreSealedProg Sp (150 * allocLen + 120) (tape, base) () (tape', base) :=
  ProgRuns_flipLastPreTrue hbt hpre_n hnLen hsp

attribute [irreducible] seekPreEndProg appendPreFalseProg flipLastPreTrueProg
  FlipLastPreQ flipLastPreSealedProg

def greedyLoopBody (M_net A : QCSD_DetTM) :=
  seqProg seekPreEndProg
    (bindProg (readSlotProg ⟨4, by decide⟩) (fun hasMore =>
      ifProg hasMore
        (seqProg appendPreFalseProg
          (seqProg (evalPrefixProg M_net A)
            (bindProg scanCountPosProg (fun c0Pos =>
              ifProg c0Pos
                (mapExitProg (fun _ => true) nopProg)
                (mapExitProg (fun _ => true) flipLastPreSealedProg)))))
        (mapExitProg (fun _ => false) rewindToBlock0Prog)))

def GreedyLoopQ (M_net A : QCSD_DetTM) : Type := ProgState (greedyLoopBody M_net A)
instance (M_net A : QCSD_DetTM) : Fintype (GreedyLoopQ M_net A) := by
  unfold GreedyLoopQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance (M_net A : QCSD_DetTM) : DecidableEq (GreedyLoopQ M_net A) := by
  unfold GreedyLoopQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def greedyLoopBodySealed (M_net A : QCSD_DetTM) : Prog (GreedyLoopQ M_net A) Bool :=
  greedyLoopBody M_net A

def greedyLoopProg (M_net A : QCSD_DetTM) : Prog (GreedyLoopQ M_net A) Unit :=
  whileProg (greedyLoopBodySealed M_net A)

lemma ProgRuns_greedyLoopBody_done (M_net A : QCSD_DetTM)
    {Sp base aL n : ℕ} {inBits cBits pre vS t_cur : List Bool}
    (hplen : pre.length = 2 * n)
    (hpre_lt_aL : pre.length < aL)
    (hbt_c : BlockTape base aL inBits (2 * n) cBits pre vS none none t_cur)
    (hsp_aL : base + 11 * aL ≤ Sp) :
    ∃ t₃ : List Bool,
      BlockTape base aL inBits (2 * n) cBits pre vS none none t₃ ∧
      ProgRuns (greedyLoopBodySealed M_net A) Sp
        ((71 * pre.length + 22) + (20 + (51 * pre.length + 22)))
        (t_cur, base) false (t₃, base) := by
  obtain ⟨t₁, hbt₁, hrSeek⟩ := ProgRuns_seekPreEnd hbt_c hpre_lt_aL hsp_aL
  obtain ⟨t₂, hbt₂, hrRead⟩ := ProgRuns_readSlot ⟨4, by decide⟩ hbt₁ hpre_lt_aL hsp_aL
  have hsv4 : slotVal aL inBits (2 * n) cBits pre vS none none pre.length 4 = false := by
    simp [slotVal, hplen]
  rw [hsv4] at hrRead
  obtain ⟨t₃, hbt₃, hrRew⟩ := ProgRuns_rewindToBlock0 hbt₂ hpre_lt_aL hsp_aL
  refine ⟨t₃, hbt₃, ?_⟩
  unfold greedyLoopBodySealed greedyLoopBody
  exact ProgRuns_seq hrSeek
    (ProgRuns_bind (k := fun hasMore =>
      ifProg hasMore
        (seqProg appendPreFalseProg
          (seqProg (evalPrefixProg M_net A)
            (bindProg scanCountPosProg (fun c0Pos =>
              ifProg c0Pos
                (mapExitProg (fun _ => true) nopProg)
                (mapExitProg (fun _ => true) flipLastPreSealedProg)))))
        (mapExitProg (fun _ => false) rewindToBlock0Prog))
      hrRead (ProgRuns_if_false (ProgRuns_mapExit (fun _ => false) hrRew)))

lemma ProgRuns_greedyLoopBody_step (M_net A : QCSD_DetTM)
    {Sp SpM SpA TM TA base aL n : ℕ}
    {inBits cBits pre vS t_cur encNet : List Bool}
    {sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2))}
    (hCard : sols.card < 2 ^ (2 * n))
    (hpre_lt_2n : pre.length < 2 * n)
    (h2n_lt_aL : 2 * n < aL)
    (hpos : 0 < (sols.filter (fun q => (qcsdIface n q.1 q.2).take pre.length = pre)).card)
    (hbt_c : BlockTape base aL inBits (2 * n) cBits pre vS none none t_cur)
    (hcap : inBits.length + 2 * (pre ++ [false]).length + 2 < aL + 1)
    (hM₀ : ∃ k₁ ≤ TM,
      (QCSD_configAt2 M_net (inBits ++ QCSD_natToUnary (pre ++ [false]).length ++ (pre ++ [false])) k₁).state = M_net.qhalt ∧
      tapeEq (QCSD_configAt2 M_net (inBits ++ QCSD_natToUnary (pre ++ [false]).length ++ (pre ++ [false])) k₁).tape encNet ∧
      (∀ j ≤ k₁, QCSD_spaceUse2 (QCSD_configAt2 M_net (inBits ++ QCSD_natToUnary (pre ++ [false]).length ++ (pre ++ [false])) j) ≤ SpM))
    (hA₀ : ∃ k₂ ≤ TA,
      (QCSD_configAt2 A encNet k₂).state = A.qhalt ∧
      QCSD_bitsToNat (QCSD_configAt2 A encNet k₂).tape =
        (sols.filter (fun q => (qcsdIface n q.1 q.2).take (pre ++ [false]).length = pre ++ [false])).card ∧
      (∀ j ≤ k₂, QCSD_spaceUse2 (QCSD_configAt2 A encNet j) ≤ SpA))
    (hsp : base + 11 * (Nat.max (Nat.max (aL + 1) (SpM + 1)) (SpA + 1) + 1) ≤ Sp) :
    let aMax := Nat.max (Nat.max (aL + 1) (SpM + 1)) (SpA + 1)
    ∃ aL₄ bNext vS₄ t₆,
      aL + 1 ≤ aL₄ ∧
      aL₄ ≤ aMax ∧
      0 < (sols.filter (fun q => (qcsdIface n q.1 q.2).take (pre.length + 1) = pre ++ [bNext])).card ∧
      BlockTape base aL₄ inBits (2 * n) cBits (pre ++ [bNext]) vS₄ none none t₆ ∧
      ProgRuns (greedyLoopBodySealed M_net A) Sp
        ((1800 * aMax + 4000) * (aMax + 1) + 92 * TM + 92 * TA)
        (t_cur, base) true (t₆, base) := by
  let aMax := Nat.max (Nat.max (aL + 1) (SpM + 1)) (SpA + 1)
  have ha1 : aL + 1 ≤ aMax := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hpre_lt_aL : pre.length < aL := by omega
  have hsp_aL : base + 11 * aL ≤ Sp := by omega
  obtain ⟨t₁, hbt₁, hrSeek⟩ := ProgRuns_seekPreEnd hbt_c hpre_lt_aL hsp_aL
  obtain ⟨t₂, hbt₂, hrRead⟩ := ProgRuns_readSlot ⟨4, by decide⟩ hbt₁ hpre_lt_aL hsp_aL
  have hsv4 : slotVal aL inBits (2 * n) cBits pre vS none none pre.length 4 = true := by
    simp [slotVal, hpre_lt_aL, hpre_lt_2n]
  rw [hsv4] at hrRead
  obtain ⟨t₃, hbt₃, hrApp⟩ := ProgRuns_appendPreFalse hbt₂ hpre_lt_2n h2n_lt_aL hsp_aL
  obtain ⟨aL₄, vS₄, t₄, haL₄_ge, haL₄_le, hbits₄, hbt₄, hrEval⟩ :=
    ProgRuns_evalPrefix M_net A (Sp := Sp) hbt₃ hcap hM₀ hA₀ hsp
  have hc0_lt_pow : QCSD_bitsToNat vS₄ < 2 ^ (2 * n) := by
    rw [hbits₄]
    exact Nat.lt_of_le_of_lt (Finset.card_filter_le _ _) hCard
  have hsp_aL₄ : base + 11 * aL₄ ≤ Sp := by omega
  obtain ⟨t₅, hbt₅, hrScan⟩ :=
    ProgRuns_scanCountPos hbt₄ (by omega) hc0_lt_pow hsp_aL₄
  let c0 := (sols.filter (fun q =>
    (qcsdIface n q.1 q.2).take (pre.length + 1) = pre ++ [false])).card
  have hc0_eq : QCSD_bitsToNat vS₄ = c0 := by simpa [c0] using hbits₄
  rw [hc0_eq] at hrScan
  have hstep_pos := greedy_bit_step n sols pre hpre_lt_2n hpos
  dsimp only at hstep_pos
  change 0 < (sols.filter (fun q =>
    (qcsdIface n q.1 q.2).take (pre.length + 1) =
      pre ++ [if 0 < c0 then false else true])).card at hstep_pos
  by_cases hc0 : 0 < c0
  · rw [decide_eq_true hc0] at hrScan
    rw [ite_eq_left hc0] at hstep_pos
    have hlen₅ : t₅.length ≤ base + 11 * aL₄ := hbt₅.2.2.2.2.2.2.2.2.1
    obtain ⟨t₆, heq₆, hlen₆, hrNop⟩ :=
      ProgRuns_nop (Sp := Sp) (t := t₅) (h := base) (by simp only [Nat.max_eq_max]; omega)
    have hbt₆ := BlockTape_of_tapeEq hbt₅ heq₆ (by simp only [Nat.max_eq_max] at hlen₆ ⊢; omega)
    refine ⟨aL₄, false, vS₄, t₆, haL₄_ge, haL₄_le, hstep_pos, hbt₆, ?_⟩
    unfold greedyLoopBodySealed greedyLoopBody
    exact (ProgRuns_seq hrSeek
      (ProgRuns_bind (k := fun hasMore =>
        ifProg hasMore
          (seqProg appendPreFalseProg
            (seqProg (evalPrefixProg M_net A)
              (bindProg scanCountPosProg (fun c0Pos =>
                ifProg c0Pos
                  (mapExitProg (fun _ => true) nopProg)
                  (mapExitProg (fun _ => true) flipLastPreSealedProg)))))
          (mapExitProg (fun _ => false) rewindToBlock0Prog))
        hrRead (ProgRuns_if_true
          (ProgRuns_seq hrApp
            (ProgRuns_seq hrEval
              (ProgRuns_bind (k := fun c0Pos =>
                ifProg c0Pos
                  (mapExitProg (fun _ => true) nopProg)
                  (mapExitProg (fun _ => true) flipLastPreSealedProg))
                hrScan (ProgRuns_if_true (ProgRuns_mapExit (fun _ => true) hrNop)))))))).mono
      (Nat.le_refl Sp) (by nlinarith)
  · rw [decide_eq_false hc0] at hrScan
    rw [ite_eq_right hc0] at hstep_pos
    obtain ⟨t₆, hbt₆, hrFlip⟩ :=
      ProgRuns_flipLastPreSealed hbt₅ hpre_lt_2n (by omega) hsp_aL₄
    refine ⟨aL₄, true, vS₄, t₆, haL₄_ge, haL₄_le, hstep_pos, hbt₆, ?_⟩
    unfold greedyLoopBodySealed greedyLoopBody
    exact (ProgRuns_seq hrSeek
      (ProgRuns_bind (k := fun hasMore =>
        ifProg hasMore
          (seqProg appendPreFalseProg
            (seqProg (evalPrefixProg M_net A)
              (bindProg scanCountPosProg (fun c0Pos =>
                ifProg c0Pos
                  (mapExitProg (fun _ => true) nopProg)
                  (mapExitProg (fun _ => true) flipLastPreSealedProg)))))
          (mapExitProg (fun _ => false) rewindToBlock0Prog))
        hrRead (ProgRuns_if_true
          (ProgRuns_seq hrApp
            (ProgRuns_seq hrEval
              (ProgRuns_bind (k := fun c0Pos =>
                ifProg c0Pos
                  (mapExitProg (fun _ => true) nopProg)
                  (mapExitProg (fun _ => true) flipLastPreSealedProg))
                hrScan (ProgRuns_if_false (ProgRuns_mapExit (fun _ => true) hrFlip)))))))).mono
      (Nat.le_refl Sp) (by nlinarith)

attribute [irreducible] GreedyLoopQ greedyLoopBodySealed

lemma ProgRuns_greedyLoop (M_net A : QCSD_DetTM)
    {n Sp SpM SpA TM TA base allocLen₀ : ℕ}
    {inBits cBits vSub₀ tape₀ : List Bool}
    {sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2))}
    (_hn : 2 ≤ n)
    (hCard : sols.card < 2 ^ (2 * n))
    (hbt₀ : BlockTape base allocLen₀ inBits (2 * n) cBits [] vSub₀ none none tape₀)
    (hcap₀ : inBits.length + 4 * n + 3 ≤ allocLen₀)
    (hpos₀ : 0 < (sols.filter (fun q => (qcsdIface n q.1 q.2).take 0 = [])).card)
    (hOracle : ∀ pre : List Bool, pre.length ≤ 2 * n →
      ∃ encNet : List Bool,
        (∃ k₁ ≤ TM,
          (QCSD_configAt2 M_net (inBits ++ QCSD_natToUnary pre.length ++ pre) k₁).state = M_net.qhalt ∧
          tapeEq (QCSD_configAt2 M_net (inBits ++ QCSD_natToUnary pre.length ++ pre) k₁).tape encNet ∧
          (∀ j ≤ k₁, QCSD_spaceUse2 (QCSD_configAt2 M_net (inBits ++ QCSD_natToUnary pre.length ++ pre) j) ≤ SpM)) ∧
        (∃ k₂ ≤ TA,
          (QCSD_configAt2 A encNet k₂).state = A.qhalt ∧
          QCSD_bitsToNat (QCSD_configAt2 A encNet k₂).tape =
            (sols.filter (fun q => (qcsdIface n q.1 q.2).take pre.length = pre)).card ∧
          (∀ j ≤ k₂, QCSD_spaceUse2 (QCSD_configAt2 A encNet j) ≤ SpA)))
    (hsp : base + 11 * (Nat.max (Nat.max allocLen₀ (SpM + 1)) (SpA + 1) + 2 * n + 2) ≤ Sp) :
    let aCap := Nat.max (Nat.max allocLen₀ (SpM + 1)) (SpA + 1) + 2 * n + 1
    ∃ allocLen' preOut vSub' tape',
      allocLen₀ ≤ allocLen' ∧
      allocLen' ≤ aCap ∧
      preOut.length = 2 * n ∧
      0 < (sols.filter (fun q => (qcsdIface n q.1 q.2).take (2 * n) = preOut)).card ∧
      BlockTape base allocLen' inBits (2 * n) cBits preOut vSub' none none tape' ∧
      ProgRuns (greedyLoopProg M_net A) Sp
        ((2 * n + 1) * ((1800 * aCap + 4000) * (aCap + 1) + 92 * TM + 92 * TA))
        (tape₀, base) () (tape', base) := by
  let aBase := Nat.max (Nat.max allocLen₀ (SpM + 1)) (SpA + 1)
  let aCap := aBase + 2 * n + 1
  let iterBudget := (1800 * aCap + 4000) * (aCap + 1) + 92 * TM + 92 * TA
  have hloop : ∀ (rem r : ℕ), r + rem = 2 * n →
      ∀ (aL : ℕ) (pre vS t_cur : List Bool),
        pre.length = r →
        allocLen₀ ≤ aL →
        aL ≤ aBase + r →
        0 < (sols.filter (fun q => (qcsdIface n q.1 q.2).take pre.length = pre)).card →
        BlockTape base aL inBits (2 * n) cBits pre vS none none t_cur →
        ∃ allocLen' preOut vSub' tape',
          allocLen₀ ≤ allocLen' ∧
          allocLen' ≤ aCap ∧
          preOut.length = 2 * n ∧
          0 < (sols.filter (fun q => (qcsdIface n q.1 q.2).take (2 * n) = preOut)).card ∧
          BlockTape base allocLen' inBits (2 * n) cBits preOut vSub' none none tape' ∧
          ProgRuns (whileProg (greedyLoopBodySealed M_net A)) Sp ((rem + 1) * iterBudget)
            (t_cur, base) () (tape', base) := by
    intro rem
    induction rem with
    | zero =>
      intro r hr_eq aL pre vS t_cur hplen haL_ge haL_le hpos hbt_c
      have hr2n : r = 2 * n := by omega
      subst hr2n
      have hpre_lt_aL : pre.length < aL := by omega
      have hsp_aL : base + 11 * aL ≤ Sp := by simp only [aBase] at hsp haL_le; omega
      obtain ⟨t₃, hbt₃, hExit⟩ := ProgRuns_greedyLoopBody_done M_net A hplen hpre_lt_aL hbt_c hsp_aL
      rw [hplen] at hpos
      refine ⟨aL, pre, vS, t₃, haL_ge, by dsimp [aCap]; omega, hplen, hpos, hbt₃, ?_⟩
      have hp_le : pre.length ≤ aCap := by dsimp [aCap]; omega
      exact (ProgRuns_while_false hExit).mono (Nat.le_refl Sp) (by dsimp [iterBudget]; nlinarith)
    | succ rem ih =>
      intro r hr_eq aL pre vS t_cur hplen haL_ge haL_le hpos hbt_c
      have hpre_lt_2n : pre.length < 2 * n := by omega
      have h2n_lt_aL : 2 * n < aL := by omega
      obtain ⟨encNet, hM₀, hA₀⟩ := hOracle (pre ++ [false]) (by simp; omega)
      have haMax_le : Nat.max (Nat.max (aL + 1) (SpM + 1)) (SpA + 1) ≤ aBase + (r + 1) := by
        simp only [aBase, Nat.max_eq_max] at haL_le ⊢; omega
      obtain ⟨aL₄, bNext, vS₄, t₆, haL₄_ge, haL₄_le_max, hpos_next, hbt₆, hBody⟩ :=
        ProgRuns_greedyLoopBody_step M_net A (Sp := Sp) hCard hpre_lt_2n h2n_lt_aL hpos hbt_c
          (by simp; omega) hM₀ hA₀ (by simp only [aBase] at hsp haMax_le ⊢; omega)
      have haL₄_le : aL₄ ≤ aBase + (r + 1) := haL₄_le_max.trans haMax_le
      have haMax_cap : Nat.max (Nat.max (aL + 1) (SpM + 1)) (SpA + 1) ≤ aCap := by
        dsimp [aCap]; omega
      have hBody' : ProgRuns (greedyLoopBodySealed M_net A) Sp iterBudget (t_cur, base) true (t₆, base) :=
        hBody.mono (Nat.le_refl Sp) (by dsimp [iterBudget]; nlinarith)
      obtain ⟨aL', preOut, vSub', tape', hg1, hg2, hg3, hg4, hg5, hrRest⟩ :=
        ih (r + 1) (by omega) aL₄ (pre ++ [bNext]) vS₄ t₆
          (by simp [hplen]) (by omega) haL₄_le (by simpa using hpos_next) hbt₆
      refine ⟨aL', preOut, vSub', tape', hg1, hg2, hg3, hg4, hg5, ?_⟩
      exact (ProgRuns_while_true hBody' hrRest).mono (Nat.le_refl Sp) (by nlinarith)
  exact hloop (2 * n) 0 (Nat.zero_add _) allocLen₀ [] vSub₀ tape₀ rfl
    (Nat.le_refl _) (by simp only [aBase, Nat.add_zero, Nat.max_eq_max]; omega)
    hpos₀ hbt₀

attribute [irreducible] greedyLoopProg

/-! ### Section 6c: Output Packing (`buildOutSubProg`) & Sentinel Unpacker (`flushSubToOriginProg`) -/

lemma ProgRuns_readSlot_raw (s : Fin 11) {Sp : ℕ} {t : List Bool} {pos : ℕ}
    (hsp : Nat.max t.length (pos + 11) ≤ Sp) :
    ∃ t' : List Bool,
      tapeEq t' t ∧ t'.length ≤ Nat.max t.length (pos + 11) ∧
      ProgRuns (readSlotProg s) Sp 20 (t, pos) (QCSD_tapeRead t (pos + s.val)) (t', pos) := by
  obtain ⟨t', hread, hlen, hr⟩ :=
    ProgRuns_accessSlot false s (fun b => (b, b)) (t := t) (base := pos) hsp
  refine ⟨t', fun p => ?_, hlen, hr⟩
  rw [hread p]
  split_ifs with hp
  · subst hp; rfl
  · rfl

lemma ProgRuns_writeSlot_raw (s : Fin 11) (val : Bool) {Sp : ℕ} {t : List Bool} {pos : ℕ}
    (hsp : Nat.max t.length (pos + 11) ≤ Sp) :
    ∃ t' : List Bool,
      (∀ p, QCSD_tapeRead t' p = if p = pos + s.val then val else QCSD_tapeRead t p) ∧
      t'.length ≤ Nat.max t.length (pos + 11) ∧
      ProgRuns (writeSlotProg s val) Sp 20 (t, pos) () (t', pos) :=
  ProgRuns_accessSlot () s (fun _ => ((), val)) (t := t) (base := pos) hsp

def outSubList (cBits preBits : List Bool) (hasWit : Bool) : List Bool :=
  cBits ++ [hasWit] ++ (if hasWit then preBits else [])

def buildOutSubRaw (hasWit : Bool) :=
  seqProg clearSubTapeProg
    (seqProg (writeSlotProg ⟨10, by decide⟩ true)
      (seqProg (copyRangeToSubProg ⟨4, by decide⟩ ⟨5, by decide⟩)
        (seqProg (emitSubBitProg hasWit)
          (ifProg hasWit
            (copyRangeToSubProg ⟨6, by decide⟩ ⟨7, by decide⟩)
            nopProg))))

def BuildOutSubQ : Type := ProgState (buildOutSubRaw true)
instance : Fintype BuildOutSubQ := by
  unfold BuildOutSubQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance : DecidableEq BuildOutSubQ := by
  unfold BuildOutSubQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def buildOutSubProg (hasWit : Bool) : Prog BuildOutSubQ Unit := buildOutSubRaw hasWit

lemma ProgRuns_buildOutSub (hasWit : Bool)
    {Sp base allocLen n : ℕ} {inBits cBits preBits vSub tape : List Bool}
    (hbt : BlockTape base allocLen inBits (2 * n) cBits preBits vSub none none tape)
    (hcLen : cBits.length = 2 * n)
    (hpreLen : hasWit = true → preBits.length = 2 * n)
    (hcap : 4 * n + 2 ≤ allocLen)
    (hsp : base + 11 * (allocLen + 1) ≤ Sp) :
    let outL := outSubList cBits preBits hasWit
    ∃ tape' : List Bool,
      BlockTape base (allocLen + 1) inBits (2 * n) cBits preBits outL none (some outL.length) tape' ∧
      ProgRuns (buildOutSubProg hasWit) Sp ((900 * (allocLen + 1) + 2000) * (allocLen + 2))
        (tape, base) () (tape', base) := by
  obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_clearSubTape hbt hsp
  obtain ⟨t₂, hbt₂, hr₂⟩ := ProgRuns_setWMark0 hbt₁ hsp
  have h0len : ([] : List Bool).length = 0 := rfl
  rw [← h0len] at hbt₂
  obtain ⟨t₃, hbt₃, hr₃⟩ :=
    ProgRuns_copyRangeToSub ⟨4, by decide⟩ ⟨5, by decide⟩ cBits hbt₂
      (by simp [hcLen]; omega) (by rw [hcLen]; omega) hsp
      (fun r _ _ hr => by simp [slotVal, hr, hcLen])
      (fun r hr _ _ => by
        have hr_lt : r < allocLen + 1 := by rw [hcLen] at hr; omega
        simp [slotVal, hr_lt, QCSD_tapeRead, List.getD_eq_getElem?_getD, hr])
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hbt₃
  obtain ⟨t₄, hbt₄, hr₄⟩ :=
    ProgRuns_emitSubBit hasWit hbt₃ (by rw [hcLen]; omega) hsp
  cases hasWit
  · have hlen₄ : t₄.length ≤ base + 11 * (allocLen + 1) := hbt₄.2.2.2.2.2.2.2.2.1
    obtain ⟨t₅, heq₅, hlen₅, hr₅⟩ :=
      ProgRuns_nop (Sp := Sp) (t := t₄) (h := base) (by simp only [Nat.max_eq_max]; omega)
    have hbt₅ := BlockTape_of_tapeEq hbt₄ heq₅
      (by simp only [Nat.max_eq_max] at hlen₅ ⊢; omega)
    have hout : outSubList cBits preBits false = cBits ++ [false] := by simp [outSubList]
    have houtL : (outSubList cBits preBits false).length = cBits.length + 1 := by
      simp [outSubList]
    refine ⟨t₅, ?_, ?_⟩
    · simpa [hout, houtL] using hbt₅
    · unfold buildOutSubProg buildOutSubRaw
      have hpr := ProgRuns_seq hr₁ (ProgRuns_seq hr₂ (ProgRuns_seq hr₃
        (ProgRuns_seq hr₄
          (ProgRuns_if_false (pT := copyRangeToSubProg ⟨6, by decide⟩ ⟨7, by decide⟩) hr₅))))
      exact hpr.mono (Nat.le_refl Sp) (by rw [hcLen]; nlinarith)
  · have hpL : preBits.length = 2 * n := hpreLen rfl
    have hcwL : (cBits ++ [true]).length = cBits.length + 1 := by simp
    rw [← hcwL] at hbt₄
    obtain ⟨t₅, hbt₅, hr₅⟩ :=
      ProgRuns_copyRangeToSub ⟨6, by decide⟩ ⟨7, by decide⟩ preBits hbt₄
        (by simp [hcLen, hpL]; omega) (by rw [hpL]; omega) hsp
        (fun r _ _ hr => by simp [slotVal, hr])
        (fun r hr _ _ => by
          have hr_lt : r < allocLen + 1 := by rw [hpL] at hr; omega
          simp [slotVal, hr_lt, QCSD_tapeRead, List.getD_eq_getElem?_getD, hr])
    have hout : outSubList cBits preBits true = cBits ++ [true] ++ preBits := by
      simp [outSubList]
    refine ⟨t₅, ?_, ?_⟩
    · rw [hout, List.length_append]
      exact hbt₅
    · unfold buildOutSubProg buildOutSubRaw
      have hpr := ProgRuns_seq hr₁ (ProgRuns_seq hr₂ (ProgRuns_seq hr₃
        (ProgRuns_seq hr₄ (ProgRuns_if_true (pF := nopProg) hr₅))))
      exact hpr.mono (Nat.le_refl Sp) (by rw [hcLen, hpL]; nlinarith)

attribute [irreducible] BuildOutSubQ buildOutSubProg

def walkRightToTrueStep : Bool → Bool × Bool × QCSD_HeadDir :=
  fun c => if c then (false, true, QCSD_HeadDir.left) else (true, false, QCSD_HeadDir.right)

def walkRightToTrueProg :=
  seqProg (whileProg (primProg walkRightToTrueStep)) (stepDirProg QCSD_HeadDir.right)

lemma ProgRuns_walkRightToTrue {Sp pos target : ℕ} {t : List Bool}
    (hle : pos ≤ target)
    (htpos : 1 ≤ target)
    (hfalse : ∀ p, pos ≤ p → p < target → QCSD_tapeRead t p = false)
    (htrue : QCSD_tapeRead t target = true)
    (hsp : Nat.max t.length (target + 2) ≤ Sp) :
    ∃ t' : List Bool,
      tapeEq t' t ∧ t'.length ≤ Nat.max t.length (target + 1) ∧
      ProgRuns walkRightToTrueProg Sp (target - pos + 2) (t, pos) () (t', target) := by
  have hloop : ∀ (rem cur : ℕ), pos ≤ cur → cur + rem = target → ∀ t_c : List Bool,
      tapeEq t_c t →
      t_c.length ≤ Nat.max t.length (target + 1) →
      ∃ t_e : List Bool,
        tapeEq t_e t ∧ t_e.length ≤ Nat.max t.length (target + 1) ∧
        ProgRuns (whileProg (primProg walkRightToTrueStep)) Sp (rem + 1)
          (t_c, cur) () (t_e, target - 1) := by
    intro rem
    induction rem with
    | zero =>
      intro cur _ hcur t_c heq hlen
      have hct : cur = target := by omega
      subst hct
      have hread : QCSD_tapeRead t_c cur = true := (heq cur).trans htrue
      let t_e := QCSD_tapeWrite2 t_c cur true
      have heq_e : tapeEq t_e t := by
        intro p; rw [tapeRead_tapeWrite2]; split_ifs with hp
        · subst hp; exact htrue.symm
        · exact heq p
      have hlen_e : t_e.length ≤ Nat.max t.length (cur + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen ⊢; omega
      refine ⟨t_e, heq_e, hlen_e, ?_⟩
      apply ProgRuns_while_false
      have hprim := ProgRuns_prim walkRightToTrueStep (Sp := Sp) (t := t_c) (h := cur)
        (by simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
        (by rw [hread]; dsimp [walkRightToTrueStep, stepHead]
            rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
      rw [hread] at hprim
      exact hprim
    | succ rem ih =>
      intro cur hpc hcur t_c heq hlen
      have hlt : cur < target := by omega
      have hread : QCSD_tapeRead t_c cur = false := (heq cur).trans (hfalse cur hpc hlt)
      let t₁ := QCSD_tapeWrite2 t_c cur false
      have heq₁ : tapeEq t₁ t := by
        intro p; rw [tapeRead_tapeWrite2]; split_ifs with hp
        · subst hp; exact (hfalse p hpc hlt).symm
        · exact heq p
      have hlen₁ : t₁.length ≤ Nat.max t.length (target + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen ⊢; omega
      have hstep : ProgRuns (primProg walkRightToTrueStep) Sp 1 (t_c, cur) true (t₁, cur + 1) := by
        have hprim := ProgRuns_prim walkRightToTrueStep (Sp := Sp) (t := t_c) (h := cur)
          (by simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
          (by rw [hread]; dsimp [walkRightToTrueStep, stepHead]
              rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
        rw [hread] at hprim
        exact hprim
      obtain ⟨t_e, heq_e, hlen_e, hrRest⟩ :=
        ih (cur + 1) (by omega) (by omega) t₁ heq₁ hlen₁
      refine ⟨t_e, heq_e, hlen_e, ?_⟩
      exact (ProgRuns_while_true hstep hrRest).mono (Nat.le_refl Sp) (by omega)
  obtain ⟨t₁, heq₁, hlen₁, hr₁⟩ :=
    hloop (target - pos) pos (Nat.le_refl pos) (by omega) t (tapeEq_refl t) (Nat.le_max_left _ _)
  obtain ⟨t₂, heq₂, hlen₂, hr₂⟩ :=
    ProgRuns_stepRight (Sp := Sp) (t := t₁) (h := target - 1)
      (by simp only [Nat.max_eq_max] at hlen₁ hsp ⊢; omega)
  have hsub : target - 1 + 1 = target := by omega
  rw [hsub] at hr₂ hlen₂
  refine ⟨t₂, tapeEq_trans heq₂ heq₁, ?_, ?_⟩
  · simp only [Nat.max_eq_max] at hlen₂ hlen₁ ⊢; omega
  · exact (ProgRuns_seq hr₁ hr₂).mono (Nat.le_refl Sp) (by omega)

def walkToZeroBody :=
  seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.left)))
    (bindProg (primProg (fun b => (b, b, QCSD_HeadDir.right))) (fun b =>
      ifProg b
        (primProg (fun c => (false, c, QCSD_HeadDir.left)))
        (primProg (fun _ => (true, false, QCSD_HeadDir.left)))))

def initOriginSentinelProg :=
  seqProg (stepDirProg QCSD_HeadDir.left)
    (seqProg (whileProg walkToZeroBody)
      (seqProg (stepDirProg QCSD_HeadDir.right) walkRightToTrueProg))

lemma ProgRuns_initOriginSentinel {Sp base : ℕ} {t : List Bool}
    (hbase : 2 ≤ base)
    (hlow : ∀ p < base, QCSD_tapeRead t p = false)
    (htrue : QCSD_tapeRead t base = true)
    (hsp : Nat.max t.length (base + 2) ≤ Sp) :
    ∃ t' : List Bool,
      (∀ p, QCSD_tapeRead t' p = if p = 0 then true else QCSD_tapeRead t p) ∧
      t'.length ≤ Nat.max t.length (base + 1) ∧
      ProgRuns initOriginSentinelProg Sp (4 * base + 3) (t, base) () (t', base) := by
  obtain ⟨t₀, heq₀, hlen₀, hrLeft⟩ :=
    ProgRuns_stepLeft (Sp := Sp) (t := t) (h := base)
      (by simp only [Nat.max_eq_max] at hsp ⊢; omega)
  have hloop : ∀ (cur : ℕ), cur < base → ∀ t_c : List Bool,
      tapeEq t_c t →
      t_c.length ≤ Nat.max t.length (base + 1) →
      ∃ t_z : List Bool,
        (∀ p, QCSD_tapeRead t_z p = if p = 0 then true else QCSD_tapeRead t p) ∧
        t_z.length ≤ Nat.max t.length (base + 1) ∧
        ProgRuns (whileProg walkToZeroBody) Sp (3 * (cur + 1)) (t_c, cur) () (t_z, 0) := by
    intro cur
    induction cur with
    | zero =>
      intro _ t_c heq hlen
      let t₁ := QCSD_tapeWrite2 t_c 0 true
      have hlen₁ : t₁.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen ⊢; omega
      have hs1 : ProgRuns (primProg (fun _ => ((), true, QCSD_HeadDir.left))) Sp 1 (t_c, 0) () (t₁, 0) := by
        have hp := ProgRuns_prim (fun _ => ((), true, QCSD_HeadDir.left)) (Sp := Sp) (t := t_c) (h := 0)
          (by simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
        exact hp
      have ht₁0 : QCSD_tapeRead t₁ 0 = true := by simp [t₁, tapeRead_tapeWrite2]
      let t₂ := QCSD_tapeWrite2 t₁ 0 true
      have hlen₂ : t₂.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen₁ ⊢; omega
      have hs2 : ProgRuns (primProg (fun b => (b, b, QCSD_HeadDir.right))) Sp 1 (t₁, 0) true (t₂, 1) := by
        have hp := ProgRuns_prim (fun b => (b, b, QCSD_HeadDir.right)) (Sp := Sp) (t := t₁) (h := 0)
          (by simp only [Nat.max_eq_max] at hlen₁ hsp ⊢; omega)
          (by rw [ht₁0]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlen₁ hsp ⊢; omega)
        rw [ht₁0] at hp
        exact hp
      let t₃ := QCSD_tapeWrite2 t₂ 1 (QCSD_tapeRead t₂ 1)
      have hlen₃ : t₃.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen₂ ⊢; omega
      have hs3 : ProgRuns (primProg (fun c => (false, c, QCSD_HeadDir.left))) Sp 1 (t₂, 1) false (t₃, 0) := by
        have hp := ProgRuns_prim (fun c => (false, c, QCSD_HeadDir.left)) (Sp := Sp) (t := t₂) (h := 1)
          (by simp only [Nat.max_eq_max] at hlen₂ hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlen₂ hsp ⊢; omega)
        exact hp
      refine ⟨t₃, fun p => ?_, hlen₃, ?_⟩
      · rw [tapeEq_write_self t₂ 1 p]
        dsimp [t₂, t₁]
        rw [tapeRead_tapeWrite2, tapeRead_tapeWrite2]
        split_ifs with hp
        · rfl
        · exact heq p
      · have hexit : ProgRuns walkToZeroBody Sp 3 (t_c, 0) false (t₃, 0) := by
          unfold walkToZeroBody
          exact ProgRuns_seq hs1
            (ProgRuns_bind (k := fun b =>
              ifProg b
                (primProg (fun c => (false, c, QCSD_HeadDir.left)))
                (primProg (fun _ => (true, false, QCSD_HeadDir.left))))
              hs2 (ProgRuns_if_true hs3))
        exact (ProgRuns_while_false hexit).mono (Nat.le_refl Sp) (by omega)
    | succ cur ih =>
      intro hcur_lt t_c heq hlen
      let t₁ := QCSD_tapeWrite2 t_c (cur + 1) true
      have hlen₁ : t₁.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen ⊢; omega
      have hs1 : ProgRuns (primProg (fun _ => ((), true, QCSD_HeadDir.left))) Sp 1
          (t_c, cur + 1) () (t₁, cur) := by
        have hp := ProgRuns_prim (fun _ => ((), true, QCSD_HeadDir.left)) (Sp := Sp) (t := t_c) (h := cur + 1)
          (by simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
        simpa [stepHead] using hp
      have ht₁_cur : QCSD_tapeRead t₁ cur = false := by
        dsimp [t₁]; rw [tapeRead_tapeWrite2, ite_eq_right (by omega), heq cur]
        exact hlow cur (by omega)
      let t₂ := QCSD_tapeWrite2 t₁ cur false
      have hlen₂ : t₂.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen₁ ⊢; omega
      have hs2 : ProgRuns (primProg (fun b => (b, b, QCSD_HeadDir.right))) Sp 1
          (t₁, cur) false (t₂, cur + 1) := by
        have hp := ProgRuns_prim (fun b => (b, b, QCSD_HeadDir.right)) (Sp := Sp) (t := t₁) (h := cur)
          (by simp only [Nat.max_eq_max] at hlen₁ hsp ⊢; omega)
          (by rw [ht₁_cur]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlen₁ hsp ⊢; omega)
        rw [ht₁_cur] at hp
        exact hp
      let t₃ := QCSD_tapeWrite2 t₂ (cur + 1) false
      have hlen₃ : t₃.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen₂ ⊢; omega
      have hs3 : ProgRuns (primProg (fun _ => (true, false, QCSD_HeadDir.left))) Sp 1
          (t₂, cur + 1) true (t₃, cur) := by
        have hp := ProgRuns_prim (fun _ => (true, false, QCSD_HeadDir.left)) (Sp := Sp) (t := t₂) (h := cur + 1)
          (by simp only [Nat.max_eq_max] at hlen₂ hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen₂ hsp ⊢; omega)
        simpa [stepHead] using hp
      have heq₃ : tapeEq t₃ t := by
        intro p
        dsimp [t₃, t₂, t₁]
        rw [tapeRead_tapeWrite2]
        by_cases hp1 : p = cur + 1
        · rw [ite_eq_left hp1, hp1]; exact (hlow (cur + 1) hcur_lt).symm
        · rw [ite_eq_right hp1, tapeRead_tapeWrite2]
          by_cases hp0 : p = cur
          · rw [ite_eq_left hp0, hp0]; exact (hlow cur (by omega)).symm
          · rw [ite_eq_right hp0, tapeRead_tapeWrite2, ite_eq_right hp1]
            exact heq p
      have hbody : ProgRuns walkToZeroBody Sp 3 (t_c, cur + 1) true (t₃, cur) := by
        unfold walkToZeroBody
        exact ProgRuns_seq hs1
          (ProgRuns_bind (k := fun b =>
            ifProg b
              (primProg (fun c => (false, c, QCSD_HeadDir.left)))
              (primProg (fun _ => (true, false, QCSD_HeadDir.left))))
            hs2 (ProgRuns_if_false hs3))
      obtain ⟨t_z, hz_read, hz_len, hrRest⟩ := ih (by omega) t₃ heq₃ hlen₃
      exact ⟨t_z, hz_read, hz_len,
        (ProgRuns_while_true hbody hrRest).mono (Nat.le_refl Sp) (by omega)⟩
  obtain ⟨t_z, hz_read, hz_len, hrZ⟩ :=
    hloop (base - 1) (by omega) t₀ heq₀ (by simp only [Nat.max_eq_max] at hlen₀ ⊢; omega)
  obtain ⟨t_r, heq_r, hlen_r, hrR⟩ :=
    ProgRuns_stepRight (Sp := Sp) (t := t_z) (h := 0)
      (by simp only [Nat.max_eq_max] at hz_len hsp ⊢; omega)
  obtain ⟨t', heq', hlen', hrWalk⟩ :=
    ProgRuns_walkRightToTrue (Sp := Sp) (pos := 1) (target := base) (t := t_r)
      (by omega) (by omega)
      (fun p hp1 hpb => by
        rw [heq_r p, hz_read p, ite_eq_right (by omega)]
        exact hlow p hpb)
      (by rw [heq_r base, hz_read base, ite_eq_right (by omega)]; exact htrue)
      (by simp only [Nat.max_eq_max] at hlen_r hz_len hsp ⊢; omega)
  refine ⟨t', fun p => ?_, ?_, ?_⟩
  · rw [heq' p, heq_r p, hz_read p]
  · simp only [Nat.max_eq_max] at hlen' hlen_r hz_len ⊢; omega
  · unfold initOriginSentinelProg
    exact (ProgRuns_seq hrLeft (ProgRuns_seq hrZ (ProgRuns_seq hrR hrWalk))).mono
      (Nat.le_refl Sp) (by omega)

def emitPhysScanStep (b : Bool) : Bool → Bool × Bool × QCSD_HeadDir :=
  fun c => if c then (false, b, QCSD_HeadDir.right) else (true, false, QCSD_HeadDir.left)

def emitPhysBitProg (b : Bool) :=
  seqProg (stepDirProg QCSD_HeadDir.left)
    (seqProg (whileProg (primProg (emitPhysScanStep b)))
      (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.right)))
        walkRightToTrueProg))

lemma ProgRuns_emitPhysBit (b : Bool) {Sp r base : ℕ} {t : List Bool}
    (hr1 : r + 1 < base)
    (hr_true : QCSD_tapeRead t r = true)
    (hmid : ∀ p, r < p → p < base → QCSD_tapeRead t p = false)
    (hbase_true : QCSD_tapeRead t base = true)
    (hsp : Nat.max t.length (base + 2) ≤ Sp) :
    ∃ t' : List Bool,
      (∀ p, QCSD_tapeRead t' p =
        if p = r + 1 then true else if p = r then b else QCSD_tapeRead t p) ∧
      t'.length ≤ Nat.max t.length (base + 1) ∧
      ProgRuns (emitPhysBitProg b) Sp (2 * base + 2) (t, base) () (t', base) := by
  obtain ⟨t₀, heq₀, hlen₀, hrLeft⟩ :=
    ProgRuns_stepLeft (Sp := Sp) (t := t) (h := base)
      (by simp only [Nat.max_eq_max] at hsp ⊢; omega)
  have hscan : ∀ (rem : ℕ), r + rem < base → ∀ t_c : List Bool,
      tapeEq t_c t →
      t_c.length ≤ Nat.max t.length (base + 1) →
      ∃ t_s : List Bool,
        (∀ p, QCSD_tapeRead t_s p = if p = r then b else QCSD_tapeRead t p) ∧
        t_s.length ≤ Nat.max t.length (base + 1) ∧
        ProgRuns (whileProg (primProg (emitPhysScanStep b))) Sp (rem + 1)
          (t_c, r + rem) () (t_s, r + 1) := by
    intro rem
    induction rem with
    | zero =>
      intro _ t_c heq hlen
      rw [Nat.add_zero]
      have hread : QCSD_tapeRead t_c r = true := (heq r).trans hr_true
      let t_s := QCSD_tapeWrite2 t_c r b
      have hlen_s : t_s.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen ⊢; omega
      refine ⟨t_s, fun p => ?_, hlen_s, ?_⟩
      · dsimp [t_s]; rw [tapeRead_tapeWrite2]
        split_ifs with hp
        · rfl
        · exact heq p
      · apply ProgRuns_while_false
        have hp := ProgRuns_prim (emitPhysScanStep b) (Sp := Sp) (t := t_c) (h := r)
          (by simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
          (by rw [hread]; dsimp [emitPhysScanStep, stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
        rw [hread] at hp
        exact hp
    | succ rem ih =>
      intro hlt t_c heq hlen
      let cur := r + (rem + 1)
      have hread : QCSD_tapeRead t_c cur = false :=
        (heq cur).trans (hmid cur (by dsimp [cur]; omega) hlt)
      let t₁ := QCSD_tapeWrite2 t_c cur false
      have heq₁ : tapeEq t₁ t := by
        intro p; dsimp [t₁]; rw [tapeRead_tapeWrite2]
        split_ifs with hp
        · subst hp; exact (hmid cur (by dsimp [cur]; omega) hlt).symm
        · exact heq p
      have hlen₁ : t₁.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, cur] at hlen ⊢; omega
      have hstep : ProgRuns (primProg (emitPhysScanStep b)) Sp 1 (t_c, cur) true (t₁, r + rem) := by
        have hp := ProgRuns_prim (emitPhysScanStep b) (Sp := Sp) (t := t_c) (h := cur)
          (by simp only [Nat.max_eq_max, cur] at hlen hsp ⊢; omega)
          (by rw [hread]; dsimp [emitPhysScanStep, stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, cur] at hlen hsp ⊢; omega)
        rw [hread] at hp
        simpa [emitPhysScanStep, stepHead, cur] using hp
      obtain ⟨t_s, hs_read, hs_len, hrRest⟩ := ih (by omega) t₁ heq₁ hlen₁
      exact ⟨t_s, hs_read, hs_len,
        (ProgRuns_while_true hstep hrRest).mono (Nat.le_refl Sp) (by omega)⟩
  have hrem_eq : r + (base - 1 - r) = base - 1 := by omega
  obtain ⟨t_s, hs_read, hs_len, hrScan⟩ :=
    hscan (base - 1 - r) (by omega) t₀ heq₀ (by simp only [Nat.max_eq_max] at hlen₀ ⊢; omega)
  rw [hrem_eq] at hrScan
  let t_w := QCSD_tapeWrite2 t_s (r + 1) true
  have hlen_w : t_w.length ≤ Nat.max t.length (base + 1) := by
    rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hs_len ⊢; omega
  have hrWrite : ProgRuns (primProg (fun _ => ((), true, QCSD_HeadDir.right))) Sp 1
      (t_s, r + 1) () (t_w, r + 2) := by
    have hp := ProgRuns_prim (fun _ => ((), true, QCSD_HeadDir.right)) (Sp := Sp) (t := t_s) (h := r + 1)
      (by simp only [Nat.max_eq_max] at hs_len hsp ⊢; omega)
      (by dsimp [stepHead]; rw [tapeWrite2_length]
          simp only [Nat.max_eq_max] at hs_len hsp ⊢; omega)
    simpa [stepHead] using hp
  obtain ⟨t', heq', hlen', hrWalk⟩ :=
    ProgRuns_walkRightToTrue (Sp := Sp) (pos := r + 2) (target := base) (t := t_w)
      (by omega) (by omega)
      (fun p hp2 hpb => by
        dsimp [t_w]; rw [tapeRead_tapeWrite2, ite_eq_right (by omega),
          hs_read p, ite_eq_right (by omega)]
        exact hmid p (by omega) hpb)
      (by
        dsimp [t_w]; rw [tapeRead_tapeWrite2, ite_eq_right (by omega),
          hs_read base, ite_eq_right (by omega)]
        exact hbase_true)
      (by simp only [Nat.max_eq_max] at hlen_w hsp ⊢; omega)
  refine ⟨t', fun p => ?_, ?_, ?_⟩
  · rw [heq' p]; dsimp [t_w]; rw [tapeRead_tapeWrite2]
    by_cases hp1 : p = r + 1
    · rw [ite_eq_left hp1, ite_eq_left hp1]
    · rw [ite_eq_right hp1, ite_eq_right hp1]
      exact hs_read p
  · simp only [Nat.max_eq_max] at hlen' hlen_w ⊢; omega
  · unfold emitPhysBitProg
    exact (ProgRuns_seq hrLeft (ProgRuns_seq hrScan (ProgRuns_seq hrWrite hrWalk))).mono
      (Nat.le_refl Sp) (by omega)

def FlushInv (base allocLen : ℕ) (outList : List Bool) (r : ℕ) (t : List Bool) : Prop :=
  1 ≤ allocLen ∧
  outList.length < allocLen ∧
  r ≤ outList.length ∧
  outList.length + 2 ≤ base ∧
  t.length ≤ base + 11 * allocLen ∧
  (∀ p < r, QCSD_tapeRead t p = QCSD_tapeRead outList p) ∧
  QCSD_tapeRead t r = true ∧
  (∀ p, r < p → p < base → QCSD_tapeRead t p = false) ∧
  (∀ i < allocLen,
    QCSD_tapeRead t (base + 11 * i + 0) = true ∧
    QCSD_tapeRead t (base + 11 * i + 1) = decide (i = 0) ∧
    QCSD_tapeRead t (base + 11 * i + 8) = QCSD_tapeRead outList i ∧
    QCSD_tapeRead t (base + 11 * i + 9) = decide (i < r) ∧
    QCSD_tapeRead t (base + 11 * i + 10) = decide (i = outList.length))

lemma FlushInv_of_tapeEq {base allocLen : ℕ} {outList : List Bool} {r : ℕ} {t₁ t₂ : List Bool}
    (hinv : FlushInv base allocLen outList r t₁)
    (heq : tapeEq t₂ t₁)
    (hlen : t₂.length ≤ base + 11 * allocLen) :
    FlushInv base allocLen outList r t₂ := by
  obtain ⟨h1, h2, h3, h4, _, hpre, hrT, hmid, hblk⟩ := hinv
  refine ⟨h1, h2, h3, h4, hlen,
    fun p hp => (heq p).trans (hpre p hp),
    (heq r).trans hrT,
    fun p hp1 hp2 => (heq p).trans (hmid p hp1 hp2),
    fun i hi => ?_⟩
  obtain ⟨b0, b1, b8, b9, b10⟩ := hblk i hi
  exact ⟨(heq _).trans b0, (heq _).trans b1, (heq _).trans b8, (heq _).trans b9, (heq _).trans b10⟩

def flushSeekUnseenProg :=
  whileProg
    (bindProg (readSlotProg ⟨9, by decide⟩) (fun seen =>
      ifProg seen
        (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.right 10))
        (mapExitProg (fun _ => false) nopProg)))

lemma ProgRuns_flushSeekUnseen {Sp base allocLen : ℕ} {outList : List Bool} {r : ℕ} {t : List Bool}
    (hinv : FlushInv base allocLen outList r t)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ t' : List Bool,
      FlushInv base allocLen outList r t' ∧
      ProgRuns flushSeekUnseenProg Sp (31 * r + 22) (t, base) () (t', base + 11 * r) := by
  have hr_lt : r < allocLen := Nat.lt_of_le_of_lt hinv.2.2.1 hinv.2.1
  let body :=
    bindProg (readSlotProg ⟨9, by decide⟩) (fun seen =>
      ifProg seen
        (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.right 10))
        (mapExitProg (fun _ => false) nopProg))
  have hloop : ∀ (rem cur : ℕ), cur + rem = r → ∀ t_c : List Bool,
      FlushInv base allocLen outList r t_c →
      ∃ t_e : List Bool,
        FlushInv base allocLen outList r t_e ∧
        ProgRuns (whileProg body) Sp (31 * rem + 22) (t_c, base + 11 * cur) () (t_e, base + 11 * r) := by
    intro rem
    induction rem with
    | zero =>
      intro cur hcur t_c hc
      have hcr : cur = r := by omega
      subst hcr
      have hlen_c : t_c.length ≤ base + 11 * allocLen := hc.2.2.2.2.1
      obtain ⟨t₁, heq₁, hlen₁, hrR⟩ :=
        ProgRuns_readSlot_raw ⟨9, by decide⟩ (Sp := Sp) (t := t_c) (pos := base + 11 * cur)
          (by simp only [Nat.max_eq_max]; omega)
      have hb9 : QCSD_tapeRead t_c (base + 11 * cur + 9) = false := by
        rw [(hc.2.2.2.2.2.2.2.2 cur hr_lt).2.2.2.1]; simp
      dsimp only at hrR
      rw [hb9] at hrR
      obtain ⟨t₂, heq₂, hlen₂, hrN⟩ :=
        ProgRuns_nop (Sp := Sp) (t := t₁) (h := base + 11 * cur)
          (by simp only [Nat.max_eq_max] at hlen₁ ⊢; omega)
      have hc₂ := FlushInv_of_tapeEq hc (tapeEq_trans heq₂ heq₁)
        (by simp only [Nat.max_eq_max] at hlen₂ hlen₁ ⊢; omega)
      refine ⟨t₂, hc₂, ?_⟩
      rw [Nat.mul_zero, Nat.zero_add]
      apply ProgRuns_while_false
      exact ProgRuns_bind (k := fun seen =>
        ifProg seen
          (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.right 10))
          (mapExitProg (fun _ => false) nopProg))
        hrR (ProgRuns_if_false (ProgRuns_mapExit (fun _ => false) hrN))
    | succ rem ih =>
      intro cur hcur t_c hc
      have hcur_lt_r : cur < r := by omega
      have hcur_lt : cur < allocLen := by omega
      have hlen_c : t_c.length ≤ base + 11 * allocLen := hc.2.2.2.2.1
      obtain ⟨t₁, heq₁, hlen₁, hrR⟩ :=
        ProgRuns_readSlot_raw ⟨9, by decide⟩ (Sp := Sp) (t := t_c) (pos := base + 11 * cur)
          (by simp only [Nat.max_eq_max]; omega)
      have hb9 : QCSD_tapeRead t_c (base + 11 * cur + 9) = true := by
        rw [(hc.2.2.2.2.2.2.2.2 cur hcur_lt).2.2.2.1]; simp [hcur_lt_r]
      dsimp only at hrR
      rw [hb9] at hrR
      obtain ⟨t₂, heq₂, hlen₂, hrM⟩ :=
        ProgRuns_moveRightPos 10 (Sp := Sp) (t := t₁) (h := base + 11 * cur)
          (by simp only [Nat.max_eq_max] at hlen₁ ⊢; omega)
      have hpos : base + 11 * cur + 10 + 1 = base + 11 * (cur + 1) := by omega
      rw [hpos] at hrM hlen₂
      have hc₂ := FlushInv_of_tapeEq hc (tapeEq_trans heq₂ heq₁)
        (by simp only [Nat.max_eq_max] at hlen₂ hlen₁ ⊢; omega)
      obtain ⟨t_e, hc_e, hrRest⟩ := ih (cur + 1) (by omega) t₂ hc₂
      have hstep : ProgRuns body Sp 31 (t_c, base + 11 * cur) true (t₂, base + 11 * (cur + 1)) :=
        ProgRuns_bind (k := fun seen =>
          ifProg seen
            (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.right 10))
            (mapExitProg (fun _ => false) nopProg))
          hrR (ProgRuns_if_true (ProgRuns_mapExit (fun _ => true) hrM))
      exact ⟨t_e, hc_e,
        (ProgRuns_while_true hstep hrRest).mono (Nat.le_refl Sp) (by omega)⟩
  obtain ⟨t_e, hc_e, hr⟩ := hloop r 0 (Nat.zero_add r) t hinv
  have hbz : base + 11 * 0 = base := by omega
  rw [hbz] at hr
  exact ⟨t_e, hc_e, hr⟩

def flushRewindOrigProg :=
  whileProg
    (bindProg (readSlotProg ⟨1, by decide⟩) (fun isOrig =>
      ifProg isOrig
        (mapExitProg (fun _ => false) nopProg)
        (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 10))))

lemma ProgRuns_flushRewindOrig {Sp base allocLen cur : ℕ} {t : List Bool}
    (hcur : cur < allocLen)
    (hlen : t.length ≤ base + 11 * allocLen)
    (horig : ∀ i < allocLen, QCSD_tapeRead t (base + 11 * i + 1) = decide (i = 0))
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ t' : List Bool,
      tapeEq t' t ∧
      t'.length ≤ base + 11 * allocLen ∧
      ProgRuns flushRewindOrigProg Sp (31 * cur + 22) (t, base + 11 * cur) () (t', base) := by
  let body :=
    bindProg (readSlotProg ⟨1, by decide⟩) (fun isOrig =>
      ifProg isOrig
        (mapExitProg (fun _ => false) nopProg)
        (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 10)))
  have hloop : ∀ (k : ℕ), k < allocLen → ∀ t_c : List Bool,
      tapeEq t_c t →
      t_c.length ≤ base + 11 * allocLen →
      ∃ t_e : List Bool,
        tapeEq t_e t ∧
        t_e.length ≤ base + 11 * allocLen ∧
        ProgRuns (whileProg body) Sp (31 * k + 22) (t_c, base + 11 * k) () (t_e, base) := by
    intro k
    induction k with
    | zero =>
      intro hk_lt t_c heq_c hlen_c
      have hbz : base + 11 * 0 = base := by omega
      rw [hbz]
      obtain ⟨t₁, heq₁, hlen₁, hrR⟩ :=
        ProgRuns_readSlot_raw ⟨1, by decide⟩ (Sp := Sp) (t := t_c) (pos := base)
          (by simp only [Nat.max_eq_max]; omega)
      have hb1 : QCSD_tapeRead t_c (base + 1) = true := by
        rw [heq_c]; simpa using horig 0 hk_lt
      dsimp only at hrR
      rw [hb1] at hrR
      obtain ⟨t₂, heq₂, hlen₂, hrN⟩ :=
        ProgRuns_nop (Sp := Sp) (t := t₁) (h := base)
          (by simp only [Nat.max_eq_max] at hlen₁ ⊢; omega)
      refine ⟨t₂, tapeEq_trans heq₂ (tapeEq_trans heq₁ heq_c),
        by simp only [Nat.max_eq_max] at hlen₂ hlen₁ ⊢; omega, ?_⟩
      rw [Nat.mul_zero, Nat.zero_add]
      apply ProgRuns_while_false
      exact ProgRuns_bind (k := fun isOrig =>
        ifProg isOrig
          (mapExitProg (fun _ => false) nopProg)
          (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 10)))
        hrR (ProgRuns_if_true (ProgRuns_mapExit (fun _ => false) hrN))
    | succ k ih =>
      intro hk_lt t_c heq_c hlen_c
      obtain ⟨t₁, heq₁, hlen₁, hrR⟩ :=
        ProgRuns_readSlot_raw ⟨1, by decide⟩ (Sp := Sp) (t := t_c) (pos := base + 11 * (k + 1))
          (by simp only [Nat.max_eq_max]; omega)
      have hb1 : QCSD_tapeRead t_c (base + 11 * (k + 1) + 1) = false := by
        rw [heq_c, horig (k + 1) hk_lt]; simp
      dsimp only at hrR
      rw [hb1] at hrR
      obtain ⟨t₂, heq₂, hlen₂, hrM⟩ :=
        ProgRuns_moveLeftPos 10 (Sp := Sp) (t := t₁) (h := base + 11 * (k + 1))
          (by simp only [Nat.max_eq_max] at hlen₁ ⊢; omega)
      have hpos : base + 11 * (k + 1) - (10 + 1) = base + 11 * k := by omega
      rw [hpos] at hrM
      obtain ⟨t_e, heq_e, hlen_e, hrRest⟩ :=
        ih (by omega) t₂ (tapeEq_trans heq₂ (tapeEq_trans heq₁ heq_c))
          (by simp only [Nat.max_eq_max] at hlen₂ hlen₁ ⊢; omega)
      have hstep : ProgRuns body Sp 31 (t_c, base + 11 * (k + 1)) true (t₂, base + 11 * k) :=
        ProgRuns_bind (k := fun isOrig =>
          ifProg isOrig
            (mapExitProg (fun _ => false) nopProg)
            (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 10)))
          hrR (ProgRuns_if_false (ProgRuns_mapExit (fun _ => true) hrM))
      exact ⟨t_e, heq_e, hlen_e,
        (ProgRuns_while_true hstep hrRest).mono (Nat.le_refl Sp) (by omega)⟩
  exact hloop cur hcur t (tapeEq_refl t) hlen

def flushLoopBody :=
  seqProg flushSeekUnseenProg
    (bindProg (readSlotProg ⟨10, by decide⟩) (fun isEnd =>
      ifProg isEnd
        (mapExitProg (fun _ => false) nopProg)
        (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
          seqProg (writeSlotProg ⟨9, by decide⟩ true)
            (seqProg flushRewindOrigProg
              (mapExitProg (fun _ => true) (emitPhysBitProg b)))))))

def flushSubToOriginRaw :=
  seqProg initOriginSentinelProg (whileProg flushLoopBody)

def FlushSubQ : Type := ProgState flushSubToOriginRaw
instance : Fintype FlushSubQ := by
  unfold FlushSubQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance : DecidableEq FlushSubQ := by
  unfold FlushSubQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def flushSubToOriginProg : Prog FlushSubQ Unit := flushSubToOriginRaw

lemma ProgRuns_flushSubToOrigin
    {Sp base allocLen nLen : ℕ} {inBits cBits preBits outList tape : List Bool}
    (hbt : BlockTape base allocLen inBits nLen cBits preBits outList none (some outList.length) tape)
    (hbase : outList.length + 2 ≤ base)
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ (tape' : List Bool) (hout : ℕ),
      QCSD_tapeRead tape' base = true ∧
      (∀ p < outList.length, QCSD_tapeRead tape' p = QCSD_tapeRead outList p) ∧
      ProgRuns flushSubToOriginProg Sp
        ((4 * base + 3) + (outList.length + 1) * (62 * allocLen + 2 * base + 120))
        (tape, base) () (tape', hout) := by
  have h1 : 1 ≤ allocLen := hbt.1
  have hout_lt : outList.length < allocLen := hbt.2.2.2.2.2.2.2.1 _ rfl
  have hlen₀ : tape.length ≤ base + 11 * allocLen := hbt.2.2.2.2.2.2.2.2.1
  have hbase_t : QCSD_tapeRead tape base = true := by
    have h0_lt : 0 < allocLen := hbt.1
    have hb := BlockTape_read_slot hbt 0 ⟨0, by decide⟩
    simpa [slotVal, h0_lt] using hb
  obtain ⟨t₀, ht₀_read, ht₀_len, hrInit⟩ :=
    ProgRuns_initOriginSentinel (Sp := Sp) (base := base) (t := tape)
      (by omega) hbt.2.2.2.2.2.2.2.2.2.1 hbase_t
      (by simp only [Nat.max_eq_max]; omega)
  have hinv₀ : FlushInv base allocLen outList 0 t₀ := by
    refine ⟨h1, hout_lt, Nat.zero_le _, hbase,
      by simp only [Nat.max_eq_max] at ht₀_len ⊢; omega,
      fun p hp => by omega,
      by rw [ht₀_read 0, ite_eq_left rfl],
      fun p hp1 hp2 => by
        rw [ht₀_read p, ite_eq_right (by omega)]
        exact hbt.2.2.2.2.2.2.2.2.2.1 p hp2,
      fun i hi => ?_⟩
    have hrSlot : ∀ s : Fin 11, QCSD_tapeRead t₀ (base + 11 * i + s.val) =
        slotVal allocLen inBits nLen cBits preBits outList none (some outList.length) i s.val := by
      intro s
      rw [ht₀_read _, ite_eq_right (by omega)]
      exact BlockTape_read_slot hbt i s
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [slotVal, hi] using hrSlot ⟨0, by decide⟩
    · simpa [slotVal, hi] using hrSlot ⟨1, by decide⟩
    · simpa [slotVal, hi] using hrSlot ⟨8, by decide⟩
    · simpa [slotVal, hi] using hrSlot ⟨9, by decide⟩
    · simpa [slotVal, hi, eq_comm] using hrSlot ⟨10, by decide⟩
  let stepBudget := 62 * allocLen + 2 * base + 120
  have hloop : ∀ (rem r : ℕ), r + rem = outList.length → ∀ t_c : List Bool,
      FlushInv base allocLen outList r t_c →
      ∃ (t_e : List Bool) (hout : ℕ),
        FlushInv base allocLen outList outList.length t_e ∧
        ProgRuns (whileProg flushLoopBody) Sp ((rem + 1) * stepBudget)
          (t_c, base) () (t_e, hout) := by
    intro rem
    induction rem with
    | zero =>
      intro r hr_eq t_c hc
      have hro : r = outList.length := by omega
      subst hro
      obtain ⟨t₁, hc₁, hrSeek⟩ := ProgRuns_flushSeekUnseen hc hsp
      have hlen₁ : t₁.length ≤ base + 11 * allocLen := hc₁.2.2.2.2.1
      obtain ⟨t₂, heq₂, hlen₂, hrEnd⟩ :=
        ProgRuns_readSlot_raw ⟨10, by decide⟩ (Sp := Sp) (t := t₁)
          (pos := base + 11 * outList.length) (by simp only [Nat.max_eq_max]; omega)
      have hb10 : QCSD_tapeRead t₁ (base + 11 * outList.length + 10) = true := by
        rw [(hc₁.2.2.2.2.2.2.2.2 outList.length hout_lt).2.2.2.2]; simp
      dsimp only at hrEnd
      rw [hb10] at hrEnd
      obtain ⟨t₃, heq₃, hlen₃, hrNop⟩ :=
        ProgRuns_nop (Sp := Sp) (t := t₂) (h := base + 11 * outList.length)
          (by simp only [Nat.max_eq_max] at hlen₂ ⊢; omega)
      have hc₃ := FlushInv_of_tapeEq hc₁ (tapeEq_trans heq₃ heq₂)
        (by simp only [Nat.max_eq_max] at hlen₃ hlen₂ ⊢; omega)
      refine ⟨t₃, base + 11 * outList.length, hc₃, ?_⟩
      have hexit : ProgRuns flushLoopBody Sp ((31 * outList.length + 22) + (20 + 2))
          (t_c, base) false (t₃, base + 11 * outList.length) := by
        unfold flushLoopBody
        exact ProgRuns_seq hrSeek
          (ProgRuns_bind (k := fun isEnd =>
            ifProg isEnd
              (mapExitProg (fun _ => false) nopProg)
              (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
                seqProg (writeSlotProg ⟨9, by decide⟩ true)
                  (seqProg flushRewindOrigProg
                    (mapExitProg (fun _ => true) (emitPhysBitProg b))))))
            hrEnd (ProgRuns_if_true (ProgRuns_mapExit (fun _ => false) hrNop)))
      exact (ProgRuns_while_false hexit).mono (Nat.le_refl Sp) (by dsimp [stepBudget]; omega)
    | succ rem ih =>
      intro r hr_eq t_c hc
      have hr_lt_out : r < outList.length := by omega
      have hr_lt : r < allocLen := by omega
      obtain ⟨t₁, hc₁, hrSeek⟩ := ProgRuns_flushSeekUnseen hc hsp
      have hlen₁ : t₁.length ≤ base + 11 * allocLen := hc₁.2.2.2.2.1
      obtain ⟨t₂, heq₂, hlen₂, hrEnd⟩ :=
        ProgRuns_readSlot_raw ⟨10, by decide⟩ (Sp := Sp) (t := t₁)
          (pos := base + 11 * r) (by simp only [Nat.max_eq_max]; omega)
      have hb10 : QCSD_tapeRead t₁ (base + 11 * r + 10) = false := by
        rw [(hc₁.2.2.2.2.2.2.2.2 r hr_lt).2.2.2.2]
        exact decide_eq_false (by omega)
      dsimp only at hrEnd
      rw [hb10] at hrEnd
      have hc₂ := FlushInv_of_tapeEq hc₁ heq₂ (by simp only [Nat.max_eq_max] at hlen₂ ⊢; omega)
      have hlen₂' : t₂.length ≤ base + 11 * allocLen := hc₂.2.2.2.2.1
      obtain ⟨t₃, heq₃, hlen₃, hrB⟩ :=
        ProgRuns_readSlot_raw ⟨8, by decide⟩ (Sp := Sp) (t := t₂)
          (pos := base + 11 * r) (by simp only [Nat.max_eq_max]; omega)
      have hb8 : QCSD_tapeRead t₂ (base + 11 * r + 8) = QCSD_tapeRead outList r :=
        (hc₂.2.2.2.2.2.2.2.2 r hr_lt).2.2.1
      dsimp only at hrB
      rw [hb8] at hrB
      have hc₃ := FlushInv_of_tapeEq hc₂ heq₃ (by simp only [Nat.max_eq_max] at hlen₃ ⊢; omega)
      have hlen₃' : t₃.length ≤ base + 11 * allocLen := hc₃.2.2.2.2.1
      obtain ⟨t₄, ht₄_read, hlen₄, hrW9⟩ :=
        ProgRuns_writeSlot_raw ⟨9, by decide⟩ true (Sp := Sp) (t := t₃)
          (pos := base + 11 * r) (by simp only [Nat.max_eq_max]; omega)
      dsimp only at ht₄_read
      have hlen₄' : t₄.length ≤ base + 11 * allocLen := by
        simp only [Nat.max_eq_max] at hlen₄ ⊢; omega
      obtain ⟨t₅, heq₅, hlen₅, hrRew⟩ :=
        ProgRuns_flushRewindOrig hr_lt hlen₄'
          (fun i hi => by
            rw [ht₄_read _, ite_eq_right (by omega)]
            exact (hc₃.2.2.2.2.2.2.2.2 i hi).2.1)
          hsp
      obtain ⟨t₆, ht₆_read, hlen₆, hrEmit⟩ :=
        ProgRuns_emitPhysBit (QCSD_tapeRead outList r) (Sp := Sp) (r := r) (base := base) (t := t₅)
          (by omega)
          (by rw [heq₅ r, ht₄_read r, ite_eq_right (by omega)]; exact hc₃.2.2.2.2.2.2.1)
          (fun p hp1 hp2 => by
            rw [heq₅ p, ht₄_read p, ite_eq_right (by omega)]
            exact hc₃.2.2.2.2.2.2.2.1 p hp1 hp2)
          (by
            rw [heq₅ base, ht₄_read base, ite_eq_right (by omega)]
            simpa using (hc₃.2.2.2.2.2.2.2.2 0 h1).1)
          (by simp only [Nat.max_eq_max]; omega)
      have hc₆ : FlushInv base allocLen outList (r + 1) t₆ := by
        refine ⟨h1, hout_lt, by omega, hbase,
          by simp only [Nat.max_eq_max] at hlen₆ ⊢; omega,
          fun p hp => ?_,
          by rw [ht₆_read (r + 1), ite_eq_left rfl],
          fun p hp1 hp2 => ?_,
          fun i hi => ?_⟩
        · rw [ht₆_read p, ite_eq_right (by omega)]
          by_cases hpr : p = r
          · subst hpr; rw [ite_eq_left rfl]
          · rw [ite_eq_right hpr, heq₅ p, ht₄_read p, ite_eq_right (by omega)]
            exact hc₃.2.2.2.2.2.1 p (by omega)
        · rw [ht₆_read p, ite_eq_right (by omega), ite_eq_right (by omega),
              heq₅ p, ht₄_read p, ite_eq_right (by omega)]
          exact hc₃.2.2.2.2.2.2.2.1 p (by omega) hp2
        · have hge : ∀ s : ℕ, QCSD_tapeRead t₆ (base + 11 * i + s) =
              QCSD_tapeRead t₄ (base + 11 * i + s) := by
            intro s
            rw [ht₆_read _, ite_eq_right (by omega), ite_eq_right (by omega), heq₅ _]
          obtain ⟨b0, b1, b8, b9, b10⟩ := hc₃.2.2.2.2.2.2.2.2 i hi
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [hge 0, ht₄_read _, ite_eq_right (by omega)]; exact b0
          · rw [hge 1, ht₄_read _, ite_eq_right (by omega)]; exact b1
          · rw [hge 8, ht₄_read _, ite_eq_right (by omega)]; exact b8
          · rw [hge 9, ht₄_read _]
            by_cases hir : i = r
            · subst hir; rw [ite_eq_left rfl]; simp
            · have hne : base + 11 * i + 9 ≠ base + 11 * r + 9 := by omega
              rw [ite_eq_right hne, b9]
              have hiff : (i < r) ↔ (i < r + 1) := by omega
              simp [hiff]
          · rw [hge 10, ht₄_read _, ite_eq_right (by omega)]; exact b10
      obtain ⟨t_e, hout, hc_e, hrRest⟩ := ih (r + 1) (by omega) t₆ hc₆
      have hbody : ProgRuns flushLoopBody Sp stepBudget (t_c, base) true (t₆, base) := by
        unfold flushLoopBody
        exact (ProgRuns_seq hrSeek
          (ProgRuns_bind (k := fun isEnd =>
            ifProg isEnd
              (mapExitProg (fun _ => false) nopProg)
              (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
                seqProg (writeSlotProg ⟨9, by decide⟩ true)
                  (seqProg flushRewindOrigProg
                    (mapExitProg (fun _ => true) (emitPhysBitProg b))))))
            hrEnd (ProgRuns_if_false
              (ProgRuns_bind (k := fun b =>
                seqProg (writeSlotProg ⟨9, by decide⟩ true)
                  (seqProg flushRewindOrigProg
                    (mapExitProg (fun _ => true) (emitPhysBitProg b))))
                hrB (ProgRuns_seq hrW9
                  (ProgRuns_seq hrRew (ProgRuns_mapExit (fun _ => true) hrEmit))))))).mono
          (Nat.le_refl Sp) (by dsimp [stepBudget]; omega)
      refine ⟨t_e, hout, hc_e, ?_⟩
      exact (ProgRuns_while_true hbody hrRest).mono (Nat.le_refl Sp) (by nlinarith)
  obtain ⟨t_e, hout, hc_e, hrL⟩ := hloop outList.length 0 (Nat.zero_add _) t₀ hinv₀
  refine ⟨t_e, hout, ?_, hc_e.2.2.2.2.2.1, ?_⟩
  · simpa using (hc_e.2.2.2.2.2.2.2.2 0 h1).1
  · unfold flushSubToOriginProg flushSubToOriginRaw
    exact ProgRuns_seq hrInit hrL

attribute [irreducible] FlushSubQ flushSubToOriginProg

lemma decodeOutputN2_of_flushed {n base : ℕ} {cBits preBits tape : List Bool} {hasWit : Bool}
    (hcLen : cBits.length = 2 * n)
    (hpreLen : hasWit = true → preBits.length = 2 * n)
    (hbase : 4 * n + 3 ≤ base)
    (htBase : QCSD_tapeRead tape base = true)
    (htOut : ∀ p < (outSubList cBits preBits hasWit).length,
      QCSD_tapeRead tape p = QCSD_tapeRead (outSubList cBits preBits hasWit) p) :
    QCSD_decodeOutputN2 n tape =
      some (QCSD_bitsToNat cBits, if hasWit then some preBits else none) := by
  let outL := outSubList cBits preBits hasWit
  have hlen_gt : base < tape.length := by
    by_contra hle
    have hf : QCSD_tapeRead tape base = false := by
      unfold QCSD_tapeRead
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.not_lt.mp hle)]
      rfl
    rw [htBase] at hf
    cases hf
  have htake_c : tape.take (2 * n) = cBits := by
    apply List.ext_getElem
    · rw [List.length_take, hcLen]; omega
    · intro i hi₁ hi₂
      rw [List.getElem_take]
      have hi_2n : i < 2 * n := by rw [hcLen] at hi₂; exact hi₂
      have hi_out : i < outL.length := by
        dsimp [outL, outSubList]
        cases hasWit <;> simp [hcLen] <;> omega
      have h1 : QCSD_tapeRead tape i = tape[i]'(by omega) := by
        unfold QCSD_tapeRead
        simp [List.getD_eq_getElem?_getD, show i < tape.length by omega]
      have h2 : QCSD_tapeRead outL i = cBits[i]'hi₂ := by
        unfold QCSD_tapeRead
        dsimp [outL, outSubList]
        rw [List.append_assoc, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hi₂, List.getElem?_eq_getElem hi₂]
        rfl
      rw [← h1, htOut i hi_out, h2]
  have hbit_2n : tape.getD (2 * n) false = hasWit := by
    have h2n_out : 2 * n < outL.length := by
      dsimp [outL, outSubList]
      cases hasWit <;> simp [hcLen]
    change QCSD_tapeRead tape (2 * n) = hasWit
    rw [htOut (2 * n) h2n_out]
    unfold QCSD_tapeRead
    dsimp [outL, outSubList]
    have hge : cBits.length ≤ 2 * n := by omega
    have hsub : 2 * n - cBits.length = 0 := by omega
    rw [List.append_assoc, List.getD_eq_getElem?_getD,
        List.getElem?_append_right hge, hsub]
    simp
  unfold QCSD_decodeOutputN2
  rw [ite_eq_right (by omega), htake_c, hbit_2n]
  cases hasWit
  · simp
  · have hpL : preBits.length = 2 * n := hpreLen rfl
    have hw_eq : (tape.drop (2 * n + 1)).take (2 * n) = preBits := by
      apply List.ext_getElem
      · rw [List.length_take, List.length_drop, hpL]; omega
      · intro i hi₁ hi₂
        rw [List.getElem_take, List.getElem_drop]
        have hi_2n : i < 2 * n := by rw [hpL] at hi₂; exact hi₂
        have hidx_out : 2 * n + 1 + i < outL.length := by
          dsimp [outL, outSubList]; simp [hcLen, hpL]; omega
        have h1 : QCSD_tapeRead tape (2 * n + 1 + i) = tape[2 * n + 1 + i]'(by omega) := by
          unfold QCSD_tapeRead
          simp [List.getD_eq_getElem?_getD, show 2 * n + 1 + i < tape.length by omega]
        have h2 : QCSD_tapeRead outL (2 * n + 1 + i) = preBits[i]'hi₂ := by
          unfold QCSD_tapeRead
          dsimp [outL, outSubList]
          have hge : (cBits ++ [true]).length ≤ 2 * n + 1 + i := by simp [hcLen]
          have hsub : 2 * n + 1 + i - (cBits ++ [true]).length = i := by simp [hcLen]
          rw [List.getD_eq_getElem?_getD,
              List.getElem?_append_right hge, hsub, List.getElem?_eq_getElem hi₂]
          rfl
        rw [← h1, htOut (2 * n + 1 + i) hidx_out, h2]
    simp [hw_eq, hpL]

/-! ### Section 7a: Phase 1 Unary-Quadruple Sliding Window & Raw Sentinel Popper -/

def winCell (w k off : ℕ) : Bool :=
  if off < 2 then false
  else if off < 2 * w + 2 then
    if off % 2 = 0 then true else decide ((off - 2) / 2 < k)
  else false

def WinPrefix (pos w k : ℕ) (leftBits : List Bool) (t : List Bool) : Prop :=
  k ≤ w ∧
  leftBits.length = pos ∧
  (∀ p < pos, QCSD_tapeRead t p = QCSD_tapeRead leftBits p) ∧
  (∀ off < 2 * w + 3, QCSD_tapeRead t (pos + off) = winCell w k off)

lemma WinPrefix_of_tapeEq {pos w k : ℕ} {leftBits t₁ t₂ : List Bool}
    (hw : WinPrefix pos w k leftBits t₁) (heq : tapeEq t₂ t₁) :
    WinPrefix pos w k leftBits t₂ :=
  ⟨hw.1, hw.2.1,
   fun p hp => (heq p).trans (hw.2.2.1 p hp),
   fun off hoff => (heq _).trans (hw.2.2.2 off hoff)⟩

lemma tapeRead_append_singleton (l : List Bool) (b : Bool) (i : ℕ) (hi : i < l.length + 1) :
    QCSD_tapeRead (l ++ [b]) i = if i = l.length then b else QCSD_tapeRead l i := by
  unfold QCSD_tapeRead
  by_cases heq : i = l.length
  · subst heq
    simp [List.getD_eq_getElem?_getD]
  · have hlt : i < l.length := by omega
    rw [ite_eq_right heq, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hlt, List.getD_eq_getElem?_getD]

def walkWinRightEndProg :=
  whileProg
    (bindProg (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) (fun c₀ =>
      ifProg c₀
        (mapExitProg (fun _ => true) (stepDirProg QCSD_HeadDir.right))
        (mapExitProg (fun _ => false) nopProg)))

lemma ProgRuns_walkWinRightEnd {Sp pos w k j : ℕ} {leftBits t : List Bool}
    (hw : WinPrefix pos w k leftBits t)
    (hj : j ≤ w)
    (hsp : Nat.max t.length (pos + 2 * w + 5) ≤ Sp) :
    ∃ t' : List Bool,
      tapeEq t' t ∧
      t'.length ≤ Nat.max t.length (pos + 2 * w + 5) ∧
      ProgRuns walkWinRightEndProg Sp (3 * (w - j) + 3)
        (t, pos + 2 + 2 * j) () (t', pos + 2 * w + 3) := by
  let body :=
    bindProg (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) (fun c₀ =>
      ifProg c₀
        (mapExitProg (fun _ => true) (stepDirProg QCSD_HeadDir.right))
        (mapExitProg (fun _ => false) nopProg))
  have hloop : ∀ (rem cur : ℕ), cur + rem = w → ∀ t_c : List Bool,
      tapeEq t_c t →
      t_c.length ≤ Nat.max t.length (pos + 2 * w + 5) →
      ∃ t_e : List Bool,
        tapeEq t_e t ∧
        t_e.length ≤ Nat.max t.length (pos + 2 * w + 5) ∧
        ProgRuns (whileProg body) Sp (3 * rem + 3)
          (t_c, pos + 2 + 2 * cur) () (t_e, pos + 2 * w + 3) := by
    intro rem
    induction rem with
    | zero =>
      intro cur hcur t_c heq hlen
      have hcw : cur = w := by omega
      subst hcw
      let p := pos + 2 + 2 * cur
      have hp_eq : p = pos + (2 * cur + 2) := by dsimp [p]; omega
      have hread : QCSD_tapeRead t_c p = false := by
        rw [heq p, hp_eq, hw.2.2.2 (2 * cur + 2) (by omega)]
        simp [winCell]
      let t₁ := QCSD_tapeWrite2 t_c p false
      have heq₁ : tapeEq t₁ t := by
        intro q; dsimp [t₁]; rw [tapeRead_tapeWrite2]
        split_ifs with hq
        · rw [hq, ← heq p]; exact hread.symm
        · exact heq q
      have hlen₁ : t₁.length ≤ Nat.max t.length (pos + 2 * cur + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, p] at hlen ⊢; omega
      have hs1 : ProgRuns (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) Sp 1
          (t_c, p) false (t₁, p + 1) := by
        have hp0 := ProgRuns_prim (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))
          (Sp := Sp) (t := t_c) (h := p)
          (by simp only [Nat.max_eq_max, p] at hlen hsp ⊢; omega)
          (by rw [hread]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, p] at hlen hsp ⊢; omega)
        rw [hread] at hp0
        exact hp0
      obtain ⟨t₂, heq₂, hlen₂, hs2⟩ :=
        ProgRuns_nop (Sp := Sp) (t := t₁) (h := p + 1)
          (by simp only [Nat.max_eq_max, p] at hlen₁ hsp ⊢; omega)
      have hp1 : p + 1 = pos + 2 * cur + 3 := by dsimp [p]; omega
      refine ⟨t₂, tapeEq_trans heq₂ heq₁,
        by rw [hp1] at hlen₂; simp only [Nat.max_eq_max] at hlen₂ hlen₁ ⊢; omega, ?_⟩
      rw [Nat.mul_zero, Nat.zero_add, ← hp1]
      apply ProgRuns_while_false
      exact ProgRuns_bind (k := fun c₀ =>
        ifProg c₀
          (mapExitProg (fun _ => true) (stepDirProg QCSD_HeadDir.right))
          (mapExitProg (fun _ => false) nopProg))
        hs1 (ProgRuns_if_false
          (pT := mapExitProg (fun _ => true) (stepDirProg QCSD_HeadDir.right))
          (ProgRuns_mapExit (fun _ => false) hs2))
    | succ rem ih =>
      intro cur hcur t_c heq hlen
      have hlt : cur < w := by omega
      let p := pos + 2 + 2 * cur
      have hp_eq : p = pos + (2 * cur + 2) := by dsimp [p]; omega
      have hread : QCSD_tapeRead t_c p = true := by
        rw [heq p, hp_eq, hw.2.2.2 (2 * cur + 2) (by omega)]
        unfold winCell
        rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
      let t₁ := QCSD_tapeWrite2 t_c p true
      have heq₁ : tapeEq t₁ t := by
        intro q; dsimp [t₁]; rw [tapeRead_tapeWrite2]
        split_ifs with hq
        · rw [hq, ← heq p]; exact hread.symm
        · exact heq q
      have hlen₁ : t₁.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, p] at hlen ⊢; omega
      have hs1 : ProgRuns (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) Sp 1
          (t_c, p) true (t₁, p + 1) := by
        have hp0 := ProgRuns_prim (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))
          (Sp := Sp) (t := t_c) (h := p)
          (by simp only [Nat.max_eq_max, p] at hlen hsp ⊢; omega)
          (by rw [hread]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, p] at hlen hsp ⊢; omega)
        rw [hread] at hp0
        exact hp0
      obtain ⟨t₂, heq₂, hlen₂, hs2⟩ :=
        ProgRuns_stepRight (Sp := Sp) (t := t₁) (h := p + 1)
          (by simp only [Nat.max_eq_max, p] at hlen₁ hsp ⊢; omega)
      have hp2 : p + 1 + 1 = pos + 2 + 2 * (cur + 1) := by dsimp [p]; omega
      rw [hp2] at hs2
      obtain ⟨t_e, heq_e, hlen_e, hrRest⟩ :=
        ih (cur + 1) (by omega) t₂ (tapeEq_trans heq₂ heq₁)
          (by simp only [Nat.max_eq_max, p] at hlen₂ hlen₁ ⊢; omega)
      have hstep : ProgRuns body Sp 2 (t_c, p) true (t₂, pos + 2 + 2 * (cur + 1)) :=
        ProgRuns_bind (k := fun c₀ =>
          ifProg c₀
            (mapExitProg (fun _ => true) (stepDirProg QCSD_HeadDir.right))
            (mapExitProg (fun _ => false) nopProg))
          hs1 (ProgRuns_if_true
            (pF := mapExitProg (fun _ => false) nopProg)
            (ProgRuns_mapExit (fun _ => true) hs2))
      exact ⟨t_e, heq_e, hlen_e,
        (ProgRuns_while_true hstep hrRest).mono (Nat.le_refl Sp) (by omega)⟩
  exact hloop (w - j) j (by omega) t (tapeEq_refl t) (Nat.le_max_left _ _)

def initWinPairBody :=
  bindProg (primProg (fun b₀ => (b₀, b₀, QCSD_HeadDir.right))) (fun b₀ =>
    ifProg b₀
      (bindProg (primProg (fun b₁ => (b₁, b₁, QCSD_HeadDir.right))) (fun b₁ =>
        ifProg b₁
          (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool)) nopProg)
          (seqProg (moveDirPosProg QCSD_HeadDir.left 1)
            (primProg (fun _ => (Sum.inr true, false, QCSD_HeadDir.right))))))
      (mapExitProg (fun _ => (Sum.inr false : Unit ⊕ Bool)) nopProg))

def initWinProg :=
  seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
    (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
      (loopStateProg () (fun _ => initWinPairBody)))

lemma ProgRuns_initWin {Sp n : ℕ} {rest : List Bool}
    (hn : 2 ≤ n)
    (hsp : (QCSD_natToUnary n ++ rest).length + 4 ≤ Sp) :
    let inp := QCSD_natToUnary n ++ rest
    let w := (n - 2) / 2
    let remBool := decide ((n - 2) % 2 = 1)
    let G := 2 * w + 3
    let midRest := (if remBool then [false] else []) ++ rest
    ∃ t' : List Bool,
      WinPrefix 0 w w [] t' ∧
      (∀ p, G ≤ p → QCSD_tapeRead t' p = QCSD_tapeRead midRest (p - G)) ∧
      t'.length ≤ inp.length + 2 ∧
      ProgRuns initWinProg Sp (4 * n + 10) (inp, 0) remBool (t', G) := by
  let inp := QCSD_natToUnary n ++ rest
  let w := (n - 2) / 2
  let remBool := decide ((n - 2) % 2 = 1)
  let G := 2 * w + 3
  have hsp_inp : inp.length + 4 ≤ Sp := hsp
  have hw_le : 2 * w + 2 ≤ n := by dsimp [w]; omega
  have hinp_len : n + 1 + rest.length = inp.length := by
    simp [inp, QCSD_natToUnary, List.append_assoc]; omega
  have hinp_unary : ∀ p ≤ n, QCSD_tapeRead inp p = decide (p < n) := by
    intro p hp
    unfold QCSD_tapeRead
    dsimp [inp, QCSD_natToUnary]
    rw [List.append_assoc, List.getD_eq_getElem?_getD]
    by_cases hlt : p < n
    · have hrep : p < (List.replicate n true).length := by simpa using hlt
      rw [List.getElem?_append_left hrep]
      simp [hlt]
    · have hp_eq : p = n := by omega
      subst hp_eq
      have hge : (List.replicate p true).length ≤ p := by simp
      rw [List.getElem?_append_right hge]
      simp
  have hinp_rest : ∀ p, n + 1 ≤ p → QCSD_tapeRead inp p = QCSD_tapeRead rest (p - (n + 1)) := by
    intro p hp
    unfold QCSD_tapeRead
    dsimp [inp, QCSD_natToUnary]
    have hge : (List.replicate n true ++ [false]).length ≤ p := by simp; omega
    have hsub : p - (List.replicate n true ++ [false]).length = p - (n + 1) := by simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, hsub,
        List.getD_eq_getElem?_getD]
  let t₁ := QCSD_tapeWrite2 inp 0 false
  have hs1 : ProgRuns (primProg (fun _ => ((), false, QCSD_HeadDir.right))) Sp 1
      (inp, 0) () (t₁, 1) :=
    ProgRuns_prim (fun _ => ((), false, QCSD_HeadDir.right)) (Sp := Sp) (t := inp) (h := 0)
      (by simp only [Nat.max_eq_max]; omega)
      (by dsimp [stepHead]; rw [tapeWrite2_length]; simp only [Nat.max_eq_max]; omega)
  let t₂ := QCSD_tapeWrite2 t₁ 1 false
  have hs2 : ProgRuns (primProg (fun _ => ((), false, QCSD_HeadDir.right))) Sp 1
      (t₁, 1) () (t₂, 2) :=
    ProgRuns_prim (fun _ => ((), false, QCSD_HeadDir.right)) (Sp := Sp) (t := t₁) (h := 1)
      (by dsimp [t₁]; rw [tapeWrite2_length]; simp only [Nat.max_eq_max]; omega)
      (by dsimp [stepHead, t₁]; rw [tapeWrite2_length, tapeWrite2_length]
          simp only [Nat.max_eq_max]; omega)
  have ht₂_len : t₂.length ≤ inp.length + 2 := by
    dsimp [t₂, t₁]; rw [tapeWrite2_length, tapeWrite2_length]
    simp only [Nat.max_eq_max]; omega
  have ht₂_read : ∀ p, QCSD_tapeRead t₂ p = if p < 2 then false else QCSD_tapeRead inp p := by
    intro p; dsimp [t₂, t₁]; rw [tapeRead_tapeWrite2, tapeRead_tapeWrite2]
    by_cases hp1 : p = 1
    · rw [ite_eq_left hp1, ite_eq_left (by omega)]
    · rw [ite_eq_right hp1]
      by_cases hp0 : p = 0
      · rw [ite_eq_left hp0, ite_eq_left (by omega)]
      · rw [ite_eq_right hp0, ite_eq_right (by omega)]
  have hpair : ∀ (rem j : ℕ), j + rem = w → ∀ t_c : List Bool,
      tapeEq t_c t₂ →
      t_c.length ≤ inp.length + 2 →
      ∃ t_e : List Bool,
        WinPrefix 0 w w [] t_e ∧
        (∀ p, G ≤ p → QCSD_tapeRead t_e p =
          QCSD_tapeRead ((if remBool then [false] else []) ++ rest) (p - G)) ∧
        t_e.length ≤ inp.length + 2 ∧
        ProgRuns (loopStateProg () (fun _ => initWinPairBody)) Sp (4 * rem + 6)
          (t_c, 2 + 2 * j) remBool (t_e, G) := by
    intro rem
    induction rem with
    | zero =>
      intro j hj t_c heq hlen
      have hjw : j = w := by omega
      subst hjw
      by_cases hmod : (n - 2) % 2 = 0
      · have hn_eq : n = 2 + 2 * w := by dsimp [w] at *; omega
        have hrem_f : remBool = false := decide_eq_false (by omega)
        have hG_eq : G = n + 1 := by dsimp [G]; omega
        have hb0 : QCSD_tapeRead t_c n = false := by
          rw [heq n, ht₂_read n, ite_eq_right (by omega), hinp_unary n (Nat.le_refl n)]
          simp
        let ta := QCSD_tapeWrite2 t_c n false
        have heqa : tapeEq ta t₂ := by
          intro q; dsimp [ta]; rw [tapeRead_tapeWrite2]
          split_ifs with hq
          · rw [hq, ← heq n]; exact hb0.symm
          · exact heq q
        have hlena : ta.length ≤ inp.length + 2 := by
          rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen ⊢; omega
        have hp1 : ProgRuns (primProg (fun b₀ => (b₀, b₀, QCSD_HeadDir.right))) Sp 1
            (t_c, n) false (ta, n + 1) := by
          have hp := ProgRuns_prim (fun b₀ => (b₀, b₀, QCSD_HeadDir.right))
            (Sp := Sp) (t := t_c) (h := n)
            (by simp only [Nat.max_eq_max] at hlen ⊢; omega)
            (by rw [hb0]; dsimp [stepHead]; rw [tapeWrite2_length]
                simp only [Nat.max_eq_max] at hlen ⊢; omega)
          rw [hb0] at hp; exact hp
        obtain ⟨tb, heqb, hlenb, hp2⟩ :=
          ProgRuns_nop (Sp := Sp) (t := ta) (h := n + 1)
            (by simp only [Nat.max_eq_max] at hlena ⊢; omega)
        have heq_tb : tapeEq tb t₂ := tapeEq_trans heqb heqa
        refine ⟨tb, ?_, ?_, by simp only [Nat.max_eq_max] at hlenb hlena ⊢; omega, ?_⟩
        · refine ⟨Nat.le_refl w, rfl, fun p hp => by omega, fun off hoff => ?_⟩
          rw [Nat.zero_add, heq_tb off, ht₂_read off]
          by_cases h2 : off < 2
          · simp [winCell, h2]
          · rw [ite_eq_right h2, hinp_unary off (by omega)]
            by_cases hlt_n : off < 2 * w + 2
            · have hoff_lt_n : off < n := by omega
              rw [decide_eq_true hoff_lt_n]
              unfold winCell
              rw [ite_eq_right h2, ite_eq_left hlt_n]
              split_ifs
              · rfl
              · exact (decide_eq_true (by omega)).symm
            · have hoff_eq_n : off = n := by omega
              rw [hoff_eq_n]
              have hn2 : ¬ n < 2 := by omega
              have hnw : ¬ n < 2 * w + 2 := by omega
              simp [winCell, hn2, hnw]
        · intro p hp
          rw [hG_eq] at hp ⊢
          rw [hrem_f]
          simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
          rw [heq_tb p, ht₂_read p, ite_eq_right (by omega)]
          exact hinp_rest p hp
        · rw [← hn_eq, hG_eq, hrem_f]
          exact (ProgRuns_loopState_exit (by
            unfold initWinPairBody
            exact ProgRuns_bind (k := fun b₀ =>
              ifProg b₀
                (bindProg (primProg (fun b₁ => (b₁, b₁, QCSD_HeadDir.right))) (fun b₁ =>
                  ifProg b₁
                    (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool)) nopProg)
                    (seqProg (moveDirPosProg QCSD_HeadDir.left 1)
                      (primProg (fun _ => (Sum.inr true, false, QCSD_HeadDir.right))))))
                (mapExitProg (fun _ => (Sum.inr false : Unit ⊕ Bool)) nopProg))
              hp1 (ProgRuns_if_false
                (pT := bindProg (primProg (fun b₁ => (b₁, b₁, QCSD_HeadDir.right))) (fun b₁ =>
                  ifProg b₁
                    (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool)) nopProg)
                    (seqProg (moveDirPosProg QCSD_HeadDir.left 1)
                      (primProg (fun _ => (Sum.inr true, false, QCSD_HeadDir.right))))))
                (ProgRuns_mapExit (fun _ => (Sum.inr false : Unit ⊕ Bool)) hp2)))).mono
            (Nat.le_refl Sp) (by omega)
      · have hmod1 : (n - 2) % 2 = 1 := by omega
        have hn_eq : n = 2 + 2 * w + 1 := by dsimp [w] at *; omega
        have hrem_t : remBool = true := by dsimp [remBool]; exact decide_eq_true hmod1
        have hG_eq : G = n := by dsimp [G]; omega
        let p0 := 2 + 2 * w
        have hb0 : QCSD_tapeRead t_c p0 = true := by
          rw [heq p0, ht₂_read p0, ite_eq_right (by dsimp [p0]; omega),
              hinp_unary p0 (by dsimp [p0]; omega)]
          exact decide_eq_true (by dsimp [p0]; omega)
        let ta := QCSD_tapeWrite2 t_c p0 true
        have heqa : tapeEq ta t₂ := by
          intro q; dsimp [ta]; rw [tapeRead_tapeWrite2]
          split_ifs with hq
          · rw [hq, ← heq p0]; exact hb0.symm
          · exact heq q
        have hlena : ta.length ≤ inp.length + 2 := by
          rw [tapeWrite2_length]; simp only [Nat.max_eq_max, p0] at hlen ⊢; omega
        have hp1 : ProgRuns (primProg (fun b₀ => (b₀, b₀, QCSD_HeadDir.right))) Sp 1
            (t_c, p0) true (ta, n) := by
          have hp := ProgRuns_prim (fun b₀ => (b₀, b₀, QCSD_HeadDir.right))
            (Sp := Sp) (t := t_c) (h := p0)
            (by simp only [Nat.max_eq_max, p0] at hlen ⊢; omega)
            (by rw [hb0]; dsimp [stepHead]; rw [tapeWrite2_length]
                simp only [Nat.max_eq_max, p0] at hlen ⊢; omega)
          rw [hb0] at hp
          have hp01 : stepHead p0 QCSD_HeadDir.right = n := by dsimp [stepHead, p0]; omega
          rw [hp01] at hp; exact hp
        have hb1 : QCSD_tapeRead ta n = false := by
          rw [heqa n, ht₂_read n, ite_eq_right (by omega), hinp_unary n (Nat.le_refl n)]
          simp
        let tb := QCSD_tapeWrite2 ta n false
        have heqb : tapeEq tb t₂ := by
          intro q; dsimp [tb]; rw [tapeRead_tapeWrite2]
          split_ifs with hq
          · rw [hq, ← heqa n]; exact hb1.symm
          · exact heqa q
        have hlenb : tb.length ≤ inp.length + 2 := by
          rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlena ⊢; omega
        have hp2 : ProgRuns (primProg (fun b₁ => (b₁, b₁, QCSD_HeadDir.right))) Sp 1
            (ta, n) false (tb, n + 1) := by
          have hp := ProgRuns_prim (fun b₁ => (b₁, b₁, QCSD_HeadDir.right))
            (Sp := Sp) (t := ta) (h := n)
            (by simp only [Nat.max_eq_max] at hlena ⊢; omega)
            (by rw [hb1]; dsimp [stepHead]; rw [tapeWrite2_length]
                simp only [Nat.max_eq_max] at hlena ⊢; omega)
          rw [hb1] at hp; exact hp
        obtain ⟨tc, heqc, hlenc, hp3⟩ :=
          ProgRuns_moveLeftPos 1 (Sp := Sp) (t := tb) (h := n + 1)
            (by simp only [Nat.max_eq_max] at hlenb ⊢; omega)
        have hsub_p0 : n + 1 - (1 + 1) = p0 := by dsimp [p0]; omega
        rw [hsub_p0] at hp3
        let td := QCSD_tapeWrite2 tc p0 false
        have hlend : td.length ≤ inp.length + 2 := by
          rw [tapeWrite2_length]; simp only [Nat.max_eq_max, p0] at hlenc hlenb ⊢; omega
        have hp4 : ProgRuns (primProg (fun _ => (Sum.inr true, false, QCSD_HeadDir.right))) Sp 1
            (tc, p0) (Sum.inr true : Unit ⊕ Bool) (td, n) := by
          have hp := ProgRuns_prim (fun _ => ((Sum.inr true : Unit ⊕ Bool), false, QCSD_HeadDir.right))
            (Sp := Sp) (t := tc) (h := p0)
            (by simp only [Nat.max_eq_max, p0] at hlenc hlenb ⊢; omega)
            (by dsimp [stepHead]; rw [tapeWrite2_length]
                simp only [Nat.max_eq_max, p0] at hlenc hlenb ⊢; omega)
          have hp01 : stepHead p0 QCSD_HeadDir.right = n := by dsimp [stepHead, p0]; omega
          rw [hp01] at hp; exact hp
        have heq_tc : tapeEq tc t₂ := tapeEq_trans heqc heqb
        refine ⟨td, ?_, ?_, hlend, ?_⟩
        · refine ⟨Nat.le_refl w, rfl, fun p hp => by omega, fun off hoff => ?_⟩
          rw [Nat.zero_add]
          dsimp [td]; rw [tapeRead_tapeWrite2]
          by_cases hoff_p0 : off = p0
          · rw [ite_eq_left hoff_p0, hoff_p0]
            unfold winCell
            have h1 : ¬ p0 < 2 := by dsimp [p0]; omega
            have h2 : ¬ p0 < 2 * w + 2 := by dsimp [p0]; omega
            rw [ite_eq_right h1, ite_eq_right h2]
          · rw [ite_eq_right hoff_p0, heq_tc off, ht₂_read off]
            by_cases h2 : off < 2
            · simp [winCell, h2]
            · have hoff_lt_p0 : off < 2 * w + 2 := by dsimp [p0] at hoff_p0; omega
              rw [ite_eq_right h2, hinp_unary off (by omega), decide_eq_true (by omega)]
              unfold winCell
              rw [ite_eq_right h2, ite_eq_left hoff_lt_p0]
              split_ifs
              · rfl
              · exact (decide_eq_true (by omega)).symm
        · intro p hp
          rw [hG_eq] at hp ⊢
          rw [hrem_t]
          simp only [↓reduceIte, List.singleton_append]
          dsimp [td]; rw [tapeRead_tapeWrite2, ite_eq_right (by dsimp [p0]; omega),
            heq_tc p, ht₂_read p, ite_eq_right (by omega)]
          by_cases hpn : p = n
          · subst hpn
            rw [hinp_unary p (Nat.le_refl p), Nat.sub_self]
            simp [QCSD_tapeRead]
          · have hgt : n + 1 ≤ p := by omega
            rw [hinp_rest p hgt]
            have hsub : p - n = (p - (n + 1)) + 1 := by omega
            rw [hsub]
            unfold QCSD_tapeRead
            simp [List.getD_eq_getElem?_getD]
        · rw [hG_eq, hrem_t]
          exact (ProgRuns_loopState_exit (by
            unfold initWinPairBody
            exact ProgRuns_bind (k := fun b₀ =>
              ifProg b₀
                (bindProg (primProg (fun b₁ => (b₁, b₁, QCSD_HeadDir.right))) (fun b₁ =>
                  ifProg b₁
                    (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool)) nopProg)
                    (seqProg (moveDirPosProg QCSD_HeadDir.left 1)
                      (primProg (fun _ => (Sum.inr true, false, QCSD_HeadDir.right))))))
                (mapExitProg (fun _ => (Sum.inr false : Unit ⊕ Bool)) nopProg))
              hp1 (ProgRuns_if_true
                (pF := mapExitProg (fun _ => (Sum.inr false : Unit ⊕ Bool)) nopProg)
                (ProgRuns_bind (k := fun b₁ =>
                  ifProg b₁
                    (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool)) nopProg)
                    (seqProg (moveDirPosProg QCSD_HeadDir.left 1)
                      (primProg (fun _ => (Sum.inr true, false, QCSD_HeadDir.right)))))
                  hp2 (ProgRuns_if_false
                    (pT := mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool)) nopProg)
                    (ProgRuns_seq hp3 hp4)))))).mono (Nat.le_refl Sp) (by omega)
    | succ rem ih =>
      intro j hj t_c heq hlen
      let p0 := 2 + 2 * j
      have hp0_1 : p0 + 1 < n := by dsimp [p0, w] at *; omega
      have hb0 : QCSD_tapeRead t_c p0 = true := by
        rw [heq p0, ht₂_read p0, ite_eq_right (by dsimp [p0]; omega),
            hinp_unary p0 (by omega)]
        exact decide_eq_true (by omega)
      let ta := QCSD_tapeWrite2 t_c p0 true
      have heqa : tapeEq ta t₂ := by
        intro q; dsimp [ta]; rw [tapeRead_tapeWrite2]
        split_ifs with hq
        · rw [hq, ← heq p0]; exact hb0.symm
        · exact heq q
      have hlena : ta.length ≤ inp.length + 2 := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, p0] at hlen ⊢; omega
      have hp1 : ProgRuns (primProg (fun b₀ => (b₀, b₀, QCSD_HeadDir.right))) Sp 1
          (t_c, p0) true (ta, p0 + 1) := by
        have hp := ProgRuns_prim (fun b₀ => (b₀, b₀, QCSD_HeadDir.right))
          (Sp := Sp) (t := t_c) (h := p0)
          (by simp only [Nat.max_eq_max, p0] at hlen ⊢; omega)
          (by rw [hb0]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, p0] at hlen ⊢; omega)
        rw [hb0] at hp; exact hp
      have hb1 : QCSD_tapeRead ta (p0 + 1) = true := by
        rw [heqa (p0 + 1), ht₂_read (p0 + 1), ite_eq_right (by dsimp [p0]; omega),
            hinp_unary (p0 + 1) (by omega)]
        exact decide_eq_true hp0_1
      let tb := QCSD_tapeWrite2 ta (p0 + 1) true
      have heqb : tapeEq tb t₂ := by
        intro q; dsimp [tb]; rw [tapeRead_tapeWrite2]
        split_ifs with hq
        · rw [hq, ← heqa (p0 + 1)]; exact hb1.symm
        · exact heqa q
      have hlenb : tb.length ≤ inp.length + 2 := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, p0] at hlena ⊢; omega
      have hp2 : ProgRuns (primProg (fun b₁ => (b₁, b₁, QCSD_HeadDir.right))) Sp 1
          (ta, p0 + 1) true (tb, 2 + 2 * (j + 1)) := by
        have hp := ProgRuns_prim (fun b₁ => (b₁, b₁, QCSD_HeadDir.right))
          (Sp := Sp) (t := ta) (h := p0 + 1)
          (by simp only [Nat.max_eq_max, p0] at hlena ⊢; omega)
          (by rw [hb1]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, p0] at hlena ⊢; omega)
        rw [hb1] at hp
        have hp12 : stepHead (p0 + 1) QCSD_HeadDir.right = 2 + 2 * (j + 1) := by
          dsimp [stepHead, p0]; omega
        rw [hp12] at hp; exact hp
      obtain ⟨tc, heqc, hlenc, hp3⟩ :=
        ProgRuns_nop (Sp := Sp) (t := tb) (h := 2 + 2 * (j + 1))
          (by simp only [Nat.max_eq_max] at hlenb ⊢; omega)
      obtain ⟨t_e, hw_e, hr_e, hlen_e, hrRest⟩ :=
        ih (j + 1) (by omega) tc (tapeEq_trans heqc heqb)
          (by simp only [Nat.max_eq_max] at hlenc hlenb ⊢; omega)
      have hbody : ProgRuns initWinPairBody Sp 4
          (t_c, p0) (Sum.inl () : Unit ⊕ Bool) (tc, 2 + 2 * (j + 1)) := by
        unfold initWinPairBody
        exact ProgRuns_bind (k := fun b₀ =>
          ifProg b₀
            (bindProg (primProg (fun b₁ => (b₁, b₁, QCSD_HeadDir.right))) (fun b₁ =>
              ifProg b₁
                (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool)) nopProg)
                (seqProg (moveDirPosProg QCSD_HeadDir.left 1)
                  (primProg (fun _ => (Sum.inr true, false, QCSD_HeadDir.right))))))
            (mapExitProg (fun _ => (Sum.inr false : Unit ⊕ Bool)) nopProg))
          hp1 (ProgRuns_if_true
            (pF := mapExitProg (fun _ => (Sum.inr false : Unit ⊕ Bool)) nopProg)
            (ProgRuns_bind (k := fun b₁ =>
              ifProg b₁
                (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool)) nopProg)
                (seqProg (moveDirPosProg QCSD_HeadDir.left 1)
                  (primProg (fun _ => (Sum.inr true, false, QCSD_HeadDir.right)))))
              hp2 (ProgRuns_if_true
                (pF := seqProg (moveDirPosProg QCSD_HeadDir.left 1)
                  (primProg (fun _ => (Sum.inr true, false, QCSD_HeadDir.right))))
                (ProgRuns_mapExit (fun _ => (Sum.inl () : Unit ⊕ Bool)) hp3))))
      exact ⟨t_e, hw_e, hr_e, hlen_e,
        (ProgRuns_loopState_cont hbody hrRest).mono (Nat.le_refl Sp) (by omega)⟩
  obtain ⟨t_e, hw_e, hr_e, hlen_e, hrLoop⟩ :=
    hpair w 0 (Nat.zero_add w) t₂ (tapeEq_refl t₂) ht₂_len
  refine ⟨t_e, hw_e, hr_e, hlen_e, ?_⟩
  unfold initWinProg
  exact (ProgRuns_seq hs1 (ProgRuns_seq hs2 hrLoop)).mono (Nat.le_refl Sp) (by dsimp [w]; omega)

def slideShiftBody (bNext : Bool) :=
  bindProg (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) (fun c₀ =>
    ifProg c₀
      (bindProg (primProg (fun m => (m, true, QCSD_HeadDir.right))) (fun m =>
        seqProg (primProg (fun _ => ((), m, QCSD_HeadDir.left)))
          (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 2))))
      (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
        (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
          (seqProg (stepDirProg QCSD_HeadDir.left)
            (seqProg (primProg (fun _ => ((), bNext, QCSD_HeadDir.right)))
              (mapExitProg (fun _ => false) (moveDirPosProg QCSD_HeadDir.right 1)))))))

def slideWinRightRaw :=
  bindProg (primProg (fun bNext => (bNext, false, QCSD_HeadDir.left))) (fun bNext =>
    seqProg (moveDirPosProg QCSD_HeadDir.left 1)
      (seqProg (whileProg (slideShiftBody bNext)) walkWinRightEndProg))

def SlideWinRightQ : Type := ProgState slideWinRightRaw
instance : Fintype SlideWinRightQ := by
  unfold SlideWinRightQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance : DecidableEq SlideWinRightQ := by
  unfold SlideWinRightQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def slideWinRightProg : Prog SlideWinRightQ Unit := slideWinRightRaw

lemma ProgRuns_slideWinRight {Sp pos w k : ℕ} {leftBits t : List Bool}
    (hw : WinPrefix pos w k leftBits t)
    (hsp : Nat.max t.length (pos + 2 * w + 6) ≤ Sp) :
    let bNext := QCSD_tapeRead t (pos + 2 * w + 3)
    ∃ t' : List Bool,
      WinPrefix (pos + 1) w k (leftBits ++ [bNext]) t' ∧
      (∀ p, pos + 2 * w + 4 ≤ p → QCSD_tapeRead t' p = QCSD_tapeRead t p) ∧
      t'.length ≤ Nat.max t.length (pos + 2 * w + 6) ∧
      ProgRuns slideWinRightProg Sp (12 * w + 20)
        (t, pos + 2 * w + 3) () (t', (pos + 1) + 2 * w + 3) := by
  let bNext := QCSD_tapeRead t (pos + 2 * w + 3)
  let t₀ := QCSD_tapeWrite2 t (pos + 2 * w + 3) false
  have hlen₀ : t₀.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
    rw [tapeWrite2_length]; simp only [Nat.max_eq_max]; omega
  have hs0 : ProgRuns (primProg (fun b => (b, false, QCSD_HeadDir.left))) Sp 1
      (t, pos + 2 * w + 3) bNext (t₀, pos + 2 * w + 2) := by
    have hp := ProgRuns_prim (fun b => (b, false, QCSD_HeadDir.left))
      (Sp := Sp) (t := t) (h := pos + 2 * w + 3)
      (by simp only [Nat.max_eq_max] at hsp ⊢; omega)
      (by dsimp [stepHead]; rw [tapeWrite2_length]
          simp only [Nat.max_eq_max] at hsp ⊢; omega)
    simpa [bNext, stepHead] using hp
  obtain ⟨t₁, heq₁, hlen₁, hs1⟩ :=
    ProgRuns_moveLeftPos 1 (Sp := Sp) (t := t₀) (h := pos + 2 * w + 2)
      (by simp only [Nat.max_eq_max] at hlen₀ hsp ⊢; omega)
  have hsub₁ : pos + 2 * w + 2 - (1 + 1) = pos + 2 * w := by omega
  rw [hsub₁] at hs1
  have hshift : ∀ (r : ℕ), r ≤ w → ∀ t_c : List Bool,
      t_c.length ≤ Nat.max t.length (pos + 2 * w + 5) →
      (∀ p < pos + 2 * r + 2, QCSD_tapeRead t_c p = QCSD_tapeRead t p) →
      (∀ off, 2 * r + 2 ≤ off → off < 2 * w + 3 →
        QCSD_tapeRead t_c ((pos + 1) + off) = winCell w k off) →
      (∀ p, pos + 2 * w + 4 ≤ p → QCSD_tapeRead t_c p = QCSD_tapeRead t p) →
      ∃ t_s : List Bool,
        WinPrefix (pos + 1) w k (leftBits ++ [bNext]) t_s ∧
        (∀ p, pos + 2 * w + 4 ≤ p → QCSD_tapeRead t_s p = QCSD_tapeRead t p) ∧
        t_s.length ≤ Nat.max t.length (pos + 2 * w + 5) ∧
        ProgRuns (whileProg (slideShiftBody bNext)) Sp (6 * r + 7)
          (t_c, pos + 2 * r) () (t_s, (pos + 1) + 2) := by
    intro r
    induction r with
    | zero =>
      intro _ t_c hlen hlow hmid hhigh
      rw [Nat.mul_zero, Nat.add_zero]
      have hc0 : QCSD_tapeRead t_c pos = false := by
        rw [hlow pos (by omega)]
        simpa [winCell] using hw.2.2.2 0 (by omega)
      let ta := QCSD_tapeWrite2 t_c pos false
      have hlena : ta.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen ⊢; omega
      have hp1 : ProgRuns (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) Sp 1
          (t_c, pos) false (ta, pos + 1) := by
        have hp := ProgRuns_prim (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))
          (Sp := Sp) (t := t_c) (h := pos)
          (by simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
          (by rw [hc0]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
        rw [hc0] at hp; exact hp
      let tb := QCSD_tapeWrite2 ta (pos + 1) false
      have hlenb : tb.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlena ⊢; omega
      have hp2 : ProgRuns (primProg (fun _ => ((), false, QCSD_HeadDir.right))) Sp 1
          (ta, pos + 1) () (tb, pos + 2) :=
        ProgRuns_prim (fun _ => ((), false, QCSD_HeadDir.right))
          (Sp := Sp) (t := ta) (h := pos + 1)
          (by simp only [Nat.max_eq_max] at hlena hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlena hsp ⊢; omega)
      let tc := QCSD_tapeWrite2 tb (pos + 2) false
      have hlenc : tc.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlenb ⊢; omega
      have hp3 : ProgRuns (primProg (fun _ => ((), false, QCSD_HeadDir.left))) Sp 1
          (tb, pos + 2) () (tc, pos + 1) := by
        have hp := ProgRuns_prim (fun _ => ((), false, QCSD_HeadDir.left))
          (Sp := Sp) (t := tb) (h := pos + 2)
          (by simp only [Nat.max_eq_max] at hlenb hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlenb hsp ⊢; omega)
        simpa [stepHead] using hp
      obtain ⟨td, heqd, hlend, hp4⟩ :=
        ProgRuns_stepLeft (Sp := Sp) (t := tc) (h := pos + 1)
          (by simp only [Nat.max_eq_max] at hlenc hsp ⊢; omega)
      have hsubd : pos + 1 - 1 = pos := by omega
      rw [hsubd] at hp4
      let te := QCSD_tapeWrite2 td pos bNext
      have hlene : te.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlend hlenc ⊢; omega
      have hp5 : ProgRuns (primProg (fun _ => ((), bNext, QCSD_HeadDir.right))) Sp 1
          (td, pos) () (te, pos + 1) :=
        ProgRuns_prim (fun _ => ((), bNext, QCSD_HeadDir.right))
          (Sp := Sp) (t := td) (h := pos)
          (by simp only [Nat.max_eq_max] at hlend hlenc hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlend hlenc hsp ⊢; omega)
      obtain ⟨tf, heqf, hlenf, hp6⟩ :=
        ProgRuns_moveRightPos 1 (Sp := Sp) (t := te) (h := pos + 1)
          (by simp only [Nat.max_eq_max] at hlene hsp ⊢; omega)
      have haddf : pos + 1 + 1 + 1 = (pos + 1) + 2 := by omega
      rw [haddf] at hp6 hlenf
      have htf_read : ∀ p, QCSD_tapeRead tf p =
          if p = pos then bNext
          else if p = pos + 1 ∨ p = pos + 2 then false
          else QCSD_tapeRead t_c p := by
        intro p
        rw [heqf p]; dsimp [te]
        rw [tapeRead_tapeWrite2]
        by_cases h0 : p = pos
        · rw [ite_eq_left h0, ite_eq_left h0]
        · rw [ite_eq_right h0, ite_eq_right h0, heqd p]
          dsimp [tc, tb, ta]
          rw [tapeRead_tapeWrite2, tapeRead_tapeWrite2, tapeRead_tapeWrite2, ite_eq_right h0]
          by_cases h2 : p = pos + 2
          · rw [ite_eq_left h2, ite_eq_left (Or.inr h2)]
          · rw [ite_eq_right h2]
            by_cases h1 : p = pos + 1
            · rw [ite_eq_left h1, ite_eq_left (Or.inl h1)]
            · rw [ite_eq_right h1, ite_eq_right (fun h => h.elim h1 h2)]
      refine ⟨tf, ?_, ?_, by simp only [Nat.max_eq_max] at hlenf hlene ⊢; omega, ?_⟩
      · refine ⟨hw.1, by simp [hw.2.1], fun p hp => ?_, fun off hoff => ?_⟩
        · rw [tapeRead_append_singleton leftBits bNext p (by rw [hw.2.1]; exact hp), hw.2.1]
          by_cases h0 : p = pos
          · rw [ite_eq_left h0, htf_read p, ite_eq_left h0]
          · rw [ite_eq_right h0, htf_read p, ite_eq_right h0,
                ite_eq_right (by omega), hlow p (by omega)]
            exact hw.2.2.1 p (by omega)
        · rw [htf_read ((pos + 1) + off), ite_eq_right (by omega)]
          by_cases hoff2 : off < 2
          · have hor : (pos + 1) + off = pos + 1 ∨ (pos + 1) + off = pos + 2 := by omega
            rw [ite_eq_left hor]
            simp [winCell, hoff2]
          · rw [ite_eq_right (by omega)]
            exact hmid off (by omega) hoff
      · intro p hp
        rw [htf_read p, ite_eq_right (by omega), ite_eq_right (by omega)]
        exact hhigh p hp
      · have hexit : ProgRuns (slideShiftBody bNext) Sp 7 (t_c, pos) false (tf, (pos + 1) + 2) := by
          unfold slideShiftBody
          exact ProgRuns_bind (k := fun c₀ =>
            ifProg c₀
              (bindProg (primProg (fun m => (m, true, QCSD_HeadDir.right))) (fun m =>
                seqProg (primProg (fun _ => ((), m, QCSD_HeadDir.left)))
                  (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 2))))
              (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                  (seqProg (stepDirProg QCSD_HeadDir.left)
                    (seqProg (primProg (fun _ => ((), bNext, QCSD_HeadDir.right)))
                      (mapExitProg (fun _ => false) (moveDirPosProg QCSD_HeadDir.right 1)))))))
            hp1 (ProgRuns_if_false
              (pT := bindProg (primProg (fun m => (m, true, QCSD_HeadDir.right))) (fun m =>
                seqProg (primProg (fun _ => ((), m, QCSD_HeadDir.left)))
                  (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 2))))
              (ProgRuns_seq hp2 (ProgRuns_seq hp3 (ProgRuns_seq hp4
                (ProgRuns_seq hp5 (ProgRuns_mapExit (fun _ => false) hp6))))))
        exact (ProgRuns_while_false hexit).mono (Nat.le_refl Sp) (by omega)
    | succ r ih =>
      intro hr_le t_c hlen hlow hmid hhigh
      let q := pos + 2 * (r + 1)
      have hq_eq : q = pos + (2 * r + 2) := by dsimp [q]; omega
      have hc0 : QCSD_tapeRead t_c q = true := by
        rw [hlow q (by dsimp [q]; omega), hq_eq, hw.2.2.2 (2 * r + 2) (by omega)]
        unfold winCell
        rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
      let ta := QCSD_tapeWrite2 t_c q true
      have hlena : ta.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, q] at hlen ⊢; omega
      have hp1 : ProgRuns (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) Sp 1
          (t_c, q) true (ta, q + 1) := by
        have hp := ProgRuns_prim (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))
          (Sp := Sp) (t := t_c) (h := q)
          (by simp only [Nat.max_eq_max, q] at hlen hsp ⊢; omega)
          (by rw [hc0]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, q] at hlen hsp ⊢; omega)
        rw [hc0] at hp; exact hp
      let mVal := winCell w k (2 * r + 3)
      have hm_read : QCSD_tapeRead ta (q + 1) = mVal := by
        dsimp [ta]; rw [tapeRead_tapeWrite2, ite_eq_right (by omega),
          hlow (q + 1) (by dsimp [q]; omega)]
        have hq1 : q + 1 = pos + (2 * r + 3) := by dsimp [q]; omega
        rw [hq1]; exact hw.2.2.2 (2 * r + 3) (by omega)
      let tb := QCSD_tapeWrite2 ta (q + 1) true
      have hlenb : tb.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, q] at hlena ⊢; omega
      have hp2 : ProgRuns (primProg (fun m => (m, true, QCSD_HeadDir.right))) Sp 1
          (ta, q + 1) mVal (tb, q + 2) := by
        have hp := ProgRuns_prim (fun m => (m, true, QCSD_HeadDir.right))
          (Sp := Sp) (t := ta) (h := q + 1)
          (by simp only [Nat.max_eq_max, q] at hlena hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, q] at hlena hsp ⊢; omega)
        rw [hm_read] at hp; exact hp
      let tc := QCSD_tapeWrite2 tb (q + 2) mVal
      have hlenc : tc.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, q] at hlenb ⊢; omega
      have hp3 : ProgRuns (primProg (fun _ => ((), mVal, QCSD_HeadDir.left))) Sp 1
          (tb, q + 2) () (tc, q + 1) := by
        have hp := ProgRuns_prim (fun _ => ((), mVal, QCSD_HeadDir.left))
          (Sp := Sp) (t := tb) (h := q + 2)
          (by simp only [Nat.max_eq_max, q] at hlenb hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, q] at hlenb hsp ⊢; omega)
        simpa [stepHead] using hp
      obtain ⟨td, heqd, hlend, hp4⟩ :=
        ProgRuns_moveLeftPos 2 (Sp := Sp) (t := tc) (h := q + 1)
          (by simp only [Nat.max_eq_max, q] at hlenc hsp ⊢; omega)
      have hsubd : q + 1 - (2 + 1) = pos + 2 * r := by dsimp [q]; omega
      rw [hsubd] at hp4
      have htd_read : ∀ p, QCSD_tapeRead td p =
          if p = q + 2 then mVal
          else if p = q + 1 then true
          else QCSD_tapeRead t_c p := by
        intro p
        rw [heqd p]; dsimp [tc, tb, ta]
        rw [tapeRead_tapeWrite2]
        by_cases hq2 : p = q + 2
        · rw [ite_eq_left hq2, ite_eq_left hq2]
        · rw [ite_eq_right hq2, ite_eq_right hq2, tapeRead_tapeWrite2]
          by_cases hq1 : p = q + 1
          · rw [ite_eq_left hq1, ite_eq_left hq1]
          · rw [ite_eq_right hq1, ite_eq_right hq1, tapeRead_tapeWrite2]
            by_cases hq0 : p = q
            · rw [ite_eq_left hq0, hq0]; exact hc0.symm
            · rw [ite_eq_right hq0]
      obtain ⟨t_s, hw_s, hhigh_s, hlen_s, hrRest⟩ :=
        ih (by omega) td
          (by simp only [Nat.max_eq_max] at hlend hlenc ⊢; omega)
          (fun p hp => by
            rw [htd_read p, ite_eq_right (by dsimp [q]; omega),
                ite_eq_right (by dsimp [q]; omega)]
            exact hlow p (by omega))
          (fun off hoff1 hoff2 => by
            rw [htd_read ((pos + 1) + off)]
            by_cases heq3 : off = 2 * r + 3
            · subst heq3
              rw [ite_eq_left (by dsimp [q]; omega)]
            · by_cases heq2 : off = 2 * r + 2
              · subst heq2
                rw [ite_eq_right (by dsimp [q]; omega), ite_eq_left (by dsimp [q]; omega)]
                unfold winCell
                rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
              · rw [ite_eq_right (by dsimp [q]; omega), ite_eq_right (by dsimp [q]; omega)]
                exact hmid off (by omega) hoff2)
          (fun p hp => by
            rw [htd_read p, ite_eq_right (by dsimp [q]; omega),
                ite_eq_right (by dsimp [q]; omega)]
            exact hhigh p hp)
      have hbody : ProgRuns (slideShiftBody bNext) Sp 6 (t_c, q) true (td, pos + 2 * r) := by
        unfold slideShiftBody
        exact ProgRuns_bind (k := fun c₀ =>
          ifProg c₀
            (bindProg (primProg (fun m => (m, true, QCSD_HeadDir.right))) (fun m =>
              seqProg (primProg (fun _ => ((), m, QCSD_HeadDir.left)))
                (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 2))))
            (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
              (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                (seqProg (stepDirProg QCSD_HeadDir.left)
                  (seqProg (primProg (fun _ => ((), bNext, QCSD_HeadDir.right)))
                    (mapExitProg (fun _ => false) (moveDirPosProg QCSD_HeadDir.right 1)))))))
          hp1 (ProgRuns_if_true
            (pF := seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
              (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                (seqProg (stepDirProg QCSD_HeadDir.left)
                  (seqProg (primProg (fun _ => ((), bNext, QCSD_HeadDir.right)))
                    (mapExitProg (fun _ => false) (moveDirPosProg QCSD_HeadDir.right 1))))))
            (ProgRuns_bind (k := fun m =>
              seqProg (primProg (fun _ => ((), m, QCSD_HeadDir.left)))
                (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 2)))
              hp2 (ProgRuns_seq hp3 (ProgRuns_mapExit (fun _ => true) hp4))))
      exact ⟨t_s, hw_s, hhigh_s, hlen_s,
        (ProgRuns_while_true hbody hrRest).mono (Nat.le_refl Sp) (by omega)⟩
  obtain ⟨t_s, hw_s, hhigh_s, hlen_s, hrShift⟩ :=
    hshift w (Nat.le_refl w) t₁
      (by simp only [Nat.max_eq_max] at hlen₁ hlen₀ ⊢; omega)
      (fun p hp => by
        rw [heq₁ p]; dsimp [t₀]; rw [tapeRead_tapeWrite2, ite_eq_right (by omega)])
      (fun off hoff1 hoff2 => by
        have hoff_eq : off = 2 * w + 2 := by omega
        subst hoff_eq
        rw [heq₁]; dsimp [t₀]
        have hp_eq : (pos + 1) + (2 * w + 2) = pos + 2 * w + 3 := by omega
        rw [hp_eq, tapeRead_tapeWrite2, ite_eq_left rfl]
        simp [winCell])
      (fun p hp => by
        rw [heq₁ p]; dsimp [t₀]; rw [tapeRead_tapeWrite2, ite_eq_right (by omega)])
  obtain ⟨t', heq', hlen', hrEnd⟩ :=
    ProgRuns_walkWinRightEnd (Sp := Sp) hw_s (j := 0) (Nat.zero_le w)
      (by simp only [Nat.max_eq_max] at hlen_s hsp ⊢; omega)
  rw [Nat.mul_zero, Nat.add_zero] at hrEnd
  refine ⟨t', WinPrefix_of_tapeEq hw_s heq',
    fun p hp => (heq' p).trans (hhigh_s p hp),
    by simp only [Nat.max_eq_max] at hlen' hlen_s ⊢; omega, ?_⟩
  unfold slideWinRightProg slideWinRightRaw
  exact (ProgRuns_bind (k := fun bNext =>
    seqProg (moveDirPosProg QCSD_HeadDir.left 1)
      (seqProg (whileProg (slideShiftBody bNext)) walkWinRightEndProg))
    hs0 (ProgRuns_seq hs1 (ProgRuns_seq hrShift hrEnd))).mono
    (Nat.le_refl Sp) (by omega)

attribute [irreducible] SlideWinRightQ slideWinRightProg

def resetMarksBody :=
  bindProg (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) (fun c₀ =>
    ifProg c₀
      (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.left)))
        (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 1)))
      (mapExitProg (fun _ => false) (stepDirProg QCSD_HeadDir.right)))

def resetAllMarksProg :=
  seqProg (moveDirPosProg QCSD_HeadDir.left 2)
    (seqProg (whileProg resetMarksBody) walkWinRightEndProg)

lemma ProgRuns_resetAllMarks {Sp pos w k : ℕ} {leftBits t : List Bool}
    (hw : WinPrefix pos w k leftBits t)
    (hsp : Nat.max t.length (pos + 2 * w + 5) ≤ Sp) :
    ∃ t' : List Bool,
      WinPrefix pos w w leftBits t' ∧
      (∀ p, pos + 2 * w + 3 ≤ p → QCSD_tapeRead t' p = QCSD_tapeRead t p) ∧
      t'.length ≤ Nat.max t.length (pos + 2 * w + 5) ∧
      ProgRuns resetAllMarksProg Sp (8 * w + 12)
        (t, pos + 2 * w + 3) () (t', pos + 2 * w + 3) := by
  obtain ⟨t₀, heq₀, hlen₀, hs0⟩ :=
    ProgRuns_moveLeftPos 2 (Sp := Sp) (t := t) (h := pos + 2 * w + 3)
      (by simp only [Nat.max_eq_max] at hsp ⊢; omega)
  have hsub₀ : pos + 2 * w + 3 - (2 + 1) = pos + 2 * w := by omega
  rw [hsub₀] at hs0
  have hloop : ∀ (r : ℕ), r ≤ w → ∀ t_c : List Bool,
      t_c.length ≤ Nat.max t.length (pos + 2 * w + 5) →
      (∀ p < pos, QCSD_tapeRead t_c p = QCSD_tapeRead t p) →
      (∀ off < 2 * w + 3, QCSD_tapeRead t_c (pos + off) =
        if 2 * r + 2 ≤ off then winCell w w off else winCell w k off) →
      (∀ p, pos + 2 * w + 3 ≤ p → QCSD_tapeRead t_c p = QCSD_tapeRead t p) →
      ∃ t_r : List Bool,
        WinPrefix pos w w leftBits t_r ∧
        (∀ p, pos + 2 * w + 3 ≤ p → QCSD_tapeRead t_r p = QCSD_tapeRead t p) ∧
        t_r.length ≤ Nat.max t.length (pos + 2 * w + 5) ∧
        ProgRuns (whileProg resetMarksBody) Sp (4 * r + 2)
          (t_c, pos + 2 * r) () (t_r, pos + 2) := by
    intro r
    induction r with
    | zero =>
      intro _ t_c hlen hlow hwin hhigh
      rw [Nat.mul_zero, Nat.add_zero]
      have hc0 : QCSD_tapeRead t_c pos = false := by
        simpa [winCell] using hwin 0 (by omega)
      let ta := QCSD_tapeWrite2 t_c pos false
      have heqa : tapeEq ta t_c := by
        intro q; dsimp [ta]; rw [tapeRead_tapeWrite2]
        split_ifs with hq
        · rw [hq]; exact hc0.symm
        · rfl
      have hlena : ta.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen ⊢; omega
      have hp1 : ProgRuns (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) Sp 1
          (t_c, pos) false (ta, pos + 1) := by
        have hp := ProgRuns_prim (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))
          (Sp := Sp) (t := t_c) (h := pos)
          (by simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
          (by rw [hc0]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
        rw [hc0] at hp; exact hp
      obtain ⟨tb, heqb, hlenb, hp2⟩ :=
        ProgRuns_stepRight (Sp := Sp) (t := ta) (h := pos + 1)
          (by simp only [Nat.max_eq_max] at hlena hsp ⊢; omega)
      have heq_tb : tapeEq tb t_c := tapeEq_trans heqb heqa
      refine ⟨tb, ?_, fun p hp => (heq_tb p).trans (hhigh p hp),
        by simp only [Nat.max_eq_max] at hlenb hlena ⊢; omega, ?_⟩
      · refine ⟨Nat.le_refl w, hw.2.1,
          fun p hp => (heq_tb p).trans ((hlow p hp).trans (hw.2.2.1 p hp)),
          fun off hoff => ?_⟩
        rw [heq_tb (pos + off), hwin off hoff]
        by_cases h2 : 2 ≤ off
        · rw [ite_eq_left (by omega)]
        · simp [winCell, show off < 2 by omega]
      · have hexit : ProgRuns resetMarksBody Sp 2 (t_c, pos) false (tb, pos + 2) := by
          unfold resetMarksBody
          exact ProgRuns_bind (k := fun c₀ =>
            ifProg c₀
              (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.left)))
                (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 1)))
              (mapExitProg (fun _ => false) (stepDirProg QCSD_HeadDir.right)))
            hp1 (ProgRuns_if_false
              (pT := seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.left)))
                (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 1)))
              (ProgRuns_mapExit (fun _ => false) hp2))
        exact (ProgRuns_while_false hexit).mono (Nat.le_refl Sp) (by omega)
    | succ r ih =>
      intro hr_le t_c hlen hlow hwin hhigh
      let q := pos + 2 * (r + 1)
      have hc0 : QCSD_tapeRead t_c q = true := by
        have h := hwin (2 * r + 2) (by omega)
        have hq_eq : pos + (2 * r + 2) = q := by dsimp [q]; omega
        rw [hq_eq, ite_eq_right (by omega)] at h
        rw [h]; unfold winCell
        rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
      let ta := QCSD_tapeWrite2 t_c q true
      have hlena : ta.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, q] at hlen ⊢; omega
      have hp1 : ProgRuns (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) Sp 1
          (t_c, q) true (ta, q + 1) := by
        have hp := ProgRuns_prim (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))
          (Sp := Sp) (t := t_c) (h := q)
          (by simp only [Nat.max_eq_max, q] at hlen hsp ⊢; omega)
          (by rw [hc0]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, q] at hlen hsp ⊢; omega)
        rw [hc0] at hp; exact hp
      let tb := QCSD_tapeWrite2 ta (q + 1) true
      have hlenb : tb.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, q] at hlena ⊢; omega
      have hp2 : ProgRuns (primProg (fun _ => ((), true, QCSD_HeadDir.left))) Sp 1
          (ta, q + 1) () (tb, q) := by
        have hp := ProgRuns_prim (fun _ => ((), true, QCSD_HeadDir.left))
          (Sp := Sp) (t := ta) (h := q + 1)
          (by simp only [Nat.max_eq_max, q] at hlena hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, q] at hlena hsp ⊢; omega)
        simpa [stepHead] using hp
      obtain ⟨tc, heqc, hlenc, hp3⟩ :=
        ProgRuns_moveLeftPos 1 (Sp := Sp) (t := tb) (h := q)
          (by simp only [Nat.max_eq_max, q] at hlenb hsp ⊢; omega)
      have hsubc : q - (1 + 1) = pos + 2 * r := by dsimp [q]; omega
      rw [hsubc] at hp3
      have htc_read : ∀ p, QCSD_tapeRead tc p =
          if p = q + 1 then true else QCSD_tapeRead t_c p := by
        intro p
        rw [heqc p]; dsimp [tb, ta]; rw [tapeRead_tapeWrite2]
        by_cases hq1 : p = q + 1
        · rw [ite_eq_left hq1, ite_eq_left hq1]
        · rw [ite_eq_right hq1, ite_eq_right hq1, tapeRead_tapeWrite2]
          by_cases hq0 : p = q
          · rw [ite_eq_left hq0, hq0]; exact hc0.symm
          · rw [ite_eq_right hq0]
      obtain ⟨t_r, hw_r, hhigh_r, hlen_r, hrRest⟩ :=
        ih (by omega) tc
          (by simp only [Nat.max_eq_max] at hlenc hlenb ⊢; omega)
          (fun p hp => by rw [htc_read p, ite_eq_right (by dsimp [q]; omega)]; exact hlow p hp)
          (fun off hoff => by
            rw [htc_read (pos + off)]
            by_cases heq3 : off = 2 * r + 3
            · subst heq3
              rw [ite_eq_left (by dsimp [q]; omega), ite_eq_left (by omega)]
              unfold winCell
              rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
              exact (decide_eq_true (by omega)).symm
            · rw [ite_eq_right (by dsimp [q]; omega), hwin off hoff]
              by_cases heq2 : off = 2 * r + 2
              · subst heq2
                rw [ite_eq_right (by omega), ite_eq_left (by omega)]
                unfold winCell
                rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
                    ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
              · have hiff : (2 * (r + 1) + 2 ≤ off) ↔ (2 * r + 2 ≤ off) := by omega
                simp [hiff])
          (fun p hp => by rw [htc_read p, ite_eq_right (by dsimp [q]; omega)]; exact hhigh p hp)
      have hbody : ProgRuns resetMarksBody Sp 4 (t_c, q) true (tc, pos + 2 * r) := by
        unfold resetMarksBody
        exact ProgRuns_bind (k := fun c₀ =>
          ifProg c₀
            (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.left)))
              (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.left 1)))
            (mapExitProg (fun _ => false) (stepDirProg QCSD_HeadDir.right)))
          hp1 (ProgRuns_if_true
            (pF := mapExitProg (fun _ => false) (stepDirProg QCSD_HeadDir.right))
            (ProgRuns_seq hp2 (ProgRuns_mapExit (fun _ => true) hp3)))
      exact ⟨t_r, hw_r, hhigh_r, hlen_r,
        (ProgRuns_while_true hbody hrRest).mono (Nat.le_refl Sp) (by omega)⟩
  obtain ⟨t_r, hw_r, hhigh_r, hlen_r, hrLoop⟩ :=
    hloop w (Nat.le_refl w) t₀
      (by simp only [Nat.max_eq_max] at hlen₀ ⊢; omega)
      (fun p _ => heq₀ p)
      (fun off hoff => by
        rw [heq₀ (pos + off), hw.2.2.2 off hoff]
        by_cases hge : 2 * w + 2 ≤ off
        · have heq_off : off = 2 * w + 2 := by omega
          subst heq_off; simp [winCell]
        · rw [ite_eq_right hge])
      (fun p _ => heq₀ p)
  obtain ⟨t', heq', hlen', hrEnd⟩ :=
    ProgRuns_walkWinRightEnd (Sp := Sp) hw_r (j := 0) (Nat.zero_le w)
      (by simp only [Nat.max_eq_max] at hlen_r hsp ⊢; omega)
  rw [Nat.mul_zero, Nat.add_zero] at hrEnd
  refine ⟨t', WinPrefix_of_tapeEq hw_r heq',
    fun p hp => (heq' p).trans (hhigh_r p hp),
    by simp only [Nat.max_eq_max] at hlen' hlen_r ⊢; omega, ?_⟩
  unfold resetAllMarksProg
  exact (ProgRuns_seq hs0 (ProgRuns_seq hrLoop hrEnd)).mono (Nat.le_refl Sp) (by omega)

def consumeMarksBody :=
  bindProg (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) (fun c₀ =>
    ifProg c₀
      (bindProg (primProg (fun m => (m, false, QCSD_HeadDir.right))) (fun m =>
        ifProg m
          (mapExitProg (fun _ => (Sum.inr true : Unit ⊕ Bool)) nopProg)
          (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool))
            (moveDirPosProg QCSD_HeadDir.left 3))))
      (seqProg (stepDirProg QCSD_HeadDir.right)
        (mapExitProg (fun _ => (Sum.inr false : Unit ⊕ Bool)) nopProg)))

def consumeOneMarkRaw :=
  seqProg (moveDirPosProg QCSD_HeadDir.left 2)
    (bindProg (loopStateProg () (fun _ => consumeMarksBody)) (fun ok =>
      mapExitProg (fun _ => ok) walkWinRightEndProg))

def ConsumeOneMarkQ : Type := ProgState consumeOneMarkRaw
instance : Fintype ConsumeOneMarkQ := by
  unfold ConsumeOneMarkQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance : DecidableEq ConsumeOneMarkQ := by
  unfold ConsumeOneMarkQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def consumeOneMarkProg : Prog ConsumeOneMarkQ Bool := consumeOneMarkRaw

lemma ProgRuns_consumeOneMark {Sp pos w k : ℕ} {leftBits t : List Bool}
    (hw : WinPrefix pos w k leftBits t)
    (hsp : Nat.max t.length (pos + 2 * w + 5) ≤ Sp) :
    ∃ t' : List Bool,
      WinPrefix pos w (k - 1) leftBits t' ∧
      (∀ p, pos + 2 * w + 3 ≤ p → QCSD_tapeRead t' p = QCSD_tapeRead t p) ∧
      t'.length ≤ Nat.max t.length (pos + 2 * w + 5) ∧
      ProgRuns consumeOneMarkProg Sp (10 * w + 16)
        (t, pos + 2 * w + 3) (decide (0 < k)) (t', pos + 2 * w + 3) := by
  have hk_le : k ≤ w := hw.1
  obtain ⟨t₀, heq₀, hlen₀, hs0⟩ :=
    ProgRuns_moveLeftPos 2 (Sp := Sp) (t := t) (h := pos + 2 * w + 3)
      (by simp only [Nat.max_eq_max] at hsp ⊢; omega)
  have hsub₀ : pos + 2 * w + 3 - (2 + 1) = pos + 2 * w := by omega
  rw [hsub₀] at hs0
  have hskip : ∀ (rem : ℕ), k + rem ≤ w → ∀ t_c : List Bool,
      tapeEq t_c t →
      t_c.length ≤ Nat.max t.length (pos + 2 * w + 5) →
      ∃ t_k : List Bool,
        WinPrefix pos w (k - 1) leftBits t_k ∧
        (∀ p, pos + 2 * w + 3 ≤ p → QCSD_tapeRead t_k p = QCSD_tapeRead t p) ∧
        t_k.length ≤ Nat.max t.length (pos + 2 * w + 5) ∧
        ProgRuns (loopStateProg () (fun _ => consumeMarksBody)) Sp (6 * rem + 5)
          (t_c, pos + 2 * (k + rem)) (decide (0 < k)) (t_k, pos + 2 + 2 * k) := by
    intro rem
    induction rem with
    | zero =>
      intro _ t_c heq hlen
      rw [Nat.add_zero]
      cases k with
      | zero =>
        rw [Nat.mul_zero, Nat.add_zero]
        have hc0 : QCSD_tapeRead t_c pos = false := by
          rw [heq pos]; simpa [winCell] using hw.2.2.2 0 (by omega)
        let ta := QCSD_tapeWrite2 t_c pos false
        have heqa : tapeEq ta t := by
          intro q; dsimp [ta]; rw [tapeRead_tapeWrite2]
          split_ifs with hq
          · rw [hq, ← heq pos]; exact hc0.symm
          · exact heq q
        have hlena : ta.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
          rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen ⊢; omega
        have hp1 : ProgRuns (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) Sp 1
            (t_c, pos) false (ta, pos + 1) := by
          have hp := ProgRuns_prim (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))
            (Sp := Sp) (t := t_c) (h := pos)
            (by simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
            (by rw [hc0]; dsimp [stepHead]; rw [tapeWrite2_length]
                simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
          rw [hc0] at hp; exact hp
        obtain ⟨tb, heqb, hlenb, hp2⟩ :=
          ProgRuns_stepRight (Sp := Sp) (t := ta) (h := pos + 1)
            (by simp only [Nat.max_eq_max] at hlena hsp ⊢; omega)
        obtain ⟨tc, heqc, hlenc, hp3⟩ :=
          ProgRuns_nop (Sp := Sp) (t := tb) (h := pos + 2)
            (by simp only [Nat.max_eq_max] at hlenb hlena hsp ⊢; omega)
        have heq_tc : tapeEq tc t := tapeEq_trans heqc (tapeEq_trans heqb heqa)
        refine ⟨tc, WinPrefix_of_tapeEq hw heq_tc,
          fun p _ => heq_tc p,
          by simp only [Nat.max_eq_max] at hlenc hlenb hlena ⊢; omega, ?_⟩
        have hexit : ProgRuns consumeMarksBody Sp 4
            (t_c, pos) (Sum.inr false : Unit ⊕ Bool) (tc, pos + 2) := by
          unfold consumeMarksBody
          exact ProgRuns_bind (k := fun c₀ =>
            ifProg c₀
              (bindProg (primProg (fun m => (m, false, QCSD_HeadDir.right))) (fun m =>
                ifProg m
                  (mapExitProg (fun _ => (Sum.inr true : Unit ⊕ Bool)) nopProg)
                  (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool))
                    (moveDirPosProg QCSD_HeadDir.left 3))))
              (seqProg (stepDirProg QCSD_HeadDir.right)
                (mapExitProg (fun _ => (Sum.inr false : Unit ⊕ Bool)) nopProg)))
            hp1 (ProgRuns_if_false
              (pT := bindProg (primProg (fun m => (m, false, QCSD_HeadDir.right))) (fun m =>
                ifProg m
                  (mapExitProg (fun _ => (Sum.inr true : Unit ⊕ Bool)) nopProg)
                  (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool))
                    (moveDirPosProg QCSD_HeadDir.left 3))))
              (ProgRuns_seq hp2 (ProgRuns_mapExit (fun _ => (Sum.inr false : Unit ⊕ Bool)) hp3)))
        exact (ProgRuns_loopState_exit hexit).mono (Nat.le_refl Sp) (by omega)
      | succ k₀ =>
        let q := pos + 2 * (k₀ + 1)
        have hq_eq : q = pos + (2 * k₀ + 2) := by dsimp [q]; omega
        have hc0 : QCSD_tapeRead t_c q = true := by
          rw [heq q, hq_eq, hw.2.2.2 (2 * k₀ + 2) (by omega)]
          unfold winCell
          rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
        let ta := QCSD_tapeWrite2 t_c q true
        have heqa : tapeEq ta t := by
          intro p; dsimp [ta]; rw [tapeRead_tapeWrite2]
          split_ifs with hp
          · rw [hp, ← heq q]; exact hc0.symm
          · exact heq p
        have hlena : ta.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
          rw [tapeWrite2_length]; simp only [Nat.max_eq_max, q] at hlen ⊢; omega
        have hp1 : ProgRuns (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) Sp 1
            (t_c, q) true (ta, q + 1) := by
          have hp := ProgRuns_prim (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))
            (Sp := Sp) (t := t_c) (h := q)
            (by simp only [Nat.max_eq_max, q] at hlen hsp ⊢; omega)
            (by rw [hc0]; dsimp [stepHead]; rw [tapeWrite2_length]
                simp only [Nat.max_eq_max, q] at hlen hsp ⊢; omega)
          rw [hc0] at hp; exact hp
        have hm1 : QCSD_tapeRead ta (q + 1) = true := by
          rw [heqa (q + 1)]
          have hq1 : q + 1 = pos + (2 * k₀ + 3) := by dsimp [q]; omega
          rw [hq1, hw.2.2.2 (2 * k₀ + 3) (by omega)]
          unfold winCell
          rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
          exact decide_eq_true (by omega)
        let tb := QCSD_tapeWrite2 ta (q + 1) false
        have hlenb : tb.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
          rw [tapeWrite2_length]; simp only [Nat.max_eq_max, q] at hlena ⊢; omega
        have hp2 : ProgRuns (primProg (fun m => (m, false, QCSD_HeadDir.right))) Sp 1
            (ta, q + 1) true (tb, pos + 2 + 2 * (k₀ + 1)) := by
          have hp := ProgRuns_prim (fun m => (m, false, QCSD_HeadDir.right))
            (Sp := Sp) (t := ta) (h := q + 1)
            (by simp only [Nat.max_eq_max, q] at hlena hsp ⊢; omega)
            (by rw [hm1]; dsimp [stepHead]; rw [tapeWrite2_length]
                simp only [Nat.max_eq_max, q] at hlena hsp ⊢; omega)
          rw [hm1] at hp
          have hq2 : stepHead (q + 1) QCSD_HeadDir.right = pos + 2 + 2 * (k₀ + 1) := by
            dsimp [stepHead, q]; omega
          rw [hq2] at hp; exact hp
        obtain ⟨tc, heqc, hlenc, hp3⟩ :=
          ProgRuns_nop (Sp := Sp) (t := tb) (h := pos + 2 + 2 * (k₀ + 1))
            (by simp only [Nat.max_eq_max] at hlenb hsp ⊢; omega)
        refine ⟨tc, ?_, ?_, by simp only [Nat.max_eq_max] at hlenc hlenb ⊢; omega, ?_⟩
        · refine ⟨by omega, hw.2.1, fun p hp => ?_, fun off hoff => ?_⟩
          · rw [heqc p]; dsimp [tb]
            rw [tapeRead_tapeWrite2, ite_eq_right (by dsimp [q]; omega), heqa p]
            exact hw.2.2.1 p hp
          · rw [heqc (pos + off)]; dsimp [tb]
            rw [tapeRead_tapeWrite2]
            by_cases heq_off : off = 2 * k₀ + 3
            · subst heq_off
              rw [ite_eq_left (by dsimp [q]; omega)]
              unfold winCell
              rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
              exact (decide_eq_false (by omega)).symm
            · rw [ite_eq_right (by dsimp [q]; omega), heqa (pos + off), hw.2.2.2 off hoff]
              unfold winCell
              by_cases h2 : off < 2
              · simp [h2]
              · rw [ite_eq_right h2, ite_eq_right h2]
                by_cases hlt_w : off < 2 * w + 2
                · rw [ite_eq_left hlt_w, ite_eq_left hlt_w]
                  by_cases hev : off % 2 = 0
                  · rw [ite_eq_left hev, ite_eq_left hev]
                  · rw [ite_eq_right hev, ite_eq_right hev]
                    have hiff : ((off - 2) / 2 < k₀ + 1) ↔ ((off - 2) / 2 < k₀) := by omega
                    simp [hiff]
                · rw [ite_eq_right hlt_w, ite_eq_right hlt_w]
        · intro p hp
          rw [heqc p]; dsimp [tb]
          rw [tapeRead_tapeWrite2, ite_eq_right (by dsimp [q]; omega)]
          exact heqa p
        · have hdec : decide (0 < k₀ + 1) = true := decide_eq_true (Nat.zero_lt_succ k₀)
          rw [hdec]
          have hexit : ProgRuns consumeMarksBody Sp 4
              (t_c, q) (Sum.inr true : Unit ⊕ Bool) (tc, pos + 2 + 2 * (k₀ + 1)) := by
            unfold consumeMarksBody
            exact ProgRuns_bind (k := fun c₀ =>
              ifProg c₀
                (bindProg (primProg (fun m => (m, false, QCSD_HeadDir.right))) (fun m =>
                  ifProg m
                    (mapExitProg (fun _ => (Sum.inr true : Unit ⊕ Bool)) nopProg)
                    (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool))
                      (moveDirPosProg QCSD_HeadDir.left 3))))
                (seqProg (stepDirProg QCSD_HeadDir.right)
                  (mapExitProg (fun _ => (Sum.inr false : Unit ⊕ Bool)) nopProg)))
              hp1 (ProgRuns_if_true
                (pF := seqProg (stepDirProg QCSD_HeadDir.right)
                  (mapExitProg (fun _ => (Sum.inr false : Unit ⊕ Bool)) nopProg))
                (ProgRuns_bind (k := fun m =>
                  ifProg m
                    (mapExitProg (fun _ => (Sum.inr true : Unit ⊕ Bool)) nopProg)
                    (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool))
                      (moveDirPosProg QCSD_HeadDir.left 3)))
                  hp2 (ProgRuns_if_true
                    (pF := mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool))
                      (moveDirPosProg QCSD_HeadDir.left 3))
                    (ProgRuns_mapExit (fun _ => (Sum.inr true : Unit ⊕ Bool)) hp3))))
          exact (ProgRuns_loopState_exit hexit).mono (Nat.le_refl Sp) (by omega)
    | succ rem ih =>
      intro hrem_le t_c heq hlen
      let r := k + rem
      let q := pos + 2 * (r + 1)
      have hq_eq : q = pos + (2 * r + 2) := by dsimp [q]; omega
      have hc0 : QCSD_tapeRead t_c q = true := by
        rw [heq q, hq_eq, hw.2.2.2 (2 * r + 2) (by dsimp [r]; omega)]
        unfold winCell
        rw [ite_eq_right (by omega), ite_eq_left (by dsimp [r]; omega), ite_eq_left (by omega)]
      let ta := QCSD_tapeWrite2 t_c q true
      have heqa : tapeEq ta t := by
        intro p; dsimp [ta]; rw [tapeRead_tapeWrite2]
        split_ifs with hp
        · rw [hp, ← heq q]; exact hc0.symm
        · exact heq p
      have hlena : ta.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, q, r] at hlen ⊢; omega
      have hp1 : ProgRuns (primProg (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))) Sp 1
          (t_c, q) true (ta, q + 1) := by
        have hp := ProgRuns_prim (fun c₀ => (c₀, c₀, QCSD_HeadDir.right))
          (Sp := Sp) (t := t_c) (h := q)
          (by simp only [Nat.max_eq_max, q, r] at hlen hsp ⊢; omega)
          (by rw [hc0]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, q, r] at hlen hsp ⊢; omega)
        rw [hc0] at hp; exact hp
      have hm0 : QCSD_tapeRead ta (q + 1) = false := by
        rw [heqa (q + 1)]
        have hq1 : q + 1 = pos + (2 * r + 3) := by dsimp [q]; omega
        rw [hq1, hw.2.2.2 (2 * r + 3) (by dsimp [r]; omega)]
        unfold winCell
        rw [ite_eq_right (by omega), ite_eq_left (by dsimp [r]; omega), ite_eq_right (by omega)]
        exact decide_eq_false (by dsimp [r]; omega)
      let tb := QCSD_tapeWrite2 ta (q + 1) false
      have heqb : tapeEq tb t := by
        intro p; dsimp [tb]; rw [tapeRead_tapeWrite2]
        split_ifs with hp
        · rw [hp, ← heqa (q + 1)]; exact hm0.symm
        · exact heqa p
      have hlenb : tb.length ≤ Nat.max t.length (pos + 2 * w + 5) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, q, r] at hlena ⊢; omega
      have hp2 : ProgRuns (primProg (fun m => (m, false, QCSD_HeadDir.right))) Sp 1
          (ta, q + 1) false (tb, q + 2) := by
        have hp := ProgRuns_prim (fun m => (m, false, QCSD_HeadDir.right))
          (Sp := Sp) (t := ta) (h := q + 1)
          (by simp only [Nat.max_eq_max, q, r] at hlena hsp ⊢; omega)
          (by rw [hm0]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, q, r] at hlena hsp ⊢; omega)
        rw [hm0] at hp; exact hp
      obtain ⟨tc, heqc, hlenc, hp3⟩ :=
        ProgRuns_moveLeftPos 3 (Sp := Sp) (t := tb) (h := q + 2)
          (by simp only [Nat.max_eq_max, q, r] at hlenb hsp ⊢; omega)
      have hsubc : q + 2 - (3 + 1) = pos + 2 * r := by dsimp [q]; omega
      rw [hsubc] at hp3
      obtain ⟨t_k, hw_k, hhigh_k, hlen_k, hrRest⟩ :=
        ih (by omega) tc (tapeEq_trans heqc heqb)
          (by simp only [Nat.max_eq_max, q, r] at hlenc hlenb ⊢; omega)
      have hbody : ProgRuns consumeMarksBody Sp 6
          (t_c, pos + 2 * (k + (rem + 1))) (Sum.inl () : Unit ⊕ Bool) (tc, pos + 2 * (k + rem)) := by
        unfold consumeMarksBody
        exact ProgRuns_bind (k := fun c₀ =>
          ifProg c₀
            (bindProg (primProg (fun m => (m, false, QCSD_HeadDir.right))) (fun m =>
              ifProg m
                (mapExitProg (fun _ => (Sum.inr true : Unit ⊕ Bool)) nopProg)
                (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool))
                  (moveDirPosProg QCSD_HeadDir.left 3))))
            (seqProg (stepDirProg QCSD_HeadDir.right)
              (mapExitProg (fun _ => (Sum.inr false : Unit ⊕ Bool)) nopProg)))
          hp1 (ProgRuns_if_true
            (pF := seqProg (stepDirProg QCSD_HeadDir.right)
              (mapExitProg (fun _ => (Sum.inr false : Unit ⊕ Bool)) nopProg))
            (ProgRuns_bind (k := fun m =>
              ifProg m
                (mapExitProg (fun _ => (Sum.inr true : Unit ⊕ Bool)) nopProg)
                (mapExitProg (fun _ => (Sum.inl () : Unit ⊕ Bool))
                  (moveDirPosProg QCSD_HeadDir.left 3)))
              hp2 (ProgRuns_if_false
                (pT := mapExitProg (fun _ => (Sum.inr true : Unit ⊕ Bool)) nopProg)
                (ProgRuns_mapExit (fun _ => (Sum.inl () : Unit ⊕ Bool)) hp3))))
      exact ⟨t_k, hw_k, hhigh_k, hlen_k,
        (ProgRuns_loopState_cont hbody hrRest).mono (Nat.le_refl Sp) (by omega)⟩
  have hkw : k + (w - k) = w := by omega
  obtain ⟨t_k, hw_k, hhigh_k, hlen_k, hrLoop⟩ :=
    hskip (w - k) (by omega) t₀ heq₀
      (by simp only [Nat.max_eq_max] at hlen₀ ⊢; omega)
  rw [hkw] at hrLoop
  obtain ⟨t', heq', hlen', hrEnd⟩ :=
    ProgRuns_walkWinRightEnd (Sp := Sp) hw_k (j := k) hk_le
      (by simp only [Nat.max_eq_max] at hlen_k hsp ⊢; omega)
  refine ⟨t', WinPrefix_of_tapeEq hw_k heq',
    fun p hp => (heq' p).trans (hhigh_k p hp),
    by simp only [Nat.max_eq_max] at hlen' hlen_k ⊢; omega, ?_⟩
  unfold consumeOneMarkProg consumeOneMarkRaw
  exact (ProgRuns_seq hs0
    (ProgRuns_bind (k := fun ok => mapExitProg (fun _ => ok) walkWinRightEndProg)
      hrLoop (ProgRuns_mapExit (fun _ => decide (0 < k)) hrEnd))).mono
    (Nat.le_refl Sp) (by omega)

attribute [irreducible] ConsumeOneMarkQ consumeOneMarkProg

def popRawBitLeftRaw :=
  seqProg (stepDirProg QCSD_HeadDir.left)
    (seqProg (whileProg (primProg (emitPhysScanStep false)))
      (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.left)))
        (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.left)))
          (bindProg (primProg (fun r₁ => (r₁, r₁, QCSD_HeadDir.right))) (fun r₁ =>
            ifProg r₁
              (seqProg (stepDirProg QCSD_HeadDir.right)
                (bindProg (primProg (fun r₂ => (r₂, false, QCSD_HeadDir.left))) (fun r₂ =>
                  ifProg r₂
                    (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                      (mapExitProg (fun _ => (true, true)) walkRightToTrueProg))
                    (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                      (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                        (mapExitProg (fun _ => (false, false)) walkRightToTrueProg))))))
              (seqProg (stepDirProg QCSD_HeadDir.right)
                (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                  (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                    (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.right)))
                      (mapExitProg (fun _ => (true, false)) walkRightToTrueProg))))))))))

def PopRawBitQ : Type := ProgState popRawBitLeftRaw
instance : Fintype PopRawBitQ := by
  unfold PopRawBitQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance : DecidableEq PopRawBitQ := by
  unfold PopRawBitQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def popRawBitLeftProg : Prog PopRawBitQ (Bool × Bool) := popRawBitLeftRaw

lemma ProgRuns_popRawBitLeft {Sp pos base : ℕ} {t : List Bool}
    (hpos2 : pos + 2 < base)
    (hpos_true : QCSD_tapeRead t pos = true)
    (hmid : ∀ p, pos < p → p < base → QCSD_tapeRead t p = false)
    (hbase_true : QCSD_tapeRead t base = true)
    (hsp : Nat.max t.length (base + 2) ≤ Sp) :
    let outPair : Bool × Bool :=
      if pos = 0 then (false, false) else (true, QCSD_tapeRead t (pos - 1))
    ∃ t' : List Bool,
      (∀ p, QCSD_tapeRead t' p =
        if pos = 0 then
          (if p < base then false else QCSD_tapeRead t p)
        else
          (if p = pos - 1 then true
           else if pos ≤ p ∧ p < base then false
           else QCSD_tapeRead t p)) ∧
      t'.length ≤ Nat.max t.length (base + 1) ∧
      ProgRuns popRawBitLeftProg Sp (2 * base + 12) (t, base) outPair (t', base) := by
  obtain ⟨t₀, heq₀, hlen₀, hrLeft⟩ :=
    ProgRuns_stepLeft (Sp := Sp) (t := t) (h := base)
      (by simp only [Nat.max_eq_max] at hsp ⊢; omega)
  have hscan : ∀ (rem : ℕ), pos + rem < base → ∀ t_c : List Bool,
      tapeEq t_c t →
      t_c.length ≤ Nat.max t.length (base + 1) →
      ∃ t_s : List Bool,
        (∀ p, QCSD_tapeRead t_s p = if p = pos then false else QCSD_tapeRead t p) ∧
        t_s.length ≤ Nat.max t.length (base + 1) ∧
        ProgRuns (whileProg (primProg (emitPhysScanStep false))) Sp (rem + 1)
          (t_c, pos + rem) () (t_s, pos + 1) := by
    intro rem
    induction rem with
    | zero =>
      intro _ t_c heq hlen
      rw [Nat.add_zero]
      have hread : QCSD_tapeRead t_c pos = true := (heq pos).trans hpos_true
      let t_s := QCSD_tapeWrite2 t_c pos false
      have hlen_s : t_s.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen ⊢; omega
      refine ⟨t_s, fun p => ?_, hlen_s, ?_⟩
      · dsimp [t_s]; rw [tapeRead_tapeWrite2]
        split_ifs with hp
        · rfl
        · exact heq p
      · apply ProgRuns_while_false
        have hp := ProgRuns_prim (emitPhysScanStep false) (Sp := Sp) (t := t_c) (h := pos)
          (by simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
          (by rw [hread]; dsimp [emitPhysScanStep, stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlen hsp ⊢; omega)
        rw [hread] at hp; exact hp
    | succ rem ih =>
      intro hlt t_c heq hlen
      let cur := pos + (rem + 1)
      have hread : QCSD_tapeRead t_c cur = false :=
        (heq cur).trans (hmid cur (by dsimp [cur]; omega) hlt)
      let t₁ := QCSD_tapeWrite2 t_c cur false
      have heq₁ : tapeEq t₁ t := by
        intro p; dsimp [t₁]; rw [tapeRead_tapeWrite2]
        split_ifs with hp
        · rw [hp]; exact (hmid cur (by dsimp [cur]; omega) hlt).symm
        · exact heq p
      have hlen₁ : t₁.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, cur] at hlen ⊢; omega
      have hstep : ProgRuns (primProg (emitPhysScanStep false)) Sp 1 (t_c, cur) true (t₁, pos + rem) := by
        have hp := ProgRuns_prim (emitPhysScanStep false) (Sp := Sp) (t := t_c) (h := cur)
          (by simp only [Nat.max_eq_max, cur] at hlen hsp ⊢; omega)
          (by rw [hread]; dsimp [emitPhysScanStep, stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, cur] at hlen hsp ⊢; omega)
        rw [hread] at hp
        simpa [emitPhysScanStep, stepHead, cur] using hp
      obtain ⟨t_s, hs_read, hs_len, hrRest⟩ := ih (by omega) t₁ heq₁ hlen₁
      exact ⟨t_s, hs_read, hs_len,
        (ProgRuns_while_true hstep hrRest).mono (Nat.le_refl Sp) (by omega)⟩
  have hrem_eq : pos + (base - 1 - pos) = base - 1 := by omega
  obtain ⟨t_s, hs_read, hs_len, hrScan⟩ :=
    hscan (base - 1 - pos) (by omega) t₀ heq₀
      (by simp only [Nat.max_eq_max] at hlen₀ ⊢; omega)
  rw [hrem_eq] at hrScan
  let ta := QCSD_tapeWrite2 t_s (pos + 1) true
  have hlena : ta.length ≤ Nat.max t.length (base + 1) := by
    rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hs_len ⊢; omega
  have hp1 : ProgRuns (primProg (fun _ => ((), true, QCSD_HeadDir.left))) Sp 1
      (t_s, pos + 1) () (ta, pos) := by
    have hp := ProgRuns_prim (fun _ => ((), true, QCSD_HeadDir.left))
      (Sp := Sp) (t := t_s) (h := pos + 1)
      (by simp only [Nat.max_eq_max] at hs_len hsp ⊢; omega)
      (by dsimp [stepHead]; rw [tapeWrite2_length]
          simp only [Nat.max_eq_max] at hs_len hsp ⊢; omega)
    simpa [stepHead] using hp
  let tb := QCSD_tapeWrite2 ta pos true
  have hlenb : tb.length ≤ Nat.max t.length (base + 1) := by
    rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlena ⊢; omega
  have hp2 : ProgRuns (primProg (fun _ => ((), true, QCSD_HeadDir.left))) Sp 1
      (ta, pos) () (tb, pos - 1) := by
    have hp := ProgRuns_prim (fun _ => ((), true, QCSD_HeadDir.left))
      (Sp := Sp) (t := ta) (h := pos)
      (by simp only [Nat.max_eq_max] at hlena hsp ⊢; omega)
      (by dsimp [stepHead]; rw [tapeWrite2_length]
          simp only [Nat.max_eq_max] at hlena hsp ⊢; omega)
    simpa [stepHead] using hp
  have htb_read : ∀ p, QCSD_tapeRead tb p =
      if p = pos ∨ p = pos + 1 then true else QCSD_tapeRead t p := by
    intro p; dsimp [tb, ta]; rw [tapeRead_tapeWrite2]
    by_cases hp0 : p = pos
    · rw [ite_eq_left hp0, ite_eq_left (Or.inl hp0)]
    · rw [ite_eq_right hp0, tapeRead_tapeWrite2]
      by_cases hp1' : p = pos + 1
      · rw [ite_eq_left hp1', ite_eq_left (Or.inr hp1')]
      · rw [ite_eq_right hp1', ite_eq_right (fun h => h.elim hp0 hp1'),
            hs_read p, ite_eq_right hp0]
  cases pos with
  | zero =>
    have hr1_t : QCSD_tapeRead tb 0 = true := by rw [htb_read 0]; simp
    let tc := QCSD_tapeWrite2 tb 0 true
    have hlenc : tc.length ≤ Nat.max t.length (base + 1) := by
      rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlenb ⊢; omega
    have hp3 : ProgRuns (primProg (fun r₁ => (r₁, r₁, QCSD_HeadDir.right))) Sp 1
        (tb, 0) true (tc, 1) := by
      have hp := ProgRuns_prim (fun r₁ => (r₁, r₁, QCSD_HeadDir.right))
        (Sp := Sp) (t := tb) (h := 0)
        (by simp only [Nat.max_eq_max] at hlenb hsp ⊢; omega)
        (by rw [hr1_t]; dsimp [stepHead]; rw [tapeWrite2_length]
            simp only [Nat.max_eq_max] at hlenb hsp ⊢; omega)
      rw [hr1_t] at hp; exact hp
    obtain ⟨td, heqd, hlend, hp4⟩ :=
      ProgRuns_stepRight (Sp := Sp) (t := tc) (h := 1)
        (by simp only [Nat.max_eq_max] at hlenc hsp ⊢; omega)
    have hr2_f : QCSD_tapeRead td 2 = false := by
      rw [heqd 2]; dsimp [tc]; rw [tapeRead_tapeWrite2, ite_eq_right (by omega),
        htb_read 2, ite_eq_right (by omega)]
      exact hmid 2 (by omega) hpos2
    let te := QCSD_tapeWrite2 td 2 false
    have hlene : te.length ≤ Nat.max t.length (base + 1) := by
      rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlend hlenc ⊢; omega
    have hp5 : ProgRuns (primProg (fun r₂ => (r₂, false, QCSD_HeadDir.left))) Sp 1
        (td, 2) false (te, 1) := by
      have hp := ProgRuns_prim (fun r₂ => (r₂, false, QCSD_HeadDir.left))
        (Sp := Sp) (t := td) (h := 2)
        (by simp only [Nat.max_eq_max] at hlend hlenc hsp ⊢; omega)
        (by rw [hr2_f]; dsimp [stepHead]; rw [tapeWrite2_length]
            simp only [Nat.max_eq_max] at hlend hlenc hsp ⊢; omega)
      rw [hr2_f] at hp; exact hp
    let tf := QCSD_tapeWrite2 te 1 false
    have hlenf : tf.length ≤ Nat.max t.length (base + 1) := by
      rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlene ⊢; omega
    have hp6 : ProgRuns (primProg (fun _ => ((), false, QCSD_HeadDir.left))) Sp 1
        (te, 1) () (tf, 0) :=
      ProgRuns_prim (fun _ => ((), false, QCSD_HeadDir.left))
        (Sp := Sp) (t := te) (h := 1)
        (by simp only [Nat.max_eq_max] at hlene hsp ⊢; omega)
        (by dsimp [stepHead]; rw [tapeWrite2_length]
            simp only [Nat.max_eq_max] at hlene hsp ⊢; omega)
    let tg := QCSD_tapeWrite2 tf 0 false
    have hleng : tg.length ≤ Nat.max t.length (base + 1) := by
      rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlenf ⊢; omega
    have hp7 : ProgRuns (primProg (fun _ => ((), false, QCSD_HeadDir.right))) Sp 1
        (tf, 0) () (tg, 1) :=
      ProgRuns_prim (fun _ => ((), false, QCSD_HeadDir.right))
        (Sp := Sp) (t := tf) (h := 0)
        (by simp only [Nat.max_eq_max] at hlenf hsp ⊢; omega)
        (by dsimp [stepHead]; rw [tapeWrite2_length]
            simp only [Nat.max_eq_max] at hlenf hsp ⊢; omega)
    have htg_read : ∀ p, QCSD_tapeRead tg p = if p < base then false else QCSD_tapeRead t p := by
      intro p
      dsimp [tg, tf, te]; rw [tapeRead_tapeWrite2]
      by_cases h0 : p = 0
      · rw [ite_eq_left h0, ite_eq_left (by omega)]
      · rw [ite_eq_right h0, tapeRead_tapeWrite2]
        by_cases h1 : p = 1
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
        · rw [ite_eq_right h1, tapeRead_tapeWrite2]
          by_cases h2 : p = 2
          · rw [ite_eq_left h2, ite_eq_left (by omega)]
          · rw [ite_eq_right h2, heqd p]; dsimp [tc]
            rw [tapeRead_tapeWrite2, ite_eq_right h0, htb_read p,
                ite_eq_right (fun h => h.elim h0 h1)]
            by_cases hlt : p < base
            · rw [ite_eq_left hlt]; exact hmid p (by omega) hlt
            · rw [ite_eq_right hlt]
    obtain ⟨t', heq', hlen', hrWalk⟩ :=
      ProgRuns_walkRightToTrue (Sp := Sp) (pos := 1) (target := base) (t := tg)
        (by omega) (by omega)
        (fun p _ hpb => by rw [htg_read p, ite_eq_left hpb])
        (by rw [htg_read base, ite_eq_right (Nat.lt_irrefl base)]; exact hbase_true)
        (by simp only [Nat.max_eq_max] at hleng hsp ⊢; omega)
    refine ⟨t', fun p => by simpa using (heq' p).trans (htg_read p),
      by simp only [Nat.max_eq_max] at hlen' hleng ⊢; omega, ?_⟩
    unfold popRawBitLeftProg popRawBitLeftRaw
    exact (ProgRuns_seq hrLeft (ProgRuns_seq hrScan (ProgRuns_seq hp1 (ProgRuns_seq hp2
      (ProgRuns_bind (k := fun r₁ =>
        ifProg r₁
          (seqProg (stepDirProg QCSD_HeadDir.right)
            (bindProg (primProg (fun r₂ => (r₂, false, QCSD_HeadDir.left))) (fun r₂ =>
              ifProg r₂
                (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                  (mapExitProg (fun _ => (true, true)) walkRightToTrueProg))
                (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                  (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                    (mapExitProg (fun _ => (false, false)) walkRightToTrueProg))))))
          (seqProg (stepDirProg QCSD_HeadDir.right)
            (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
              (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.right)))
                  (mapExitProg (fun _ => (true, false)) walkRightToTrueProg))))))
        hp3 (ProgRuns_if_true
          (pF := seqProg (stepDirProg QCSD_HeadDir.right)
            (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
              (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.right)))
                  (mapExitProg (fun _ => (true, false)) walkRightToTrueProg)))))
          (ProgRuns_seq hp4
            (ProgRuns_bind (k := fun r₂ =>
              ifProg r₂
                (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                  (mapExitProg (fun _ => (true, true)) walkRightToTrueProg))
                (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                  (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                    (mapExitProg (fun _ => (false, false)) walkRightToTrueProg))))
              hp5 (ProgRuns_if_false
                (pT := seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                  (mapExitProg (fun _ => (true, true)) walkRightToTrueProg))
                (ProgRuns_seq hp6 (ProgRuns_seq hp7
                  (ProgRuns_mapExit (fun _ => (false, false)) hrWalk)))))))))))).mono
      (Nat.le_refl Sp) (by omega)
  | succ m =>
    have hm_sub : m + 1 - 1 = m := by omega
    rw [hm_sub] at hp2
    let bPrev := QCSD_tapeRead t m
    have hr1_eq : QCSD_tapeRead tb m = bPrev := by
      rw [htb_read m, ite_eq_right (by omega)]
    let tc := QCSD_tapeWrite2 tb m bPrev
    have hlenc : tc.length ≤ Nat.max t.length (base + 1) := by
      rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlenb ⊢; omega
    have hp3 : ProgRuns (primProg (fun r₁ => (r₁, r₁, QCSD_HeadDir.right))) Sp 1
        (tb, m) bPrev (tc, m + 1) := by
      have hp := ProgRuns_prim (fun r₁ => (r₁, r₁, QCSD_HeadDir.right))
        (Sp := Sp) (t := tb) (h := m)
        (by simp only [Nat.max_eq_max] at hlenb hsp ⊢; omega)
        (by rw [hr1_eq]; dsimp [stepHead]; rw [tapeWrite2_length]
            simp only [Nat.max_eq_max] at hlenb hsp ⊢; omega)
      rw [hr1_eq] at hp; exact hp
    have heq_tc : tapeEq tc tb := by
      intro p; dsimp [tc]; rw [tapeRead_tapeWrite2]
      split_ifs with hp
      · rw [hp]; exact hr1_eq.symm
      · rfl
    cases hbP : bPrev with
    | false =>
      rw [hbP] at hp3
      obtain ⟨td, heqd, hlend, hp4⟩ :=
        ProgRuns_stepRight (Sp := Sp) (t := tc) (h := m + 1)
          (by simp only [Nat.max_eq_max] at hlenc hsp ⊢; omega)
      let te := QCSD_tapeWrite2 td (m + 2) false
      have hlene : te.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlend hlenc ⊢; omega
      have hp5 : ProgRuns (primProg (fun _ => ((), false, QCSD_HeadDir.left))) Sp 1
          (td, m + 2) () (te, m + 1) := by
        have hp := ProgRuns_prim (fun _ => ((), false, QCSD_HeadDir.left))
          (Sp := Sp) (t := td) (h := m + 2)
          (by simp only [Nat.max_eq_max] at hlend hlenc hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlend hlenc hsp ⊢; omega)
        simpa [stepHead] using hp
      let tf := QCSD_tapeWrite2 te (m + 1) false
      have hlenf : tf.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlene ⊢; omega
      have hp6 : ProgRuns (primProg (fun _ => ((), false, QCSD_HeadDir.left))) Sp 1
          (te, m + 1) () (tf, m) := by
        have hp := ProgRuns_prim (fun _ => ((), false, QCSD_HeadDir.left))
          (Sp := Sp) (t := te) (h := m + 1)
          (by simp only [Nat.max_eq_max] at hlene hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlene hsp ⊢; omega)
        simpa [stepHead] using hp
      let tg := QCSD_tapeWrite2 tf m true
      have hleng : tg.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlenf ⊢; omega
      have hp7 : ProgRuns (primProg (fun _ => ((), true, QCSD_HeadDir.right))) Sp 1
          (tf, m) () (tg, m + 1) :=
        ProgRuns_prim (fun _ => ((), true, QCSD_HeadDir.right))
          (Sp := Sp) (t := tf) (h := m)
          (by simp only [Nat.max_eq_max] at hlenf hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlenf hsp ⊢; omega)
      have htg_read : ∀ p, QCSD_tapeRead tg p =
          if p = m then true else if m + 1 ≤ p ∧ p < base then false else QCSD_tapeRead t p := by
        intro p
        dsimp [tg, tf, te]; rw [tapeRead_tapeWrite2]
        by_cases hm0 : p = m
        · rw [ite_eq_left hm0, ite_eq_left hm0]
        · rw [ite_eq_right hm0, ite_eq_right hm0, tapeRead_tapeWrite2]
          by_cases hm1 : p = m + 1
          · rw [ite_eq_left hm1, ite_eq_left (by omega)]
          · rw [ite_eq_right hm1, tapeRead_tapeWrite2]
            by_cases hm2 : p = m + 2
            · rw [ite_eq_left hm2, ite_eq_left (by omega)]
            · rw [ite_eq_right hm2, heqd p, heq_tc p, htb_read p,
                  ite_eq_right (fun h => h.elim hm1 hm2)]
              by_cases hmid_p : m + 1 ≤ p ∧ p < base
              · rw [ite_eq_left hmid_p]; exact hmid p (by omega) hmid_p.2
              · rw [ite_eq_right hmid_p]
      obtain ⟨t', heq', hlen', hrWalk⟩ :=
        ProgRuns_walkRightToTrue (Sp := Sp) (pos := m + 1) (target := base) (t := tg)
          (by omega) (by omega)
          (fun p hp_ge hpb => by
            rw [htg_read p, ite_eq_right (by omega), ite_eq_left ⟨hp_ge, hpb⟩])
          (by rw [htg_read base, ite_eq_right (by omega), ite_eq_right (by omega)]; exact hbase_true)
          (by simp only [Nat.max_eq_max] at hleng hsp ⊢; omega)
      refine ⟨t', fun p => ?_,
        by simp only [Nat.max_eq_max] at hlen' hleng ⊢; omega, ?_⟩
      · simpa [hm_sub] using (heq' p).trans (htg_read p)
      · rw [ite_eq_right (Nat.succ_ne_zero m), hm_sub,
            show QCSD_tapeRead t m = false from hbP]
        unfold popRawBitLeftProg popRawBitLeftRaw
        exact (ProgRuns_seq hrLeft (ProgRuns_seq hrScan (ProgRuns_seq hp1 (ProgRuns_seq hp2
          (ProgRuns_bind (k := fun r₁ =>
            ifProg r₁
              (seqProg (stepDirProg QCSD_HeadDir.right)
                (bindProg (primProg (fun r₂ => (r₂, false, QCSD_HeadDir.left))) (fun r₂ =>
                  ifProg r₂
                    (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                      (mapExitProg (fun _ => (true, true)) walkRightToTrueProg))
                    (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                      (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                        (mapExitProg (fun _ => (false, false)) walkRightToTrueProg))))))
              (seqProg (stepDirProg QCSD_HeadDir.right)
                (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                  (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                    (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.right)))
                      (mapExitProg (fun _ => (true, false)) walkRightToTrueProg))))))
            hp3 (ProgRuns_if_false
              (pT := seqProg (stepDirProg QCSD_HeadDir.right)
                (bindProg (primProg (fun r₂ => (r₂, false, QCSD_HeadDir.left))) (fun r₂ =>
                  ifProg r₂
                    (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                      (mapExitProg (fun _ => (true, true)) walkRightToTrueProg))
                    (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                      (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                        (mapExitProg (fun _ => (false, false)) walkRightToTrueProg))))))
              (ProgRuns_seq hp4 (ProgRuns_seq hp5 (ProgRuns_seq hp6
                (ProgRuns_seq hp7 (ProgRuns_mapExit (fun _ => (true, false)) hrWalk))))))))))).mono
          (Nat.le_refl Sp) (by omega)
    | true =>
      rw [hbP] at hp3
      obtain ⟨td, heqd, hlend, hp4⟩ :=
        ProgRuns_stepRight (Sp := Sp) (t := tc) (h := m + 1)
          (by simp only [Nat.max_eq_max] at hlenc hsp ⊢; omega)
      have hr2_t : QCSD_tapeRead td (m + 2) = true := by
        rw [heqd (m + 2), heq_tc (m + 2), htb_read (m + 2),
            ite_eq_left (Or.inr rfl)]
      let te := QCSD_tapeWrite2 td (m + 2) false
      have hlene : te.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlend hlenc ⊢; omega
      have hp5 : ProgRuns (primProg (fun r₂ => (r₂, false, QCSD_HeadDir.left))) Sp 1
          (td, m + 2) true (te, m + 1) := by
        have hp := ProgRuns_prim (fun r₂ => (r₂, false, QCSD_HeadDir.left))
          (Sp := Sp) (t := td) (h := m + 2)
          (by simp only [Nat.max_eq_max] at hlend hlenc hsp ⊢; omega)
          (by rw [hr2_t]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlend hlenc hsp ⊢; omega)
        rw [hr2_t] at hp
        simpa [stepHead] using hp
      let tf := QCSD_tapeWrite2 te (m + 1) false
      have hlenf : tf.length ≤ Nat.max t.length (base + 1) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlene ⊢; omega
      have hp6 : ProgRuns (primProg (fun _ => ((), false, QCSD_HeadDir.right))) Sp 1
          (te, m + 1) () (tf, m + 2) :=
        ProgRuns_prim (fun _ => ((), false, QCSD_HeadDir.right))
          (Sp := Sp) (t := te) (h := m + 1)
          (by simp only [Nat.max_eq_max] at hlene hsp ⊢; omega)
          (by dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max] at hlene hsp ⊢; omega)
      have htf_read : ∀ p, QCSD_tapeRead tf p =
          if p = m then true else if m + 1 ≤ p ∧ p < base then false else QCSD_tapeRead t p := by
        intro p
        dsimp [tf, te]; rw [tapeRead_tapeWrite2]
        by_cases hm1 : p = m + 1
        · rw [ite_eq_left hm1, ite_eq_right (by omega), ite_eq_left (by omega)]
        · rw [ite_eq_right hm1, tapeRead_tapeWrite2]
          by_cases hm2 : p = m + 2
          · rw [ite_eq_left hm2, ite_eq_right (by omega), ite_eq_left (by omega)]
          · rw [ite_eq_right hm2, heqd p, heq_tc p, htb_read p,
                ite_eq_right (fun h => h.elim hm1 hm2)]
            by_cases hm0 : p = m
            · rw [ite_eq_left hm0, hm0]; exact hbP
            · rw [ite_eq_right hm0]
              by_cases hmid_p : m + 1 ≤ p ∧ p < base
              · rw [ite_eq_left hmid_p]; exact hmid p (by omega) hmid_p.2
              · rw [ite_eq_right hmid_p]
      obtain ⟨t', heq', hlen', hrWalk⟩ :=
        ProgRuns_walkRightToTrue (Sp := Sp) (pos := m + 2) (target := base) (t := tf)
          (by omega) (by omega)
          (fun p hp_ge hpb => by
            rw [htf_read p, ite_eq_right (by omega), ite_eq_left ⟨by omega, hpb⟩])
          (by rw [htf_read base, ite_eq_right (by omega), ite_eq_right (by omega)]; exact hbase_true)
          (by simp only [Nat.max_eq_max] at hlenf hsp ⊢; omega)
      refine ⟨t', fun p => ?_,
        by simp only [Nat.max_eq_max] at hlen' hlenf ⊢; omega, ?_⟩
      · simpa [hm_sub] using (heq' p).trans (htf_read p)
      · rw [ite_eq_right (Nat.succ_ne_zero m), hm_sub,
            show QCSD_tapeRead t m = true from hbP]
        unfold popRawBitLeftProg popRawBitLeftRaw
        exact (ProgRuns_seq hrLeft (ProgRuns_seq hrScan (ProgRuns_seq hp1 (ProgRuns_seq hp2
          (ProgRuns_bind (k := fun r₁ =>
            ifProg r₁
              (seqProg (stepDirProg QCSD_HeadDir.right)
                (bindProg (primProg (fun r₂ => (r₂, false, QCSD_HeadDir.left))) (fun r₂ =>
                  ifProg r₂
                    (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                      (mapExitProg (fun _ => (true, true)) walkRightToTrueProg))
                    (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                      (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                        (mapExitProg (fun _ => (false, false)) walkRightToTrueProg))))))
              (seqProg (stepDirProg QCSD_HeadDir.right)
                (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                  (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                    (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.right)))
                      (mapExitProg (fun _ => (true, false)) walkRightToTrueProg))))))
            hp3 (ProgRuns_if_true
              (pF := seqProg (stepDirProg QCSD_HeadDir.right)
                (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                  (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                    (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.right)))
                      (mapExitProg (fun _ => (true, false)) walkRightToTrueProg)))))
              (ProgRuns_seq hp4
                (ProgRuns_bind (k := fun r₂ =>
                  ifProg r₂
                    (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                      (mapExitProg (fun _ => (true, true)) walkRightToTrueProg))
                    (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                      (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                        (mapExitProg (fun _ => (false, false)) walkRightToTrueProg))))
                  hp5 (ProgRuns_if_true
                    (pF := seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.left)))
                      (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
                        (mapExitProg (fun _ => (false, false)) walkRightToTrueProg)))
                    (ProgRuns_seq hp6
                      (ProgRuns_mapExit (fun _ => (true, true)) hrWalk))))))))))).mono
          (Nat.le_refl Sp) (by omega)

attribute [irreducible] PopRawBitQ popRawBitLeftProg

/-! ### Section 7b: `do2nTimesProg`, `slideMidRestProg` & `rawInputToBlockTapeProg` -/

def rep4Prog {Q : Type} (act : Prog Q Unit) :=
  seqProg act (seqProg act (seqProg act act))

def rep6Prog {Q : Type} (act : Prog Q Unit) :=
  seqProg act (seqProg act (rep4Prog act))

def do2nTimesProg {Q : Type} (remBool : Bool) (act : Prog Q Unit) :=
  seqProg resetAllMarksProg
    (seqProg (ifProg remBool (rep6Prog act) (rep4Prog act))
      (whileProg
        (bindProg consumeOneMarkProg (fun ok =>
          ifProg ok
            (mapExitProg (fun _ => true) (rep4Prog act))
            (mapExitProg (fun _ => false) nopProg)))))

lemma ProgRuns_do2nTimes {Q : Type} {act : Prog Q Unit}
    {Sp n k₀ Lmax Tact : ℕ} {posOf : ℕ → ℕ} {leftOf : ℕ → List Bool}
    {Extra : ℕ → List Bool → Prop} {t₀ : List Bool}
    (hn : 2 ≤ n)
    (hw₀ : WinPrefix (posOf 0) ((n - 2) / 2) k₀ (leftOf 0) t₀)
    (hex₀ : Extra 0 t₀)
    (hlen₀ : t₀.length ≤ Lmax)
    (hsp_max : Lmax ≤ Sp)
    (hlen_win : ∀ i ≤ 2 * n, posOf i + 2 * ((n - 2) / 2) + 5 ≤ Lmax)
    (hex_high : ∀ i ≤ 2 * n, ∀ t₁ t₂ : List Bool,
      (∀ p, posOf i + 2 * ((n - 2) / 2) + 3 ≤ p → QCSD_tapeRead t₂ p = QCSD_tapeRead t₁ p) →
      Extra i t₁ → Extra i t₂)
    (hAct : ∀ i < 2 * n, ∀ k ≤ (n - 2) / 2, ∀ t : List Bool,
      WinPrefix (posOf i) ((n - 2) / 2) k (leftOf i) t →
      Extra i t →
      t.length ≤ Lmax →
      ∃ t' : List Bool,
        WinPrefix (posOf (i + 1)) ((n - 2) / 2) k (leftOf (i + 1)) t' ∧
        Extra (i + 1) t' ∧
        t'.length ≤ Lmax ∧
        ProgRuns act Sp Tact
          (t, posOf i + 2 * ((n - 2) / 2) + 3) ()
          (t', posOf (i + 1) + 2 * ((n - 2) / 2) + 3)) :
    let w := (n - 2) / 2
    let remBool := decide ((n - 2) % 2 = 1)
    ∃ t' : List Bool,
      WinPrefix (posOf (2 * n)) w 0 (leftOf (2 * n)) t' ∧
      Extra (2 * n) t' ∧
      t'.length ≤ Lmax ∧
      ProgRuns (do2nTimesProg remBool act) Sp
        (2 * n * Tact + (w + 2) * (10 * w + 20))
        (t₀, posOf 0 + 2 * w + 3) () (t', posOf (2 * n) + 2 * w + 3) := by
  let w := (n - 2) / 2
  let remBool := decide ((n - 2) % 2 = 1)
  have hRep4 : ∀ i, i + 4 ≤ 2 * n → ∀ k ≤ w, ∀ t : List Bool,
      WinPrefix (posOf i) w k (leftOf i) t → Extra i t → t.length ≤ Lmax →
      ∃ t₄ : List Bool,
        WinPrefix (posOf (i + 4)) w k (leftOf (i + 4)) t₄ ∧
        Extra (i + 4) t₄ ∧ t₄.length ≤ Lmax ∧
        ProgRuns (rep4Prog act) Sp (4 * Tact)
          (t, posOf i + 2 * w + 3) () (t₄, posOf (i + 4) + 2 * w + 3) := by
    intro i hi k hk t hwi hexi hleni
    obtain ⟨t₁, hw₁, hex₁, hlen₁, hr₁⟩ := hAct i (by omega) k hk t hwi hexi hleni
    obtain ⟨t₂, hw₂, hex₂, hlen₂, hr₂⟩ := hAct (i + 1) (by omega) k hk t₁ hw₁ hex₁ hlen₁
    obtain ⟨t₃, hw₃, hex₃, hlen₃, hr₃⟩ := hAct (i + 2) (by omega) k hk t₂ hw₂ hex₂ hlen₂
    obtain ⟨t₄, hw₄, hex₄, hlen₄, hr₄⟩ := hAct (i + 3) (by omega) k hk t₃ hw₃ hex₃ hlen₃
    refine ⟨t₄, hw₄, hex₄, hlen₄, ?_⟩
    unfold rep4Prog
    exact (ProgRuns_seq hr₁ (ProgRuns_seq hr₂ (ProgRuns_seq hr₃ hr₄))).mono
      (Nat.le_refl Sp) (by omega)
  have hsp0 : Nat.max t₀.length (posOf 0 + 2 * w + 5) ≤ Sp := by
    have h0 := hlen_win 0 (Nat.zero_le _); simp only [Nat.max_eq_max]; omega
  obtain ⟨t_rst, hw_rst, hhigh_rst, hlen_rst_m, hrRst⟩ :=
    ProgRuns_resetAllMarks (Sp := Sp) hw₀ hsp0
  have hlen_rst : t_rst.length ≤ Lmax := by
    have h0 := hlen_win 0 (Nat.zero_le _); simp only [Nat.max_eq_max] at hlen_rst_m; omega
  have hex_rst : Extra 0 t_rst := hex_high 0 (Nat.zero_le _) t₀ t_rst hhigh_rst hex₀
  let initSteps : ℕ := if remBool then 6 else 4
  have hinit_eq : initSteps + 4 * w = 2 * n := by
    dsimp [initSteps, remBool, w]
    by_cases hm : (n - 2) % 2 = 1
    · simp [hm]; omega
    · simp [hm]; omega
  have hInitRun : ∃ t_i : List Bool,
      WinPrefix (posOf initSteps) w w (leftOf initSteps) t_i ∧
      Extra initSteps t_i ∧ t_i.length ≤ Lmax ∧
      ProgRuns (ifProg remBool (rep6Prog act) (rep4Prog act)) Sp (initSteps * Tact)
        (t_rst, posOf 0 + 2 * w + 3) () (t_i, posOf initSteps + 2 * w + 3) := by
    by_cases hm : (n - 2) % 2 = 1
    · have hrB : remBool = true := decide_eq_true hm
      have his : initSteps = 6 := by simp [initSteps, hrB]
      rw [hrB, his]
      obtain ⟨ta, hwa, hexa, hlena, hra⟩ := hAct 0 (by omega) w (Nat.le_refl w) t_rst hw_rst hex_rst hlen_rst
      obtain ⟨tb, hwb, hexb, hlenb, hrb⟩ := hAct 1 (by omega) w (Nat.le_refl w) ta hwa hexa hlena
      obtain ⟨tc, hwc, hexc, hlenc, hrc⟩ := hRep4 2 (by omega) w (Nat.le_refl w) tb hwb hexb hlenb
      refine ⟨tc, hwc, hexc, hlenc, ?_⟩
      apply ProgRuns_if_true (pF := rep4Prog act)
      unfold rep6Prog
      exact (ProgRuns_seq hra (ProgRuns_seq hrb hrc)).mono (Nat.le_refl Sp) (by omega)
    · have hrB : remBool = false := decide_eq_false hm
      have his : initSteps = 4 := by simp [initSteps, hrB]
      rw [hrB, his]
      obtain ⟨tc, hwc, hexc, hlenc, hrc⟩ := hRep4 0 (by omega) w (Nat.le_refl w) t_rst hw_rst hex_rst hlen_rst
      exact ⟨tc, hwc, hexc, hlenc, ProgRuns_if_false (pT := rep6Prog act) hrc⟩
  obtain ⟨t_i, hw_i, hex_i, hlen_i, hrInit⟩ := hInitRun
  let loopBody :=
    bindProg consumeOneMarkProg (fun ok =>
      ifProg ok
        (mapExitProg (fun _ => true) (rep4Prog act))
        (mapExitProg (fun _ => false) nopProg))
  have hloop : ∀ (k i : ℕ), k ≤ w → i + 4 * k = 2 * n → ∀ t_c : List Bool,
      WinPrefix (posOf i) w k (leftOf i) t_c → Extra i t_c → t_c.length ≤ Lmax →
      ∃ t_e : List Bool,
        WinPrefix (posOf (2 * n)) w 0 (leftOf (2 * n)) t_e ∧
        Extra (2 * n) t_e ∧ t_e.length ≤ Lmax ∧
        ProgRuns (whileProg loopBody) Sp (4 * k * Tact + (k + 1) * (10 * w + 20))
          (t_c, posOf i + 2 * w + 3) () (t_e, posOf (2 * n) + 2 * w + 3) := by
    intro k
    induction k with
    | zero =>
      intro i _ hi_eq t_c hwc hexc hlenc
      have hi2n : i = 2 * n := by omega
      subst hi2n
      have hw_lim := hlen_win (2 * n) (Nat.le_refl (2 * n))
      obtain ⟨t₁, hw₁, hhigh₁, hlen₁_m, hrC⟩ :=
        ProgRuns_consumeOneMark (Sp := Sp) hwc (by simp only [Nat.max_eq_max]; omega)
      have hlen₁ : t₁.length ≤ Lmax := by simp only [Nat.max_eq_max] at hlen₁_m; omega
      have hex₁ : Extra (2 * n) t₁ := hex_high (2 * n) (Nat.le_refl (2 * n)) t_c t₁ hhigh₁ hexc
      simp only [Nat.lt_irrefl, decide_false] at hrC
      obtain ⟨t₂, heq₂, hlen₂_m, hrN⟩ :=
        ProgRuns_nop (Sp := Sp) (t := t₁) (h := posOf (2 * n) + 2 * w + 3)
          (by simp only [Nat.max_eq_max]; omega)
      have hlen₂ : t₂.length ≤ Lmax := by simp only [Nat.max_eq_max] at hlen₂_m; omega
      have hex₂ : Extra (2 * n) t₂ := hex_high (2 * n) (Nat.le_refl (2 * n)) t₁ t₂ (fun p _ => heq₂ p) hex₁
      refine ⟨t₂, WinPrefix_of_tapeEq hw₁ heq₂, hex₂, hlen₂, ?_⟩
      have hexit : ProgRuns loopBody Sp ((10 * w + 16) + 2)
          (t_c, posOf (2 * n) + 2 * w + 3) false (t₂, posOf (2 * n) + 2 * w + 3) :=
        ProgRuns_bind (k := fun ok =>
          ifProg ok
            (mapExitProg (fun _ => true) (rep4Prog act))
            (mapExitProg (fun _ => false) nopProg))
          hrC (ProgRuns_if_false
            (pT := mapExitProg (fun _ => true) (rep4Prog act))
            (ProgRuns_mapExit (fun _ => false) hrN))
      exact (ProgRuns_while_false hexit).mono (Nat.le_refl Sp) (by omega)
    | succ k ih =>
      intro i hk_le hi_eq t_c hwc hexc hlenc
      have hi_le : i ≤ 2 * n := by omega
      have hw_lim := hlen_win i hi_le
      obtain ⟨t₁, hw₁, hhigh₁, hlen₁_m, hrC⟩ :=
        ProgRuns_consumeOneMark (Sp := Sp) hwc (by simp only [Nat.max_eq_max]; omega)
      have hlen₁ : t₁.length ≤ Lmax := by simp only [Nat.max_eq_max] at hlen₁_m; omega
      have hex₁ : Extra i t₁ := hex_high i hi_le t_c t₁ hhigh₁ hexc
      have hpos_k : decide (0 < k + 1) = true := decide_eq_true (Nat.zero_lt_succ k)
      rw [hpos_k] at hrC
      have hk_sub : k + 1 - 1 = k := by omega
      rw [hk_sub] at hw₁
      obtain ⟨t₂, hw₂, hex₂, hlen₂, hr4⟩ :=
        hRep4 i (by omega) k (by omega) t₁ hw₁ hex₁ hlen₁
      obtain ⟨t_e, hw_e, hex_e, hlen_e, hrRest⟩ :=
        ih (i + 4) (by omega) (by omega) t₂ hw₂ hex₂ hlen₂
      have hbody : ProgRuns loopBody Sp ((10 * w + 16) + 4 * Tact)
          (t_c, posOf i + 2 * w + 3) true (t₂, posOf (i + 4) + 2 * w + 3) :=
        ProgRuns_bind (k := fun ok =>
          ifProg ok
            (mapExitProg (fun _ => true) (rep4Prog act))
            (mapExitProg (fun _ => false) nopProg))
          hrC (ProgRuns_if_true
            (pF := mapExitProg (fun _ => false) nopProg)
            (ProgRuns_mapExit (fun _ => true) hr4))
      refine ⟨t_e, hw_e, hex_e, hlen_e, ?_⟩
      exact (ProgRuns_while_true hbody hrRest).mono (Nat.le_refl Sp) (by nlinarith)
  obtain ⟨t', hw', hex', hlen', hrL⟩ :=
    hloop w initSteps (Nat.le_refl w) hinit_eq t_i hw_i hex_i hlen_i
  refine ⟨t', hw', hex', hlen', ?_⟩
  unfold do2nTimesProg
  have hrRst' : ProgRuns resetAllMarksProg Sp (8 * w + 12)
      (t₀, posOf 0 + 2 * w + 3) () (t_rst, posOf 0 + 2 * w + 3) := hrRst
  exact (ProgRuns_seq hrRst' (ProgRuns_seq hrInit hrL)).mono (Nat.le_refl Sp) (by
    dsimp only [w] at hinit_eq ⊢; rw [← hinit_eq]; ring_nf; omega)

def slideOneUnaryProg :=
  whileProg
    (bindProg (primProg (fun b => (b, b, QCSD_HeadDir.right))) (fun b =>
      seqProg (stepDirProg QCSD_HeadDir.left)
        (mapExitProg (fun _ => b) slideWinRightProg)))

lemma ProgRuns_slideOneUnary {Sp Lmax pos w k c : ℕ} {leftBits rest t : List Bool}
    (hw : WinPrefix pos w k leftBits t)
    (hrest : ∀ p, pos + 2 * w + 3 ≤ p →
      QCSD_tapeRead t p = QCSD_tapeRead (QCSD_natToUnary c ++ rest) (p - (pos + 2 * w + 3)))
    (hlen : t.length ≤ Lmax)
    (hL : pos + 2 * w + 6 + c ≤ Lmax)
    (hsp : Lmax + 2 ≤ Sp) :
    let uLen := c + 1
    ∃ t' : List Bool,
      WinPrefix (pos + uLen) w k (leftBits ++ QCSD_natToUnary c) t' ∧
      (∀ p, (pos + uLen) + 2 * w + 3 ≤ p →
        QCSD_tapeRead t' p = QCSD_tapeRead rest (p - ((pos + uLen) + 2 * w + 3))) ∧
      t'.length ≤ Lmax ∧
      ProgRuns slideOneUnaryProg Sp ((c + 1) * (12 * w + 25))
        (t, pos + 2 * w + 3) () (t', (pos + uLen) + 2 * w + 3) := by
  let body :=
    bindProg (primProg (fun b => (b, b, QCSD_HeadDir.right))) (fun b =>
      seqProg (stepDirProg QCSD_HeadDir.left)
        (mapExitProg (fun _ => b) slideWinRightProg))
  have hloop : ∀ (rem j : ℕ), j + rem = c → ∀ t_c : List Bool,
      WinPrefix (pos + j) w k (leftBits ++ List.replicate j true) t_c →
      (∀ p, (pos + j) + 2 * w + 3 ≤ p →
        QCSD_tapeRead t_c p =
          QCSD_tapeRead (QCSD_natToUnary rem ++ rest) (p - ((pos + j) + 2 * w + 3))) →
      t_c.length ≤ Lmax →
      ∃ t_e : List Bool,
        WinPrefix (pos + (c + 1)) w k (leftBits ++ QCSD_natToUnary c) t_e ∧
        (∀ p, (pos + (c + 1)) + 2 * w + 3 ≤ p →
          QCSD_tapeRead t_e p = QCSD_tapeRead rest (p - ((pos + (c + 1)) + 2 * w + 3))) ∧
        t_e.length ≤ Lmax ∧
        ProgRuns (whileProg body) Sp ((rem + 1) * (12 * w + 25))
          (t_c, (pos + j) + 2 * w + 3) () (t_e, (pos + (c + 1)) + 2 * w + 3) := by
    intro rem
    induction rem with
    | zero =>
      intro j hj t_c hwc hrc hlenc
      have hjc : j = c := by omega
      subst hjc
      let h0 := (pos + j) + 2 * w + 3
      have hb0 : QCSD_tapeRead t_c h0 = false := by
        rw [hrc h0 (Nat.le_refl h0), Nat.sub_self]
        simp [QCSD_natToUnary, QCSD_tapeRead]
      let ta := QCSD_tapeWrite2 t_c h0 false
      have heqa : tapeEq ta t_c := by
        intro q; dsimp [ta]; rw [tapeRead_tapeWrite2]
        split_ifs with hq
        · rw [hq]; exact hb0.symm
        · rfl
      have hlena : ta.length ≤ Lmax := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, h0] at hlenc ⊢; omega
      have hs1 : ProgRuns (primProg (fun b => (b, b, QCSD_HeadDir.right))) Sp 1
          (t_c, h0) false (ta, h0 + 1) := by
        have hp := ProgRuns_prim (fun b => (b, b, QCSD_HeadDir.right))
          (Sp := Sp) (t := t_c) (h := h0)
          (by simp only [Nat.max_eq_max, h0] at hlenc hsp ⊢; omega)
          (by rw [hb0]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, h0] at hlenc hsp ⊢; omega)
        rw [hb0] at hp; exact hp
      obtain ⟨tb, heqb, hlenb, hs2⟩ :=
        ProgRuns_stepLeft (Sp := Sp) (t := ta) (h := h0 + 1)
          (by simp only [Nat.max_eq_max, h0] at hlena hsp ⊢; omega)
      have hsub : h0 + 1 - 1 = h0 := by omega
      rw [hsub] at hs2
      have heq_tb : tapeEq tb t_c := tapeEq_trans heqb heqa
      obtain ⟨t_e, hw_e, hhigh_e, hlen_e, hs3⟩ :=
        ProgRuns_slideWinRight (Sp := Sp) (WinPrefix_of_tapeEq hwc heq_tb)
          (by simp only [Nat.max_eq_max, h0] at hlenb hlena hsp ⊢; omega)
      have hb_tb : QCSD_tapeRead tb h0 = false := (heq_tb h0).trans hb0
      rw [hb_tb] at hw_e
      have hunary_eq : (leftBits ++ List.replicate j true) ++ [false] =
          leftBits ++ QCSD_natToUnary j := by
        simp [QCSD_natToUnary, List.append_assoc]
      have hpos_eq : pos + j + 1 = pos + (j + 1) := by omega
      rw [hunary_eq] at hw_e
      rw [hpos_eq] at hw_e hs3
      refine ⟨t_e, hw_e, ?_, by simp only [Nat.max_eq_max, h0] at hlen_e hlenb hlena ⊢; omega, ?_⟩
      · intro p hp
        rw [hhigh_e p (by omega), heq_tb p, hrc p (by omega)]
        have hdiff : p - h0 = (p - ((pos + (j + 1)) + 2 * w + 3)) + 1 := by dsimp [h0]; omega
        rw [hdiff]
        unfold QCSD_tapeRead
        simp [QCSD_natToUnary, List.getD_eq_getElem?_getD]
      · have hexit : ProgRuns body Sp (1 + (1 + (12 * w + 20)))
            (t_c, h0) false (t_e, (pos + (j + 1)) + 2 * w + 3) :=
          ProgRuns_bind (k := fun b =>
            seqProg (stepDirProg QCSD_HeadDir.left)
              (mapExitProg (fun _ => b) slideWinRightProg))
            hs1 (ProgRuns_seq hs2 (ProgRuns_mapExit (fun _ => false) hs3))
        exact (ProgRuns_while_false hexit).mono (Nat.le_refl Sp) (by omega)
    | succ rem ih =>
      intro j hj t_c hwc hrc hlenc
      let h0 := (pos + j) + 2 * w + 3
      have hb0 : QCSD_tapeRead t_c h0 = true := by
        rw [hrc h0 (Nat.le_refl h0), Nat.sub_self]
        simp [QCSD_natToUnary, QCSD_tapeRead, List.replicate_succ]
      let ta := QCSD_tapeWrite2 t_c h0 true
      have heqa : tapeEq ta t_c := by
        intro q; dsimp [ta]; rw [tapeRead_tapeWrite2]
        split_ifs with hq
        · rw [hq]; exact hb0.symm
        · rfl
      have hlena : ta.length ≤ Lmax := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, h0] at hlenc ⊢; omega
      have hs1 : ProgRuns (primProg (fun b => (b, b, QCSD_HeadDir.right))) Sp 1
          (t_c, h0) true (ta, h0 + 1) := by
        have hp := ProgRuns_prim (fun b => (b, b, QCSD_HeadDir.right))
          (Sp := Sp) (t := t_c) (h := h0)
          (by simp only [Nat.max_eq_max, h0] at hlenc hsp ⊢; omega)
          (by rw [hb0]; dsimp [stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, h0] at hlenc hsp ⊢; omega)
        rw [hb0] at hp; exact hp
      obtain ⟨tb, heqb, hlenb, hs2⟩ :=
        ProgRuns_stepLeft (Sp := Sp) (t := ta) (h := h0 + 1)
          (by simp only [Nat.max_eq_max, h0] at hlena hsp ⊢; omega)
      have hsub : h0 + 1 - 1 = h0 := by omega
      rw [hsub] at hs2
      have heq_tb : tapeEq tb t_c := tapeEq_trans heqb heqa
      obtain ⟨t_m, hw_m, hhigh_m, hlen_m, hs3⟩ :=
        ProgRuns_slideWinRight (Sp := Sp) (WinPrefix_of_tapeEq hwc heq_tb)
          (by simp only [Nat.max_eq_max, h0] at hlenb hlena hsp ⊢; omega)
      have hb_tb : QCSD_tapeRead tb h0 = true := (heq_tb h0).trans hb0
      rw [hb_tb] at hw_m
      have hrep_eq : (leftBits ++ List.replicate j true) ++ [true] =
          leftBits ++ List.replicate (j + 1) true := by
        rw [List.append_assoc, ← List.replicate_succ']
      have hpos_eq : pos + j + 1 = pos + (j + 1) := by omega
      rw [hrep_eq] at hw_m
      rw [hpos_eq] at hw_m hs3
      obtain ⟨t_e, hw_e, hr_e, hlen_e, hrRest⟩ :=
        ih (j + 1) (by omega) t_m hw_m
          (fun p hp => by
            rw [hhigh_m p (by omega), heq_tb p, hrc p (by omega)]
            have hdiff : p - h0 = (p - ((pos + (j + 1)) + 2 * w + 3)) + 1 := by dsimp [h0]; omega
            rw [hdiff]
            unfold QCSD_tapeRead
            simp [QCSD_natToUnary, List.replicate_succ, List.getD_eq_getElem?_getD])
          (by simp only [Nat.max_eq_max, h0] at hlen_m hlenb hlena ⊢; omega)
      have hstep : ProgRuns body Sp (12 * w + 25)
          (t_c, h0) true (t_m, (pos + (j + 1)) + 2 * w + 3) :=
        (ProgRuns_bind (k := fun b =>
          seqProg (stepDirProg QCSD_HeadDir.left)
            (mapExitProg (fun _ => b) slideWinRightProg))
          hs1 (ProgRuns_seq hs2 (ProgRuns_mapExit (fun _ => true) hs3))).mono
          (Nat.le_refl Sp) (by omega)
      exact ⟨t_e, hw_e, hr_e, hlen_e,
        (ProgRuns_while_true hstep hrRest).mono (Nat.le_refl Sp) (by nlinarith)⟩
  have hw0 : WinPrefix (pos + 0) w k (leftBits ++ List.replicate 0 true) t := by simpa using hw
  exact hloop c 0 (Nat.zero_add c) t hw0 (by simpa using hrest) hlen

def slideUnaryTailBody (u : ℕ) (idx : Fin (u + 1)) :=
  ifProg (decide (idx.val < u))
    (mapExitProg (fun _ =>
      (if hlt : idx.val + 1 < u + 1 then Sum.inl ⟨idx.val + 1, hlt⟩ else Sum.inr () :
        Fin (u + 1) ⊕ Unit)) slideOneUnaryProg)
    (mapExitProg (fun _ => (Sum.inr () : Fin (u + 1) ⊕ Unit)) nopProg)

def slideUnaryTailProg (u : ℕ) :=
  loopStateProg (⟨0, Nat.zero_lt_succ u⟩ : Fin (u + 1)) (slideUnaryTailBody u)

lemma ProgRuns_slideUnaryTail {Sp Lmax pos₀ w k u : ℕ} {left₀ : List Bool} {ts : List ℕ} {t : List Bool}
    (hu : ts.length = u)
    (hw : WinPrefix pos₀ w k left₀ t)
    (hrest : ∀ p, pos₀ + 2 * w + 3 ≤ p →
      QCSD_tapeRead t p =
        QCSD_tapeRead (ts.flatMap QCSD_natToUnary) (p - (pos₀ + 2 * w + 3)))
    (hlen : t.length ≤ Lmax)
    (hL : pos₀ + 2 * w + 6 + (ts.flatMap QCSD_natToUnary).length ≤ Lmax)
    (hsp : Lmax + 2 ≤ Sp) :
    let tail := ts.flatMap QCSD_natToUnary
    ∃ t' : List Bool,
      WinPrefix (pos₀ + tail.length) w k (left₀ ++ tail) t' ∧
      (∀ p, (pos₀ + tail.length) + 2 * w + 3 ≤ p → QCSD_tapeRead t' p = false) ∧
      t'.length ≤ Lmax ∧
      ProgRuns (slideUnaryTailProg u) Sp ((tail.length + 1) * (12 * w + 25))
        (t, pos₀ + 2 * w + 3) () (t', (pos₀ + tail.length) + 2 * w + 3) := by
  let tail := ts.flatMap QCSD_natToUnary
  have hL_t : pos₀ + 2 * w + 6 + tail.length ≤ Lmax := hL
  have hloop : ∀ (rem : List ℕ) (idx : ℕ) (hidx : idx + rem.length = u)
      (pCur : ℕ) (lCur t_c : List Bool),
      pCur + (rem.flatMap QCSD_natToUnary).length = pos₀ + tail.length →
      lCur ++ rem.flatMap QCSD_natToUnary = left₀ ++ tail →
      WinPrefix pCur w k lCur t_c →
      (∀ p, pCur + 2 * w + 3 ≤ p →
        QCSD_tapeRead t_c p =
          QCSD_tapeRead (rem.flatMap QCSD_natToUnary) (p - (pCur + 2 * w + 3))) →
      t_c.length ≤ Lmax →
      ∃ t_e : List Bool,
        WinPrefix (pos₀ + tail.length) w k (left₀ ++ tail) t_e ∧
        (∀ p, (pos₀ + tail.length) + 2 * w + 3 ≤ p → QCSD_tapeRead t_e p = false) ∧
        t_e.length ≤ Lmax ∧
        ProgRuns (loopStateProg ⟨idx, by omega⟩ (slideUnaryTailBody u)) Sp
          (((rem.flatMap QCSD_natToUnary).length + 1) * (12 * w + 25))
          (t_c, pCur + 2 * w + 3) () (t_e, (pos₀ + tail.length) + 2 * w + 3) := by
    intro rem
    induction rem with
    | nil =>
      intro idx hidx pCur lCur t_c hp_eq hl_eq hwc hrc hlenc
      simp only [List.length_nil, Nat.add_zero, List.flatMap_nil, List.append_nil] at hidx hp_eq hl_eq hrc ⊢
      subst hidx hp_eq hl_eq
      obtain ⟨t_e, heq_e, hlen_e, hrNop⟩ :=
        ProgRuns_nop (Sp := Sp) (t := t_c) (h := (pos₀ + tail.length) + 2 * w + 3)
          (by simp only [Nat.max_eq_max]; omega)
      refine ⟨t_e, WinPrefix_of_tapeEq hwc heq_e, ?_,
        by simp only [Nat.max_eq_max] at hlen_e ⊢; omega, ?_⟩
      · intro p hp
        rw [heq_e p, hrc p hp]
        rfl
      · have hexit : ProgRuns (slideUnaryTailBody idx ⟨idx, Nat.lt_succ_self idx⟩) Sp 2
            (t_c, (pos₀ + tail.length) + 2 * w + 3)
            (Sum.inr () : Fin (idx + 1) ⊕ Unit)
            (t_e, (pos₀ + tail.length) + 2 * w + 3) := by
          unfold slideUnaryTailBody
          simp only [Nat.lt_irrefl, decide_false]
          exact ProgRuns_if_false
            (pT := mapExitProg _ slideOneUnaryProg)
            (ProgRuns_mapExit (fun _ => (Sum.inr () : Fin (idx + 1) ⊕ Unit)) hrNop)
        exact (ProgRuns_loopState_exit hexit).mono (Nat.le_refl Sp) (by omega)
    | cons c cs ih =>
      intro idx hidx pCur lCur t_c hp_eq hl_eq hwc hrc hlenc
      simp only [List.flatMap_cons] at hp_eq hl_eq hrc ⊢
      have hlen_c : (QCSD_natToUnary c).length = c + 1 := by simp [QCSD_natToUnary]
      have hlen_app : (QCSD_natToUnary c ++ cs.flatMap QCSD_natToUnary).length =
          (c + 1) + (cs.flatMap QCSD_natToUnary).length := by
        rw [List.length_append, hlen_c]
      rw [hlen_app] at hp_eq
      obtain ⟨t_m, hw_m, hr_m, hlen_m, hrOne⟩ :=
        ProgRuns_slideOneUnary (Sp := Sp) (Lmax := Lmax) (c := c)
          (rest := cs.flatMap QCSD_natToUnary) hwc hrc hlenc (by omega) hsp
      obtain ⟨t_e, hw_e, hr_e, hlen_e, hrRest⟩ :=
        ih (idx + 1) (by simp at hidx; omega) (pCur + (c + 1)) (lCur ++ QCSD_natToUnary c) t_m
          (by omega) (by rw [List.append_assoc]; exact hl_eq) hw_m hr_m hlen_m
      have hlt_u : idx < u := by simp at hidx; omega
      have hlt_u1 : idx + 1 < u + 1 := by omega
      have hstep : ProgRuns (slideUnaryTailBody u ⟨idx, by omega⟩) Sp ((c + 1) * (12 * w + 25))
          (t_c, pCur + 2 * w + 3)
          (Sum.inl ⟨idx + 1, hlt_u1⟩ : Fin (u + 1) ⊕ Unit)
          (t_m, (pCur + (c + 1)) + 2 * w + 3) := by
        unfold slideUnaryTailBody
        simp only [decide_eq_true hlt_u, hlt_u1, ↓reduceDIte]
        exact ProgRuns_if_true
          (pF := mapExitProg (fun _ => (Sum.inr () : Fin (u + 1) ⊕ Unit)) nopProg)
          (ProgRuns_mapExit _ hrOne)
      refine ⟨t_e, hw_e, hr_e, hlen_e, ?_⟩
      exact (ProgRuns_loopState_cont hstep hrRest).mono (Nat.le_refl Sp) (by
        rw [hlen_app]; nlinarith)
  exact hloop ts 0 (by omega) pos₀ left₀ t rfl rfl hw hrest hlen

def slideMidRestRaw (u : ℕ) (remBool : Bool) :=
  seqProg (ifProg remBool slideWinRightProg nopProg)
    (seqProg (do2nTimesProg remBool slideWinRightProg)
      (slideUnaryTailProg u))

def SlideMidRestQ (u : ℕ) : Type := ProgState (slideMidRestRaw u true)
instance (u : ℕ) : Fintype (SlideMidRestQ u) := by
  unfold SlideMidRestQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance (u : ℕ) : DecidableEq (SlideMidRestQ u) := by
  unfold SlideMidRestQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def slideMidRestProg (u : ℕ) (remBool : Bool) : Prog (SlideMidRestQ u) Unit :=
  slideMidRestRaw u remBool

lemma ProgRuns_slideMidRest (u : ℕ) {Sp n : ℕ} {body : List Bool} {ts : List ℕ} {t₀ : List Bool}
    (hn : 2 ≤ n)
    (hbody : body.length = 2 * n)
    (hu : ts.length = u)
    (hw₀ : WinPrefix 0 ((n - 2) / 2) ((n - 2) / 2) [] t₀)
    (hrest₀ : ∀ p, 2 * ((n - 2) / 2) + 3 ≤ p →
      QCSD_tapeRead t₀ p =
        QCSD_tapeRead ((if decide ((n - 2) % 2 = 1) then [false] else []) ++ body ++
          ts.flatMap QCSD_natToUnary) (p - (2 * ((n - 2) / 2) + 3)))
    (hlen₀ : t₀.length ≤ (QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary).length + 4)
    (hsp : (QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary).length + 10 ≤ Sp) :
    let w := (n - 2) / 2
    let remBool := decide ((n - 2) % 2 = 1)
    let G := 2 * w + 3
    let tail := ts.flatMap QCSD_natToUnary
    let midRest := (if remBool then [false] else []) ++ body ++ tail
    let m := (QCSD_natToUnary n ++ body ++ tail).length
    ∃ t' : List Bool,
      midRest.length + G = m ∧
      WinPrefix midRest.length w 0 midRest t' ∧
      (∀ p, m ≤ p → QCSD_tapeRead t' p = false) ∧
      t'.length ≤ m + 6 ∧
      ProgRuns (slideMidRestProg u remBool) Sp
        ((m + 2) * (12 * w + 30) + (w + 2) * (10 * w + 20))
        (t₀, G) () (t', m) := by
  let w := (n - 2) / 2
  let remBool := decide ((n - 2) % 2 = 1)
  let G := 2 * w + 3
  let tail := ts.flatMap QCSD_natToUnary
  let midRest := (if remBool then [false] else []) ++ body ++ tail
  let m := (QCSD_natToUnary n ++ body ++ tail).length
  have hlen₀_m : t₀.length ≤ m + 4 := hlen₀
  have hsp_m : m + 10 ≤ Sp := hsp
  have hw_le : 2 * w + 2 ≤ n := by dsimp [w]; omega
  have hm_eq : midRest.length + G = m := by
    dsimp [midRest, m, G, w, remBool, QCSD_natToUnary]
    by_cases hm : (n - 2) % 2 = 1
    · simp [hm]; omega
    · simp [hm]; omega
  let r0 : ℕ := if remBool then 1 else 0
  let l0 : List Bool := if remBool then [false] else []
  have hStepA : ∃ t₁ : List Bool,
      WinPrefix r0 w w l0 t₁ ∧
      (∀ p, r0 + G ≤ p → QCSD_tapeRead t₁ p = QCSD_tapeRead (body ++ tail) (p - (r0 + G))) ∧
      t₁.length ≤ m + 6 ∧
      ProgRuns (ifProg remBool slideWinRightProg nopProg) Sp (12 * w + 20)
        (t₀, G) () (t₁, r0 + G) := by
    by_cases hm : (n - 2) % 2 = 1
    · have hrB : remBool = true := decide_eq_true hm
      have hr0 : r0 = 1 := by simp [r0, hrB]
      have hl0 : l0 = [false] := by simp [l0, hrB]
      rw [hrB, hr0, hl0]
      obtain ⟨t₁, hw₁, hhigh₁, hlen₁, hr₁⟩ :=
        ProgRuns_slideWinRight (Sp := Sp) hw₀
          (by simp only [Nat.max_eq_max, G] at hm_eq ⊢; omega)
      have hb0 : QCSD_tapeRead t₀ (0 + 2 * ((n - 2) / 2) + 3) = false := by
        have h := hrest₀ (2 * ((n - 2) / 2) + 3) (Nat.le_refl _)
        rw [Nat.sub_self, decide_eq_true hm] at h
        simpa [QCSD_tapeRead] using h
      rw [hb0, List.nil_append] at hw₁
      rw [Nat.zero_add] at hw₁ hr₁
      refine ⟨t₁, hw₁, ?_, by simp only [Nat.max_eq_max, G] at hlen₁ hm_eq ⊢; omega,
        ProgRuns_if_true (pF := nopProg) hr₁⟩
      intro p hp
      rw [hhigh₁ p (by dsimp [G, w] at hp; omega), hrest₀ p (by dsimp [G, w] at hp; omega)]
      have hsub : p - (2 * ((n - 2) / 2) + 3) = (p - (1 + G)) + 1 := by dsimp [G, w]; omega
      rw [hsub, decide_eq_true hm]
      unfold QCSD_tapeRead
      simp [List.getD_eq_getElem?_getD]; rfl
    · have hrB : remBool = false := decide_eq_false hm
      have hr0 : r0 = 0 := by simp [r0, hrB]
      have hl0 : l0 = [] := by simp [l0, hrB]
      rw [hrB, hr0, hl0, Nat.zero_add]
      obtain ⟨t₁, heq₁, hlen₁, hr₁⟩ :=
        ProgRuns_nop (Sp := Sp) (t := t₀) (h := G)
          (by simp only [Nat.max_eq_max, G] at hm_eq ⊢; omega)
      refine ⟨t₁, WinPrefix_of_tapeEq hw₀ heq₁, ?_,
        by simp only [Nat.max_eq_max, G] at hlen₁ hm_eq ⊢; omega,
        (ProgRuns_if_false (pT := slideWinRightProg) hr₁).mono (Nat.le_refl Sp) (by omega)⟩
      intro p hp
      rw [heq₁ p, hrest₀ p hp, decide_eq_false hm]
      simp; rfl
  obtain ⟨t₁, hw₁, hrest₁, hlen₁, hrA⟩ := hStepA
  have hr0_len : l0.length = r0 := by dsimp [l0, r0]; split_ifs <;> rfl
  obtain ⟨t₂, hw₂, hrest₂, hlen₂, hrB_run⟩ :=
    ProgRuns_do2nTimes (Sp := Sp) (n := n) (k₀ := w) (Lmax := m + 6) (Tact := 12 * w + 20)
      (posOf := fun i => r0 + i)
      (leftOf := fun i => l0 ++ body.take i)
      (Extra := fun i t => ∀ p, (r0 + i) + G ≤ p →
        QCSD_tapeRead t p = QCSD_tapeRead (body.drop i ++ tail) (p - ((r0 + i) + G)))
      hn (by simpa using hw₁) (by simpa using hrest₁) hlen₁
      (by omega)
      (fun i hi => by
        have hmid_len : r0 + 2 * n ≤ midRest.length := by
          dsimp [midRest]; rw [List.length_append, List.length_append, hbody]
          change l0.length + 2 * n + tail.length ≥ r0 + 2 * n; omega
        dsimp [G, w] at hm_eq ⊢; omega)
      (fun i _ ta tb hhigh hEx p hp => (hhigh p hp).trans (hEx p hp))
      (fun i hi k hk t hwi hExi hleni => by
        have hmid_len : r0 + 2 * n ≤ midRest.length := by
          dsimp [midRest]; rw [List.length_append, List.length_append, hbody]
          change l0.length + 2 * n + tail.length ≥ r0 + 2 * n; omega
        obtain ⟨t', hw', hhigh', hlen', hrS⟩ :=
          ProgRuns_slideWinRight (Sp := Sp) hwi
            (by simp only [Nat.max_eq_max]; dsimp [G, w] at hm_eq ⊢; omega)
        have hi_b : i < body.length := by omega
        have hb_eq : QCSD_tapeRead t ((r0 + i) + 2 * ((n - 2) / 2) + 3) = body[i] := by
          have h := hExi ((r0 + i) + G) (Nat.le_refl _)
          rw [Nat.sub_self] at h
          change QCSD_tapeRead t ((r0 + i) + 2 * ((n - 2) / 2) + 3) = _ at h
          rw [h]
          unfold QCSD_tapeRead
          have hdrop_cons : body.drop i = body[i] :: body.drop (i + 1) :=
            List.drop_eq_getElem_cons hi_b
          rw [hdrop_cons, List.cons_append]
          simp
        rw [hb_eq] at hw'
        have htake_eq : (l0 ++ body.take i) ++ [body[i]] = l0 ++ body.take (i + 1) := by
          rw [List.append_assoc, List.take_concat_get' body i hi_b]
        have hpos_add : r0 + i + 1 = r0 + (i + 1) := by omega
        rw [htake_eq] at hw'
        rw [hpos_add] at hw' hrS
        refine ⟨t', hw', ?_,
          by simp only [Nat.max_eq_max] at hlen'; dsimp [G, w] at hm_eq ⊢; omega, hrS⟩
        intro p hp
        rw [hhigh' p (by dsimp [G, w] at hp; omega), hExi p (by dsimp [G, w] at hp; omega)]
        have hdrop_cons : body.drop i = body[i] :: body.drop (i + 1) :=
          List.drop_eq_getElem_cons hi_b
        have hdiff : p - ((r0 + i) + G) = (p - ((r0 + (i + 1)) + G)) + 1 := by omega
        rw [hdrop_cons, List.cons_append, hdiff]
        unfold QCSD_tapeRead
        simp [List.getD_eq_getElem?_getD])
  have htake_2n : body.take (2 * n) = body := by rw [← hbody, List.take_length]
  have hdrop_2n : body.drop (2 * n) = [] := by rw [← hbody, List.drop_length]
  rw [htake_2n] at hw₂
  rw [hdrop_2n, List.nil_append] at hrest₂
  have htail_len : (r0 + 2 * n) + tail.length = midRest.length := by
    dsimp [midRest]; rw [List.length_append, List.length_append, hbody]
    change (r0 + 2 * n) + tail.length = l0.length + 2 * n + tail.length
    rw [hr0_len]
  have hm_exp : (r0 + 2 * n) + tail.length + (2 * w + 3) = m := by
    rw [htail_len]; exact hm_eq
  obtain ⟨t₃, hw₃, hrest₃, hlen₃, hrC⟩ :=
    ProgRuns_slideUnaryTail (Sp := Sp) (Lmax := m + 6) (pos₀ := r0 + 2 * n) hu hw₂ hrest₂ hlen₂
      (by change r0 + 2 * n + 2 * w + 6 + tail.length ≤ m + 6; omega)
      (by omega)
  have hl_eq : (l0 ++ body) ++ tail = midRest := rfl
  rw [htail_len] at hw₃ hrest₃ hrC
  rw [hl_eq] at hw₃
  have hm_head : midRest.length + 2 * ((n - 2) / 2) + 3 = m := hm_eq
  rw [hm_head] at hrest₃ hrC
  refine ⟨t₃, hm_eq, hw₃, hrest₃, hlen₃, ?_⟩
  unfold slideMidRestProg slideMidRestRaw
  have hm_ge : 2 * n + tail.length + 1 ≤ m := by
    dsimp [m, QCSD_natToUnary]; simp [hbody]
  exact (ProgRuns_seq hrA (ProgRuns_seq hrB_run hrC)).mono
    (Nat.le_refl Sp) (by dsimp only [w, m, tail] at hm_ge ⊢; nlinarith)

attribute [irreducible] SlideMidRestQ slideMidRestProg

def initBaseCursorProg :=
  seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.right)))
    (seqProg (moveDirPosProg QCSD_HeadDir.right 2)
      (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.left)))
        (moveDirPosProg QCSD_HeadDir.left 2)))

def advanceCursorOnceProg :=
  seqProg (stepDirProg QCSD_HeadDir.right)
    (seqProg walkRightToTrueProg
      (seqProg (primProg (fun _ => ((), false, QCSD_HeadDir.right)))
        (seqProg (primProg (fun _ => ((), true, QCSD_HeadDir.left)))
          (seqProg (stepDirProg QCSD_HeadDir.left)
            (seqProg (whileProg (primProg (emitPhysScanStep true)))
              (stepDirProg QCSD_HeadDir.left))))))

def setupBaseAndBlock0Raw (remBool : Bool) :=
  seqProg initBaseCursorProg
    (seqProg (do2nTimesProg remBool advanceCursorOnceProg)
      (seqProg resetAllMarksProg
        (seqProg (stepDirProg QCSD_HeadDir.right)
          (seqProg walkRightToTrueProg
            (seqProg (writeSlotProg ⟨1, by decide⟩ true)
              (seqProg (writeSlotProg ⟨9, by decide⟩ true)
                (writeSlotProg ⟨10, by decide⟩ true)))))))

def SetupBaseQ : Type := ProgState (setupBaseAndBlock0Raw true)
instance : Fintype SetupBaseQ := by
  unfold SetupBaseQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance : DecidableEq SetupBaseQ := by
  unfold SetupBaseQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def setupBaseAndBlock0Prog (remBool : Bool) : Prog SetupBaseQ Unit :=
  setupBaseAndBlock0Raw remBool

def HighBlock (base allocLen : ℕ) (inBits vSub : List Bool) (r wM : ℕ) (t : List Bool) : Prop :=
  1 ≤ allocLen ∧
  inBits.length = r ∧
  vSub.length = wM ∧
  r < allocLen ∧
  wM < allocLen ∧
  t.length ≤ base + 11 * allocLen ∧
  (∀ p, base ≤ p →
    QCSD_tapeRead t p =
      slotVal allocLen inBits 0 [] [] vSub (some r) (some wM)
        ((p - base) / 11) ((p - base) % 11))

lemma ProgRuns_advanceCursorOnce {Sp m cur : ℕ} {t : List Bool}
    (hm_lt : m + 2 ≤ cur)
    (hm_t : QCSD_tapeRead t m = true)
    (hmid : ∀ p, m < p → p < cur → QCSD_tapeRead t p = false)
    (hcur_t : QCSD_tapeRead t cur = true)
    (hhigh : ∀ p, cur < p → QCSD_tapeRead t p = false)
    (hsp : Nat.max t.length (cur + 4) ≤ Sp) :
    ∃ t' : List Bool,
      (∀ p < m, QCSD_tapeRead t' p = QCSD_tapeRead t p) ∧
      QCSD_tapeRead t' m = true ∧
      (∀ p, m < p → p < cur + 1 → QCSD_tapeRead t' p = false) ∧
      QCSD_tapeRead t' (cur + 1) = true ∧
      (∀ p, cur + 1 < p → QCSD_tapeRead t' p = false) ∧
      t'.length ≤ Nat.max t.length (cur + 3) ∧
      ProgRuns advanceCursorOnceProg Sp (2 * (cur - m) + 10) (t, m) () (t', m) := by
  obtain ⟨t₁, heq₁, hlen₁, hs1⟩ :=
    ProgRuns_stepRight (Sp := Sp) (t := t) (h := m)
      (by simp only [Nat.max_eq_max] at hsp ⊢; omega)
  obtain ⟨t₂, heq₂, hlen₂, hs2⟩ :=
    ProgRuns_walkRightToTrue (Sp := Sp) (pos := m + 1) (target := cur) (t := t₁)
      (by omega) (by omega)
      (fun p hp1 hp2 => (heq₁ p).trans (hmid p (by omega) hp2))
      ((heq₁ cur).trans hcur_t)
      (by simp only [Nat.max_eq_max] at hlen₁ hsp ⊢; omega)
  have heq_t₂ : tapeEq t₂ t := tapeEq_trans heq₂ heq₁
  let t₃ := QCSD_tapeWrite2 t₂ cur false
  have hlen₃ : t₃.length ≤ Nat.max t.length (cur + 3) := by
    rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen₂ hlen₁ ⊢; omega
  have hs3 : ProgRuns (primProg (fun _ => ((), false, QCSD_HeadDir.right))) Sp 1
      (t₂, cur) () (t₃, cur + 1) :=
    ProgRuns_prim (fun _ => ((), false, QCSD_HeadDir.right))
      (Sp := Sp) (t := t₂) (h := cur)
      (by simp only [Nat.max_eq_max] at hlen₂ hlen₁ hsp ⊢; omega)
      (by dsimp [stepHead]; rw [tapeWrite2_length]
          simp only [Nat.max_eq_max] at hlen₂ hlen₁ hsp ⊢; omega)
  let t₄ := QCSD_tapeWrite2 t₃ (cur + 1) true
  have hlen₄ : t₄.length ≤ Nat.max t.length (cur + 3) := by
    rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen₃ ⊢; omega
  have hs4 : ProgRuns (primProg (fun _ => ((), true, QCSD_HeadDir.left))) Sp 1
      (t₃, cur + 1) () (t₄, cur) := by
    have hp := ProgRuns_prim (fun _ => ((), true, QCSD_HeadDir.left))
      (Sp := Sp) (t := t₃) (h := cur + 1)
      (by simp only [Nat.max_eq_max] at hlen₃ hsp ⊢; omega)
      (by dsimp [stepHead]; rw [tapeWrite2_length]
          simp only [Nat.max_eq_max] at hlen₃ hsp ⊢; omega)
    simpa [stepHead] using hp
  obtain ⟨t₅, heq₅, hlen₅, hs5⟩ :=
    ProgRuns_stepLeft (Sp := Sp) (t := t₄) (h := cur)
      (by simp only [Nat.max_eq_max] at hlen₄ hsp ⊢; omega)
  have ht₅_read : ∀ p, QCSD_tapeRead t₅ p =
      if p = cur + 1 then true else if p = cur then false else QCSD_tapeRead t p := by
    intro p
    rw [heq₅ p]; dsimp [t₄, t₃]; rw [tapeRead_tapeWrite2]
    by_cases hc1 : p = cur + 1
    · rw [ite_eq_left hc1, ite_eq_left hc1]
    · rw [ite_eq_right hc1, ite_eq_right hc1, tapeRead_tapeWrite2]
      by_cases hc0 : p = cur
      · rw [ite_eq_left hc0, ite_eq_left hc0]
      · rw [ite_eq_right hc0, ite_eq_right hc0]; exact heq_t₂ p
  have hscan : ∀ (rem : ℕ), m + rem ≤ cur - 1 → ∀ t_c : List Bool,
      tapeEq t_c t₅ →
      t_c.length ≤ Nat.max t.length (cur + 3) →
      ∃ t_s : List Bool,
        tapeEq t_s t₅ ∧
        t_s.length ≤ Nat.max t.length (cur + 3) ∧
        ProgRuns (whileProg (primProg (emitPhysScanStep true))) Sp (rem + 1)
          (t_c, m + rem) () (t_s, m + 1) := by
    intro rem
    induction rem with
    | zero =>
      intro _ t_c heq hlen_c
      rw [Nat.add_zero]
      have hrm : QCSD_tapeRead t_c m = true := by
        rw [heq m, ht₅_read m, ite_eq_right (by omega), ite_eq_right (by omega)]
        exact hm_t
      let t_s := QCSD_tapeWrite2 t_c m true
      have heq_s : tapeEq t_s t₅ := by
        intro q; dsimp [t_s]; rw [tapeRead_tapeWrite2]
        split_ifs with hq
        · rw [hq, ← heq m]; exact hrm.symm
        · exact heq q
      have hlen_s : t_s.length ≤ Nat.max t.length (cur + 3) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlen_c ⊢; omega
      refine ⟨t_s, heq_s, hlen_s, ?_⟩
      apply ProgRuns_while_false
      have hp := ProgRuns_prim (emitPhysScanStep true) (Sp := Sp) (t := t_c) (h := m)
        (by simp only [Nat.max_eq_max] at hlen_c hsp ⊢; omega)
        (by rw [hrm]; dsimp [emitPhysScanStep, stepHead]; rw [tapeWrite2_length]
            simp only [Nat.max_eq_max] at hlen_c hsp ⊢; omega)
      rw [hrm] at hp; exact hp
    | succ rem ih =>
      intro hlt t_c heq hlen_c
      let pos := m + (rem + 1)
      have hrp : QCSD_tapeRead t_c pos = false := by
        rw [heq pos, ht₅_read pos, ite_eq_right (by dsimp [pos]; omega),
            ite_eq_right (by dsimp [pos]; omega)]
        exact hmid pos (by dsimp [pos]; omega) (by dsimp [pos]; omega)
      let ta := QCSD_tapeWrite2 t_c pos false
      have heqa : tapeEq ta t₅ := by
        intro q; dsimp [ta]; rw [tapeRead_tapeWrite2]
        split_ifs with hq
        · rw [hq, ← heq pos]; exact hrp.symm
        · exact heq q
      have hlena : ta.length ≤ Nat.max t.length (cur + 3) := by
        rw [tapeWrite2_length]; simp only [Nat.max_eq_max, pos] at hlen_c ⊢; omega
      have hstep : ProgRuns (primProg (emitPhysScanStep true)) Sp 1 (t_c, pos) true (ta, m + rem) := by
        have hp := ProgRuns_prim (emitPhysScanStep true) (Sp := Sp) (t := t_c) (h := pos)
          (by simp only [Nat.max_eq_max, pos] at hlen_c hsp ⊢; omega)
          (by rw [hrp]; dsimp [emitPhysScanStep, stepHead]; rw [tapeWrite2_length]
              simp only [Nat.max_eq_max, pos] at hlen_c hsp ⊢; omega)
        rw [hrp] at hp
        simpa [emitPhysScanStep, stepHead, pos] using hp
      obtain ⟨t_s, heq_s, hlen_s, hrRest⟩ := ih (by omega) ta heqa hlena
      exact ⟨t_s, heq_s, hlen_s,
        (ProgRuns_while_true hstep hrRest).mono (Nat.le_refl Sp) (by omega)⟩
  have hrem_eq : m + (cur - 1 - m) = cur - 1 := by omega
  obtain ⟨t₆, heq₆, hlen₆, hs6⟩ :=
    hscan (cur - 1 - m) (by omega) t₅ (tapeEq_refl t₅)
      (by simp only [Nat.max_eq_max] at hlen₅ hlen₄ ⊢; omega)
  rw [hrem_eq] at hs6
  obtain ⟨t', heq', hlen', hs7⟩ :=
    ProgRuns_stepLeft (Sp := Sp) (t := t₆) (h := m + 1)
      (by simp only [Nat.max_eq_max] at hlen₆ hsp ⊢; omega)
  have hsub_m : m + 1 - 1 = m := by omega
  rw [hsub_m] at hs7
  have heq_all : tapeEq t' t₅ := tapeEq_trans heq' heq₆
  refine ⟨t', ?_, ?_, ?_, ?_, ?_,
    by simp only [Nat.max_eq_max] at hlen' hlen₆ ⊢; omega, ?_⟩
  · intro p hp
    rw [heq_all p, ht₅_read p, ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [heq_all m, ht₅_read m, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hm_t
  · intro p hp1 hp2
    rw [heq_all p, ht₅_read p, ite_eq_right (by omega)]
    by_cases hpc : p = cur
    · rw [ite_eq_left hpc]
    · rw [ite_eq_right hpc]; exact hmid p hp1 (by omega)
  · rw [heq_all (cur + 1), ht₅_read (cur + 1), ite_eq_left rfl]
  · intro p hp
    rw [heq_all p, ht₅_read p, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hhigh p (by omega)
  · unfold advanceCursorOnceProg
    exact (ProgRuns_seq hs1 (ProgRuns_seq hs2 (ProgRuns_seq hs3 (ProgRuns_seq hs4
      (ProgRuns_seq hs5 (ProgRuns_seq hs6 hs7)))))).mono (Nat.le_refl Sp) (by omega)

lemma ProgRuns_setupBaseAndBlock0 {Sp n midLen : ℕ} {midRest t₀ : List Bool}
    (hn : 2 ≤ n)
    (hw₀ : WinPrefix midLen ((n - 2) / 2) 0 midRest t₀)
    (hhigh₀ : ∀ p, midLen + (2 * ((n - 2) / 2) + 3) ≤ p → QCSD_tapeRead t₀ p = false)
    (hlen₀ : t₀.length ≤ midLen + (2 * ((n - 2) / 2) + 3) + 6)
    (hsp : midLen + (2 * ((n - 2) / 2) + 3) + 4 + 2 * n + 15 ≤ Sp) :
    let w := (n - 2) / 2
    let remBool := decide ((n - 2) % 2 = 1)
    let m := midLen + (2 * w + 3)
    let base := m + 4 + 2 * n
    ∃ t' : List Bool,
      WinPrefix midLen w w midRest t' ∧
      QCSD_tapeRead t' m = true ∧
      (∀ p, m < p → p < base → QCSD_tapeRead t' p = false) ∧
      HighBlock base 1 [] [] 0 0 t' ∧
      ProgRuns (setupBaseAndBlock0Prog remBool) Sp
        ((2 * n + 2) * (4 * n + 30) + (w + 2) * (10 * w + 20) + 100)
        (t₀, m) () (t', base) := by
  let w := (n - 2) / 2
  let remBool := decide ((n - 2) % 2 = 1)
  let m := midLen + (2 * w + 3)
  let base := m + 4 + 2 * n
  have hsp_b : base + 15 ≤ Sp := hsp
  let ta := QCSD_tapeWrite2 t₀ m true
  have hlena : ta.length ≤ m + 6 := by
    rw [tapeWrite2_length]; simp only [Nat.max_eq_max, m] at hlen₀ ⊢; omega
  have hi1 : ProgRuns (primProg (fun _ => ((), true, QCSD_HeadDir.right))) Sp 1
      (t₀, m) () (ta, m + 1) :=
    ProgRuns_prim (fun _ => ((), true, QCSD_HeadDir.right))
      (Sp := Sp) (t := t₀) (h := m)
      (by simp only [Nat.max_eq_max, m] at hlen₀ ⊢; omega)
      (by dsimp [stepHead]; rw [tapeWrite2_length]; simp only [Nat.max_eq_max, m] at hlen₀ ⊢; omega)
  obtain ⟨tb, heqb, hlenb, hi2⟩ :=
    ProgRuns_moveRightPos 2 (Sp := Sp) (t := ta) (h := m + 1)
      (by simp only [Nat.max_eq_max]; omega)
  have hm4 : m + 1 + 2 + 1 = m + 4 := by omega
  rw [hm4] at hi2 hlenb
  let tc := QCSD_tapeWrite2 tb (m + 4) true
  have hlenc : tc.length ≤ m + 6 := by
    rw [tapeWrite2_length]; simp only [Nat.max_eq_max] at hlenb hlena ⊢; omega
  have hi3 : ProgRuns (primProg (fun _ => ((), true, QCSD_HeadDir.left))) Sp 1
      (tb, m + 4) () (tc, m + 3) := by
    have hp := ProgRuns_prim (fun _ => ((), true, QCSD_HeadDir.left))
      (Sp := Sp) (t := tb) (h := m + 4)
      (by simp only [Nat.max_eq_max] at hlenb hlena ⊢; omega)
      (by dsimp [stepHead]; rw [tapeWrite2_length]
          simp only [Nat.max_eq_max] at hlenb hlena ⊢; omega)
    simpa [stepHead] using hp
  obtain ⟨td, heqd, hlend, hi4⟩ :=
    ProgRuns_moveLeftPos 2 (Sp := Sp) (t := tc) (h := m + 3)
      (by simp only [Nat.max_eq_max]; omega)
  have hm0 : m + 3 - (2 + 1) = m := by omega
  rw [hm0] at hi4
  have hrInitC : ProgRuns initBaseCursorProg Sp 8 (t₀, m) () (td, m) :=
    ProgRuns_seq hi1 (ProgRuns_seq hi2 (ProgRuns_seq hi3 hi4))
  have htd_read : ∀ p, QCSD_tapeRead td p =
      if p = m ∨ p = m + 4 then true else QCSD_tapeRead t₀ p := by
    intro p
    rw [heqd p]; dsimp [tc]; rw [tapeRead_tapeWrite2]
    by_cases h4 : p = m + 4
    · rw [ite_eq_left h4, ite_eq_left (Or.inr h4)]
    · rw [ite_eq_right h4, heqb p]; dsimp [ta]; rw [tapeRead_tapeWrite2]
      by_cases h0 : p = m
      · rw [ite_eq_left h0, ite_eq_left (Or.inl h0)]
      · rw [ite_eq_right h0, ite_eq_right (fun h => h.elim h0 h4)]
  have hw_td : WinPrefix midLen w 0 midRest td := by
    refine ⟨Nat.zero_le w, hw₀.2.1, fun p hp => ?_, fun off hoff => ?_⟩
    · rw [htd_read p, ite_eq_right (by dsimp [m]; omega)]
      exact hw₀.2.2.1 p hp
    · rw [htd_read (midLen + off), ite_eq_right (by dsimp [m]; omega)]
      exact hw₀.2.2.2 off hoff
  let CurExtra (i : ℕ) (t : List Bool) : Prop :=
    QCSD_tapeRead t m = true ∧
    (∀ p, m < p → p < m + 4 + i → QCSD_tapeRead t p = false) ∧
    QCSD_tapeRead t (m + 4 + i) = true ∧
    (∀ p, m + 4 + i < p → QCSD_tapeRead t p = false)
  obtain ⟨t_adv, hw_adv, hex_adv, hlen_adv, hrAdv⟩ :=
    ProgRuns_do2nTimes (Sp := Sp) (n := n) (k₀ := 0) (Lmax := base + 6)
      (Tact := 4 * n + 20)
      (posOf := fun _ => midLen)
      (leftOf := fun _ => midRest)
      (Extra := CurExtra)
      hn hw_td
      ⟨by rw [htd_read m, ite_eq_left (Or.inl rfl)],
       fun p hp1 hp2 => by
         rw [htd_read p, ite_eq_right (by omega)]; exact hhigh₀ p (by dsimp [m] at hp1; omega),
       by rw [Nat.add_zero, htd_read (m + 4), ite_eq_left (Or.inr rfl)],
       fun p hp => by
         rw [htd_read p, ite_eq_right (by omega)]; exact hhigh₀ p (by dsimp [m] at hp; omega)⟩
      (by simp only [Nat.max_eq_max, base] at hlend hlenc ⊢; omega)
      (by omega)
      (fun _ _ => by dsimp [base, m, w]; omega)
      (fun i _ ta' tb' hhigh ⟨h1, h2, h3, h4⟩ =>
        ⟨(hhigh m (Nat.le_refl m)).trans h1,
         fun p hp1 hp2 => (hhigh p (by dsimp [m] at hp1; omega)).trans (h2 p hp1 hp2),
         (hhigh _ (by dsimp [m]; omega)).trans h3,
         fun p hp => (hhigh p (by dsimp [m] at hp; omega)).trans (h4 p hp)⟩)
      (fun i hi k hk t hwi ⟨h1, h2, h3, h4⟩ hleni => by
        obtain ⟨t', hlow', hm', hmid', hcur', hhigh', hlen', hrStep⟩ :=
          ProgRuns_advanceCursorOnce (Sp := Sp) (m := m) (cur := m + 4 + i) (t := t)
            (by omega) h1 h2 h3 h4
            (by simp only [Nat.max_eq_max, base] at hleni ⊢; omega)
        have hw' : WinPrefix midLen ((n - 2) / 2) k midRest t' :=
          ⟨hk, hwi.2.1,
           fun p hp => (hlow' p (by dsimp [m]; omega)).trans (hwi.2.2.1 p hp),
           fun off hoff => (hlow' _ (by dsimp [m, w]; omega)).trans (hwi.2.2.2 off hoff)⟩
        have hadd : m + 4 + i + 1 = m + 4 + (i + 1) := by omega
        rw [hadd] at hmid' hcur' hhigh'
        exact ⟨t', hw', ⟨hm', hmid', hcur', hhigh'⟩,
          by simp only [Nat.max_eq_max, base] at hlen' hleni ⊢; omega,
          hrStep.mono (Nat.le_refl Sp) (by omega)⟩)
  obtain ⟨t_rst, hw_rst, hhigh_rst, hlen_rst, hrRst⟩ :=
    ProgRuns_resetAllMarks (Sp := Sp) hw_adv
      (by simp only [Nat.max_eq_max, base, m, w] at hlen_adv ⊢; omega)
  have hm_head : midLen + 2 * ((n - 2) / 2) + 3 = m := by dsimp [m, w]; omega
  rw [hm_head] at hrAdv hrRst hhigh_rst
  obtain ⟨t_sr, heq_sr, hlen_sr, hrSR⟩ :=
    ProgRuns_stepRight (Sp := Sp) (t := t_rst) (h := m)
      (by simp only [Nat.max_eq_max, base] at hlen_rst hlen_adv ⊢; omega)
  obtain ⟨t_wk, heq_wk, hlen_wk, hrWk⟩ :=
    ProgRuns_walkRightToTrue (Sp := Sp) (pos := m + 1) (target := base) (t := t_sr)
      (by dsimp [base]; omega) (by dsimp [base]; omega)
      (fun p hp1 hp2 => by
        rw [heq_sr p, hhigh_rst p (by omega)]
        exact hex_adv.2.1 p (by omega) hp2)
      (by
        rw [heq_sr base, hhigh_rst base (by dsimp [base]; omega)]
        exact hex_adv.2.2.1)
      (by simp only [Nat.max_eq_max, base] at hlen_sr hlen_rst hlen_adv ⊢; omega)
  have heq_wk_rst : tapeEq t_wk t_rst := tapeEq_trans heq_wk heq_sr
  have hlen_wk_b : t_wk.length ≤ base + 6 := by
    simp only [Nat.max_eq_max, base] at hlen_wk hlen_sr hlen_rst hlen_adv ⊢; omega
  obtain ⟨t_w1, hw1_r, hlen_w1, hrW1⟩ :=
    ProgRuns_writeSlot_raw ⟨1, by decide⟩ true (Sp := Sp) (t := t_wk) (pos := base)
      (by simp only [Nat.max_eq_max]; omega)
  obtain ⟨t_w9, hw9_r, hlen_w9, hrW9⟩ :=
    ProgRuns_writeSlot_raw ⟨9, by decide⟩ true (Sp := Sp) (t := t_w1) (pos := base)
      (by simp only [Nat.max_eq_max] at hlen_w1 ⊢; omega)
  obtain ⟨t', hw10_r, hlen', hrW10⟩ :=
    ProgRuns_writeSlot_raw ⟨10, by decide⟩ true (Sp := Sp) (t := t_w9) (pos := base)
      (by simp only [Nat.max_eq_max] at hlen_w9 hlen_w1 ⊢; omega)
  dsimp only at hw1_r hw9_r hw10_r
  have hlow_eq : ∀ p < base, QCSD_tapeRead t' p = QCSD_tapeRead t_rst p := by
    intro p hp
    rw [hw10_r p, ite_eq_right (by omega), hw9_r p, ite_eq_right (by omega),
        hw1_r p, ite_eq_right (by omega), heq_wk_rst p]
  refine ⟨t', ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hw_rst.1, hw_rst.2.1,
      fun p hp => (hlow_eq p (by dsimp [base, m]; omega)).trans (hw_rst.2.2.1 p hp),
      fun off hoff => (hlow_eq _ (by dsimp [base, m, w]; omega)).trans (hw_rst.2.2.2 off hoff)⟩
  · rw [hlow_eq m (by dsimp [base]; omega), hhigh_rst m (Nat.le_refl m)]
    exact hex_adv.1
  · intro p hp1 hp2
    rw [hlow_eq p hp2, hhigh_rst p (by omega)]
    exact hex_adv.2.1 p hp1 hp2
  · refine ⟨Nat.le_refl 1, rfl, rfl, Nat.zero_lt_one, Nat.zero_lt_one,
      by simp only [Nat.max_eq_max] at hlen' hlen_w9 hlen_w1 ⊢; omega, fun p hp => ?_⟩
    rw [hw10_r p]
    by_cases hp10 : p = base + 10
    · rw [ite_eq_left hp10, hp10]
      have hd : (base + 10 - base) / 11 = 0 := by omega
      have hm10 : (base + 10 - base) % 11 = 10 := by omega
      rw [hd, hm10]; simp [slotVal]
    · rw [ite_eq_right hp10, hw9_r p]
      by_cases hp9 : p = base + 9
      · rw [ite_eq_left hp9, hp9]
        have hd : (base + 9 - base) / 11 = 0 := by omega
        have hm9 : (base + 9 - base) % 11 = 9 := by omega
        rw [hd, hm9]; simp [slotVal]
      · rw [ite_eq_right hp9, hw1_r p]
        by_cases hp1 : p = base + 1
        · rw [ite_eq_left hp1, hp1]
          have hd : (base + 1 - base) / 11 = 0 := by omega
          have hm1 : (base + 1 - base) % 11 = 1 := by omega
          rw [hd, hm1]; simp [slotVal]
        · rw [ite_eq_right hp1, heq_wk_rst p,
              hhigh_rst p (by have : m ≤ base := by dsimp [base]; omega
                              omega)]
          by_cases hp0 : p = base
          · rw [hp0]
            have hd : (base - base) / 11 = 0 := by omega
            have hm0' : (base - base) % 11 = 0 := by omega
            rw [hd, hm0']
            exact hex_adv.2.2.1
          · rw [hex_adv.2.2.2 p (by omega)]
            set bi := (p - base) / 11
            set bs := (p - base) % 11
            by_cases hbi : bi < 1
            · have hbi0 : bi = 0 := by omega
              have hbs_lt : bs < 11 := Nat.mod_lt _ (by decide)
              have hdm := Nat.div_add_mod (p - base) 11
              change 11 * bi + bs = p - base at hdm
              have hbs_ne : bs ≠ 0 ∧ bs ≠ 1 ∧ bs ≠ 9 ∧ bs ≠ 10 := by omega
              rw [hbi0]
              unfold slotVal
              rw [ite_eq_left Nat.zero_lt_one]
              rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                           bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                h | h | h | h | h | h | h | h | h | h | h <;>
                (rw [h] at hbs_ne ⊢; simp [QCSD_tapeRead] at hbs_ne ⊢)
            · simp [slotVal, hbi]
  · unfold setupBaseAndBlock0Prog setupBaseAndBlock0Raw
    have hbm : base - (m + 1) + 2 = 2 * n + 5 := by dsimp [base]; omega
    rw [hbm] at hrWk
    have hw_le : (n - 2) / 2 ≤ n := by omega
    exact (ProgRuns_seq hrInitC (ProgRuns_seq hrAdv (ProgRuns_seq hrRst
      (ProgRuns_seq hrSR (ProgRuns_seq hrWk
        (ProgRuns_seq hrW1 (ProgRuns_seq hrW9 hrW10))))))).mono
      (Nat.le_refl Sp) (by dsimp only [w] at *; nlinarith)

attribute [irreducible] SetupBaseQ setupBaseAndBlock0Prog

def seekSlotTrueHighProg (s : Fin 11) :=
  whileProg
    (bindProg (readSlotProg s) (fun found =>
      ifProg found
        (mapExitProg (fun _ => false) nopProg)
        (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.right 10))))

lemma ProgRuns_seekSlotTrueHigh (s : Fin 11) {Sp base allocLen target : ℕ} {t : List Bool}
    (htarget : target < allocLen)
    (hlen : t.length ≤ base + 11 * allocLen)
    (hslot : ∀ i ≤ target, QCSD_tapeRead t (base + 11 * i + s.val) = decide (i = target))
    (hsp : base + 11 * allocLen ≤ Sp) :
    ∃ t' : List Bool,
      tapeEq t' t ∧
      t'.length ≤ base + 11 * allocLen ∧
      ProgRuns (seekSlotTrueHighProg s) Sp (31 * target + 22) (t, base) () (t', base + 11 * target) := by
  let body :=
    bindProg (readSlotProg s) (fun found =>
      ifProg found
        (mapExitProg (fun _ => false) nopProg)
        (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.right 10)))
  have hloop : ∀ (rem cur : ℕ), cur + rem = target → ∀ t_c : List Bool,
      tapeEq t_c t →
      t_c.length ≤ base + 11 * allocLen →
      ∃ t_e : List Bool,
        tapeEq t_e t ∧
        t_e.length ≤ base + 11 * allocLen ∧
        ProgRuns (whileProg body) Sp (31 * rem + 22)
          (t_c, base + 11 * cur) () (t_e, base + 11 * target) := by
    intro rem
    induction rem with
    | zero =>
      intro cur hcur t_c heq_c hlen_c
      have hct : cur = target := by omega
      subst hct
      obtain ⟨t₁, heq₁, hlen₁, hrR⟩ :=
        ProgRuns_readSlot_raw s (Sp := Sp) (t := t_c) (pos := base + 11 * cur)
          (by simp only [Nat.max_eq_max]; omega)
      have hbs : QCSD_tapeRead t_c (base + 11 * cur + s.val) = true := by
        rw [heq_c, hslot cur (Nat.le_refl cur)]; simp
      rw [hbs] at hrR
      obtain ⟨t₂, heq₂, hlen₂, hrN⟩ :=
        ProgRuns_nop (Sp := Sp) (t := t₁) (h := base + 11 * cur)
          (by simp only [Nat.max_eq_max] at hlen₁ ⊢; omega)
      refine ⟨t₂, tapeEq_trans heq₂ (tapeEq_trans heq₁ heq_c),
        by simp only [Nat.max_eq_max] at hlen₂ hlen₁ ⊢; omega, ?_⟩
      rw [Nat.mul_zero, Nat.zero_add]
      apply ProgRuns_while_false
      exact ProgRuns_bind (k := fun found =>
        ifProg found
          (mapExitProg (fun _ => false) nopProg)
          (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.right 10)))
        hrR (ProgRuns_if_true
          (pF := mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.right 10))
          (ProgRuns_mapExit (fun _ => false) hrN))
    | succ rem ih =>
      intro cur hcur t_c heq_c hlen_c
      obtain ⟨t₁, heq₁, hlen₁, hrR⟩ :=
        ProgRuns_readSlot_raw s (Sp := Sp) (t := t_c) (pos := base + 11 * cur)
          (by simp only [Nat.max_eq_max]; omega)
      have hbs : QCSD_tapeRead t_c (base + 11 * cur + s.val) = false := by
        rw [heq_c, hslot cur (by omega)]; exact decide_eq_false (by omega)
      rw [hbs] at hrR
      obtain ⟨t₂, heq₂, hlen₂, hrM⟩ :=
        ProgRuns_moveRightPos 10 (Sp := Sp) (t := t₁) (h := base + 11 * cur)
          (by simp only [Nat.max_eq_max] at hlen₁ ⊢; omega)
      have hpos : base + 11 * cur + 10 + 1 = base + 11 * (cur + 1) := by omega
      rw [hpos] at hrM hlen₂
      obtain ⟨t_e, heq_e, hlen_e, hrRest⟩ :=
        ih (cur + 1) (by omega) t₂ (tapeEq_trans heq₂ (tapeEq_trans heq₁ heq_c))
          (by simp only [Nat.max_eq_max] at hlen₂ hlen₁ ⊢; omega)
      have hstep : ProgRuns body Sp 31 (t_c, base + 11 * cur) true (t₂, base + 11 * (cur + 1)) :=
        ProgRuns_bind (k := fun found =>
          ifProg found
            (mapExitProg (fun _ => false) nopProg)
            (mapExitProg (fun _ => true) (moveDirPosProg QCSD_HeadDir.right 10)))
          hrR (ProgRuns_if_false
            (pT := mapExitProg (fun _ => false) nopProg)
            (ProgRuns_mapExit (fun _ => true) hrM))
      exact ⟨t_e, heq_e, hlen_e,
        (ProgRuns_while_true hstep hrRest).mono (Nat.le_refl Sp) (by omega)⟩
  obtain ⟨t_e, heq_e, hlen_e, hr⟩ := hloop target 0 (Nat.zero_add target) t (tapeEq_refl t) hlen
  have hbz : base + 11 * 0 = base := by omega
  rw [hbz] at hr
  exact ⟨t_e, heq_e, hlen_e, hr⟩

def appendInZeroHighProg :=
  seqProg (seekSlotTrueHighProg ⟨9, by decide⟩)
    (seqProg (writeSlotProg ⟨2, by decide⟩ true)
      (seqProg (writeSlotProg ⟨9, by decide⟩ false)
        (seqProg (moveDirPosProg QCSD_HeadDir.right 10)
          (seqProg (writeSlotProg ⟨0, by decide⟩ true)
            (seqProg (writeSlotProg ⟨9, by decide⟩ true)
              flushRewindOrigProg)))))

lemma HighBlock_read_slot {base allocLen : ℕ} {inBits vSub : List Bool} {r wM : ℕ} {t : List Bool}
    (hb : HighBlock base allocLen inBits vSub r wM t) (i : ℕ) (s : Fin 11) :
    QCSD_tapeRead t (base + 11 * i + s.val) =
      slotVal allocLen inBits 0 [] [] vSub (some r) (some wM) i s.val := by
  rw [hb.2.2.2.2.2.2 _ (by omega)]
  have hs := s.isLt
  have hd : (base + 11 * i + s.val - base) / 11 = i := by omega
  have hm : (base + 11 * i + s.val - base) % 11 = s.val := by omega
  rw [hd, hm]

lemma ProgRuns_appendInZeroHigh {Sp base allocLen r wM : ℕ} {vSub t : List Bool}
    (hb : HighBlock base allocLen (List.replicate r false) vSub r wM t)
    (hsp : base + 11 * Nat.max allocLen (r + 2) ≤ Sp) :
    let aL' := Nat.max allocLen (r + 2)
    ∃ t' : List Bool,
      (∀ p < base, QCSD_tapeRead t' p = QCSD_tapeRead t p) ∧
      HighBlock base aL' (List.replicate (r + 1) false) vSub (r + 1) wM t' ∧
      ProgRuns appendInZeroHighProg Sp (62 * aL' + 150) (t, base) () (t', base) := by
  let aL' := Nat.max allocLen (r + 2)
  have haL_le : allocLen ≤ aL' := Nat.le_max_left _ _
  have hr2_le : r + 2 ≤ aL' := Nat.le_max_right _ _
  have hr_lt : r < allocLen := hb.2.2.2.1
  have hlen₀ : t.length ≤ base + 11 * allocLen := hb.2.2.2.2.2.1
  obtain ⟨t₁, heq₁, hlen₁, hs1⟩ :=
    ProgRuns_seekSlotTrueHigh ⟨9, by decide⟩ (Sp := Sp) hr_lt hlen₀
      (fun i hi => by
        rw [HighBlock_read_slot hb i ⟨9, by decide⟩]
        simp [slotVal, show i < allocLen by omega, eq_comm])
      (by omega)
  obtain ⟨t₂, hr₂_eq, hlen₂, hs2⟩ :=
    ProgRuns_writeSlot_raw ⟨2, by decide⟩ true (Sp := Sp) (t := t₁) (pos := base + 11 * r)
      (by simp only [Nat.max_eq_max]; omega)
  obtain ⟨t₃, hr₃_eq, hlen₃, hs3⟩ :=
    ProgRuns_writeSlot_raw ⟨9, by decide⟩ false (Sp := Sp) (t := t₂) (pos := base + 11 * r)
      (by simp only [Nat.max_eq_max] at hlen₂ ⊢; omega)
  obtain ⟨t₄, heq₄, hlen₄, hs4⟩ :=
    ProgRuns_moveRightPos 10 (Sp := Sp) (t := t₃) (h := base + 11 * r)
      (by simp only [Nat.max_eq_max] at hlen₃ hlen₂ ⊢; omega)
  have hpos1 : base + 11 * r + 10 + 1 = base + 11 * (r + 1) := by omega
  rw [hpos1] at hs4 hlen₄
  obtain ⟨t₅, hr₅_eq, hlen₅, hs5⟩ :=
    ProgRuns_writeSlot_raw ⟨0, by decide⟩ true (Sp := Sp) (t := t₄) (pos := base + 11 * (r + 1))
      (by simp only [Nat.max_eq_max] at hlen₄ hlen₃ hlen₂ ⊢; omega)
  obtain ⟨t₆, hr₆_eq, hlen₆, hs6⟩ :=
    ProgRuns_writeSlot_raw ⟨9, by decide⟩ true (Sp := Sp) (t := t₅) (pos := base + 11 * (r + 1))
      (by simp only [Nat.max_eq_max] at hlen₅ hlen₄ hlen₃ hlen₂ ⊢; omega)
  dsimp only at hr₂_eq hr₃_eq hr₅_eq hr₆_eq
  have ht₆_read : ∀ p, QCSD_tapeRead t₆ p =
      if p = base + 11 * (r + 1) + 9 then true
      else if p = base + 11 * (r + 1) + 0 then true
      else if p = base + 11 * r + 9 then false
      else if p = base + 11 * r + 2 then true
      else QCSD_tapeRead t p := by
    intro p
    rw [hr₆_eq p]
    by_cases hp1 : p = base + 11 * (r + 1) + 9
    · rw [ite_eq_left hp1, ite_eq_left hp1]
    · rw [ite_eq_right hp1, ite_eq_right hp1, hr₅_eq p]
      by_cases hp2 : p = base + 11 * (r + 1) + 0
      · rw [ite_eq_left hp2, ite_eq_left hp2]
      · rw [ite_eq_right hp2, ite_eq_right hp2, heq₄ p, hr₃_eq p]
        by_cases hp3 : p = base + 11 * r + 9
        · rw [ite_eq_left hp3, ite_eq_left hp3]
        · rw [ite_eq_right hp3, ite_eq_right hp3, hr₂_eq p]
          by_cases hp4 : p = base + 11 * r + 2
          · rw [ite_eq_left hp4, ite_eq_left hp4]
          · rw [ite_eq_right hp4, ite_eq_right hp4, heq₁ p]
  have hlen₆_aL : t₆.length ≤ base + 11 * aL' := by
    simp only [Nat.max_eq_max] at hlen₆ hlen₅ hlen₄ hlen₃ hlen₂ ⊢; omega
  obtain ⟨t', heq', hlen', hs7⟩ :=
    ProgRuns_flushRewindOrig (Sp := Sp) (base := base) (allocLen := aL') (cur := r + 1) (t := t₆)
      (by omega) hlen₆_aL
      (fun i hi => by
        rw [ht₆_read _, ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega), ite_eq_right (by omega),
            HighBlock_read_slot hb i ⟨1, by decide⟩]
        by_cases hlt : i < allocLen
        · simp [slotVal, hlt]
        · have hi_nz : i ≠ 0 := by have := hb.1; omega
          simp [slotVal, hlt, hi_nz])
      hsp
  refine ⟨t', ?_, ?_, ?_⟩
  · intro p hp
    rw [heq' p, ht₆_read p, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega)]
  · refine ⟨by omega, by simp, hb.2.2.1, by omega,
      Nat.lt_of_lt_of_le hb.2.2.2.2.1 haL_le, hlen', fun p hp => ?_⟩
    rw [heq' p, ht₆_read p]
    set bi := (p - base) / 11
    set bs := (p - base) % 11
    have hbs_lt : bs < 11 := Nat.mod_lt _ (by decide)
    have hp_dm : p = base + 11 * bi + bs := by
      have hdm := Nat.div_add_mod (p - base) 11
      change 11 * bi + bs = p - base at hdm; omega
    by_cases hc1 : p = base + 11 * (r + 1) + 9
    · rw [ite_eq_left hc1]
      have hbi : bi = r + 1 := by omega
      have hbs : bs = 9 := by omega
      rw [hbi, hbs]; unfold slotVal; rw [ite_eq_left (by omega)]; simp
    · rw [ite_eq_right hc1]
      by_cases hc2 : p = base + 11 * (r + 1) + 0
      · rw [ite_eq_left hc2]
        have hbi : bi = r + 1 := by omega
        have hbs : bs = 0 := by omega
        rw [hbi, hbs]; unfold slotVal; rw [ite_eq_left (by omega)]; simp
      · rw [ite_eq_right hc2]
        by_cases hc3 : p = base + 11 * r + 9
        · rw [ite_eq_left hc3]
          have hbi : bi = r := by omega
          have hbs : bs = 9 := by omega
          rw [hbi, hbs]; unfold slotVal; rw [ite_eq_left (by omega)]; simp
        · rw [ite_eq_right hc3]
          by_cases hc4 : p = base + 11 * r + 2
          · rw [ite_eq_left hc4]
            have hbi : bi = r := by omega
            have hbs : bs = 2 := by omega
            rw [hbi, hbs]; unfold slotVal; rw [ite_eq_left (by omega)]; simp
          · rw [ite_eq_right hc4, hb.2.2.2.2.2.2 p hp]
            change slotVal allocLen (List.replicate r false) 0 [] [] vSub (some r) (some wM) bi bs =
              slotVal aL' (List.replicate (r + 1) false) 0 [] [] vSub (some (r + 1)) (some wM) bi bs
            by_cases hbi_lt : bi < allocLen
            · have hbi_lt' : bi < aL' := by omega
              unfold slotVal
              rw [ite_eq_left hbi_lt, ite_eq_left hbi_lt']
              rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                           bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs
              · rw [hbs]; rfl
              · rw [hbs]; rfl
              · rw [hbs]; simp only [List.length_replicate]
                have hne_r : bi ≠ r := by omega
                have hiff : (bi < r) ↔ (bi < r + 1) := by omega
                simp [hiff]
              · rw [hbs]; simp [tapeRead_replicate_false]
              · rw [hbs]; rfl
              · rw [hbs]; rfl
              · rw [hbs]; rfl
              · rw [hbs]; rfl
              · rw [hbs]; rfl
              · rw [hbs]
                have hne1 : r ≠ bi := by omega
                have hne2 : r + 1 ≠ bi := by omega
                simp [hne1, hne2]
              · rw [hbs]; rfl
            · by_cases hbi_lt' : bi < aL'
              · have hbi_eq : bi = r + 1 := by
                  simp only [aL', Nat.max_eq_max] at hbi_lt'; omega
                have hbs_ne : bs ≠ 0 ∧ bs ≠ 9 := by omega
                have hwM_ne : wM ≠ r + 1 := by have := hb.2.2.2.2.1; omega
                have hvSub_f : QCSD_tapeRead vSub (r + 1) = false := by
                  unfold QCSD_tapeRead
                  have hge : vSub.length ≤ r + 1 := by have := hb.2.2.1; have := hb.2.2.2.2.1; omega
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
                unfold slotVal
                rw [ite_eq_right hbi_lt, ite_eq_left hbi_lt', hbi_eq]
                rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                             bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                  hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs
                · exact absurd hbs hbs_ne.1
                · rw [hbs]; simp
                · rw [hbs]; simp
                · rw [hbs]; simp [tapeRead_replicate_false]
                · rw [hbs]; simp
                · rw [hbs]; simp [QCSD_tapeRead]
                · rw [hbs]; simp
                · rw [hbs]; simp [QCSD_tapeRead]
                · rw [hbs]; exact hvSub_f.symm
                · exact absurd hbs hbs_ne.2
                · rw [hbs]; simp [hwM_ne]
              · simp [slotVal, hbi_lt, hbi_lt']
  · unfold appendInZeroHighProg
    exact (ProgRuns_seq hs1 (ProgRuns_seq hs2 (ProgRuns_seq hs3
      (ProgRuns_seq hs4 (ProgRuns_seq hs5 (ProgRuns_seq hs6 hs7)))))).mono
      (Nat.le_refl Sp) (by omega)

def appendSubHighProg (b : Bool) :=
  seqProg (seekSlotTrueHighProg ⟨10, by decide⟩)
    (seqProg (writeSlotProg ⟨8, by decide⟩ b)
      (seqProg (writeSlotProg ⟨10, by decide⟩ false)
        (seqProg (moveDirPosProg QCSD_HeadDir.right 10)
          (seqProg (writeSlotProg ⟨0, by decide⟩ true)
            (seqProg (writeSlotProg ⟨10, by decide⟩ true)
              flushRewindOrigProg)))))

lemma ProgRuns_appendSubHigh (b : Bool) {Sp base allocLen r wM : ℕ} {inBits vSub t : List Bool}
    (hb : HighBlock base allocLen inBits vSub r wM t)
    (hsp : base + 11 * Nat.max allocLen (wM + 2) ≤ Sp) :
    let aL' := Nat.max allocLen (wM + 2)
    ∃ t' : List Bool,
      (∀ p < base, QCSD_tapeRead t' p = QCSD_tapeRead t p) ∧
      HighBlock base aL' inBits (vSub ++ [b]) r (wM + 1) t' ∧
      ProgRuns (appendSubHighProg b) Sp (62 * aL' + 150) (t, base) () (t', base) := by
  let aL' := Nat.max allocLen (wM + 2)
  have haL_le : allocLen ≤ aL' := Nat.le_max_left _ _
  have hw2_le : wM + 2 ≤ aL' := Nat.le_max_right _ _
  have hw_lt : wM < allocLen := hb.2.2.2.2.1
  have hlen₀ : t.length ≤ base + 11 * allocLen := hb.2.2.2.2.2.1
  obtain ⟨t₁, heq₁, hlen₁, hs1⟩ :=
    ProgRuns_seekSlotTrueHigh ⟨10, by decide⟩ (Sp := Sp) hw_lt hlen₀
      (fun i hi => by
        rw [HighBlock_read_slot hb i ⟨10, by decide⟩]
        simp [slotVal, show i < allocLen by omega, eq_comm])
      (by omega)
  obtain ⟨t₂, hr₂_eq, hlen₂, hs2⟩ :=
    ProgRuns_writeSlot_raw ⟨8, by decide⟩ b (Sp := Sp) (t := t₁) (pos := base + 11 * wM)
      (by simp only [Nat.max_eq_max]; omega)
  obtain ⟨t₃, hr₃_eq, hlen₃, hs3⟩ :=
    ProgRuns_writeSlot_raw ⟨10, by decide⟩ false (Sp := Sp) (t := t₂) (pos := base + 11 * wM)
      (by simp only [Nat.max_eq_max] at hlen₂ ⊢; omega)
  obtain ⟨t₄, heq₄, hlen₄, hs4⟩ :=
    ProgRuns_moveRightPos 10 (Sp := Sp) (t := t₃) (h := base + 11 * wM)
      (by simp only [Nat.max_eq_max] at hlen₃ hlen₂ ⊢; omega)
  have hpos1 : base + 11 * wM + 10 + 1 = base + 11 * (wM + 1) := by omega
  rw [hpos1] at hs4 hlen₄
  obtain ⟨t₅, hr₅_eq, hlen₅, hs5⟩ :=
    ProgRuns_writeSlot_raw ⟨0, by decide⟩ true (Sp := Sp) (t := t₄) (pos := base + 11 * (wM + 1))
      (by simp only [Nat.max_eq_max] at hlen₄ hlen₃ hlen₂ ⊢; omega)
  obtain ⟨t₆, hr₆_eq, hlen₆, hs6⟩ :=
    ProgRuns_writeSlot_raw ⟨10, by decide⟩ true (Sp := Sp) (t := t₅) (pos := base + 11 * (wM + 1))
      (by simp only [Nat.max_eq_max] at hlen₅ hlen₄ hlen₃ hlen₂ ⊢; omega)
  dsimp only at hr₂_eq hr₃_eq hr₅_eq hr₆_eq
  have ht₆_read : ∀ p, QCSD_tapeRead t₆ p =
      if p = base + 11 * (wM + 1) + 10 then true
      else if p = base + 11 * (wM + 1) + 0 then true
      else if p = base + 11 * wM + 10 then false
      else if p = base + 11 * wM + 8 then b
      else QCSD_tapeRead t p := by
    intro p
    rw [hr₆_eq p]
    by_cases hp1 : p = base + 11 * (wM + 1) + 10
    · rw [ite_eq_left hp1, ite_eq_left hp1]
    · rw [ite_eq_right hp1, ite_eq_right hp1, hr₅_eq p]
      by_cases hp2 : p = base + 11 * (wM + 1) + 0
      · rw [ite_eq_left hp2, ite_eq_left hp2]
      · rw [ite_eq_right hp2, ite_eq_right hp2, heq₄ p, hr₃_eq p]
        by_cases hp3 : p = base + 11 * wM + 10
        · rw [ite_eq_left hp3, ite_eq_left hp3]
        · rw [ite_eq_right hp3, ite_eq_right hp3, hr₂_eq p]
          by_cases hp4 : p = base + 11 * wM + 8
          · rw [ite_eq_left hp4, ite_eq_left hp4]
          · rw [ite_eq_right hp4, ite_eq_right hp4, heq₁ p]
  have hlen₆_aL : t₆.length ≤ base + 11 * aL' := by
    simp only [Nat.max_eq_max] at hlen₆ hlen₅ hlen₄ hlen₃ hlen₂ ⊢; omega
  obtain ⟨t', heq', hlen', hs7⟩ :=
    ProgRuns_flushRewindOrig (Sp := Sp) (base := base) (allocLen := aL') (cur := wM + 1) (t := t₆)
      (by omega) hlen₆_aL
      (fun i hi => by
        rw [ht₆_read _, ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega), ite_eq_right (by omega),
            HighBlock_read_slot hb i ⟨1, by decide⟩]
        by_cases hlt : i < allocLen
        · simp [slotVal, hlt]
        · have hi_nz : i ≠ 0 := by have := hb.1; omega
          simp [slotVal, hlt, hi_nz])
      hsp
  refine ⟨t', ?_, ?_, ?_⟩
  · intro p hp
    rw [heq' p, ht₆_read p, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega)]
  · refine ⟨by omega, hb.2.1, by simp [hb.2.2.1],
      Nat.lt_of_lt_of_le hb.2.2.2.1 haL_le, by omega, hlen', fun p hp => ?_⟩
    rw [heq' p, ht₆_read p]
    set bi := (p - base) / 11
    set bs := (p - base) % 11
    have hbs_lt : bs < 11 := Nat.mod_lt _ (by decide)
    have hp_dm : p = base + 11 * bi + bs := by
      have hdm := Nat.div_add_mod (p - base) 11
      change 11 * bi + bs = p - base at hdm; omega
    by_cases hc1 : p = base + 11 * (wM + 1) + 10
    · rw [ite_eq_left hc1]
      have hbi : bi = wM + 1 := by omega
      have hbs : bs = 10 := by omega
      rw [hbi, hbs]; unfold slotVal; rw [ite_eq_left (by omega)]; simp
    · rw [ite_eq_right hc1]
      by_cases hc2 : p = base + 11 * (wM + 1) + 0
      · rw [ite_eq_left hc2]
        have hbi : bi = wM + 1 := by omega
        have hbs : bs = 0 := by omega
        rw [hbi, hbs]; unfold slotVal; rw [ite_eq_left (by omega)]; simp
      · rw [ite_eq_right hc2]
        by_cases hc3 : p = base + 11 * wM + 10
        · rw [ite_eq_left hc3]
          have hbi : bi = wM := by omega
          have hbs : bs = 10 := by omega
          rw [hbi, hbs]; unfold slotVal; rw [ite_eq_left (by omega)]; simp
        · rw [ite_eq_right hc3]
          by_cases hc4 : p = base + 11 * wM + 8
          · rw [ite_eq_left hc4]
            have hbi : bi = wM := by omega
            have hbs : bs = 8 := by omega
            have hvr : QCSD_tapeRead (vSub ++ [b]) wM = b := by
              rw [← hb.2.2.1]
              simpa using tapeRead_append_singleton vSub b vSub.length (Nat.lt_succ_self _)
            rw [hbi, hbs]; unfold slotVal; rw [ite_eq_left (by omega)]; simp [hvr]
          · rw [ite_eq_right hc4, hb.2.2.2.2.2.2 p hp]
            change slotVal allocLen inBits 0 [] [] vSub (some r) (some wM) bi bs =
              slotVal aL' inBits 0 [] [] (vSub ++ [b]) (some r) (some (wM + 1)) bi bs
            by_cases hbi_lt : bi < allocLen
            · have hbi_lt' : bi < aL' := by omega
              unfold slotVal
              rw [ite_eq_left hbi_lt, ite_eq_left hbi_lt']
              rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                           bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs
              · rw [hbs]; rfl
              · rw [hbs]; rfl
              · rw [hbs]; rfl
              · rw [hbs]; rfl
              · rw [hbs]; rfl
              · rw [hbs]; rfl
              · rw [hbs]; rfl
              · rw [hbs]; rfl
              · rw [hbs]
                change QCSD_tapeRead vSub bi = QCSD_tapeRead (vSub ++ [b]) bi
                have hne_w : bi ≠ wM := by omega
                by_cases hlt_v : bi < vSub.length
                · unfold QCSD_tapeRead
                  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                      List.getElem?_append_left hlt_v]
                · have hgt_v : vSub.length + 1 ≤ bi := by have := hb.2.2.1; omega
                  unfold QCSD_tapeRead
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
                      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
              · rw [hbs]; rfl
              · rw [hbs]
                have hne1 : wM ≠ bi := by omega
                have hne2 : wM + 1 ≠ bi := by omega
                simp [hne1, hne2]
            · by_cases hbi_lt' : bi < aL'
              · have hbi_eq : bi = wM + 1 := by
                  simp only [aL', Nat.max_eq_max] at hbi_lt'; omega
                have hbs_ne : bs ≠ 0 ∧ bs ≠ 10 := by omega
                have hr_ne : r ≠ wM + 1 := by have := hb.2.2.2.1; omega
                have hin_lt : ¬ wM + 1 < inBits.length := by
                  have := hb.2.1; have := hb.2.2.2.1; omega
                have hin_f : QCSD_tapeRead inBits (wM + 1) = false := by
                  unfold QCSD_tapeRead
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
                have hvSub_f : QCSD_tapeRead (vSub ++ [b]) (wM + 1) = false := by
                  unfold QCSD_tapeRead
                  have hge : (vSub ++ [b]).length ≤ wM + 1 := by simp [hb.2.2.1]
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
                unfold slotVal
                rw [ite_eq_right hbi_lt, ite_eq_left hbi_lt', hbi_eq]
                rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                             bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                  hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs | hbs
                · exact absurd hbs hbs_ne.1
                · rw [hbs]; simp
                · rw [hbs]; simp [hin_lt]
                · rw [hbs]; exact hin_f.symm
                · rw [hbs]; simp
                · rw [hbs]; simp [QCSD_tapeRead]
                · rw [hbs]; simp
                · rw [hbs]; simp [QCSD_tapeRead]
                · rw [hbs]; exact hvSub_f.symm
                · rw [hbs]; simp [hr_ne]
                · exact absurd hbs hbs_ne.2
              · simp [slotVal, hbi_lt, hbi_lt']
  · unfold appendSubHighProg
    exact (ProgRuns_seq hs1 (ProgRuns_seq hs2 (ProgRuns_seq hs3
      (ProgRuns_seq hs4 (ProgRuns_seq hs5 (ProgRuns_seq hs6 hs7)))))).mono
      (Nat.le_refl Sp) (by omega)

attribute [irreducible] appendInZeroHighProg appendSubHighProg

/-! ### Section 7b Part 2: Raw Input Draining, Reverse Copy & `rawInputToBlockTapeProg` -/

lemma HighBlock_of_highEq {base allocLen : ℕ} {inBits vSub : List Bool} {r wM : ℕ} {t₁ t₂ : List Bool}
    (hb : HighBlock base allocLen inBits vSub r wM t₁)
    (hlen : t₂.length ≤ base + 11 * allocLen)
    (hhigh : ∀ p, base ≤ p → QCSD_tapeRead t₂ p = QCSD_tapeRead t₁ p) :
    HighBlock base allocLen inBits vSub r wM t₂ :=
  ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hlen,
   fun p hp => (hhigh p hp).trans (hb.2.2.2.2.2.2 p hp)⟩

lemma HighBlock_base_true {base allocLen : ℕ} {inBits vSub : List Bool} {r wM : ℕ} {t : List Bool}
    (hb : HighBlock base allocLen inBits vSub r wM t) :
    QCSD_tapeRead t base = true := by
  have h := HighBlock_read_slot hb 0 ⟨0, by decide⟩
  have h0 : 0 < allocLen := hb.1
  simpa [slotVal, h0] using h

lemma HighBlock_to_BlockTape {base allocLen : ℕ} {inBits vSub : List Bool} {r wM : ℕ} {t : List Bool}
    (hb : HighBlock base allocLen inBits vSub r wM t)
    (hlow : ∀ p < base, QCSD_tapeRead t p = false) :
    BlockTape base allocLen inBits 0 [] [] vSub (some r) (some wM) t := by
  obtain ⟨h1, hin, hvs, hr, hw, hlen, hhigh⟩ := hb
  exact ⟨h1, by omega, Nat.zero_le _, Nat.le_refl 0, Nat.le_refl 0, by omega,
    fun r' hr' => by cases hr'; exact hr,
    fun w' hw' => by cases hw'; exact hw,
    hlen, hlow, hhigh⟩

lemma BlockTape_to_HighBlock {base allocLen : ℕ} {inBits vSub : List Bool} {r wM : ℕ} {t : List Bool}
    (hbt : BlockTape base allocLen inBits 0 [] [] vSub (some r) (some wM) t)
    (hin : inBits.length = r) (hvs : vSub.length = wM) :
    HighBlock base allocLen inBits vSub r wM t ∧ (∀ p < base, QCSD_tapeRead t p = false) := by
  obtain ⟨h1, _, _, _, _, _, hr, hw, hlen, hlow, hhigh⟩ := hbt
  exact ⟨⟨h1, hin, hvs, hr r rfl, hw wM rfl, hlen, hhigh⟩, hlow⟩

def RawSentinel (rawList : List Bool) (pos base : ℕ) (t : List Bool) : Prop :=
  rawList.length = pos ∧
  pos + 2 < base ∧
  (∀ p < pos, QCSD_tapeRead t p = QCSD_tapeRead rawList p) ∧
  QCSD_tapeRead t pos = true ∧
  (∀ p, pos < p → p < base → QCSD_tapeRead t p = false)

lemma RawSentinel_of_lowEq {rawList : List Bool} {pos base : ℕ} {t₁ t₂ : List Bool}
    (hrs : RawSentinel rawList pos base t₁)
    (hlow : ∀ p < base, QCSD_tapeRead t₂ p = QCSD_tapeRead t₁ p) :
    RawSentinel rawList pos base t₂ :=
  ⟨hrs.1, hrs.2.1,
   fun p hp => (hlow p (by have := hrs.2.1; omega)).trans (hrs.2.2.1 p hp),
   (hlow pos (by have := hrs.2.1; omega)).trans hrs.2.2.2.1,
   fun p hp1 hp2 => (hlow p hp2).trans (hrs.2.2.2.2 p hp1 hp2)⟩

lemma winPrefix_to_rawSentinel {w base : ℕ} {midRest t : List Bool}
    (hw : WinPrefix midRest.length w w midRest t)
    (hm_t : QCSD_tapeRead t (midRest.length + (2 * w + 3)) = true)
    (hmid : ∀ p, midRest.length + (2 * w + 3) < p → p < base → QCSD_tapeRead t p = false)
    (hm2 : midRest.length + (2 * w + 3) + 2 < base) :
    RawSentinel (midRest ++ [false, false] ++ List.replicate (2 * w) true ++ [false])
      (midRest.length + (2 * w + 3)) base t := by
  let raw := midRest ++ [false, false] ++ List.replicate (2 * w) true ++ [false]
  have hlen : raw.length = midRest.length + (2 * w + 3) := by simp [raw]
  refine ⟨hlen, hm2, fun p hp => ?_, hm_t, hmid⟩
  by_cases hp_m : p < midRest.length
  · rw [hw.2.2.1 p hp_m]
    unfold QCSD_tapeRead
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.append_assoc, List.append_assoc, List.getElem?_append_left hp_m]
  · set off := p - midRest.length
    have hp_eq : p = midRest.length + off := by omega
    have hoff : off < 2 * w + 3 := by omega
    rw [hp_eq, hw.2.2.2 off hoff]
    unfold QCSD_tapeRead
    rw [List.append_assoc, List.append_assoc, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega),
        show midRest.length + off - midRest.length = off by omega]
    by_cases h2 : off < 2
    · have h2' : off < ([false, false] : List Bool).length := by simp; omega
      rw [List.getElem?_append_left h2']
      rcases (show off = 0 ∨ off = 1 by omega) with h0 | h0 <;> (rw [h0]; simp [winCell])
    · rw [List.getElem?_append_right (by simp; omega),
          show off - ([false, false] : List Bool).length = off - 2 by rfl]
      by_cases hlt_w : off < 2 * w + 2
      · have hrep : off - 2 < (List.replicate (2 * w) true).length := by simp; omega
        rw [List.getElem?_append_left hrep, List.getElem?_eq_getElem hrep,
            Option.getD_some, List.getElem_replicate]
        unfold winCell
        rw [ite_eq_right h2, ite_eq_left hlt_w]
        split_ifs
        · rfl
        · exact decide_eq_true (by omega)
      · have hoff_end : off = 2 * w + 2 := by omega
        rw [hoff_end, List.getElem?_append_right (by simp),
            show 2 * w + 2 - 2 - (List.replicate (2 * w) true).length = 0 by simp]
        simp [winCell]

lemma ProgRuns_popRaw_step {Sp base aL r wM : ℕ} {xs inB vS t : List Bool} {b : Bool}
    (hrs : RawSentinel (xs ++ [b]) (xs.length + 1) base t)
    (hb : HighBlock base aL inB vS r wM t)
    (hsp : base + 11 * aL ≤ Sp) :
    ∃ t' : List Bool,
      RawSentinel xs xs.length base t' ∧
      HighBlock base aL inB vS r wM t' ∧
      ProgRuns popRawBitLeftProg Sp (2 * base + 12) (t, base) (true, b) (t', base) := by
  have h1 : 1 ≤ aL := hb.1
  have hlen₀ : t.length ≤ base + 11 * aL := hb.2.2.2.2.2.1
  obtain ⟨t', ht'_read, ht'_len, hrPop⟩ :=
    ProgRuns_popRawBitLeft (Sp := Sp) (pos := xs.length + 1) (base := base) (t := t)
      hrs.2.1 hrs.2.2.2.1 hrs.2.2.2.2 (HighBlock_base_true hb)
      (by simp only [Nat.max_eq_max]; omega)
  have hne0 : xs.length + 1 ≠ 0 := Nat.succ_ne_zero _
  have hsub : xs.length + 1 - 1 = xs.length := by omega
  have hb_eq : QCSD_tapeRead t xs.length = b := by
    rw [hrs.2.2.1 xs.length (Nat.lt_succ_self _)]
    simpa using tapeRead_append_singleton xs b xs.length (Nat.lt_succ_self _)
  rw [ite_eq_right hne0, hsub, hb_eq] at hrPop
  refine ⟨t', ?_, ?_, hrPop⟩
  · refine ⟨rfl, by have := hrs.2.1; omega, fun p hp => ?_, ?_, fun p hp1 hp2 => ?_⟩
    · rw [ht'_read p, ite_eq_right hne0, hsub, ite_eq_right (by omega),
          ite_eq_right (by omega), hrs.2.2.1 p (by omega)]
      unfold QCSD_tapeRead
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hp, ← List.getD_eq_getElem?_getD]
    · rw [ht'_read xs.length, ite_eq_right hne0, hsub, ite_eq_left rfl]
    · rw [ht'_read p, ite_eq_right hne0, hsub, ite_eq_right (by omega),
          ite_eq_left ⟨by omega, hp2⟩]
  · exact HighBlock_of_highEq hb (by simp only [Nat.max_eq_max] at ht'_len ⊢; omega)
      (fun p hp => by
        rw [ht'_read p, ite_eq_right hne0, hsub, ite_eq_right (by have := hrs.2.1; omega),
            ite_eq_right (by omega)])

lemma ProgRuns_popRaw_empty {Sp base aL r wM : ℕ} {inB vS t : List Bool}
    (hrs : RawSentinel [] 0 base t)
    (hb : HighBlock base aL inB vS r wM t)
    (hsp : base + 11 * aL ≤ Sp) :
    ∃ t' : List Bool,
      (∀ p < base, QCSD_tapeRead t' p = false) ∧
      HighBlock base aL inB vS r wM t' ∧
      ProgRuns popRawBitLeftProg Sp (2 * base + 12) (t, base) (false, false) (t', base) := by
  have h1 : 1 ≤ aL := hb.1
  have hlen₀ : t.length ≤ base + 11 * aL := hb.2.2.2.2.2.1
  obtain ⟨t', ht'_read, ht'_len, hrPop⟩ :=
    ProgRuns_popRawBitLeft (Sp := Sp) (pos := 0) (base := base) (t := t)
      hrs.2.1 hrs.2.2.2.1 hrs.2.2.2.2 (HighBlock_base_true hb)
      (by simp only [Nat.max_eq_max]; omega)
  rw [ite_eq_left rfl] at hrPop
  refine ⟨t', fun p hp => ?_, ?_, hrPop⟩
  · rw [ht'_read p, ite_eq_left rfl, ite_eq_left hp]
  · exact HighBlock_of_highEq hb (by simp only [Nat.max_eq_max] at ht'_len ⊢; omega)
      (fun p hp => by rw [ht'_read p, ite_eq_left rfl, ite_eq_right (by omega)])

def drainOnesLoopProg :=
  whileProg
    (bindProg popRawBitLeftProg (fun hb =>
      ifProg hb.2
        (mapExitProg (fun _ => true) appendInZeroHighProg)
        (mapExitProg (fun _ => false) nopProg)))

def drainMidRestLoopProg :=
  whileProg
    (bindProg popRawBitLeftProg (fun hb =>
      ifProg hb.1
        (mapExitProg (fun _ => true) (appendSubHighProg hb.2))
        (mapExitProg (fun _ => false) nopProg)))

def decRAndAppendTrueProg :=
  whileProg
    (seqProg (seekMarkProg ⟨9, by decide⟩)
      (bindProg (readSlotProg ⟨1, by decide⟩) (fun isOrig =>
        ifProg isOrig
          (mapExitProg (fun _ => false) nopProg)
          (seqProg (writeSlotProg ⟨9, by decide⟩ false)
            (seqProg moveBlockLeftProg
              (seqProg (writeSlotProg ⟨2, by decide⟩ false)
                (seqProg (writeSlotProg ⟨9, by decide⟩ true)
                  (seqProg rewindToBlock0Prog
                    (mapExitProg (fun _ => true) (appendSubHighProg true))))))))))

def drainRawToRevBlockRaw (remBool : Bool) :=
  seqProg (mapExitProg (fun _ => ()) popRawBitLeftProg)
    (seqProg drainOnesLoopProg
      (seqProg (mapExitProg (fun _ => ()) popRawBitLeftProg)
        (seqProg drainMidRestLoopProg
          (seqProg (ifProg remBool (appendSubHighProg true) (appendSubHighProg false))
            (seqProg (appendSubHighProg true)
              (seqProg (appendSubHighProg true)
                decRAndAppendTrueProg))))))

def DrainRawQ : Type := ProgState (drainRawToRevBlockRaw true)
instance : Fintype DrainRawQ := by
  unfold DrainRawQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance : DecidableEq DrainRawQ := by
  unfold DrainRawQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def drainRawToRevBlockProg (remBool : Bool) : Prog DrainRawQ Unit :=
  drainRawToRevBlockRaw remBool

lemma inp_reverse_eq_midRest (n : ℕ) (hn : 2 ≤ n) (rest : List Bool) :
    let w := (n - 2) / 2
    let remBool := decide ((n - 2) % 2 = 1)
    let midRest := (if remBool then [false] else []) ++ rest
    (QCSD_natToUnary n ++ rest).reverse =
      midRest.reverse ++ [remBool, true, true] ++ List.replicate (2 * w) true := by
  intro w remBool midRest
  have hinp_eq : QCSD_natToUnary n ++ rest =
      List.replicate (2 * w) true ++ [true, true, remBool] ++ midRest := by
    by_cases hm : (n - 2) % 2 = 1
    · have hrB : remBool = true := decide_eq_true hm
      have hn_eq : n = 2 * w + 3 := by dsimp [w] at *; omega
      dsimp [QCSD_natToUnary, midRest]
      rw [hrB, hn_eq]
      simp [List.replicate_add, List.append_assoc]
    · have hrB : remBool = false := decide_eq_false hm
      have hn_eq : n = 2 * w + 2 := by dsimp [w] at *; omega
      dsimp [QCSD_natToUnary, midRest]
      rw [hrB, hn_eq]
      simp [List.replicate_add, List.append_assoc]
  rw [hinp_eq, List.reverse_append, List.reverse_append, List.reverse_append, List.reverse_replicate]
  simp [List.append_assoc]

lemma ProgRuns_drainRawToRevBlock {Sp n : ℕ} {rest t₀ : List Bool}
    (hn : 2 ≤ n)
    (hw₀ : WinPrefix (((if decide ((n - 2) % 2 = 1) then [false] else []) ++ rest).length)
      ((n - 2) / 2) ((n - 2) / 2) ((if decide ((n - 2) % 2 = 1) then [false] else []) ++ rest) t₀)
    (hm_t : QCSD_tapeRead t₀ ((QCSD_natToUnary n ++ rest).length) = true)
    (hmid₀ : ∀ p, (QCSD_natToUnary n ++ rest).length < p →
      p < (QCSD_natToUnary n ++ rest).length + 4 + 2 * n → QCSD_tapeRead t₀ p = false)
    (hb₀ : HighBlock ((QCSD_natToUnary n ++ rest).length + 4 + 2 * n) 1 [] [] 0 0 t₀)
    (hsp : ((QCSD_natToUnary n ++ rest).length + 4 + 2 * n) +
      11 * ((QCSD_natToUnary n ++ rest).length + 4) ≤ Sp) :
    let inp := QCSD_natToUnary n ++ rest
    let m := inp.length
    let base := m + 4 + 2 * n
    let remBool := decide ((n - 2) % 2 = 1)
    ∃ (aL : ℕ) (t' : List Bool),
      m < aL ∧
      aL ≤ m + 4 ∧
      BlockTape base aL [] 0 [] [] inp.reverse (some 0) (some m) t' ∧
      ProgRuns (drainRawToRevBlockProg remBool) Sp
        ((2 * m + 10) * (2 * base + 200 * (m + 4) + 500))
        (t₀, base) () (t', base) := by
  let inp := QCSD_natToUnary n ++ rest
  let m := inp.length
  let w := (n - 2) / 2
  let remBool := decide ((n - 2) % 2 = 1)
  let midRest := (if remBool then [false] else []) ++ rest
  let base := m + 4 + 2 * n
  let aMax := m + 4
  have hsp_max : base + 11 * aMax ≤ Sp := hsp
  have hm_eq : midRest.length + (2 * w + 3) = m := by
    dsimp [midRest, m, inp, w, remBool, QCSD_natToUnary]
    by_cases hm : (n - 2) % 2 = 1 <;> simp [hm] <;> omega
  have hw_le : 2 * w + 2 ≤ n := by dsimp [w]; omega
  have hrs₀ : RawSentinel (midRest ++ [false, false] ++ List.replicate (2 * w) true ++ [false])
      m base t₀ := by
    have h := winPrefix_to_rawSentinel (base := base) hw₀ (by rw [hm_eq]; exact hm_t)
      (fun p hp1 hp2 => hmid₀ p (by dsimp only [midRest, w, remBool, m, inp] at hm_eq; omega) hp2)
      (by dsimp only [midRest, w, remBool, base, m, inp] at hm_eq ⊢; omega)
    rwa [hm_eq] at h
  -- Step 1: pop trailing false
  have hlen_p1 : (midRest ++ [false, false] ++ List.replicate (2 * w) true).length + 1 = m := by
    simp; omega
  rw [← hlen_p1] at hrs₀
  obtain ⟨t₁, hrs₁, hb₁, hs1⟩ :=
    ProgRuns_popRaw_step (Sp := Sp) hrs₀ hb₀ (by dsimp [aMax] at hsp_max; omega)
  have hs1' : ProgRuns (mapExitProg (fun _ => ()) popRawBitLeftProg) Sp (2 * base + 12)
      (t₀, base) () (t₁, base) := ProgRuns_mapExit (fun _ => ()) hs1
  -- Step 2: drain 2 * w ones into inBits = replicate (2 * w) false
  let stepCost := 2 * base + 200 * aMax + 500
  have hloopOnes : ∀ (rem r : ℕ), r + rem = 2 * w → ∀ (aL : ℕ) (t_c : List Bool),
      aL ≤ aMax →
      RawSentinel (midRest ++ [false, false] ++ List.replicate rem true)
        ((midRest ++ [false, false] ++ List.replicate rem true).length) base t_c →
      HighBlock base aL (List.replicate r false) [] r 0 t_c →
      ∃ (aL_e : ℕ) (t_e : List Bool),
        aL_e ≤ aMax ∧
        RawSentinel (midRest ++ [false]) (midRest.length + 1) base t_e ∧
        HighBlock base aL_e (List.replicate (2 * w) false) [] (2 * w) 0 t_e ∧
        ProgRuns drainOnesLoopProg Sp ((rem + 1) * stepCost) (t_c, base) () (t_e, base) := by
    intro rem
    induction rem with
    | zero =>
      intro r hr_eq aL t_c haL hrsc hbc
      have hr2w : r = 2 * w := by omega
      subst hr2w
      have hraw_eq : midRest ++ [false, false] ++ List.replicate 0 true =
          (midRest ++ [false]) ++ [false] := by simp [List.append_assoc]
      rw [hraw_eq] at hrsc
      have hlen_f : ((midRest ++ [false]) ++ [false]).length = (midRest ++ [false]).length + 1 := by simp
      rw [hlen_f] at hrsc
      obtain ⟨ta, hrsa, hba, hp1⟩ :=
        ProgRuns_popRaw_step (Sp := Sp) hrsc hbc (by omega)
      obtain ⟨tb, heqb, hlenb, hp2⟩ :=
        ProgRuns_nop (Sp := Sp) (t := ta) (h := base)
          (by have := hba.1; have := hba.2.2.2.2.2.1; simp only [Nat.max_eq_max]; omega)
      have hrsb := RawSentinel_of_lowEq hrsa (fun p _ => heqb p)
      have hbb := HighBlock_of_highEq hba
        (by have := hba.1; have := hba.2.2.2.2.2.1; simp only [Nat.max_eq_max] at hlenb ⊢; omega)
        (fun p _ => heqb p)
      have hm1_len : (midRest ++ [false]).length = midRest.length + 1 := by simp
      rw [hm1_len] at hrsb
      refine ⟨aL, tb, haL, hrsb, hbb, ?_⟩
      unfold drainOnesLoopProg
      exact (ProgRuns_while_false
        (ProgRuns_bind (k := fun hb =>
          ifProg hb.2
            (mapExitProg (fun _ => true) appendInZeroHighProg)
            (mapExitProg (fun _ => false) nopProg))
          hp1 (ProgRuns_if_false
            (pT := mapExitProg (fun _ => true) appendInZeroHighProg)
            (ProgRuns_mapExit (fun _ => false) hp2)))).mono
        (Nat.le_refl Sp) (by dsimp [stepCost]; omega)
    | succ rem ih =>
      intro r hr_eq aL t_c haL hrsc hbc
      have hraw_eq : midRest ++ [false, false] ++ List.replicate (rem + 1) true =
          (midRest ++ [false, false] ++ List.replicate rem true) ++ [true] := by
        simp only [List.replicate_succ', List.append_assoc]
      rw [hraw_eq] at hrsc
      have hlen_t : ((midRest ++ [false, false] ++ List.replicate rem true) ++ [true]).length =
          (midRest ++ [false, false] ++ List.replicate rem true).length + 1 := by simp; omega
      rw [hlen_t] at hrsc
      obtain ⟨ta, hrsa, hba, hp1⟩ :=
        ProgRuns_popRaw_step (Sp := Sp) hrsc hbc (by omega)
      have haL'_le : Nat.max aL (r + 2) ≤ aMax := by
        simp only [Nat.max_eq_max, aMax] at haL ⊢; omega
      obtain ⟨tb, hlowb, hbb, hp2⟩ :=
        ProgRuns_appendInZeroHigh (Sp := Sp) hba (by omega)
      have hrsb := RawSentinel_of_lowEq hrsa hlowb
      obtain ⟨aL_e, t_e, haL_e, hrs_e, hb_e, hrRest⟩ :=
        ih (r + 1) (by omega) (Nat.max aL (r + 2)) tb haL'_le hrsb hbb
      have hbody : ProgRuns
          (bindProg popRawBitLeftProg (fun hb =>
            ifProg hb.2
              (mapExitProg (fun _ => true) appendInZeroHighProg)
              (mapExitProg (fun _ => false) nopProg)))
          Sp stepCost (t_c, base) true (tb, base) :=
        (ProgRuns_bind (k := fun hb =>
          ifProg hb.2
            (mapExitProg (fun _ => true) appendInZeroHighProg)
            (mapExitProg (fun _ => false) nopProg))
          hp1 (ProgRuns_if_true
            (pF := mapExitProg (fun _ => false) nopProg)
            (ProgRuns_mapExit (fun _ => true) hp2))).mono
          (Nat.le_refl Sp) (by dsimp [stepCost]; omega)
      exact ⟨aL_e, t_e, haL_e, hrs_e, hb_e,
        (ProgRuns_while_true hbody hrRest).mono (Nat.le_refl Sp) (by nlinarith)⟩
  obtain ⟨aL₂, t₂, haL₂, hrs₂, hb₂, hs2⟩ :=
    hloopOnes (2 * w) 0 (Nat.zero_add _) 1 t₁ (by dsimp [aMax]; omega) hrs₁ hb₁
  -- Step 3: pop remaining false before midRest
  obtain ⟨t₃, hrs₃, hb₃, hs3_raw⟩ :=
    ProgRuns_popRaw_step (Sp := Sp) hrs₂ hb₂ (by omega)
  have hs3 : ProgRuns (mapExitProg (fun _ => ()) popRawBitLeftProg) Sp (2 * base + 12)
      (t₂, base) () (t₃, base) := ProgRuns_mapExit (fun _ => ()) hs3_raw
  -- Step 4: drain midRest in reverse into vSub
  have hloopMid : ∀ (xs : List Bool) (acc : List Bool) (aL : ℕ) (t_c : List Bool),
      acc.length + xs.length = midRest.length →
      aL ≤ aMax →
      RawSentinel xs xs.length base t_c →
      HighBlock base aL (List.replicate (2 * w) false) acc (2 * w) acc.length t_c →
      ∃ (aL_e : ℕ) (t_e : List Bool),
        aL_e ≤ aMax ∧
        (∀ p < base, QCSD_tapeRead t_e p = false) ∧
        HighBlock base aL_e (List.replicate (2 * w) false) (acc ++ xs.reverse)
          (2 * w) (acc.length + xs.length) t_e ∧
        ProgRuns drainMidRestLoopProg Sp ((xs.length + 1) * stepCost) (t_c, base) () (t_e, base) := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil =>
      intro acc aL t_c _ haL hrsc hbc
      simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.append_nil] at hrsc ⊢
      obtain ⟨ta, hlowa, hba, hp1⟩ :=
        ProgRuns_popRaw_empty (Sp := Sp) hrsc hbc (by omega)
      obtain ⟨tb, heqb, hlenb, hp2⟩ :=
        ProgRuns_nop (Sp := Sp) (t := ta) (h := base)
          (by have := hba.1; have := hba.2.2.2.2.2.1; simp only [Nat.max_eq_max]; omega)
      have hbb := HighBlock_of_highEq hba
        (by have := hba.1; have := hba.2.2.2.2.2.1; simp only [Nat.max_eq_max] at hlenb ⊢; omega)
        (fun p _ => heqb p)
      refine ⟨aL, tb, haL, fun p hp => (heqb p).trans (hlowa p hp), hbb, ?_⟩
      unfold drainMidRestLoopProg
      exact (ProgRuns_while_false
        (ProgRuns_bind (k := fun hb =>
          ifProg hb.1
            (mapExitProg (fun _ => true) (appendSubHighProg hb.2))
            (mapExitProg (fun _ => false) nopProg))
          hp1 (ProgRuns_if_false
            (pT := mapExitProg (fun _ => true) (appendSubHighProg false))
            (ProgRuns_mapExit (fun _ => false) hp2)))).mono
        (Nat.le_refl Sp) (by dsimp [stepCost]; omega)
    | append_singleton ys b ih =>
      intro acc aL t_c hlen_sum haL hrsc hbc
      have hlen_ys : (ys ++ [b]).length = ys.length + 1 := by simp
      rw [hlen_ys] at hrsc hlen_sum ⊢
      obtain ⟨ta, hrsa, hba, hp1⟩ :=
        ProgRuns_popRaw_step (Sp := Sp) hrsc hbc (by omega)
      have haL'_le : Nat.max aL (acc.length + 2) ≤ aMax := by
        simp only [Nat.max_eq_max, aMax] at haL ⊢; omega
      obtain ⟨tb, hlowb, hbb, hp2⟩ :=
        ProgRuns_appendSubHigh b (Sp := Sp) hba (by omega)
      have hrsb := RawSentinel_of_lowEq hrsa hlowb
      have hacc_len : (acc ++ [b]).length = acc.length + 1 := by simp
      rw [← hacc_len] at hbb
      obtain ⟨aL_e, t_e, haL_e, hlow_e, hb_e, hrRest⟩ :=
        ih (acc ++ [b]) (Nat.max aL (acc.length + 2)) tb (by omega) haL'_le hrsb hbb
      have hrev_eq : (acc ++ [b]) ++ ys.reverse = acc ++ (ys ++ [b]).reverse := by
        simp [List.append_assoc]
      have hsum_eq : (acc ++ [b]).length + ys.length = acc.length + (ys.length + 1) := by
        simp; omega
      rw [hrev_eq, hsum_eq] at hb_e
      have hbody : ProgRuns
          (bindProg popRawBitLeftProg (fun hb =>
            ifProg hb.1
              (mapExitProg (fun _ => true) (appendSubHighProg hb.2))
              (mapExitProg (fun _ => false) nopProg)))
          Sp stepCost (t_c, base) true (tb, base) :=
        (ProgRuns_bind (k := fun hb =>
          ifProg hb.1
            (mapExitProg (fun _ => true) (appendSubHighProg hb.2))
            (mapExitProg (fun _ => false) nopProg))
          hp1 (ProgRuns_if_true
            (pF := mapExitProg (fun _ => false) nopProg)
            (ProgRuns_mapExit (fun _ => true) hp2))).mono
          (Nat.le_refl Sp) (by dsimp [stepCost]; omega)
      exact ⟨aL_e, t_e, haL_e, hlow_e, hb_e,
        (ProgRuns_while_true hbody hrRest).mono (Nat.le_refl Sp) (by nlinarith)⟩
  obtain ⟨aL₄, t₄, haL₄, hlow₄, hb₄, hs4⟩ :=
    hloopMid midRest [] aL₂ t₃ (Nat.zero_add _) haL₂ hrs₃ hb₃
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hb₄
  -- Step 5: append [remBool, true, true]
  have haL₅_le : Nat.max aL₄ (midRest.length + 2) ≤ aMax := by
    simp only [Nat.max_eq_max, aMax] at haL₄ ⊢; omega
  have hStep5a : ∃ t₅ : List Bool,
      (∀ p < base, QCSD_tapeRead t₅ p = false) ∧
      HighBlock base (Nat.max aL₄ (midRest.length + 2))
        (List.replicate (2 * w) false) (midRest.reverse ++ [remBool])
        (2 * w) (midRest.length + 1) t₅ ∧
      ProgRuns (ifProg remBool (appendSubHighProg true) (appendSubHighProg false))
        Sp (62 * aMax + 150) (t₄, base) () (t₅, base) := by
    cases hrb : remBool
    · obtain ⟨t₅, hlow₅, hb₅, hr₅⟩ :=
        ProgRuns_appendSubHigh false (Sp := Sp) hb₄ (by omega)
      exact ⟨t₅, fun p hp => (hlow₅ p hp).trans (hlow₄ p hp), hb₅,
        (ProgRuns_if_false (pT := appendSubHighProg true) hr₅).mono
          (Nat.le_refl Sp) (by omega)⟩
    · obtain ⟨t₅, hlow₅, hb₅, hr₅⟩ :=
        ProgRuns_appendSubHigh true (Sp := Sp) hb₄ (by omega)
      exact ⟨t₅, fun p hp => (hlow₅ p hp).trans (hlow₄ p hp), hb₅,
        (ProgRuns_if_true (pF := appendSubHighProg false) hr₅).mono
          (Nat.le_refl Sp) (by omega)⟩
  obtain ⟨t₅, hlow₅, hb₅, hs5a⟩ := hStep5a
  let aL₅ := Nat.max aL₄ (midRest.length + 2)
  have haL₆_le : Nat.max aL₅ ((midRest.length + 1) + 2) ≤ aMax := by
    simp only [Nat.max_eq_max, aL₅, aMax] at haL₅_le hm_eq ⊢; omega
  obtain ⟨t₆, hlow₆_eq, hb₆, hs5b_raw⟩ :=
    ProgRuns_appendSubHigh true (Sp := Sp) hb₅
      (by simp only [Nat.max_eq_max, aL₅, aMax] at haL₆_le hsp_max ⊢; omega)
  have hlow₆ : ∀ p < base, QCSD_tapeRead t₆ p = false :=
    fun p hp => (hlow₆_eq p hp).trans (hlow₅ p hp)
  have hs5b := hs5b_raw.mono (Nat.le_refl Sp)
    (show 62 * Nat.max aL₅ _ + 150 ≤ 62 * aMax + 150 by
      simp only [Nat.max_eq_max, aL₅, aMax] at haL₆_le ⊢; omega)
  let aL₆ := Nat.max aL₅ ((midRest.length + 1) + 2)
  have haL₇_le : Nat.max aL₆ ((midRest.length + 1 + 1) + 2) ≤ aMax := by
    simp only [Nat.max_eq_max, aL₆, aL₅, aMax] at haL₆_le hm_eq ⊢; omega
  obtain ⟨t₇, hlow₇_eq, hb₇, hs5c_raw⟩ :=
    ProgRuns_appendSubHigh true (Sp := Sp) hb₆
      (by simp only [Nat.max_eq_max, aL₆, aL₅, aMax] at haL₇_le hsp_max ⊢; omega)
  have hlow₇ : ∀ p < base, QCSD_tapeRead t₇ p = false :=
    fun p hp => (hlow₇_eq p hp).trans (hlow₆ p hp)
  have hs5c := hs5c_raw.mono (Nat.le_refl Sp)
    (show 62 * Nat.max aL₆ _ + 150 ≤ 62 * aMax + 150 by
      simp only [Nat.max_eq_max, aL₆, aL₅, aMax] at haL₇_le ⊢; omega)
  let aL₇ := Nat.max aL₆ ((midRest.length + 1 + 1) + 2)
  -- Step 6: decRAndAppendTrueProg (2 * w iterations)
  have hloopDec : ∀ (r : ℕ) (vS : List Bool) (aL : ℕ) (t_c : List Bool),
      r ≤ 2 * w →
      vS.length + r = m →
      aL ≤ aMax →
      (∀ p < base, QCSD_tapeRead t_c p = false) →
      HighBlock base aL (List.replicate r false) vS r vS.length t_c →
      ∃ (aL_e : ℕ) (t_e : List Bool),
        aL_e ≤ aMax ∧
        BlockTape base aL_e [] 0 [] [] (vS ++ List.replicate r true) (some 0) (some m) t_e ∧
        ProgRuns decRAndAppendTrueProg Sp ((r + 1) * stepCost) (t_c, base) () (t_e, base) := by
    intro r
    induction r with
    | zero =>
      intro vS aL t_c _ hv_eq haL hlowc hbc
      simp only [Nat.add_zero, List.replicate_zero, List.append_nil] at hv_eq hbc ⊢
      have hbtc := HighBlock_to_BlockTape hbc hlowc
      have h0_lt : 0 < aL := hbc.1
      obtain ⟨ta, hbta, hp1⟩ := ProgRuns_seekRMark (Sp := Sp) hbtc h0_lt (by omega)
      obtain ⟨tb, hbtb, hp2⟩ := ProgRuns_readSlot ⟨1, by decide⟩ (Sp := Sp) hbta h0_lt (by omega)
      have hsv1 : slotVal aL [] 0 [] [] vS (some 0) (some vS.length) 0 1 = true := by
        simp [slotVal, h0_lt]
      rw [hsv1] at hp2
      have hbz : base + 11 * 0 = base := by omega
      rw [hbz] at hp2
      obtain ⟨tc, heqc, hlenc, hp3⟩ :=
        ProgRuns_nop (Sp := Sp) (t := tb) (h := base)
          (by have := hbtb.2.2.2.2.2.2.2.2.1; simp only [Nat.max_eq_max]; omega)
      have hbtc_end := BlockTape_of_tapeEq hbtb heqc
        (by have := hbtb.1; have := hbtb.2.2.2.2.2.2.2.2.1; simp only [Nat.max_eq_max] at hlenc ⊢; omega)
      rw [hv_eq] at hbtc_end
      refine ⟨aL, tc, haL, hbtc_end, ?_⟩
      unfold decRAndAppendTrueProg
      exact (ProgRuns_while_false
        (ProgRuns_seq hp1
          (ProgRuns_bind (k := fun isOrig =>
            ifProg isOrig
              (mapExitProg (fun _ => false) nopProg)
              (seqProg (writeSlotProg ⟨9, by decide⟩ false)
                (seqProg moveBlockLeftProg
                  (seqProg (writeSlotProg ⟨2, by decide⟩ false)
                    (seqProg (writeSlotProg ⟨9, by decide⟩ true)
                      (seqProg rewindToBlock0Prog
                        (mapExitProg (fun _ => true) (appendSubHighProg true))))))))
            hp2 (ProgRuns_if_true
              (pF := seqProg (writeSlotProg ⟨9, by decide⟩ false)
                (seqProg moveBlockLeftProg
                  (seqProg (writeSlotProg ⟨2, by decide⟩ false)
                    (seqProg (writeSlotProg ⟨9, by decide⟩ true)
                      (seqProg rewindToBlock0Prog
                        (mapExitProg (fun _ => true) (appendSubHighProg true)))))))
              (ProgRuns_mapExit (fun _ => false) hp3))))).mono
        (Nat.le_refl Sp) (by dsimp [stepCost]; omega)
    | succ r ih =>
      intro vS aL t_c hr_le hv_eq haL hlowc hbc
      have hbtc := HighBlock_to_BlockTape hbc hlowc
      have hr1_lt : r + 1 < aL := hbc.2.2.2.1
      have hr_lt : r < aL := by omega
      have hsp_aL : base + 11 * aL ≤ Sp := by omega
      obtain ⟨ta, hbta, hp1⟩ := ProgRuns_seekRMark (Sp := Sp) hbtc hr1_lt hsp_aL
      obtain ⟨tb, hbtb, hp2⟩ := ProgRuns_readSlot ⟨1, by decide⟩ (Sp := Sp) hbta hr1_lt hsp_aL
      have hsv1 : slotVal aL (List.replicate (r + 1) false) 0 [] [] vS
          (some (r + 1)) (some vS.length) (r + 1) 1 = false := by
        simp [slotVal, hr1_lt]
      rw [hsv1] at hp2
      obtain ⟨tc, hbtc', hp3⟩ :=
        ProgRuns_writeSlot_spec ⟨9, by decide⟩ false
          (inBits' := List.replicate (r + 1) false) (nLen' := 0) (cBits' := []) (preBits' := [])
          (vSub' := vS) (rMark' := none) (wMark' := some vS.length)
          hbtb hr1_lt hsp_aL hbtb.2.1 hbtb.2.2.1 hbtb.2.2.2.1 hbtb.2.2.2.2.1 hbtb.2.2.2.2.2.1
          (fun _ h => by cases h) hbtb.2.2.2.2.2.2.2.1
          (by simp [slotVal, hr1_lt])
          (fun bi hbi bs _ hne => by
            by_cases hbs9 : bs = 9
            · have hbi_ne : bi ≠ r + 1 := hne.resolve_right (fun h => h hbs9)
              rw [hbs9]; simp [slotVal, hbi, hbi_ne.symm]
            · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                           bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                first | exact absurd rfl hbs9 | simp only [slotVal, hbi, ↓reduceIte])
      obtain ⟨td, hbtd, hp4⟩ := ProgRuns_moveBlockLeft (Sp := Sp) hbtc' hr1_lt hsp_aL
      have hsub_r : r + 1 - 1 = r := by omega
      rw [hsub_r] at hp4
      obtain ⟨te, hbte, hp5⟩ :=
        ProgRuns_writeSlot_spec ⟨2, by decide⟩ false
          (inBits' := List.replicate r false) (nLen' := 0) (cBits' := []) (preBits' := [])
          (vSub' := vS) (rMark' := none) (wMark' := some vS.length)
          hbtd hr_lt hsp_aL (by simp; omega) hbtd.2.2.1 hbtd.2.2.2.1 hbtd.2.2.2.2.1 hbtd.2.2.2.2.2.1
          (fun _ h => by cases h) hbtd.2.2.2.2.2.2.2.1
          (by simp [slotVal, hr_lt])
          (fun bi hbi bs _ hne => by
            by_cases hbs2 : bs = 2
            · have hbi_ne : bi ≠ r := hne.resolve_right (fun h => h hbs2)
              rw [hbs2]; unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
              simp only [List.length_replicate]
              have hiff : (bi < r) ↔ (bi < r + 1) := by omega
              simp [hiff]
            · by_cases hbs3 : bs = 3
              · rw [hbs3]; unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
                simp [tapeRead_replicate_false]
              · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                             bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                  first | exact absurd rfl hbs2 | exact absurd rfl hbs3 | simp only [slotVal, hbi, ↓reduceIte])
      obtain ⟨tf, hbtf, hp6⟩ :=
        ProgRuns_writeSlot_spec ⟨9, by decide⟩ true
          (inBits' := List.replicate r false) (nLen' := 0) (cBits' := []) (preBits' := [])
          (vSub' := vS) (rMark' := some r) (wMark' := some vS.length)
          hbte hr_lt hsp_aL hbte.2.1 hbte.2.2.1 hbte.2.2.2.1 hbte.2.2.2.2.1 hbte.2.2.2.2.2.1
          (fun r' hr' => by cases hr'; exact hr_lt) hbte.2.2.2.2.2.2.2.1
          (by simp [slotVal, hr_lt])
          (fun bi hbi bs _ hne => by
            by_cases hbs9 : bs = 9
            · have hbi_ne : bi ≠ r := hne.resolve_right (fun h => h hbs9)
              rw [hbs9]; simp [slotVal, hbi, hbi_ne.symm]
            · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                           bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                first | exact absurd rfl hbs9 | simp only [slotVal, hbi, ↓reduceIte])
      obtain ⟨tg, hbtg, hp7⟩ := ProgRuns_rewindToBlock0 (Sp := Sp) hbtf hr_lt hsp_aL
      obtain ⟨hbg, hlowg⟩ := BlockTape_to_HighBlock hbtg (by simp) rfl
      have haL'_le : Nat.max aL (vS.length + 2) ≤ aMax := by
        simp only [Nat.max_eq_max, aMax] at haL ⊢; omega
      obtain ⟨th, hlowh_eq, hbh, hp8⟩ :=
        ProgRuns_appendSubHigh true (Sp := Sp) hbg (by omega)
      have hlowh : ∀ p < base, QCSD_tapeRead th p = false :=
        fun p hp => (hlowh_eq p hp).trans (hlowg p hp)
      have hv1_len : (vS ++ [true]).length = vS.length + 1 := by simp
      rw [← hv1_len] at hbh
      obtain ⟨aL_e, t_e, haL_e, hbt_e, hrRest⟩ :=
        ih (vS ++ [true]) (Nat.max aL (vS.length + 2)) th (by omega)
          (by rw [hv1_len]; omega) haL'_le hlowh hbh
      have hrep_eq : (vS ++ [true]) ++ List.replicate r true = vS ++ List.replicate (r + 1) true := by
        rw [List.append_assoc, List.replicate_succ]
        rfl
      rw [hrep_eq] at hbt_e
      have hbody : ProgRuns
          (seqProg (seekMarkProg ⟨9, by decide⟩)
            (bindProg (readSlotProg ⟨1, by decide⟩) (fun isOrig =>
              ifProg isOrig
                (mapExitProg (fun _ => false) nopProg)
                (seqProg (writeSlotProg ⟨9, by decide⟩ false)
                  (seqProg moveBlockLeftProg
                    (seqProg (writeSlotProg ⟨2, by decide⟩ false)
                      (seqProg (writeSlotProg ⟨9, by decide⟩ true)
                        (seqProg rewindToBlock0Prog
                          (mapExitProg (fun _ => true) (appendSubHighProg true))))))))))
          Sp stepCost (t_c, base) true (th, base) :=
        (ProgRuns_seq hp1
          (ProgRuns_bind (k := fun isOrig =>
            ifProg isOrig
              (mapExitProg (fun _ => false) nopProg)
              (seqProg (writeSlotProg ⟨9, by decide⟩ false)
                (seqProg moveBlockLeftProg
                  (seqProg (writeSlotProg ⟨2, by decide⟩ false)
                    (seqProg (writeSlotProg ⟨9, by decide⟩ true)
                      (seqProg rewindToBlock0Prog
                        (mapExitProg (fun _ => true) (appendSubHighProg true))))))))
            hp2 (ProgRuns_if_false
              (pT := mapExitProg (fun _ => false) nopProg)
              (ProgRuns_seq hp3 (ProgRuns_seq hp4 (ProgRuns_seq hp5
                (ProgRuns_seq hp6 (ProgRuns_seq hp7
                  (ProgRuns_mapExit (fun _ => true) hp8))))))))).mono
          (Nat.le_refl Sp) (by
            simp only [Nat.max_eq_max, stepCost, aMax] at haL'_le haL hv_eq ⊢; omega)
      exact ⟨aL_e, t_e, haL_e, hbt_e,
        (ProgRuns_while_true hbody hrRest).mono (Nat.le_refl Sp) (by nlinarith)⟩
  let vMid3 := ((midRest.reverse ++ [remBool]) ++ [true]) ++ [true]
  have hvMid3_len : vMid3.length = midRest.length + 1 + 1 + 1 := by simp [vMid3]
  have hb₇' : HighBlock base aL₇ (List.replicate (2 * w) false) vMid3 (2 * w) vMid3.length t₇ :=
    ⟨hb₇.1, hb₇.2.1, rfl, hb₇.2.2.2.1,
     by rw [hvMid3_len]; exact hb₇.2.2.2.2.1,
     hb₇.2.2.2.2.2.1,
     fun p hp => by rw [hb₇.2.2.2.2.2.2 p hp]; congr 3; exact hvMid3_len.symm⟩
  obtain ⟨aL', t', haL', hbt', hs6⟩ :=
    hloopDec (2 * w) vMid3 aL₇ t₇ (Nat.le_refl _) (by rw [hvMid3_len]; omega) haL₇_le hlow₇ hb₇'
  have hv_final : vMid3 ++ List.replicate (2 * w) true = inp.reverse := by
    have hrev := inp_reverse_eq_midRest n hn rest
    dsimp [vMid3, inp, w, remBool, midRest] at hrev ⊢
    rw [hrev]
    simp [List.append_assoc]
  rw [hv_final] at hbt'
  have hm_lt : m < aL' := hbt'.2.2.2.2.2.2.2.1 m rfl
  refine ⟨aL', t', hm_lt, haL', hbt', ?_⟩
  unfold drainRawToRevBlockProg drainRawToRevBlockRaw
  have hmid_le : midRest.length + 2 * w ≤ m := by omega
  exact (ProgRuns_seq hs1' (ProgRuns_seq hs2 (ProgRuns_seq hs3
    (ProgRuns_seq hs4 (ProgRuns_seq hs5a (ProgRuns_seq hs5b (ProgRuns_seq hs5c hs6))))))).mono
    (Nat.le_refl Sp) (by
      dsimp only [stepCost, aMax, base, m, inp] at *
      set L := (QCSD_natToUnary n ++ rest).length
      nlinarith)

attribute [irreducible] DrainRawQ drainRawToRevBlockProg

def revCopyStepBody :=
  seqProg (seekMarkProg ⟨10, by decide⟩)
    (bindProg (readSlotProg ⟨1, by decide⟩) (fun isOrig =>
      ifProg isOrig
        (seqProg (writeSlotProg ⟨10, by decide⟩ false)
          (seqProg (seekMarkProg ⟨9, by decide⟩)
            (mapExitProg (fun _ => false)
              (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog))))
        (seqProg (writeSlotProg ⟨10, by decide⟩ false)
          (seqProg moveBlockLeftProg
            (seqProg (writeSlotProg ⟨10, by decide⟩ true)
              (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
                seqProg rewindToBlock0Prog
                  (seqProg (seekMarkProg ⟨9, by decide⟩)
                    (seqProg (writeSlotProg ⟨2, by decide⟩ true)
                      (seqProg (writeSlotProg ⟨3, by decide⟩ b)
                        (mapExitProg (fun _ => true) (advanceMarkProg ⟨9, by decide⟩))))))))))))

def RevCopyQ : Type := ProgState (whileProg revCopyStepBody)
instance : Fintype RevCopyQ := by
  unfold RevCopyQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance : DecidableEq RevCopyQ := by
  unfold RevCopyQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def revCopySubToInProg : Prog RevCopyQ Unit := whileProg revCopyStepBody

lemma ProgRuns_revCopySubToIn {Sp base aL : ℕ} {inp t₀ : List Bool}
    (hbt₀ : BlockTape base aL [] 0 [] [] inp.reverse (some 0) (some inp.length) t₀)
    (hsp : base + 11 * aL ≤ Sp) :
    ∃ t' : List Bool,
      BlockTape base aL inp 0 [] [] inp.reverse none none t' ∧
      ProgRuns revCopySubToInProg Sp ((inp.length + 1) * (350 * aL + 400))
        (t₀, base) () (t', base) := by
  have hm_lt : inp.length < aL := hbt₀.2.2.2.2.2.2.2.1 inp.length rfl
  have h0_lt : 0 < aL := hbt₀.1
  let iterCost := 350 * aL + 400
  have hloop : ∀ (w r : ℕ), r + w = inp.length → ∀ t_c : List Bool,
      BlockTape base aL (inp.take r) 0 [] [] inp.reverse (some r) (some w) t_c →
      ∃ t_e : List Bool,
        BlockTape base aL inp 0 [] [] inp.reverse none none t_e ∧
        ProgRuns (whileProg revCopyStepBody) Sp ((w + 1) * iterCost) (t_c, base) () (t_e, base) := by
    intro w
    induction w with
    | zero =>
      intro r hr_eq t_c hbtc
      have hrm : r = inp.length := by omega
      subst hrm
      rw [List.take_length] at hbtc
      obtain ⟨ta, hbta, hp1⟩ := ProgRuns_seekWMark (Sp := Sp) hbtc h0_lt hsp
      obtain ⟨tb, hbtb, hp2⟩ := ProgRuns_readSlot ⟨1, by decide⟩ (Sp := Sp) hbta h0_lt hsp
      have hsv1 : slotVal aL inp 0 [] [] inp.reverse (some inp.length) (some 0) 0 1 = true := by
        simp [slotVal, h0_lt]
      rw [hsv1] at hp2
      obtain ⟨tc, hbtc', hp3⟩ :=
        ProgRuns_writeSlot_spec ⟨10, by decide⟩ false
          (inBits' := inp) (nLen' := 0) (cBits' := []) (preBits' := [])
          (vSub' := inp.reverse) (rMark' := some inp.length) (wMark' := none)
          hbtb h0_lt hsp hbtb.2.1 hbtb.2.2.1 hbtb.2.2.2.1 hbtb.2.2.2.2.1 hbtb.2.2.2.2.2.1
          hbtb.2.2.2.2.2.2.1 (fun _ h => by cases h)
          (by simp [slotVal, h0_lt])
          (fun bi hbi bs _ hne => by
            by_cases hbs10 : bs = 10
            · have hbi_ne : bi ≠ 0 := hne.resolve_right (fun h => h hbs10)
              rw [hbs10]; simp [slotVal, hbi, hbi_ne.symm]
            · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                           bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                first | exact absurd rfl hbs10 | simp only [slotVal, hbi, ↓reduceIte])
      have hbz : base + 11 * 0 = base := by omega
      rw [hbz] at hp3
      obtain ⟨td, hbtd, hp4⟩ := ProgRuns_seekRMark (Sp := Sp) hbtc' hm_lt hsp
      obtain ⟨te, hbte, hp5⟩ := ProgRuns_clearRMarkAndRewind (Sp := Sp) hbtd hm_lt hsp
      refine ⟨te, hbte, ?_⟩
      exact (ProgRuns_while_false (by
        unfold revCopyStepBody
        exact ProgRuns_seq hp1
          (ProgRuns_bind (k := fun isOrig =>
            ifProg isOrig
              (seqProg (writeSlotProg ⟨10, by decide⟩ false)
                (seqProg (seekMarkProg ⟨9, by decide⟩)
                  (mapExitProg (fun _ => false)
                    (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog))))
              (seqProg (writeSlotProg ⟨10, by decide⟩ false)
                (seqProg moveBlockLeftProg
                  (seqProg (writeSlotProg ⟨10, by decide⟩ true)
                    (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
                      seqProg rewindToBlock0Prog
                        (seqProg (seekMarkProg ⟨9, by decide⟩)
                          (seqProg (writeSlotProg ⟨2, by decide⟩ true)
                            (seqProg (writeSlotProg ⟨3, by decide⟩ b)
                              (mapExitProg (fun _ => true) (advanceMarkProg ⟨9, by decide⟩)))))))))))
            hp2 (ProgRuns_if_true
              (pF := seqProg (writeSlotProg ⟨10, by decide⟩ false)
                (seqProg moveBlockLeftProg
                  (seqProg (writeSlotProg ⟨10, by decide⟩ true)
                    (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
                      seqProg rewindToBlock0Prog
                        (seqProg (seekMarkProg ⟨9, by decide⟩)
                          (seqProg (writeSlotProg ⟨2, by decide⟩ true)
                            (seqProg (writeSlotProg ⟨3, by decide⟩ b)
                              (mapExitProg (fun _ => true) (advanceMarkProg ⟨9, by decide⟩))))))))))
              (ProgRuns_seq (by rw [hbz]; exact hp3)
                (ProgRuns_seq hp4 (ProgRuns_mapExit (fun _ => false) hp5))))))).mono
        (Nat.le_refl Sp) (by dsimp [iterCost]; omega)
    | succ w ih =>
      intro r hr_eq t_c hbtc
      have hw1_lt : w + 1 < aL := by omega
      have hw_lt : w < aL := by omega
      have hr_inp : r < inp.length := by omega
      have hr_lt : r < aL := by omega
      have hr1_lt : r + 1 < aL := by omega
      obtain ⟨ta, hbta, hp1⟩ := ProgRuns_seekWMark (Sp := Sp) hbtc hw1_lt hsp
      obtain ⟨tb, hbtb, hp2⟩ := ProgRuns_readSlot ⟨1, by decide⟩ (Sp := Sp) hbta hw1_lt hsp
      have hsv1 : slotVal aL (inp.take r) 0 [] [] inp.reverse (some r) (some (w + 1)) (w + 1) 1 = false := by
        simp [slotVal, hw1_lt]
      rw [hsv1] at hp2
      obtain ⟨tc, hbtc', hp3⟩ :=
        ProgRuns_writeSlot_spec ⟨10, by decide⟩ false
          (inBits' := inp.take r) (nLen' := 0) (cBits' := []) (preBits' := [])
          (vSub' := inp.reverse) (rMark' := some r) (wMark' := none)
          hbtb hw1_lt hsp hbtb.2.1 hbtb.2.2.1 hbtb.2.2.2.1 hbtb.2.2.2.2.1 hbtb.2.2.2.2.2.1
          hbtb.2.2.2.2.2.2.1 (fun _ h => by cases h)
          (by simp [slotVal, hw1_lt])
          (fun bi hbi bs _ hne => by
            by_cases hbs10 : bs = 10
            · have hbi_ne : bi ≠ w + 1 := hne.resolve_right (fun h => h hbs10)
              rw [hbs10]; simp [slotVal, hbi, hbi_ne.symm]
            · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                           bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                first | exact absurd rfl hbs10 | simp only [slotVal, hbi, ↓reduceIte])
      obtain ⟨td, hbtd, hp4⟩ := ProgRuns_moveBlockLeft (Sp := Sp) hbtc' hw1_lt hsp
      have hsub_w : w + 1 - 1 = w := by omega
      rw [hsub_w] at hp4
      obtain ⟨te, hbte, hp5⟩ :=
        ProgRuns_writeSlot_spec ⟨10, by decide⟩ true
          (inBits' := inp.take r) (nLen' := 0) (cBits' := []) (preBits' := [])
          (vSub' := inp.reverse) (rMark' := some r) (wMark' := some w)
          hbtd hw_lt hsp hbtd.2.1 hbtd.2.2.1 hbtd.2.2.2.1 hbtd.2.2.2.2.1 hbtd.2.2.2.2.2.1
          hbtd.2.2.2.2.2.2.1 (fun w' hw' => by cases hw'; exact hw_lt)
          (by simp [slotVal, hw_lt])
          (fun bi hbi bs _ hne => by
            by_cases hbs10 : bs = 10
            · have hbi_ne : bi ≠ w := hne.resolve_right (fun h => h hbs10)
              rw [hbs10]; simp [slotVal, hbi, hbi_ne.symm]
            · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                           bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                first | exact absurd rfl hbs10 | simp only [slotVal, hbi, ↓reduceIte])
      obtain ⟨tf, hbtf, hp6⟩ := ProgRuns_readSlot ⟨8, by decide⟩ (Sp := Sp) hbte hw_lt hsp
      have hw_rev : w < inp.reverse.length := by simp; omega
      have hsv8 : slotVal aL (inp.take r) 0 [] [] inp.reverse (some r) (some w) w 8 = inp[r] := by
        unfold slotVal
        rw [ite_eq_left hw_lt]
        change QCSD_tapeRead inp.reverse w = inp[r]
        unfold QCSD_tapeRead
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw_rev, Option.getD_some,
            List.getElem_reverse]
        congr 1; omega
      rw [hsv8] at hp6
      obtain ⟨tg, hbtg, hp7⟩ := ProgRuns_rewindToBlock0 (Sp := Sp) hbtf hw_lt hsp
      obtain ⟨th, hbth, hp8⟩ := ProgRuns_seekRMark (Sp := Sp) hbtg hr_lt hsp
      have htake_len : (inp.take r).length = r := by simp [Nat.min_eq_left (Nat.le_of_lt hr_inp)]
      obtain ⟨ti, hbti, hp9⟩ :=
        ProgRuns_writeSlot_spec ⟨2, by decide⟩ true
          (inBits' := inp.take r ++ [false]) (nLen' := 0) (cBits' := []) (preBits' := [])
          (vSub' := inp.reverse) (rMark' := some r) (wMark' := some w)
          hbth hr_lt hsp (by simp [htake_len]; omega) hbth.2.2.1 hbth.2.2.2.1 hbth.2.2.2.2.1
          hbth.2.2.2.2.2.1 hbth.2.2.2.2.2.2.1 hbth.2.2.2.2.2.2.2.1
          (by simp [slotVal, hr_lt, htake_len])
          (fun bi hbi bs _ hne => by
            by_cases hbs2 : bs = 2
            · have hbi_ne : bi ≠ r := hne.resolve_right (fun h => h hbs2)
              rw [hbs2]; unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
              simp only [List.length_append, List.length_singleton, htake_len]
              have hiff : (bi < r + 1) ↔ (bi < r) := by omega
              simp [hiff]
            · by_cases hbs3 : bs = 3
              · rw [hbs3]; unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
                exact tapeRead_append_replicate_false (inp.take r) 1 bi
              · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                             bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                  first | exact absurd rfl hbs2 | exact absurd rfl hbs3 | simp only [slotVal, hbi, ↓reduceIte])
      have htake_succ : inp.take (r + 1) = inp.take r ++ [inp[r]] :=
        (List.take_concat_get' inp r hr_inp).symm
      obtain ⟨tj, hbtj, hp10⟩ :=
        ProgRuns_writeSlot_spec ⟨3, by decide⟩ inp[r]
          (inBits' := inp.take (r + 1)) (nLen' := 0) (cBits' := []) (preBits' := [])
          (vSub' := inp.reverse) (rMark' := some r) (wMark' := some w)
          hbti hr_lt hsp (by simp; omega) hbti.2.2.1 hbti.2.2.2.1 hbti.2.2.2.2.1
          hbti.2.2.2.2.2.1 hbti.2.2.2.2.2.2.1 hbti.2.2.2.2.2.2.2.1
          (by
            rw [htake_succ]
            unfold slotVal; rw [ite_eq_left hr_lt]
            have hvr := tapeRead_append_singleton (inp.take r) inp[r] r (by rw [htake_len]; omega)
            rw [htake_len, ite_eq_left rfl] at hvr
            exact hvr)
          (fun bi hbi bs _ hne => by
            by_cases hbs3 : bs = 3
            · have hbi_ne : bi ≠ r := hne.resolve_right (fun h => h hbs3)
              rw [hbs3, htake_succ]; unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
              change QCSD_tapeRead (inp.take r ++ [inp[r]]) bi =
                QCSD_tapeRead (inp.take r ++ [false]) bi
              by_cases hlt_r : bi < r
              · have hlt_t : bi < (inp.take r).length := by rw [htake_len]; exact hlt_r
                unfold QCSD_tapeRead
                rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt_t,
                    List.getD_eq_getElem?_getD, List.getElem?_append_left hlt_t]
              · have hge1 : (inp.take r ++ [inp[r]]).length ≤ bi := by simp; omega
                have hge2 : (inp.take r ++ [false]).length ≤ bi := by simp [htake_len]; omega
                unfold QCSD_tapeRead
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
                    List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
            · by_cases hbs2 : bs = 2
              · rw [hbs2]; unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
                simp [htake_len, Nat.min_eq_left (show r + 1 ≤ inp.length by omega)]
              · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                             bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                  first | exact absurd rfl hbs3 | exact absurd rfl hbs2 | simp only [slotVal, hbi, ↓reduceIte])
      obtain ⟨tk, hbtk, hp11⟩ := ProgRuns_advanceRMark (Sp := Sp) hbtj hr1_lt hsp
      obtain ⟨t_e, hbt_e, hrRest⟩ := ih (r + 1) (by omega) tk hbtk
      have hbody : ProgRuns revCopyStepBody Sp iterCost (t_c, base) true (tk, base) :=
        (ProgRuns_seq hp1
          (ProgRuns_bind (k := fun isOrig =>
            ifProg isOrig
              (seqProg (writeSlotProg ⟨10, by decide⟩ false)
                (seqProg (seekMarkProg ⟨9, by decide⟩)
                  (mapExitProg (fun _ => false)
                    (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog))))
              (seqProg (writeSlotProg ⟨10, by decide⟩ false)
                (seqProg moveBlockLeftProg
                  (seqProg (writeSlotProg ⟨10, by decide⟩ true)
                    (bindProg (readSlotProg ⟨8, by decide⟩) (fun b =>
                      seqProg rewindToBlock0Prog
                        (seqProg (seekMarkProg ⟨9, by decide⟩)
                          (seqProg (writeSlotProg ⟨2, by decide⟩ true)
                            (seqProg (writeSlotProg ⟨3, by decide⟩ b)
                              (mapExitProg (fun _ => true) (advanceMarkProg ⟨9, by decide⟩)))))))))))
            hp2 (ProgRuns_if_false
              (pT := seqProg (writeSlotProg ⟨10, by decide⟩ false)
                (seqProg (seekMarkProg ⟨9, by decide⟩)
                  (mapExitProg (fun _ => false)
                    (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog))))
              (ProgRuns_seq hp3 (ProgRuns_seq hp4 (ProgRuns_seq hp5
                (ProgRuns_bind (k := fun b =>
                  seqProg rewindToBlock0Prog
                    (seqProg (seekMarkProg ⟨9, by decide⟩)
                      (seqProg (writeSlotProg ⟨2, by decide⟩ true)
                        (seqProg (writeSlotProg ⟨3, by decide⟩ b)
                          (mapExitProg (fun _ => true) (advanceMarkProg ⟨9, by decide⟩))))))
                  hp6 (ProgRuns_seq hp7 (ProgRuns_seq hp8 (ProgRuns_seq hp9
                    (ProgRuns_seq hp10 (ProgRuns_mapExit (fun _ => true) hp11)))))))))))).mono
          (Nat.le_refl Sp) (by dsimp [iterCost]; omega)
      exact ⟨t_e, hbt_e,
        (ProgRuns_while_true hbody hrRest).mono (Nat.le_refl Sp) (by nlinarith)⟩
  exact hloop inp.length 0 (Nat.zero_add _) t₀ (by simpa using hbt₀)

attribute [irreducible] RevCopyQ revCopySubToInProg

def incNLenProg :=
  seqProg (seekMarkProg ⟨10, by decide⟩)
    (seqProg (writeSlotProg ⟨4, by decide⟩ true)
      (advanceMarkProg ⟨10, by decide⟩))

lemma ProgRuns_incNLen {Sp base aL k : ℕ} {inp : List Bool} {rMark : Option ℕ} {t : List Bool}
    (hbt : BlockTape base aL inp k [] [] [] rMark (some k) t)
    (hk1 : k + 1 < aL)
    (hsp : base + 11 * aL ≤ Sp) :
    ∃ t' : List Bool,
      BlockTape base aL inp (k + 1) [] [] [] rMark (some (k + 1)) t' ∧
      ProgRuns incNLenProg Sp (150 * aL + 200) (t, base) () (t', base) := by
  have hk_lt : k < aL := by omega
  obtain ⟨t₁, hbt₁, hr₁⟩ := ProgRuns_seekWMark (Sp := Sp) hbt hk_lt hsp
  obtain ⟨t₂, hbt₂, hr₂⟩ :=
    ProgRuns_writeSlot_spec ⟨4, by decide⟩ true
      (inBits' := inp) (nLen' := k + 1) (cBits' := []) (preBits' := [])
      (vSub' := []) (rMark' := rMark) (wMark' := some k)
      hbt₁ hk_lt hsp hbt₁.2.1 (by omega) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      hbt₁.2.2.2.2.2.2.1 hbt₁.2.2.2.2.2.2.2.1
      (by simp [slotVal, hk_lt])
      (fun bi hbi bs _ hne => by
        by_cases hbs4 : bs = 4
        · have hbi_ne : bi ≠ k := hne.resolve_right (fun h => h hbs4)
          rw [hbs4]; unfold slotVal; rw [ite_eq_left hbi, ite_eq_left hbi]
          have hiff : (bi < k + 1) ↔ (bi < k) := by omega
          simp [hiff]
        · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                       bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact absurd rfl hbs4 | simp only [slotVal, hbi, ↓reduceIte])
  obtain ⟨t₃, hbt₃, hr₃⟩ := ProgRuns_advanceWMark (Sp := Sp) hbt₂ hk1 hsp
  exact ⟨t₃, hbt₃, (ProgRuns_seq hr₁ (ProgRuns_seq hr₂ hr₃)).mono (Nat.le_refl Sp) (by omega)⟩

def initNLenBody :=
  seqProg (seekMarkProg ⟨9, by decide⟩)
    (bindProg (readSlotProg ⟨3, by decide⟩) (fun b =>
      ifProg b
        (seqProg (advanceMarkProg ⟨9, by decide⟩)
          (seqProg incNLenProg
            (mapExitProg (fun _ => true) incNLenProg)))
        (seqProg (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog)
          (seqProg (seekMarkProg ⟨10, by decide⟩)
            (mapExitProg (fun _ => false)
              (seqProg (writeSlotProg ⟨10, by decide⟩ false) rewindToBlock0Prog))))))

def preAllocBody :=
  seqProg (seekMarkProg ⟨9, by decide⟩)
    (bindProg (readSlotProg ⟨4, by decide⟩) (fun hasN =>
      ifProg hasN
        (seqProg (advanceMarkProg ⟨9, by decide⟩)
          (seqProg clearSubTapeProg
            (seqProg clearSubTapeProg
              (mapExitProg (fun _ => true) clearSubTapeProg))))
        (mapExitProg (fun _ => false)
          (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog))))

def initNMarkAndAllocRaw :=
  seqProg clearSubTapeProg
    (seqProg (writeSlotProg ⟨9, by decide⟩ true)
      (seqProg (writeSlotProg ⟨10, by decide⟩ true)
        (seqProg (whileProg initNLenBody)
          (seqProg (writeSlotProg ⟨9, by decide⟩ true)
            (whileProg preAllocBody)))))

def InitNAllocQ : Type := ProgState initNMarkAndAllocRaw
instance : Fintype InitNAllocQ := by
  unfold InitNAllocQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance : DecidableEq InitNAllocQ := by
  unfold InitNAllocQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def initNMarkAndAllocProg : Prog InitNAllocQ Unit := initNMarkAndAllocRaw

lemma ProgRuns_initNMarkAndAlloc {Sp base aL n : ℕ} {rest t₀ : List Bool}
    (hn : 2 ≤ n)
    (hrest_ge : 2 * n ≤ rest.length)
    (hbt₀ : BlockTape base aL (QCSD_natToUnary n ++ rest) 0 [] []
      (QCSD_natToUnary n ++ rest).reverse none none t₀)
    (hm_lt : (QCSD_natToUnary n ++ rest).length < aL)
    (hsp : base + 11 * (aL + 6 * n + 2) ≤ Sp) :
    let inp := QCSD_natToUnary n ++ rest
    ∃ t' : List Bool,
      inp.length + 4 * n + 3 ≤ aL + 1 + 6 * n ∧
      BlockTape base (aL + 1 + 6 * n) inp (2 * n) [] [] [] none none t' ∧
      ProgRuns initNMarkAndAllocProg Sp
        ((3 * n + 4) * (500 * (aL + 6 * n + 2) + 800))
        (t₀, base) () (t', base) := by
  let inp := QCSD_natToUnary n ++ rest
  have hinp_len : n + 1 + rest.length = inp.length := by simp [inp, QCSD_natToUnary]; omega
  have h2n_lt : 2 * n < aL + 1 := by dsimp only [inp] at hinp_len; omega
  have hsp1 : base + 11 * (aL + 1) ≤ Sp := by omega
  obtain ⟨t₁, hbt₁, hs1⟩ := ProgRuns_clearSubTape (Sp := Sp) hbt₀ hsp1
  let aL₁ := aL + 1
  obtain ⟨t₂, hbt₂, hs2⟩ := ProgRuns_setRMark0 (Sp := Sp) hbt₁ hsp1
  obtain ⟨t₃, hbt₃, hs3⟩ := ProgRuns_setWMark0 (Sp := Sp) hbt₂ hsp1
  let stepCost := 500 * (aL + 6 * n + 2) + 800
  have hinp_unary : ∀ r ≤ n, QCSD_tapeRead inp r = decide (r < n) := by
    intro r hr
    unfold QCSD_tapeRead
    dsimp [inp, QCSD_natToUnary]
    rw [List.append_assoc, List.getD_eq_getElem?_getD]
    by_cases hlt : r < n
    · have hrep : r < (List.replicate n true).length := by simpa using hlt
      rw [List.getElem?_append_left hrep]
      simp [hlt]
    · have hrn : r = n := by omega
      subst hrn
      rw [List.getElem?_append_right (by simp)]
      simp
  have hloopN : ∀ (rem r : ℕ), r + rem = n → ∀ t_c : List Bool,
      BlockTape base aL₁ inp (2 * r) [] [] [] (some r) (some (2 * r)) t_c →
      ∃ t_e : List Bool,
        BlockTape base aL₁ inp (2 * n) [] [] [] none none t_e ∧
        ProgRuns (whileProg initNLenBody) Sp ((rem + 1) * stepCost) (t_c, base) () (t_e, base) := by
    intro rem
    induction rem with
    | zero =>
      intro r hr_eq t_c hbtc
      have hrn : r = n := by omega
      subst hrn
      have hn_lt : r < aL₁ := by dsimp [aL₁]; omega
      have h2r_lt : 2 * r < aL₁ := h2n_lt
      obtain ⟨ta, hbta, hp1⟩ := ProgRuns_seekRMark (Sp := Sp) hbtc hn_lt hsp1
      obtain ⟨tb, hbtb, hp2⟩ := ProgRuns_readSlot ⟨3, by decide⟩ (Sp := Sp) hbta hn_lt hsp1
      have hsv3 : slotVal aL₁ inp (2 * r) [] [] [] (some r) (some (2 * r)) r 3 = false := by
        unfold slotVal; rw [ite_eq_left hn_lt]
        rw [hinp_unary r (Nat.le_refl r)]; simp
      rw [hsv3] at hp2
      obtain ⟨tc, hbtc', hp3⟩ := ProgRuns_clearRMarkAndRewind (Sp := Sp) hbtb hn_lt hsp1
      obtain ⟨td, hbtd, hp4⟩ := ProgRuns_seekWMark (Sp := Sp) hbtc' h2r_lt hsp1
      obtain ⟨te, hbte, hp5⟩ :=
        ProgRuns_writeSlot_spec ⟨10, by decide⟩ false
          (inBits' := inp) (nLen' := 2 * r) (cBits' := []) (preBits' := [])
          (vSub' := []) (rMark' := none) (wMark' := none)
          hbtd h2r_lt hsp1 hbtd.2.1 hbtd.2.2.1 hbtd.2.2.2.1 hbtd.2.2.2.2.1 hbtd.2.2.2.2.2.1
          hbtd.2.2.2.2.2.2.1 (fun _ h => by cases h)
          (by simp [slotVal, h2r_lt])
          (fun bi hbi bs _ hne => by
            by_cases hbs10 : bs = 10
            · have hbi_ne : bi ≠ 2 * r := hne.resolve_right (fun h => h hbs10)
              rw [hbs10]; simp [slotVal, hbi, hbi_ne.symm]
            · rcases (show bs = 0 ∨ bs = 1 ∨ bs = 2 ∨ bs = 3 ∨ bs = 4 ∨ bs = 5 ∨
                           bs = 6 ∨ bs = 7 ∨ bs = 8 ∨ bs = 9 ∨ bs = 10 by omega) with
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                first | exact absurd rfl hbs10 | simp only [slotVal, hbi, ↓reduceIte])
      obtain ⟨tf, hbtf, hp6⟩ := ProgRuns_rewindToBlock0 (Sp := Sp) hbte h2r_lt hsp1
      refine ⟨tf, hbtf, ?_⟩
      exact (ProgRuns_while_false (by
        unfold initNLenBody
        exact ProgRuns_seq hp1
          (ProgRuns_bind (k := fun b =>
            ifProg b
              (seqProg (advanceMarkProg ⟨9, by decide⟩)
                (seqProg incNLenProg
                  (mapExitProg (fun _ => true) incNLenProg)))
              (seqProg (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog)
                (seqProg (seekMarkProg ⟨10, by decide⟩)
                  (mapExitProg (fun _ => false)
                    (seqProg (writeSlotProg ⟨10, by decide⟩ false) rewindToBlock0Prog)))))
            hp2 (ProgRuns_if_false
              (pT := seqProg (advanceMarkProg ⟨9, by decide⟩)
                (seqProg incNLenProg
                  (mapExitProg (fun _ => true) incNLenProg)))
              (ProgRuns_seq hp3 (ProgRuns_seq hp4
                (ProgRuns_mapExit (fun _ => false) (ProgRuns_seq hp5 hp6)))))))).mono
        (Nat.le_refl Sp) (by dsimp [stepCost, aL₁]; omega)
    | succ rem ih =>
      intro r hr_eq t_c hbtc
      have hr_n : r < n := by omega
      have hr_lt : r < aL₁ := by dsimp [aL₁]; omega
      have hr1_lt : r + 1 < aL₁ := by dsimp [aL₁]; omega
      obtain ⟨ta, hbta, hp1⟩ := ProgRuns_seekRMark (Sp := Sp) hbtc hr_lt hsp1
      obtain ⟨tb, hbtb, hp2⟩ := ProgRuns_readSlot ⟨3, by decide⟩ (Sp := Sp) hbta hr_lt hsp1
      have hsv3 : slotVal aL₁ inp (2 * r) [] [] [] (some r) (some (2 * r)) r 3 = true := by
        unfold slotVal; rw [ite_eq_left hr_lt]
        rw [hinp_unary r (by omega)]; exact decide_eq_true hr_n
      rw [hsv3] at hp2
      obtain ⟨tc, hbtc', hp3⟩ := ProgRuns_advanceRMark (Sp := Sp) hbtb hr1_lt hsp1
      obtain ⟨td, hbtd, hp4⟩ := ProgRuns_incNLen (Sp := Sp) hbtc' (by omega) hsp1
      obtain ⟨te, hbte, hp5⟩ := ProgRuns_incNLen (Sp := Sp) hbtd (by omega) hsp1
      have h2r2 : 2 * r + 1 + 1 = 2 * (r + 1) := by omega
      rw [h2r2] at hbte
      obtain ⟨t_e, hbt_e, hrRest⟩ := ih (r + 1) (by omega) te hbte
      have hbody : ProgRuns initNLenBody Sp stepCost (t_c, base) true (te, base) :=
        (ProgRuns_seq hp1
          (ProgRuns_bind (k := fun b =>
            ifProg b
              (seqProg (advanceMarkProg ⟨9, by decide⟩)
                (seqProg incNLenProg
                  (mapExitProg (fun _ => true) incNLenProg)))
              (seqProg (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog)
                (seqProg (seekMarkProg ⟨10, by decide⟩)
                  (mapExitProg (fun _ => false)
                    (seqProg (writeSlotProg ⟨10, by decide⟩ false) rewindToBlock0Prog)))))
            hp2 (ProgRuns_if_true
              (pF := seqProg (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog)
                (seqProg (seekMarkProg ⟨10, by decide⟩)
                  (mapExitProg (fun _ => false)
                    (seqProg (writeSlotProg ⟨10, by decide⟩ false) rewindToBlock0Prog))))
              (ProgRuns_seq hp3 (ProgRuns_seq hp4 (ProgRuns_mapExit (fun _ => true) hp5)))))).mono
          (Nat.le_refl Sp) (by dsimp [stepCost, aL₁]; omega)
      exact ⟨t_e, hbt_e,
        (ProgRuns_while_true hbody hrRest).mono (Nat.le_refl Sp) (by nlinarith)⟩
  obtain ⟨t₄, hbt₄, hs4⟩ := hloopN n 0 (Nat.zero_add _) t₃ (by simpa using hbt₃)
  obtain ⟨t₅, hbt₅, hs5⟩ := ProgRuns_setRMark0 (Sp := Sp) hbt₄ hsp1
  have hloopAlloc : ∀ (rem r : ℕ), r + rem = 2 * n → ∀ t_c : List Bool,
      BlockTape base (aL₁ + 3 * r) inp (2 * n) [] [] [] (some r) none t_c →
      ∃ t_e : List Bool,
        BlockTape base (aL₁ + 6 * n) inp (2 * n) [] [] [] none none t_e ∧
        ProgRuns (whileProg preAllocBody) Sp ((rem + 1) * stepCost) (t_c, base) () (t_e, base) := by
    intro rem
    induction rem with
    | zero =>
      intro r hr_eq t_c hbtc
      have hr2n : r = 2 * n := by omega
      subst hr2n
      have h3r : aL₁ + 3 * (2 * n) = aL₁ + 6 * n := by omega
      rw [h3r] at hbtc
      have hr_lt : 2 * n < aL₁ + 6 * n := by dsimp [aL₁]; omega
      have hsp_e : base + 11 * (aL₁ + 6 * n) ≤ Sp := by dsimp [aL₁]; omega
      obtain ⟨ta, hbta, hp1⟩ := ProgRuns_seekRMark (Sp := Sp) hbtc hr_lt hsp_e
      obtain ⟨tb, hbtb, hp2⟩ := ProgRuns_readSlot ⟨4, by decide⟩ (Sp := Sp) hbta hr_lt hsp_e
      have hsv4 : slotVal (aL₁ + 6 * n) inp (2 * n) [] [] [] (some (2 * n)) none (2 * n) 4 = false := by
        simp [slotVal, hr_lt]
      rw [hsv4] at hp2
      obtain ⟨tc, hbtc', hp3⟩ := ProgRuns_clearRMarkAndRewind (Sp := Sp) hbtb hr_lt hsp_e
      refine ⟨tc, hbtc', ?_⟩
      exact (ProgRuns_while_false (by
        unfold preAllocBody
        exact ProgRuns_seq hp1
          (ProgRuns_bind (k := fun hasN =>
            ifProg hasN
              (seqProg (advanceMarkProg ⟨9, by decide⟩)
                (seqProg clearSubTapeProg
                  (seqProg clearSubTapeProg
                    (mapExitProg (fun _ => true) clearSubTapeProg))))
              (mapExitProg (fun _ => false)
                (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog)))
            hp2 (ProgRuns_if_false
              (pT := seqProg (advanceMarkProg ⟨9, by decide⟩)
                (seqProg clearSubTapeProg
                  (seqProg clearSubTapeProg
                    (mapExitProg (fun _ => true) clearSubTapeProg))))
              (ProgRuns_mapExit (fun _ => false) hp3))))).mono
        (Nat.le_refl Sp) (by dsimp [stepCost, aL₁]; omega)
    | succ rem ih =>
      intro r hr_eq t_c hbtc
      have hr_2n : r < 2 * n := by omega
      have hr_lt : r < aL₁ + 3 * r := by dsimp [aL₁]; omega
      have hr1_lt : r + 1 < aL₁ + 3 * r := by dsimp [aL₁]; omega
      have hsp_r : base + 11 * (aL₁ + 3 * r) ≤ Sp := by dsimp [aL₁]; omega
      obtain ⟨ta, hbta, hp1⟩ := ProgRuns_seekRMark (Sp := Sp) hbtc hr_lt hsp_r
      obtain ⟨tb, hbtb, hp2⟩ := ProgRuns_readSlot ⟨4, by decide⟩ (Sp := Sp) hbta hr_lt hsp_r
      have hsv4 : slotVal (aL₁ + 3 * r) inp (2 * n) [] [] [] (some r) none r 4 = true := by
        simp [slotVal, hr_lt, hr_2n]
      rw [hsv4] at hp2
      obtain ⟨tc, hbtc', hp3⟩ := ProgRuns_advanceRMark (Sp := Sp) hbtb hr1_lt hsp_r
      obtain ⟨td, hbtd, hp4⟩ := ProgRuns_clearSubTape (Sp := Sp) hbtc' (by dsimp [aL₁]; omega)
      obtain ⟨te, hbte, hp5⟩ := ProgRuns_clearSubTape (Sp := Sp) hbtd (by dsimp [aL₁]; omega)
      obtain ⟨tf, hbtf, hp6⟩ := ProgRuns_clearSubTape (Sp := Sp) hbte (by dsimp [aL₁]; omega)
      have ha3 : aL₁ + 3 * r + 1 + 1 + 1 = aL₁ + 3 * (r + 1) := by omega
      rw [ha3] at hbtf
      obtain ⟨t_e, hbt_e, hrRest⟩ := ih (r + 1) (by omega) tf hbtf
      have hbody : ProgRuns preAllocBody Sp stepCost (t_c, base) true (tf, base) :=
        (ProgRuns_seq hp1
          (ProgRuns_bind (k := fun hasN =>
            ifProg hasN
              (seqProg (advanceMarkProg ⟨9, by decide⟩)
                (seqProg clearSubTapeProg
                  (seqProg clearSubTapeProg
                    (mapExitProg (fun _ => true) clearSubTapeProg))))
              (mapExitProg (fun _ => false)
                (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog)))
            hp2 (ProgRuns_if_true
              (pF := mapExitProg (fun _ => false)
                (seqProg (writeSlotProg ⟨9, by decide⟩ false) rewindToBlock0Prog))
              (ProgRuns_seq hp3 (ProgRuns_seq hp4 (ProgRuns_seq hp5
                (ProgRuns_mapExit (fun _ => true) hp6))))))).mono
          (Nat.le_refl Sp) (by dsimp [stepCost, aL₁]; omega)
      exact ⟨t_e, hbt_e,
        (ProgRuns_while_true hbody hrRest).mono (Nat.le_refl Sp) (by nlinarith)⟩
  obtain ⟨t', hbt', hs6⟩ := hloopAlloc (2 * n) 0 (Nat.zero_add _) t₅ (by simpa using hbt₅)
  refine ⟨t', by omega, hbt', ?_⟩
  unfold initNMarkAndAllocProg initNMarkAndAllocRaw
  exact (ProgRuns_seq hs1 (ProgRuns_seq hs2 (ProgRuns_seq hs3
    (ProgRuns_seq hs4 (ProgRuns_seq hs5 hs6))))).mono
    (Nat.le_refl Sp) (by dsimp only [stepCost, aL₁] at *; nlinarith)

attribute [irreducible] InitNAllocQ initNMarkAndAllocProg

def rawInputToBlockTapeRaw (u : ℕ) :=
  bindProg initWinProg (fun remBool =>
    seqProg (slideMidRestProg u remBool)
      (seqProg (setupBaseAndBlock0Prog remBool)
        (seqProg (drainRawToRevBlockProg remBool)
          (seqProg revCopySubToInProg
            initNMarkAndAllocProg))))

def RawInputQ (u : ℕ) : Type := ProgState (rawInputToBlockTapeRaw u)
instance (u : ℕ) : Fintype (RawInputQ u) := by
  unfold RawInputQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance
instance (u : ℕ) : DecidableEq (RawInputQ u) := by
  unfold RawInputQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def rawInputToBlockTapeProg (u : ℕ) : Prog (RawInputQ u) Unit :=
  rawInputToBlockTapeRaw u

private lemma rawInput_time_bound (n L W aL₄ : ℕ)
    (_hn : 2 ≤ n) (hW : W ≤ n) (_hL : 3 * n + 1 ≤ L) (ha4 : aL₄ ≤ L + 4) :
    (4 * n + 10) +
      (((L + 2) * (12 * W + 30) + (W + 2) * (10 * W + 20)) +
        (((2 * n + 2) * (4 * n + 30) + (W + 2) * (10 * W + 20) + 100) +
          (((2 * L + 10) * (2 * (L + 4 + 2 * n) + 200 * (L + 4) + 500)) +
            (((L + 1) * (350 * aL₄ + 400)) +
              (3 * n + 4) * (500 * (aL₄ + 6 * n + 2) + 800))))) ≤
      5000 * (L + 6 * n + 8) * (L + 6 * n + 8) := by
  have h1 : W ≤ L + 6 * n + 8 := by omega
  have h2 : aL₄ ≤ L + 6 * n + 8 := by omega
  nlinarith

lemma ProgRuns_rawInputToBlockTape (u : ℕ) {Sp n : ℕ} {body : List Bool} {ts : List ℕ}
    (hn : 2 ≤ n)
    (hbody : body.length = 2 * n)
    (hu : ts.length = u)
    (hsp : ((QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary).length + 4 + 2 * n) +
      11 * ((QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary).length + 6 * n + 8) ≤ Sp) :
    let inp := QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary
    let base := inp.length + 4 + 2 * n
    let Amax := inp.length + 6 * n + 8
    ∃ (allocLen₀ : ℕ) (tape₀ : List Bool),
      4 * n + 3 ≤ base ∧
      inp.length + 4 * n + 3 ≤ allocLen₀ ∧
      allocLen₀ ≤ Amax ∧
      BlockTape base allocLen₀ inp (2 * n) [] [] [] none none tape₀ ∧
      ProgRuns (rawInputToBlockTapeProg u) Sp (5000 * Amax * Amax)
        (inp, 0) () (tape₀, base) := by
  let tail := ts.flatMap QCSD_natToUnary
  let rest := body ++ tail
  let inp := QCSD_natToUnary n ++ body ++ tail
  let m := inp.length
  let base := m + 4 + 2 * n
  let Amax := m + 6 * n + 8
  have hinp_assoc : QCSD_natToUnary n ++ rest = inp := by simp [inp, rest, List.append_assoc]
  have hm_ge : 3 * n + 1 ≤ m := by
    dsimp [m, inp, QCSD_natToUnary]; simp [hbody]; omega
  have hsp_a : base + 11 * Amax ≤ Sp := hsp
  obtain ⟨t₁, hw₁, hrest₁, hlen₁, hs1⟩ :=
    ProgRuns_initWin (Sp := Sp) (n := n) (rest := rest) hn
      (by rw [hinp_assoc]; dsimp [base, Amax] at hsp_a; omega)
  rw [hinp_assoc] at hs1 hlen₁
  have hmid_assoc : (if decide ((n - 2) % 2 = 1) then [false] else []) ++ rest =
      (if decide ((n - 2) % 2 = 1) then [false] else []) ++ body ++ tail := by
    simp [rest, List.append_assoc]
  obtain ⟨t₂, hm_eq, hw₂, hhigh₂, hlen₂, hs2⟩ :=
    ProgRuns_slideMidRest u (Sp := Sp) (n := n) (body := body) (ts := ts)
      hn hbody hu hw₁
      (fun p hp => by rw [hrest₁ p hp, hmid_assoc])
      (by dsimp only [m, inp, tail] at hlen₁ ⊢; omega)
      (by dsimp only [base, Amax, m, inp, tail] at hsp_a ⊢; omega)
  rw [← hmid_assoc] at hm_eq hw₂
  obtain ⟨t₃, hw₃, hm_t₃, hmid₃, hb₃, hs3⟩ :=
    ProgRuns_setupBaseAndBlock0 (Sp := Sp) (n := n)
      (midRest := (if decide ((n - 2) % 2 = 1) then [false] else []) ++ rest)
      hn hw₂ (by rw [hm_eq]; exact hhigh₂) (by rw [hm_eq]; exact hlen₂)
      (by rw [hm_eq]; dsimp only [base, Amax, m, inp, tail] at hsp_a ⊢; omega)
  rw [hm_eq] at hm_t₃ hmid₃ hb₃ hs3
  obtain ⟨aL₄, t₄, hm_lt₄, haL₄_le, hbt₄, hs4⟩ :=
    ProgRuns_drainRawToRevBlock (Sp := Sp) (n := n) (rest := rest)
      hn hw₃ (by rw [hinp_assoc]; exact hm_t₃)
      (fun p hp1 hp2 => by rw [hinp_assoc] at hp1 hp2; exact hmid₃ p hp1 hp2)
      (by rw [hinp_assoc]; exact hb₃)
      (by rw [hinp_assoc]; dsimp only [base, Amax, m, inp, tail] at hsp_a ⊢; omega)
  rw [hinp_assoc] at hm_lt₄ haL₄_le hbt₄ hs4
  obtain ⟨t₅, hbt₅, hs5⟩ :=
    ProgRuns_revCopySubToIn (Sp := Sp) hbt₄
      (by dsimp only [base, Amax, m, inp, tail] at hsp_a haL₄_le ⊢; omega)
  rw [← hinp_assoc] at hbt₅ hm_lt₄
  obtain ⟨tape₀, hcap₀, hbt₀, hs6⟩ :=
    ProgRuns_initNMarkAndAlloc (Sp := Sp) (n := n) (rest := rest)
      hn (by simp [rest, hbody]) hbt₅ hm_lt₄
      (by dsimp only [base, Amax, m, inp, tail] at hsp_a haL₄_le ⊢; omega)
  rw [hinp_assoc] at hcap₀ hbt₀ hs6
  refine ⟨aL₄ + 1 + 6 * n, tape₀,
    by dsimp only [base, m, inp, tail] at hm_ge ⊢; omega,
    hcap₀,
    by dsimp only [Amax, m, inp, tail] at haL₄_le ⊢; omega,
    hbt₀, ?_⟩
  unfold rawInputToBlockTapeProg rawInputToBlockTapeRaw
  have hw_le_n : (n - 2) / 2 ≤ n := by omega
  exact (ProgRuns_bind (k := fun remBool =>
    seqProg (slideMidRestProg u remBool)
      (seqProg (setupBaseAndBlock0Prog remBool)
        (seqProg (drainRawToRevBlockProg remBool)
          (seqProg revCopySubToInProg
            initNMarkAndAllocProg))))
    hs1 (ProgRuns_seq hs2 (ProgRuns_seq hs3
      (ProgRuns_seq hs4 (ProgRuns_seq hs5 hs6))))).mono
    (Nat.le_refl Sp)
    (rawInput_time_bound n inp.length ((n - 2) / 2) aL₄ hn hw_le_n hm_ge haL₄_le)

attribute [irreducible] RawInputQ rawInputToBlockTapeProg

/-! ### Section 8: Full Recovery TM, Generic Pinning Theorem & Concrete `Exact` / `Sep` / `Le` Instantiations -/

def fullRecoveryRaw (u : ℕ) (M_net A : QCSD_DetTM) :=
  seqProg (rawInputToBlockTapeProg u)
    (seqProg (evalPrefixProg M_net A)
      (bindProg scanAndSaveCountProg (fun hasWit =>
        seqProg
          (ifProg hasWit
            (seqProg (greedyLoopProg M_net A) (buildOutSubProg true))
            (buildOutSubProg false))
          flushSubToOriginProg)))

def FullRecoveryQ (u : ℕ) (M_net A : QCSD_DetTM) : Type :=
  ProgState (fullRecoveryRaw u M_net A)

instance (u : ℕ) (M_net A : QCSD_DetTM) : Fintype (FullRecoveryQ u M_net A) := by
  unfold FullRecoveryQ ProgState
  repeat first | apply sumFintype | apply prodFintype | infer_instance

instance (u : ℕ) (M_net A : QCSD_DetTM) : DecidableEq (FullRecoveryQ u M_net A) := by
  unfold FullRecoveryQ ProgState
  repeat first | apply sumDecEq | apply prodDecEq | infer_instance

def fullRecoveryProg (u : ℕ) (M_net A : QCSD_DetTM) :
    Prog (FullRecoveryQ u M_net A) Unit :=
  fullRecoveryRaw u M_net A

private lemma fullRecovery_time_bound
    (Amax aMax₁ n aCap base outLen aL_f B TM TA : ℕ)
    (hB_ge : 20 ≤ B)
    (hAmax : Amax ≤ B)
    (haMax₁ : aMax₁ ≤ B)
    (hn : 2 * n + 1 ≤ B)
    (haCap : aCap ≤ B)
    (hbase : base ≤ B)
    (hout : outLen + 1 ≤ B)
    (haLf : aL_f ≤ B) :
    5000 * Amax * Amax +
      (((1500 * aMax₁ + 3000) * (aMax₁ + 1) + 92 * TM + 92 * TA) +
        ((180 * (2 * n) + 100) +
          (((2 * n + 1) * ((1800 * aCap + 4000) * (aCap + 1) + 92 * TM + 92 * TA) +
              (900 * (aCap + 1) + 2000) * (aCap + 2)) +
            ((4 * base + 3) + (outLen + 1) * (62 * aL_f + 2 * base + 120))))) ≤
      25000 * B ^ 3 * (TM + TA + 1) := by
  have hB1 : 1 ≤ B := by omega
  have hB2_le_B3 : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right hB1 (by decide)
  have hB_le_B3 : B ≤ B ^ 3 := by simpa using Nat.pow_le_pow_right hB1 (show 1 ≤ 3 by decide)
  have h1_B3 : 1 ≤ B ^ 3 := Nat.one_le_pow 3 B hB1
  have h1a : 5000 * Amax * Amax ≤ 5000 * B ^ 2 := by nlinarith
  have h1 : 5000 * Amax * Amax ≤ 5000 * B ^ 3 :=
    h1a.trans (Nat.mul_le_mul_left 5000 hB2_le_B3)
  have h2a : (1500 * aMax₁ + 3000) * (aMax₁ + 1) ≤ 4500 * B ^ 2 := by nlinarith
  have h2b : (1500 * aMax₁ + 3000) * (aMax₁ + 1) ≤ 4500 * B ^ 3 :=
    h2a.trans (Nat.mul_le_mul_left 4500 hB2_le_B3)
  have h2c : TM + TA ≤ B ^ 3 * (TM + TA) := by
    simpa using Nat.mul_le_mul_right (TM + TA) h1_B3
  have h3a : 180 * (2 * n) + 100 ≤ 500 * B := by omega
  have h3 : 180 * (2 * n) + 100 ≤ 500 * B ^ 3 :=
    h3a.trans (Nat.mul_le_mul_left 500 hB_le_B3)
  have h4a : (1800 * aCap + 4000) * (aCap + 1) ≤ 5000 * B ^ 2 := by nlinarith
  have h4b : (2 * n + 1) * ((1800 * aCap + 4000) * (aCap + 1) + 92 * TM + 92 * TA) ≤
      B * (5000 * B ^ 2 + 92 * (TM + TA)) :=
    Nat.mul_le_mul hn (by omega)
  have h4b_eq : B * (5000 * B ^ 2 + 92 * (TM + TA)) =
      5000 * B ^ 3 + 92 * (B * (TM + TA)) := by ring
  have h4b_tm : B * (TM + TA) ≤ B ^ 3 * (TM + TA) :=
    Nat.mul_le_mul_right (TM + TA) hB_le_B3
  have h4c_sq : (900 * (aCap + 1) + 2000) * (aCap + 2) ≤ 3000 * B ^ 2 := by nlinarith
  have h4c : (900 * (aCap + 1) + 2000) * (aCap + 2) ≤ 3000 * B ^ 3 :=
    h4c_sq.trans (Nat.mul_le_mul_left 3000 hB2_le_B3)
  have h5a : (4 * base + 3) + (outLen + 1) * (62 * aL_f + 2 * base + 120) ≤
      1000 * B ^ 2 := by nlinarith
  have h5 : (4 * base + 3) + (outLen + 1) * (62 * aL_f + 2 * base + 120) ≤
      1000 * B ^ 3 :=
    h5a.trans (Nat.mul_le_mul_left 1000 hB2_le_B3)
  have hRHS : 25000 * B ^ 3 * (TM + TA + 1) =
      25000 * (B ^ 3 * (TM + TA)) + 25000 * B ^ 3 := by ring
  omega

lemma ProgRuns_fullRecovery (u : ℕ) (M_net A : QCSD_DetTM)
    {n Sp SpM SpA TM TA : ℕ}
    {body : List Bool} {ts : List ℕ}
    {sols : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2))}
    (hn : 2 ≤ n)
    (hbody : body.length = 2 * n)
    (hu : ts.length = u)
    (hCard : sols.card < 2 ^ (2 * n))
    (hOracle : ∀ pre : List Bool, pre.length ≤ 2 * n →
      ∃ encNet : List Bool,
        (∃ k₁ ≤ TM,
          (QCSD_configAt2 M_net
            ((QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary) ++
              QCSD_natToUnary pre.length ++ pre) k₁).state = M_net.qhalt ∧
          tapeEq (QCSD_configAt2 M_net
            ((QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary) ++
              QCSD_natToUnary pre.length ++ pre) k₁).tape encNet ∧
          (∀ j ≤ k₁, QCSD_spaceUse2 (QCSD_configAt2 M_net
            ((QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary) ++
              QCSD_natToUnary pre.length ++ pre) j) ≤ SpM)) ∧
        (∃ k₂ ≤ TA,
          (QCSD_configAt2 A encNet k₂).state = A.qhalt ∧
          QCSD_bitsToNat (QCSD_configAt2 A encNet k₂).tape =
            (sols.filter (fun q => (qcsdIface n q.1 q.2).take pre.length = pre)).card ∧
          (∀ j ≤ k₂, QCSD_spaceUse2 (QCSD_configAt2 A encNet j) ≤ SpA)))
    (hsp : 12 * ((QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary).length +
      SpM + SpA + 10 * n + 20) ≤ Sp) :
    let inp := QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary
    let B := inp.length + SpM + SpA + 10 * n + 20
    ∃ (outTape : List Bool) (hout : ℕ) (y : ℕ × Option (List Bool)),
      QCSD_decodeOutputN2 n outTape = some y ∧
      y.1 = sols.card ∧
      (y.2 = none ↔ y.1 = 0) ∧
      (∀ w : List Bool, y.2 = some w →
        ∃ e₀ e₁, QCSD_decodeSolPair n w = some (e₀, e₁) ∧ (e₀, e₁) ∈ sols) ∧
      ProgRuns (fullRecoveryProg u M_net A) Sp
        (25000 * B ^ 3 * (TM + TA + 1)) (inp, 0) () (outTape, hout) := by
  set inp := QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary
  have hinp_len_eq : (QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary).length = inp.length := rfl
  set B := inp.length + SpM + SpA + 10 * n + 20
  have h12B : 12 * B ≤ Sp := hsp
  have hm_ge : 3 * n + 1 ≤ inp.length := by
    dsimp only [inp, QCSD_natToUnary]; simp [hbody]; omega
  set base := inp.length + 4 + 2 * n
  set Amax := inp.length + 6 * n + 8
  obtain ⟨allocLen₀, tape₀, hbase_ge, hcap₀, haL₀_le, hbt₀, hs1⟩ :=
    ProgRuns_rawInputToBlockTape u (Sp := Sp) hn hbody hu (by omega)
  change 4 * n + 3 ≤ base at hbase_ge
  change inp.length + 4 * n + 3 ≤ allocLen₀ at hcap₀
  change allocLen₀ ≤ Amax at haL₀_le
  change BlockTape base allocLen₀ inp (2 * n) [] [] [] none none tape₀ at hbt₀
  change ProgRuns (rawInputToBlockTapeProg u) Sp (5000 * Amax * Amax) (inp, 0) () (tape₀, base) at hs1
  obtain ⟨encNet₀, hM₀, hA₀⟩ := hOracle ([] : List Bool) (Nat.zero_le _)
  have hfilt_nil :
      (sols.filter (fun q => (qcsdIface n q.1 q.2).take ([] : List Bool).length = [])).card =
      sols.card := by simp
  rw [hfilt_nil] at hA₀
  obtain ⟨aL₁, vSub₁, tape₁, haL₁_ge, haL₁_le, hbits₁, hbt₁, hs2⟩ :=
    ProgRuns_evalPrefix M_net A (Sp := Sp) hbt₀ (by simp; omega) hM₀ hA₀
      (by simp only [Nat.max_eq_max]; omega)
  have haL₁_B : aL₁ ≤ inp.length + SpM + SpA + 6 * n + 9 := by
    simp only [Nat.max_eq_max] at haL₁_le; omega
  set cOut := List.ofFn (fun j : Fin (2 * n) => QCSD_tapeRead vSub₁ j.val)
  set hasWit := decide (0 < QCSD_bitsToNat vSub₁)
  obtain ⟨tape₂, hcOut_len, hcOut_bits, hbt₂, hs3⟩ :=
    ProgRuns_scanAndSaveCount (Sp := Sp) hbt₁ (by omega) (by rw [hbits₁]; exact hCard)
      (by omega)
  change cOut.length = 2 * n at hcOut_len
  change QCSD_bitsToNat cOut = QCSD_bitsToNat vSub₁ at hcOut_bits
  change BlockTape base aL₁ inp (2 * n) cOut [] vSub₁ none none tape₂ at hbt₂
  change ProgRuns scanAndSaveCountProg Sp (180 * (2 * n) + 100) (tape₁, base) hasWit (tape₂, base) at hs3
  have hcOut_eq : QCSD_bitsToNat cOut = sols.card := hcOut_bits.trans hbits₁
  have hhasWit_eq : hasWit = decide (0 < sols.card) := by simp [hasWit, hbits₁]
  set aCap := Nat.max (Nat.max aL₁ (SpM + 1)) (SpA + 1) + 2 * n + 1
  have haCap_B : aCap ≤ inp.length + SpM + SpA + 8 * n + 10 := by
    simp only [aCap, Nat.max_eq_max]; omega
  set branchBudget :=
    (2 * n + 1) * ((1800 * aCap + 4000) * (aCap + 1) + 92 * TM + 92 * TA) +
      (900 * (aCap + 1) + 2000) * (aCap + 2)
  have hBranch : ∃ (aL_f : ℕ) (pre_f tape₄ : List Bool),
      aL_f ≤ aCap + 1 ∧
      (hasWit = true →
        pre_f.length = 2 * n ∧
        0 < (sols.filter (fun q => (qcsdIface n q.1 q.2).take (2 * n) = pre_f)).card) ∧
      BlockTape base aL_f inp (2 * n) cOut pre_f (outSubList cOut pre_f hasWit)
        none (some (outSubList cOut pre_f hasWit).length) tape₄ ∧
      ProgRuns
        (ifProg hasWit
          (seqProg (greedyLoopProg M_net A) (buildOutSubProg true))
          (buildOutSubProg false))
        Sp branchBudget (tape₂, base) () (tape₄, base) := by
    by_cases hhw : hasWit = true
    · rw [hhw]
      have hpos_sols : 0 < sols.card := of_decide_eq_true (hhasWit_eq.symm.trans hhw)
      have hpos₀ : 0 < (sols.filter (fun q => (qcsdIface n q.1 q.2).take 0 = [])).card := by
        simpa using hpos_sols
      obtain ⟨aL₂, preOut, vSub₂, tape₃, haL₂_ge, haL₂_le, hpre_len, hpre_pos, hbt₃, hrGreedy⟩ :=
        ProgRuns_greedyLoop M_net A (Sp := Sp) hn hCard hbt₂ (by omega) hpos₀ hOracle
          (by simp only [Nat.max_eq_max]; omega)
      change aL₂ ≤ aCap at haL₂_le
      obtain ⟨tape₄, hbt₄, hrBuild⟩ :=
        ProgRuns_buildOutSub true (Sp := Sp) hbt₃ hcOut_len (fun _ => hpre_len)
          (by omega) (by omega)
      refine ⟨aL₂ + 1, preOut, tape₄, by omega, fun _ => ⟨hpre_len, hpre_pos⟩, hbt₄, ?_⟩
      exact (ProgRuns_if_true
        (pF := buildOutSubProg false) (ProgRuns_seq hrGreedy hrBuild)).mono
        (Nat.le_refl Sp)
        (Nat.add_le_add_left (Nat.mul_le_mul (by omega) (by omega)) _)
    · have hhf : hasWit = false := Bool.eq_false_iff.mpr hhw
      rw [hhf]
      obtain ⟨tape₄, hbt₄, hrBuild⟩ :=
        ProgRuns_buildOutSub false (Sp := Sp) hbt₂ hcOut_len (fun h => by cases h)
          (by omega) (by omega)
      have haL₁_le_cap : aL₁ ≤ aCap := by simp only [aCap, Nat.max_eq_max]; omega
      refine ⟨aL₁ + 1, [], tape₄, by omega, (fun h => by cases h), hbt₄, ?_⟩
      exact (ProgRuns_if_false
        (pT := seqProg (greedyLoopProg M_net A) (buildOutSubProg true)) hrBuild).mono
        (Nat.le_refl Sp)
        ((Nat.mul_le_mul (by omega) (by omega)).trans (Nat.le_add_left _ _))
  obtain ⟨aL_f, pre_f, tape₄, haLf_le, hpre_spec, hbt₄, hs4⟩ := hBranch
  set outL := outSubList cOut pre_f hasWit
  have houtL_len : outL.length ≤ 4 * n + 1 := by
    dsimp only [outL, outSubList]
    by_cases hhw : hasWit = true
    · rw [hhw]; simp [hcOut_len, (hpre_spec hhw).1]; omega
    · rw [Bool.eq_false_iff.mpr hhw]; simp [hcOut_len]; omega
  obtain ⟨outTape, hout, htBase, htOut, hs5⟩ :=
    ProgRuns_flushSubToOrigin (Sp := Sp) hbt₄ (by omega) (by omega)
  have hdec := decodeOutputN2_of_flushed (n := n) (base := base)
    hcOut_len (fun h => (hpre_spec h).1) hbase_ge htBase htOut
  refine ⟨outTape, hout, (QCSD_bitsToNat cOut, if hasWit then some pre_f else none),
    hdec, hcOut_eq, ?_, ?_, ?_⟩
  · dsimp only
    rw [hcOut_eq]
    by_cases hhw : hasWit = true
    · have hpos : 0 < sols.card := of_decide_eq_true (hhasWit_eq.symm.trans hhw)
      rw [hhw]
      exact ⟨(fun h => by cases h), (fun h => by omega)⟩
    · have hhf : hasWit = false := Bool.eq_false_iff.mpr hhw
      have hnot : ¬ 0 < sols.card := of_decide_eq_false (hhasWit_eq.symm.trans hhf)
      rw [hhf]
      exact ⟨fun _ => by omega, fun _ => rfl⟩
  · intro w hw_eq
    dsimp only at hw_eq
    by_cases hhw : hasWit = true
    · rw [hhw] at hw_eq
      simp only [↓reduceIte, Option.some.injEq] at hw_eq
      subst hw_eq
      obtain ⟨hpre_len, hpre_pos⟩ := hpre_spec hhw
      obtain ⟨q, hq_mem⟩ := Finset.card_pos.mp hpre_pos
      obtain ⟨hq_sol, hq_take⟩ := Finset.mem_filter.mp hq_mem
      have hq_iface : qcsdIface n q.1 q.2 = pre_f := by
        rw [List.take_of_length_le (by rw [qcsdIface_length])] at hq_take
        exact hq_take
      refine ⟨q.1, q.2, ?_, hq_sol⟩
      rw [← hq_iface]
      exact decodeSolPair_qcsdIface n q.1 q.2
    · rw [Bool.eq_false_iff.mpr hhw] at hw_eq
      simp at hw_eq
  · unfold fullRecoveryProg fullRecoveryRaw
    have hrun := ProgRuns_seq hs1
      (ProgRuns_seq hs2
        (ProgRuns_bind (k := fun hw =>
          seqProg
            (ifProg hw
              (seqProg (greedyLoopProg M_net A) (buildOutSubProg true))
              (buildOutSubProg false))
            flushSubToOriginProg)
          hs3 (ProgRuns_seq hs4 hs5)))
    set aMax₁ := Nat.max (Nat.max (allocLen₀ + 1) (SpM + 1)) (SpA + 1)
    have haMax₁_le : aMax₁ ≤ B := by simp only [aMax₁, Nat.max_eq_max]; omega
    exact hrun.mono (Nat.le_refl Sp)
      (fullRecovery_time_bound Amax aMax₁ n aCap base outL.length aL_f B TM TA
        (by omega) (by omega) haMax₁_le (by omega) (by omega) (by omega) (by omega) (by omega))

attribute [irreducible] FullRecoveryQ fullRecoveryProg

theorem qcsd_tc_recover_generic_padded
    (u K_enc : ℕ)
    {Input : Type*}
    (nOf : Input → ℕ)
    (hOf sOf : (x : Input) → Fin (nOf x) → ZMod 2)
    (inEnc : Input → List Bool)
    (domain : Input → Prop)
    (solsOf : (x : Input) → Finset ((Fin (nOf x) → ZMod 2) × (Fin (nOf x) → ZMod 2)))
    (correct : Input → (ℕ × Option (List Bool)) → Prop)
    (hDom : ∀ x, domain x →
      2 ≤ nOf x ∧
      (inEnc x).length ≤ K_enc * nOf x ∧
      ∃ (body : List Bool) (ts : List ℕ),
        body.length = 2 * nOf x ∧
        ts.length = u ∧
        inEnc x = QCSD_natToUnary (nOf x) ++ body ++ ts.flatMap QCSD_natToUnary)
    (hLin : ∀ x, domain x →
      ∀ p ∈ solsOf x, ∀ k : Fin (nOf x),
        p.1 k + QCSD_cycMul (nOf x) (hOf x) p.2 k = sOf x k)
    (hCorr : ∀ x, domain x → ∀ o : ℕ × Option (List Bool),
      (o.1 = (solsOf x).card ∧
       (o.2 = none ↔ o.1 = 0) ∧
       (∀ w : List Bool, o.2 = some w →
         ∃ e₀ e₁, QCSD_decodeSolPair (nOf x) w = some (e₀, e₁) ∧ (e₀, e₁) ∈ solsOf x)) →
      correct x o)
    (hTC : QCSD_TC10)
    (CΔ : ℝ) (km Km kcost Kcost kpred Kpred : ℕ)
    (hAdm : QCSD_TCAdmissible CΔ km Km kcost Kcost kpred Kpred)
    (M_net : QCSD_DetTM) (Ctm : ℝ) (hCtm : 0 ≤ Ctm)
    (kst Cl : ℕ) (_hCl : 1 ≤ Cl)
    (N : Input → List Bool → QCSD_BoolTensorNetwork2)
    (hGen : ∀ x, domain x → ∀ pre : List Bool, pre.length ≤ 2 * nOf x →
      (∃ k ≤ QCSD_timeBound Ctm (nOf x),
        (QCSD_configAt2 M_net (inEnc x ++ QCSD_natToUnary pre.length ++ pre) k).state = M_net.qhalt ∧
        (∀ i : ℕ,
          QCSD_tapeRead (QCSD_configAt2 M_net (inEnc x ++ QCSD_natToUnary pre.length ++ pre) k).tape i =
            QCSD_tapeRead (QCSD_encodeNet2 (N x pre)) i) ∧
        (∀ j ≤ k,
          QCSD_spaceUse2 (QCSD_configAt2 M_net (inEnc x ++ QCSD_natToUnary pre.length ++ pre) j) ≤
            QCSD_spaceBound kst (nOf x))) ∧
      (QCSD_TCClass2 CΔ km Km kcost Kcost kpred Kpred (N x pre) ∧
        2 * nOf x ≤ QCSD_edgeCount2 (N x pre) ∧
        QCSD_edgeCount2 (N x pre) ≤ Cl * nOf x) ∧
      QCSD_contraction2 (N x pre) =
        ((solsOf x).filter (fun q =>
          (((List.ofFn fun i => decide (q.1 i = 1)) ++
            (List.ofFn fun i => decide (q.2 i = 1))).take pre.length = pre))).card) :
    ∃ (A' : QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD_ComputesOnEncoded3 A' inEnc
        (fun x l => QCSD_decodeOutputN2 (nOf x) l)
        domain correct
        (fun x => QCSD_timeBound Ct (nOf x))
        (fun x => QCSD_spaceBound ksp (nOf x)) := by
  obtain ⟨A, CtA, kspA, hCtA1, _, hCompA⟩ :=
    hTC CΔ km Km kcost Kcost kpred Kpred hAdm
  let d_sp := Nat.max kst (Nat.max kspA 1)
  let K_B := K_enc + 1 + Cl ^ kspA + 20
  let ksp := 12 * K_B + d_sp
  obtain ⟨Ct, hCt0, hPolyT⟩ :=
    poly_mul_timeBound_le (25000 * K_B ^ 3) (3 * d_sp) Ctm CtA hCtm Cl
  refine ⟨progToTM (fullRecoveryProg u M_net A), Ct, ksp, hCt0, fun x hx => ?_⟩
  obtain ⟨hn, hlen_enc, body, ts, hbody, hu_ts, henc_eq⟩ := hDom x hx
  set n := nOf x
  have hCard : (solsOf x).card < 2 ^ (2 * n) :=
    card_sols_lt_two_pow_two_mul n hn (hOf x) (sOf x) (solsOf x) (hLin x hx)
  let SpM := QCSD_spaceBound kst n
  let SpA := (Cl * n) ^ kspA
  let TM := QCSD_timeBound Ctm n
  let TA := QCSD_timeBound (CtA * (Cl : ℝ)) n
  have hOracle : ∀ pre : List Bool, pre.length ≤ 2 * n →
      ∃ encNet : List Bool,
        (∃ k₁ ≤ TM,
          (QCSD_configAt2 M_net
            ((QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary) ++
              QCSD_natToUnary pre.length ++ pre) k₁).state = M_net.qhalt ∧
          tapeEq (QCSD_configAt2 M_net
            ((QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary) ++
              QCSD_natToUnary pre.length ++ pre) k₁).tape encNet ∧
          (∀ j ≤ k₁, QCSD_spaceUse2 (QCSD_configAt2 M_net
            ((QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary) ++
              QCSD_natToUnary pre.length ++ pre) j) ≤ SpM)) ∧
        (∃ k₂ ≤ TA,
          (QCSD_configAt2 A encNet k₂).state = A.qhalt ∧
          QCSD_bitsToNat (QCSD_configAt2 A encNet k₂).tape =
            ((solsOf x).filter (fun q => (qcsdIface n q.1 q.2).take pre.length = pre)).card ∧
          (∀ j ≤ k₂, QCSD_spaceUse2 (QCSD_configAt2 A encNet j) ≤ SpA)) := by
    intro pre hpre
    obtain ⟨hM_pre, ⟨hTC_pre, hEdge_lo, hEdge_hi⟩, hContr_pre⟩ := hGen x hx pre hpre
    rw [henc_eq] at hM_pre
    refine ⟨QCSD_encodeNet2 (N x pre), hM_pre, ?_⟩
    obtain ⟨k₂, hk₂, hhalt₂, ⟨yA, hdecA, hyA⟩, hsp₂⟩ := hCompA (N x pre) hTC_pre
    simp only [Option.some.injEq] at hdecA
    have hk₂_TA : k₂ ≤ TA :=
      hk₂.trans (qcsd_timeBound_edge_scale (by linarith) hn (by omega) hEdge_hi)
    refine ⟨k₂, hk₂_TA, hhalt₂, ?_, fun j hj => ?_⟩
    · rw [hdecA, hyA, hContr_pre]; rfl
    · exact (hsp₂ j hj).trans (Nat.pow_le_pow_left hEdge_hi kspA)
  let inp := QCSD_natToUnary n ++ body ++ ts.flatMap QCSD_natToUnary
  have hinp_len : inp.length ≤ K_enc * n := by dsimp [inp]; rw [← henc_eq]; exact hlen_enc
  let B := inp.length + SpM + SpA + 10 * n + 20
  have hn_pos : 0 < n := by omega
  have hd_1 : 1 ≤ d_sp := le_trans (Nat.le_max_right kspA 1) (Nat.le_max_right kst _)
  have hd_kst : kst ≤ d_sp := Nat.le_max_left _ _
  have hd_kspA : kspA ≤ d_sp := le_trans (Nat.le_max_left kspA 1) (Nat.le_max_right kst _)
  have hn_pow : n ≤ n ^ d_sp := by simpa using Nat.pow_le_pow_right hn_pos hd_1
  have hSpM_le : SpM ≤ n ^ d_sp := Nat.pow_le_pow_right hn_pos hd_kst
  have hSpA_le : SpA ≤ Cl ^ kspA * n ^ d_sp := by
    dsimp [SpA]; rw [Nat.mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn_pos hd_kspA)
  have henc_pow : inp.length ≤ K_enc * n ^ d_sp :=
    hinp_len.trans (Nat.mul_le_mul_left K_enc hn_pow)
  have hB_le : B ≤ K_B * n ^ d_sp := by
    dsimp only [B, K_B]
    nlinarith
  have hSp_le : 12 * B ≤ QCSD_spaceBound ksp n := by
    calc 12 * B ≤ 12 * (K_B * n ^ d_sp) := Nat.mul_le_mul_left 12 hB_le
      _ = (12 * K_B) * n ^ d_sp := (Nat.mul_assoc 12 K_B _).symm
      _ ≤ QCSD_spaceBound ksp n := nat_const_mul_pow_le_spaceBound (12 * K_B) d_sp n hn
  have hB3_le : B ^ 3 ≤ K_B ^ 3 * n ^ (3 * d_sp) := by
    calc B ^ 3 ≤ (K_B * n ^ d_sp) ^ 3 := Nat.pow_le_pow_left hB_le 3
      _ = K_B ^ 3 * (n ^ d_sp) ^ 3 := Nat.mul_pow _ _ 3
      _ = K_B ^ 3 * n ^ (d_sp * 3) := by rw [← Nat.pow_mul]
      _ = K_B ^ 3 * n ^ (3 * d_sp) := by rw [Nat.mul_comm d_sp 3]
  have hT_le : 25000 * B ^ 3 * (TM + TA + 1) ≤ QCSD_timeBound Ct n := by
    calc 25000 * B ^ 3 * (TM + TA + 1)
        ≤ 25000 * (K_B ^ 3 * n ^ (3 * d_sp)) * (TM + TA + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 25000 hB3_le)
      _ = (25000 * K_B ^ 3) * n ^ (3 * d_sp) * (TM + TA + 1) := by ring
      _ ≤ QCSD_timeBound Ct n := hPolyT n hn
  obtain ⟨outTape, hout, y, hdec_y, hy1, hy2, hy3, hrFull⟩ :=
    ProgRuns_fullRecovery u M_net A (Sp := QCSD_spaceBound ksp n)
      hn hbody hu_ts hCard hOracle hSp_le
  have hreach := progToTM_reaches (fullRecoveryProg u M_net A)
    (hrFull.mono (Nat.le_refl _) hT_le)
  rw [← henc_eq] at hreach
  obtain ⟨k, hk_le, hcfg_eq, hsp_all⟩ := hreach
  refine ⟨k, hk_le, ?_, ⟨y, ?_, hCorr x hx y ⟨hy1, hy2, hy3⟩⟩, fun j hj => ?_⟩
  · rw [configAt2_eq_iterate, hcfg_eq]
  · rw [configAt2_eq_iterate, hcfg_eq]; exact hdec_y
  · rw [configAt2_eq_iterate]; exact hsp_all j hj

lemma vecToBits_length {n : ℕ} (v : Fin n → ZMod 2) :
    (QCSD_vecToBits v).length = n := by
  simp [QCSD_vecToBits]

end Branch1Recovery

section ConcreteRecoveryTheorems

open QCSD.Defs
open Branch1Recovery

theorem qcsd_tc_recover_exact_padded_v2
    (hTC : QCSD_TC10)
    (CΔ : ℝ) (km Km kcost Kcost kpred Kpred : ℕ)
    (hAdm : QCSD_TCAdmissible CΔ km Km kcost Kcost kpred Kpred)
    (M_net : QCSD_DetTM) (Ctm : ℝ) (hCtm : 0 ≤ Ctm)
    (kst Cl : ℕ) (hCl : 1 ≤ Cl)
    (N : QCSD_Instance → List Bool → QCSD_BoolTensorNetwork2)
    (hGen : ∀ (x : QCSD_Instance), 2 ≤ x.n ∧ x.t ≤ 2 * x.n →
      ∀ (pre : List Bool), pre.length ≤ 2 * x.n →
        (∃ k ≤ QCSD_timeBound Ctm x.n,
          (QCSD_configAt2 M_net (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) k).state =
            M_net.qhalt ∧
          (∀ i : ℕ,
            QCSD_tapeRead
              (QCSD_configAt2 M_net (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) k).tape i =
              QCSD_tapeRead (QCSD_encodeNet2 (N x pre)) i) ∧
          (∀ j ≤ k,
            QCSD_spaceUse2
              (QCSD_configAt2 M_net (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) j) ≤
              QCSD_spaceBound kst x.n)) ∧
        (QCSD_TCClass2 CΔ km Km kcost Kcost kpred Kpred (N x pre) ∧
          2 * x.n ≤ QCSD_edgeCount2 (N x pre) ∧
          QCSD_edgeCount2 (N x pre) ≤ Cl * x.n) ∧
        QCSD_contraction2 (N x pre) =
          ((QCSD_solutions x).filter (fun q =>
            (((List.ofFn fun i => decide (q.1 i = 1)) ++
              (List.ofFn fun i => decide (q.2 i = 1))).take pre.length = pre))).card) :
    ∃ (A' : QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD_ComputesOnEncoded3 A' QCSD_encodeInstance
        (fun inp l => QCSD_decodeOutputN2 inp.n l)
        (fun inp => 2 ≤ inp.n ∧ inp.t ≤ 2 * inp.n)
        QCSD_Correct
        (fun inp => QCSD_timeBound Ct inp.n)
        (fun inp => QCSD_spaceBound ksp inp.n) := by
  obtain ⟨A', Ct, ksp, hCt, hComp⟩ :=
    qcsd_tc_recover_generic_padded 1 6
      (fun x => x.n) (fun x => x.h) (fun x => x.s)
      QCSD_encodeInstance
      (fun inp => 2 ≤ inp.n ∧ inp.t ≤ 2 * inp.n)
      QCSD_solutions QCSD_Correct
      (fun x ⟨hn, ht⟩ => ⟨hn,
        by simp [QCSD_encodeInstance, QCSD_natToUnary, vecToBits_length]; omega,
        QCSD_vecToBits x.h ++ QCSD_vecToBits x.s, [x.t],
        by simp [vecToBits_length]; omega, rfl,
        by simp [QCSD_encodeInstance, List.append_assoc]⟩)
      (fun x _ p hp => by
        classical
        unfold QCSD_solutions at hp
        exact (Finset.mem_filter.mp hp).2.1)
      (fun x _ o ⟨h1, h2, h3⟩ => ⟨h1, h2, fun w hw => by
        classical
        obtain ⟨e₀, e₁, hdec, hmem⟩ := h3 w hw
        unfold QCSD_solutions at hmem
        exact ⟨e₀, e₁, hdec, (Finset.mem_filter.mp hmem).2⟩⟩)
      hTC CΔ km Km kcost Kcost kpred Kpred hAdm M_net Ctm hCtm kst Cl hCl N
      (fun x hx pre hpre => hGen x hx pre hpre)
  exact ⟨A', Ct, ksp, hCt, hComp⟩

theorem qcsd_tc_recover_exact_v2
    (hTC : QCSD_TC10)
    (CΔ : ℝ) (km Km kcost Kcost kpred Kpred : ℕ)
    (hAdm : QCSD_TCAdmissible CΔ km Km kcost Kcost kpred Kpred)
    (M_net : QCSD_DetTM) (Ctm : ℝ) (hCtm : 0 ≤ Ctm)
    (kst Cl : ℕ) (hCl : 1 ≤ Cl)
    (N : QCSD_Instance → List Bool → QCSD_BoolTensorNetwork2)
    (hGen : ∀ (x : QCSD_Instance), 2 ≤ x.n ∧ x.t ≤ 2 * x.n →
      ∀ (pre : List Bool), pre.length ≤ 2 * x.n →
        (∃ k ≤ QCSD_timeBound Ctm x.n,
          (QCSD_configAt2 M_net (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) k).state =
            M_net.qhalt ∧
          (QCSD_configAt2 M_net (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) k).tape =
            QCSD_encodeNet2 (N x pre) ∧
          (∀ j ≤ k,
            QCSD_spaceUse2
              (QCSD_configAt2 M_net (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) j) ≤
              QCSD_spaceBound kst x.n)) ∧
        (QCSD_TCClass2 CΔ km Km kcost Kcost kpred Kpred (N x pre) ∧
          2 * x.n ≤ QCSD_edgeCount2 (N x pre) ∧
          QCSD_edgeCount2 (N x pre) ≤ Cl * x.n) ∧
        QCSD_contraction2 (N x pre) =
          ((QCSD_solutions x).filter (fun q =>
            (((List.ofFn fun i => decide (q.1 i = 1)) ++
              (List.ofFn fun i => decide (q.2 i = 1))).take pre.length = pre))).card) :
    ∃ (A' : QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD_ComputesOnEncoded3 A' QCSD_encodeInstance
        (fun inp l => QCSD_decodeOutputN2 inp.n l)
        (fun inp => 2 ≤ inp.n ∧ inp.t ≤ 2 * inp.n)
        QCSD_Correct
        (fun inp => QCSD_timeBound Ct inp.n)
        (fun inp => QCSD_spaceBound ksp inp.n) := by
  refine qcsd_tc_recover_exact_padded_v2 hTC CΔ km Km kcost Kcost kpred Kpred hAdm
    M_net Ctm hCtm kst Cl hCl N (fun x hx pre hpre => ?_)
  obtain ⟨⟨k, hk, hst, htp, hsp⟩, htc, hcnt⟩ := hGen x hx pre hpre
  exact ⟨⟨k, hk, hst, fun i => by rw [htp], hsp⟩, htc, hcnt⟩

theorem qcsd_tc_recover_sep_padded_v2
    (hTC : QCSD_TC10)
    (CΔ : ℝ) (km Km kcost Kcost kpred Kpred : ℕ)
    (hAdm : QCSD_TCAdmissible CΔ km Km kcost Kcost kpred Kpred)
    (M_net : QCSD_DetTM) (Ctm : ℝ) (hCtm : 0 ≤ Ctm)
    (kst Cl : ℕ) (hCl : 1 ≤ Cl)
    (N : QCSD_InstanceSep → List Bool → QCSD_BoolTensorNetwork2)
    (hGen : ∀ (x : QCSD_InstanceSep), 2 ≤ x.n ∧ x.t₀ ≤ x.n ∧ x.t₁ ≤ x.n →
      ∀ (pre : List Bool), pre.length ≤ 2 * x.n →
        (∃ k ≤ QCSD_timeBound Ctm x.n,
          (QCSD_configAt2 M_net (QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre) k).state =
            M_net.qhalt ∧
          (∀ i : ℕ,
            QCSD_tapeRead
              (QCSD_configAt2 M_net (QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre) k).tape i =
              QCSD_tapeRead (QCSD_encodeNet2 (N x pre)) i) ∧
          (∀ j ≤ k,
            QCSD_spaceUse2
              (QCSD_configAt2 M_net (QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre) j) ≤
              QCSD_spaceBound kst x.n)) ∧
        (QCSD_TCClass2 CΔ km Km kcost Kcost kpred Kpred (N x pre) ∧
          2 * x.n ≤ QCSD_edgeCount2 (N x pre) ∧
          QCSD_edgeCount2 (N x pre) ≤ Cl * x.n) ∧
        QCSD_contraction2 (N x pre) =
          ((QCSD_solutionsSep x).filter (fun q =>
            (((List.ofFn fun i => decide (q.1 i = 1)) ++
              (List.ofFn fun i => decide (q.2 i = 1))).take pre.length = pre))).card) :
    ∃ (A' : QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD_ComputesOnEncoded3 A' QCSD_encodeInstanceSep
        (fun inp l => QCSD_decodeOutputN2 inp.n l)
        (fun inp => 2 ≤ inp.n ∧ inp.t₀ ≤ inp.n ∧ inp.t₁ ≤ inp.n)
        QCSD_CorrectSep
        (fun inp => QCSD_timeBound Ct inp.n)
        (fun inp => QCSD_spaceBound ksp inp.n) := by
  obtain ⟨A', Ct, ksp, hCt, hComp⟩ :=
    qcsd_tc_recover_generic_padded 2 7
      (fun x => x.n) (fun x => x.h) (fun x => x.s)
      QCSD_encodeInstanceSep
      (fun inp => 2 ≤ inp.n ∧ inp.t₀ ≤ inp.n ∧ inp.t₁ ≤ inp.n)
      QCSD_solutionsSep QCSD_CorrectSep
      (fun x ⟨hn, ht₀, ht₁⟩ => ⟨hn,
        by simp [QCSD_encodeInstanceSep, QCSD_natToUnary, vecToBits_length]; omega,
        QCSD_vecToBits x.h ++ QCSD_vecToBits x.s, [x.t₀, x.t₁],
        by simp [vecToBits_length]; omega, rfl,
        by simp [QCSD_encodeInstanceSep, List.append_assoc]⟩)
      (fun x _ p hp => by
        classical
        unfold QCSD_solutionsSep at hp
        exact (Finset.mem_filter.mp hp).2.1)
      (fun x _ o ⟨h1, h2, h3⟩ => ⟨h1, h2, fun w hw => by
        classical
        obtain ⟨e₀, e₁, hdec, hmem⟩ := h3 w hw
        unfold QCSD_solutionsSep at hmem
        exact ⟨e₀, e₁, hdec, (Finset.mem_filter.mp hmem).2⟩⟩)
      hTC CΔ km Km kcost Kcost kpred Kpred hAdm M_net Ctm hCtm kst Cl hCl N
      (fun x hx pre hpre => hGen x hx pre hpre)
  exact ⟨A', Ct, ksp, hCt, hComp⟩

theorem qcsd_tc_recover_sep_v2
    (hTC : QCSD_TC10)
    (CΔ : ℝ) (km Km kcost Kcost kpred Kpred : ℕ)
    (hAdm : QCSD_TCAdmissible CΔ km Km kcost Kcost kpred Kpred)
    (M_net : QCSD_DetTM) (Ctm : ℝ) (hCtm : 0 ≤ Ctm)
    (kst Cl : ℕ) (hCl : 1 ≤ Cl)
    (N : QCSD_InstanceSep → List Bool → QCSD_BoolTensorNetwork2)
    (hGen : ∀ (x : QCSD_InstanceSep), 2 ≤ x.n ∧ x.t₀ ≤ x.n ∧ x.t₁ ≤ x.n →
      ∀ (pre : List Bool), pre.length ≤ 2 * x.n →
        (∃ k ≤ QCSD_timeBound Ctm x.n,
          (QCSD_configAt2 M_net (QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre) k).state =
            M_net.qhalt ∧
          (QCSD_configAt2 M_net (QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre) k).tape =
            QCSD_encodeNet2 (N x pre) ∧
          (∀ j ≤ k,
            QCSD_spaceUse2
              (QCSD_configAt2 M_net (QCSD_encodeInstanceSep x ++ QCSD_natToUnary pre.length ++ pre) j) ≤
              QCSD_spaceBound kst x.n)) ∧
        (QCSD_TCClass2 CΔ km Km kcost Kcost kpred Kpred (N x pre) ∧
          2 * x.n ≤ QCSD_edgeCount2 (N x pre) ∧
          QCSD_edgeCount2 (N x pre) ≤ Cl * x.n) ∧
        QCSD_contraction2 (N x pre) =
          ((QCSD_solutionsSep x).filter (fun q =>
            (((List.ofFn fun i => decide (q.1 i = 1)) ++
              (List.ofFn fun i => decide (q.2 i = 1))).take pre.length = pre))).card) :
    ∃ (A' : QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD_ComputesOnEncoded3 A' QCSD_encodeInstanceSep
        (fun inp l => QCSD_decodeOutputN2 inp.n l)
        (fun inp => 2 ≤ inp.n ∧ inp.t₀ ≤ inp.n ∧ inp.t₁ ≤ inp.n)
        QCSD_CorrectSep
        (fun inp => QCSD_timeBound Ct inp.n)
        (fun inp => QCSD_spaceBound ksp inp.n) := by
  refine qcsd_tc_recover_sep_padded_v2 hTC CΔ km Km kcost Kcost kpred Kpred hAdm
    M_net Ctm hCtm kst Cl hCl N (fun x hx pre hpre => ?_)
  obtain ⟨⟨k, hk, hst, htp, hsp⟩, htc, hcnt⟩ := hGen x hx pre hpre
  exact ⟨⟨k, hk, hst, fun i => by rw [htp], hsp⟩, htc, hcnt⟩

theorem qcsd_tc_recover_le_padded_v2
    (hTC : QCSD_TC10)
    (CΔ : ℝ) (km Km kcost Kcost kpred Kpred : ℕ)
    (hAdm : QCSD_TCAdmissible CΔ km Km kcost Kcost kpred Kpred)
    (M_net : QCSD_DetTM) (Ctm : ℝ) (hCtm : 0 ≤ Ctm)
    (kst Cl : ℕ) (hCl : 1 ≤ Cl)
    (N : QCSD_Instance → List Bool → QCSD_BoolTensorNetwork2)
    (hGen : ∀ (x : QCSD_Instance), 2 ≤ x.n ∧ x.t ≤ 2 * x.n →
      ∀ (pre : List Bool), pre.length ≤ 2 * x.n →
        (∃ k ≤ QCSD_timeBound Ctm x.n,
          (QCSD_configAt2 M_net (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) k).state =
            M_net.qhalt ∧
          (∀ i : ℕ,
            QCSD_tapeRead
              (QCSD_configAt2 M_net (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) k).tape i =
              QCSD_tapeRead (QCSD_encodeNet2 (N x pre)) i) ∧
          (∀ j ≤ k,
            QCSD_spaceUse2
              (QCSD_configAt2 M_net (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) j) ≤
              QCSD_spaceBound kst x.n)) ∧
        (QCSD_TCClass2 CΔ km Km kcost Kcost kpred Kpred (N x pre) ∧
          2 * x.n ≤ QCSD_edgeCount2 (N x pre) ∧
          QCSD_edgeCount2 (N x pre) ≤ Cl * x.n) ∧
        QCSD_contraction2 (N x pre) =
          ((QCSD_solutionsLe x).filter (fun q =>
            (((List.ofFn fun i => decide (q.1 i = 1)) ++
              (List.ofFn fun i => decide (q.2 i = 1))).take pre.length = pre))).card) :
    ∃ (A' : QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD_ComputesOnEncoded3 A' QCSD_encodeInstance
        (fun inp l => QCSD_decodeOutputN2 inp.n l)
        (fun inp => 2 ≤ inp.n ∧ inp.t ≤ 2 * inp.n)
        QCSD_CorrectLe
        (fun inp => QCSD_timeBound Ct inp.n)
        (fun inp => QCSD_spaceBound ksp inp.n) := by
  obtain ⟨A', Ct, ksp, hCt, hComp⟩ :=
    qcsd_tc_recover_generic_padded 1 6
      (fun x => x.n) (fun x => x.h) (fun x => x.s)
      QCSD_encodeInstance
      (fun inp => 2 ≤ inp.n ∧ inp.t ≤ 2 * inp.n)
      QCSD_solutionsLe QCSD_CorrectLe
      (fun x ⟨hn, ht⟩ => ⟨hn,
        by simp [QCSD_encodeInstance, QCSD_natToUnary, vecToBits_length]; omega,
        QCSD_vecToBits x.h ++ QCSD_vecToBits x.s, [x.t],
        by simp [vecToBits_length]; omega, rfl,
        by simp [QCSD_encodeInstance, List.append_assoc]⟩)
      (fun x _ p hp => by
        classical
        unfold QCSD_solutionsLe at hp
        exact (Finset.mem_filter.mp hp).2.1)
      (fun x _ o ⟨h1, h2, h3⟩ => ⟨h1, h2, fun w hw => by
        classical
        obtain ⟨e₀, e₁, hdec, hmem⟩ := h3 w hw
        unfold QCSD_solutionsLe at hmem
        exact ⟨e₀, e₁, hdec, (Finset.mem_filter.mp hmem).2⟩⟩)
      hTC CΔ km Km kcost Kcost kpred Kpred hAdm M_net Ctm hCtm kst Cl hCl N
      (fun x hx pre hpre => hGen x hx pre hpre)
  exact ⟨A', Ct, ksp, hCt, hComp⟩

theorem qcsd_tc_recover_le_v2
    (hTC : QCSD_TC10)
    (CΔ : ℝ) (km Km kcost Kcost kpred Kpred : ℕ)
    (hAdm : QCSD_TCAdmissible CΔ km Km kcost Kcost kpred Kpred)
    (M_net : QCSD_DetTM) (Ctm : ℝ) (hCtm : 0 ≤ Ctm)
    (kst Cl : ℕ) (hCl : 1 ≤ Cl)
    (N : QCSD_Instance → List Bool → QCSD_BoolTensorNetwork2)
    (hGen : ∀ (x : QCSD_Instance), 2 ≤ x.n ∧ x.t ≤ 2 * x.n →
      ∀ (pre : List Bool), pre.length ≤ 2 * x.n →
        (∃ k ≤ QCSD_timeBound Ctm x.n,
          (QCSD_configAt2 M_net (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) k).state =
            M_net.qhalt ∧
          (QCSD_configAt2 M_net (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) k).tape =
            QCSD_encodeNet2 (N x pre) ∧
          (∀ j ≤ k,
            QCSD_spaceUse2
              (QCSD_configAt2 M_net (QCSD_encodeInstance x ++ QCSD_natToUnary pre.length ++ pre) j) ≤
              QCSD_spaceBound kst x.n)) ∧
        (QCSD_TCClass2 CΔ km Km kcost Kcost kpred Kpred (N x pre) ∧
          2 * x.n ≤ QCSD_edgeCount2 (N x pre) ∧
          QCSD_edgeCount2 (N x pre) ≤ Cl * x.n) ∧
        QCSD_contraction2 (N x pre) =
          ((QCSD_solutionsLe x).filter (fun q =>
            (((List.ofFn fun i => decide (q.1 i = 1)) ++
              (List.ofFn fun i => decide (q.2 i = 1))).take pre.length = pre))).card) :
    ∃ (A' : QCSD_DetTM) (Ct : ℝ) (ksp : ℕ),
      0 ≤ Ct ∧
      QCSD_ComputesOnEncoded3 A' QCSD_encodeInstance
        (fun inp l => QCSD_decodeOutputN2 inp.n l)
        (fun inp => 2 ≤ inp.n ∧ inp.t ≤ 2 * inp.n)
        QCSD_CorrectLe
        (fun inp => QCSD_timeBound Ct inp.n)
        (fun inp => QCSD_spaceBound ksp inp.n) := by
  refine qcsd_tc_recover_le_padded_v2 hTC CΔ km Km kcost Kcost kpred Kpred hAdm
    M_net Ctm hCtm kst Cl hCl N (fun x hx pre hpre => ?_)
  obtain ⟨⟨k, hk, hst, htp, hsp⟩, htc, hcnt⟩ := hGen x hx pre hpre
  exact ⟨⟨k, hk, hst, fun i => by rw [htp], hsp⟩, htc, hcnt⟩

end ConcreteRecoveryTheorems



