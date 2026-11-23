module

public import MinCostFlow.LinkCut.Gen.Call
public import WordRAM.Tactic

/-!
# A stack of noted nodes, kept below the records

Find-ready needs to know which auxiliary trees may hold a ready edge. The tree programs keep a
stack of node ids for this ("noted" nodes), with one flag word per node so that a node is on the
stack at most once. The stack lives just below the record of node `0`, at `nb`:

* the number of entries is at `nb - 1`;
* the flag of node `x` is at `nb - (2 x + 2)`;
* entry `i` of the stack is at `nb - (2 i + 3)`.

So the index takes the `2 cap + 3` words below `nb`. `IdxAt mem nb cap S` says that memory holds
the stack `S` (bottom first). `noteBody` pushes a node if it is not flagged yet; in the model this
is `noteList`. `TreeFrameN` is the frame of a tree program that may also change the index.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM NodeLayout

variable {α σ τ : Type*}

/-- Address of the flag of node `x`. -/
def flagAddr (nb x : ℕ) : ℕ := nb - (2 * x + 2)

/-- Address of entry `i` of the stack. -/
def slotAddr (nb i : ℕ) : ℕ := nb - (2 * i + 3)

/-- The cells of the index. -/
def InIndex (nb cap a : ℕ) : Prop := nb ≤ a + (2 * cap + 3) ∧ a < nb

/-- Memory holds the stack `S` of noted nodes, all at most `cap`, each once. -/
structure IdxAt (mem : ℕ → ℕ) (nb cap : ℕ) (S : List ℕ) : Prop where
  nodup : S.Nodup
  le : ∀ z ∈ S, z ≤ cap
  top : mem (nb - 1) = S.length
  slot : ∀ i (hi : i < S.length), mem (slotAddr nb i) = S[i]
  flag : ∀ x ≤ cap, mem (flagAddr nb x) = if x ∈ S then 1 else 0

/-- Push `x` unless it is already on the stack. -/
def noteList (S : List ℕ) (x : ℕ) : List ℕ := if x ∈ S then S else S ++ [x]

theorem mem_noteList {S : List ℕ} {x z : ℕ} : z ∈ noteList S x ↔ z ∈ S ∨ z = x := by
  unfold noteList
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h' | rfl)
      · exact h'
      · exact h
  · simp

theorem subset_noteList (S : List ℕ) (x : ℕ) : S ⊆ noteList S x :=
  fun _ h => mem_noteList.mpr (Or.inl h)

theorem IdxAt.length_le {mem : ℕ → ℕ} {nb cap : ℕ} {S : List ℕ} (h : IdxAt mem nb cap S) :
    S.length ≤ cap + 1 := by
  have hsub : S.toFinset ⊆ Finset.range (cap + 1) := by
    intro z hz
    rw [List.mem_toFinset] at hz
    simpa [Nat.lt_succ_iff] using h.le z hz
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup h.nodup, Finset.card_range] at this

/-- If `x ≤ cap` is not on the stack, the stack has room for it. -/
theorem IdxAt.length_lt {mem : ℕ → ℕ} {nb cap x : ℕ} {S : List ℕ} (h : IdxAt mem nb cap S)
    (hx : x ≤ cap) (hxS : x ∉ S) : S.length ≤ cap := by
  have hsub : (x :: S).toFinset ⊆ Finset.range (cap + 1) := by
    intro z hz
    rw [List.mem_toFinset, List.mem_cons] at hz
    rcases hz with rfl | hz
    · simpa [Nat.lt_succ_iff] using hx
    · simpa [Nat.lt_succ_iff] using h.le z hz
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (List.nodup_cons.mpr ⟨hxS, h.nodup⟩), Finset.card_range,
    List.length_cons] at this
  omega

/-- The index depends only on its own cells. -/
theorem IdxAt.congr {mem mem' : ℕ → ℕ} {nb cap : ℕ} {S : List ℕ} (h : IdxAt mem nb cap S)
    (hnb : 2 * cap + 3 ≤ nb) (hag : ∀ a, InIndex nb cap a → mem' a = mem a) :
    IdxAt mem' nb cap S := by
  have hlen := h.length_le
  refine ⟨h.nodup, h.le, ?_, fun i hi => ?_, fun x hx => ?_⟩
  · rw [hag _ ⟨by omega, by omega⟩]; exact h.top
  · rw [hag _ ⟨by unfold slotAddr; omega, by unfold slotAddr; omega⟩]; exact h.slot i hi
  · rw [hag _ ⟨by unfold flagAddr; omega, by unfold flagAddr; omega⟩]; exact h.flag x hx

/-- The frame of a tree program that may also change the index: memory from `h` on is zero,
and below `h` only record cells and index cells may change. -/
def TreeFrameN (Lay : NodeLayout α σ τ) (nb cap h : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  ZeroFrom mem' h ∧ ∀ a < h, ¬ Lay.InRecords nb cap a → ¬ InIndex nb cap a → mem' a = mem a

theorem TreeFrame.toN {Lay : NodeLayout α σ τ} {nb cap h : ℕ} {mem mem' : ℕ → ℕ}
    (hf : TreeFrame Lay nb cap h mem mem') : TreeFrameN Lay nb cap h mem mem' :=
  ⟨hf.1, fun a ha hr _ => hf.2 a ha hr⟩

theorem TreeFrameN.trans {Lay : NodeLayout α σ τ} {nb cap h : ℕ} {m₁ m₂ m₃ : ℕ → ℕ}
    (h₁ : TreeFrameN Lay nb cap h m₁ m₂) (h₂ : TreeFrameN Lay nb cap h m₂ m₃) :
    TreeFrameN Lay nb cap h m₁ m₃ :=
  ⟨h₂.1, fun a ha hr hi => (h₂.2 a ha hr hi).trans (h₁.2 a ha hr hi)⟩

/-- A tree program that keeps `TreeFrame` keeps the index. -/
theorem IdxAt.of_treeFrame {Lay : NodeLayout α σ τ} {nb cap h : ℕ} {mem mem' : ℕ → ℕ}
    {S : List ℕ} (hI : IdxAt mem nb cap S) (hnb : 2 * cap + 3 ≤ nb) (hnh : nb ≤ h)
    (hf : TreeFrame Lay nb cap h mem mem') : IdxAt mem' nb cap S :=
  hI.congr hnb fun a ha => hf.2 a (by have := ha.2; omega) fun hr => by
    have := hr.1; have := ha.2; omega

/-- Index cells are not record cells. -/
theorem not_inRecords_of_inIndex {Lay : NodeLayout α σ τ} {nb cap a : ℕ}
    (ha : InIndex nb cap a) : ¬ Lay.InRecords nb cap a := fun hr => by
  have := hr.1; have := ha.2; omega

/-- `note [nb, x]`: push `x` unless its flag is set. -/
def noteBody : Stmt :=
  .assign 2 (.load (.bin .sub (.reg 0) (.bin .add (.bin .add (.reg 1) (.reg 1)) (.const 2)))) ;;
  .cond (.reg 2) (.ret (.const 0))
    (.assign 3 (.load (.bin .sub (.reg 0) (.const 1))) ;;
     .store (.bin .sub (.reg 0) (.bin .add (.bin .add (.reg 3) (.reg 3)) (.const 3))) (.reg 1) ;;
     .store (.bin .sub (.reg 0) (.bin .add (.bin .add (.reg 1) (.reg 1)) (.const 2))) (.const 1) ;;
     .store (.bin .sub (.reg 0) (.const 1)) (.bin .add (.reg 3) (.const 1)) ;;
     .ret (.const 0))

theorem noteBody_noRand : noteBody.NoRand := by
  simp [noteBody, Stmt.NoRand]

/-- The run of `noteBody`: the index now holds `noteList S x`, and no other cell changes. -/
theorem noteBody_runs {w : ℕ} {p : Program} (ω : ℕ → Bool) {nb cap x pos : ℕ} {mem : ℕ → ℕ}
    {S : List ℕ} (hI : IdxAt mem nb cap S) (hx : x ≤ cap) (hnb : 2 * cap + 3 ≤ nb)
    (hw : nb < 2 ^ w) :
    ∃ o st' c, Runs w p ω noteBody (startState [nb, x] mem pos) o st' c ∧
      (IdxAt st'.mem nb cap (noteList S x) ∧ ∀ a, ¬ InIndex nb cap a → st'.mem a = mem a) ∧
      0 + c ≤ 60 := by
  have hflag : mem (nb - (x + x + 2)) = if x ∈ S then 1 else 0 := by
    have := hI.flag x hx; unfold flagAddr at this; rwa [two_mul] at this
  unfold noteBody
  rw [startState]
  wram_step; try dsimp only
  rw [hflag]
  wram_step
  · wram_step
    · exact ⟨by simpa [noteList, hcond] using hI, fun _ _ => rfl⟩
    · wram_cost
  have hxS : x ∉ S := by
    intro hxS; simp [hxS] at hcond
  have hlen := hI.length_lt hx hxS
  have htop := hI.top
  wram_step; try dsimp only
  rw [htop]
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₁ hM₁ => ?_
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₂ hM₂ => ?_
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₃ hM₃ => ?_
  wram_step
  · have hM : ∀ a, M₃ a = if a = nb - 1 then S.length + 1 else
        if a = nb - (x + x + 2) then 1 else
        if a = nb - (S.length + S.length + 3) then x else mem a := by
      intro a; rw [hM₃, hM₂, hM₁]; simp only [Function.update_apply]
    have hS' : noteList S x = S ++ [x] := by simp [noteList, hxS]
    rw [hS']
    refine ⟨⟨List.nodup_append.mpr ⟨hI.nodup, List.nodup_singleton x, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro a ha b hb; simp at hb; subst hb; rintro rfl; exact hxS ha
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hI.le z hz
      · simp at hz; omega
    · show M₃ (nb - 1) = _
      rw [hM]; simp
    · intro i hi
      show M₃ (nb - (2 * i + 3)) = _
      rw [hM, if_neg (by omega), if_neg (by omega)]
      rw [List.length_append, List.length_singleton] at hi
      by_cases hil : i < S.length
      · rw [if_neg (by omega), List.getElem_append_left hil]
        exact hI.slot i hil
      · have hiS : i = S.length := by omega
        subst hiS
        rw [if_pos (by omega)]
        simp
    · intro y hy
      show M₃ (nb - (2 * y + 2)) = _
      by_cases hyx : y = x
      · subst hyx; rw [hM, if_neg (by omega), if_pos (by omega)]; simp
      · rw [hM, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        have := hI.flag y hy
        unfold flagAddr at this
        rw [this]
        simp [hyx]
    · intro a ha
      show M₃ a = mem a
      rw [hM, if_neg ?_, if_neg ?_, if_neg ?_]
      · rintro rfl; exact ha ⟨by omega, by omega⟩
      · rintro rfl; exact ha ⟨by omega, by omega⟩
      · rintro rfl; exact ha ⟨by omega, by omega⟩
  · wram_cost

/-- `pop [nb]`: remove the top entry of a nonempty stack and clear its flag; return it. -/
def popBody : Stmt :=
  .assign 1 (.load (.bin .sub (.reg 0) (.const 1))) ;;
  .assign 2 (.load (.bin .sub (.reg 0) (.bin .add (.bin .add (.reg 1) (.reg 1)) (.const 1)))) ;;
  .store (.bin .sub (.reg 0) (.bin .add (.bin .add (.reg 2) (.reg 2)) (.const 2))) (.const 0) ;;
  .store (.bin .sub (.reg 0) (.const 1)) (.bin .sub (.reg 1) (.const 1)) ;;
  .ret (.reg 2)

theorem popBody_noRand : popBody.NoRand := by
  simp [popBody, Stmt.NoRand]

/-- The run of `popBody` on the stack `S ++ [x]`: it returns `x`, the index holds `S`, and no
other cell changes. -/
theorem popBody_runs {w : ℕ} {p : Program} (ω : ℕ → Bool) {nb cap x pos : ℕ} {mem : ℕ → ℕ}
    {S : List ℕ} (hI : IdxAt mem nb cap (S ++ [x])) (hnb : 2 * cap + 3 ≤ nb)
    (hw : nb < 2 ^ w) :
    ∃ o st' c, Runs w p ω popBody (startState [nb] mem pos) o st' c ∧
      (o.value = x ∧ IdxAt st'.mem nb cap S ∧ ∀ a, ¬ InIndex nb cap a → st'.mem a = mem a) ∧
      0 + c ≤ 40 := by
  have hlen := hI.length_le
  rw [List.length_append, List.length_singleton] at hlen
  have hx : x ≤ cap := hI.le x (by simp)
  have htop : mem (nb - 1) = S.length + 1 := by rw [hI.top]; simp
  have hslot : mem (nb - (S.length + 1 + (S.length + 1) + 1)) = x := by
    have := hI.slot S.length (by simp)
    unfold slotAddr at this
    rw [show nb - (S.length + 1 + (S.length + 1) + 1) = nb - (2 * S.length + 3) by omega, this]
    simp
  have hnd := hI.nodup
  have hxS : x ∉ S := by
    rw [List.nodup_append] at hnd
    exact fun h => hnd.2.2 x h x (by simp) rfl
  unfold popBody
  rw [startState]
  wram_step; try dsimp only
  rw [htop]
  wram_step; try dsimp only
  rw [hslot]
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₁ hM₁ => ?_
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₂ hM₂ => ?_
  wram_step
  · have hM : ∀ a, M₂ a = if a = nb - 1 then S.length else
        if a = nb - (x + x + 2) then 0 else mem a := by
      intro a; rw [hM₂, hM₁]; simp only [Function.update_apply]
      split_ifs <;> omega
    refine ⟨by simp [Outcome.value], ⟨List.nodup_append.mp hnd |>.1,
      fun z hz => hI.le z (by simp [hz]), ?_, ?_, ?_⟩, ?_⟩
    · show M₂ (nb - 1) = _
      rw [hM]; simp
    · intro i hi
      show M₂ (nb - (2 * i + 3)) = _
      rw [hM, if_neg (by omega), if_neg (by omega)]
      have := hI.slot i (by simp; omega)
      unfold slotAddr at this
      rw [this, List.getElem_append_left hi]
    · intro y hy
      show M₂ (nb - (2 * y + 2)) = _
      by_cases hyx : y = x
      · subst hyx; rw [hM, if_neg (by omega), if_pos (by omega)]; simp [hxS]
      · rw [hM, if_neg (by omega), if_neg (by omega)]
        have := hI.flag y hy
        unfold flagAddr at this
        rw [this]
        simp [hyx]
    · intro a ha
      show M₂ a = mem a
      rw [hM, if_neg ?_, if_neg ?_]
      · rintro rfl; exact ha ⟨by omega, by omega⟩
      · rintro rfl; exact ha ⟨by omega, by omega⟩
  · wram_cost

/-- The frame of a tree program that may note nodes: `TreeFrameN`, and the index holds `S`
after. -/
def IdxFrame (Lay : NodeLayout α σ τ) (nb cap h : ℕ) (mem mem' : ℕ → ℕ) (S : List ℕ) : Prop :=
  TreeFrameN Lay nb cap h mem mem' ∧ IdxAt mem' nb cap S

theorem IdxFrame.of_treeFrame {Lay : NodeLayout α σ τ} {nb cap h : ℕ} {mem mem' : ℕ → ℕ}
    {S : List ℕ} (hI : IdxAt mem nb cap S) (hnb : 2 * cap + 3 ≤ nb) (hnh : nb ≤ h)
    (hf : TreeFrame Lay nb cap h mem mem') : IdxFrame Lay nb cap h mem mem' S :=
  ⟨hf.toN, hI.of_treeFrame hnb hnh hf⟩

theorem IdxFrame.trans {Lay : NodeLayout α σ τ} {nb cap h : ℕ} {m₁ m₂ m₃ : ℕ → ℕ}
    {S T : List ℕ} (h₁ : IdxFrame Lay nb cap h m₁ m₂ S) (h₂ : IdxFrame Lay nb cap h m₂ m₃ T) :
    IdxFrame Lay nb cap h m₁ m₃ T :=
  ⟨h₁.1.trans h₂.1, h₂.2⟩

theorem IdxFrame.trans_tree {Lay : NodeLayout α σ τ} {nb cap h : ℕ} {m₁ m₂ m₃ : ℕ → ℕ}
    {S : List ℕ} (h₁ : IdxFrame Lay nb cap h m₁ m₂ S) (hnb : 2 * cap + 3 ≤ nb)
    (hnh : nb ≤ h) (h₂ : TreeFrame Lay nb cap h m₂ m₃) : IdxFrame Lay nb cap h m₁ m₃ S :=
  h₁.trans (IdxFrame.of_treeFrame h₁.2 hnb hnh h₂)

theorem IdxFrame.refl {Lay : NodeLayout α σ τ} {nb cap h : ℕ} {mem : ℕ → ℕ} {S : List ℕ}
    (hz : ZeroFrom mem h) (hI : IdxAt mem nb cap S) : IdxFrame Lay nb cap h mem mem S :=
  ⟨(TreeFrame.refl hz).toN, hI⟩

/-- A note changes no record cell and nothing from the heap pointer on. -/
theorem TreeFrameN.of_note {Lay : NodeLayout α σ τ} {nb cap h : ℕ} {mem mem' : ℕ → ℕ}
    (hz : ZeroFrom mem h) (hnh : nb ≤ h) (hkeep : ∀ a, ¬ InIndex nb cap a → mem' a = mem a) :
    TreeFrameN Lay nb cap h mem mem' :=
  ⟨fun a ha => by rw [hkeep a fun hi => by have := hi.2; omega]; exact hz a ha,
    fun a _ _ hi => hkeep a hi⟩

theorem HeapOk.nb_le {Lay : NodeLayout α σ τ} {w nb cap heap space : ℕ} {mem : ℕ → ℕ}
    (h : HeapOk Lay w nb cap heap space mem) : nb ≤ heap := by
  have := h.rec_le; unfold nodeAddr at this; omega

end MinCostFlow.LinkCut.Gen
