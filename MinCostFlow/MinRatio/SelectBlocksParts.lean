module

public import MinCostFlow.MinRatio.SelectLevelBlocks
import Mathlib.Tactic

/-!
# The level blocks part by part (`SelectBlocksParts`)

The programs that fill and change the level blocks of the select state each write one part of
one level: the forest `F_j`, the potentials `φ_j`, the core lengths of level `j`, the embedding
slots of level `j`, the last graph, or `g` on `G_0`. This file splits `SelectBlocksAt`
(`SelectLevelBlocks.lean`) into these parts, so that the proof of each program only shows its own
part, and every other part is kept because its words are not written.

* `SelBlocksData`: the model data that the blocks hold, one field per part, and
  `SelBlocksData.ofChain`: the data of a chain.
* The parts `SelPartF`, `SelPartPhi`, `SelPartLen`, `SelPartEmb`, `SelPartLast`, `SelPartG0`, and
  `SelBlocksDataAt`: all parts at all levels.
* `selectBlocksAt_iff_data`: `SelectBlocksAt` is `SelBlocksDataAt` of the data of the chain.
* The regions `regF`, `regPhi`, `regLen`, `regEmb` (inside the block of a level), `regLast` and
  `regG0` (after the level blocks), with the frame of each part (`SelPartF.of_agree`, …) and the
  disjointness of the regions.
* `SelBlocksDataAt.setF`, `setPhi`, `setLen`, `setEmb`, `setLast`, `setG0`: writing only the words
  of one region, and making its part hold for new data, keeps all other parts.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. The data and the parts -/

/-- The model data that the level blocks hold: the vertex sets `V j` and edge sets `E j` of the
level graphs, the forests `F j`, the potentials `φ`, the core lengths `len`, the edges `coreE j`
of the active cores with their walks `emb j`, the last graph `Gd`, and `g` on the edges `E0`
of `G_0`. -/
structure SelBlocksData where
  V : ℕ → Finset ℕ
  E : ℕ → Finset ℕ
  F : ℕ → MGraph
  φ : ℕ → ℕ → ℝ
  len : ℕ → ℕ → ℝ
  coreE : ℕ → Finset ℕ
  emb : ℕ → Embedding
  Gd : MGraph
  E0 : Finset ℕ
  g : ℕ → ℝ

/-- The data of the chain `C` with `d` levels. -/
noncomputable def SelBlocksData.ofChain (C : TreeChain) (d : ℕ) (g ℓ : ℕ → ℝ)
    (φ : ℕ → ℕ → ℝ) : SelBlocksData :=
  ⟨fun j => (C.G j).V, fun j => (C.G j).E, fun j => (C.activeLSF j).F.F, φ,
    fun j => C.chainLen ℓ (j + 1), fun j => (C.activeCore j).E, C.activeEmb, C.G d, (C.G 0).E, g⟩

/-- The forest of level `j`. -/
def SelPartF (mem : ℕ → ℕ) (B : SelectBlocksLoc) (j : ℕ) (F : MGraph) : Prop :=
  DynGraphAt mem (B.fPtr j) B.vCap B.eCap F

/-- The potentials of level `j` on the vertices `V`. -/
def SelPartPhi (mem : ℕ → ℕ) (B : SelectBlocksLoc) (P j : ℕ) (V : Finset ℕ) (φj : ℕ → ℝ) :
    Prop :=
  (∀ v ∈ V, v < B.vCap) ∧ EdgeValuesAt mem (B.phiPtr j) 4 B.Lk P V φj

/-- The core lengths of level `j` on the edges `E`, at precision `coreLenPrec B.d P pLast j`. -/
def SelPartLen (mem : ℕ → ℕ) (B : SelectBlocksLoc) (P j : ℕ) (E : Finset ℕ) (lenj : ℕ → ℝ)
    (pLast : ℕ := 0) : Prop :=
  (∀ e ∈ E, e < B.eCap) ∧ EdgeValuesAt mem (B.lenPtr j) 4 B.Lk (coreLenPrec B.d P pLast j) E lenj

/-- The embedding table and the slots of level `j`, for the edges `E` and the walks `emb`. -/
def SelPartEmb (mem : ℕ → ℕ) (B : SelectBlocksLoc) (j : ℕ) (E : Finset ℕ) (emb : Embedding) :
    Prop :=
  ∀ e ∈ E, e < B.eCap ∧ mem (B.embPtr j + e) = B.slotPtr j e ∧
    (mWalkEncode (emb e)).length ≤ B.slot ∧ MWalkAt mem (B.slotPtr j e) (emb e)

/-- The last graph. -/
def SelPartLast (mem : ℕ → ℕ) (B : SelectBlocksLoc) (Gd : MGraph) : Prop :=
  DynGraphAt mem B.lastGPtr B.vCap B.eCap Gd

/-- The gradient `g` on the edges `E0` of `G_0`. -/
def SelPartG0 (mem : ℕ → ℕ) (B : SelectBlocksLoc) (P : ℕ) (E0 : Finset ℕ) (g : ℕ → ℝ) : Prop :=
  (∀ e ∈ E0, e < B.eCap) ∧ EdgeValuesAt mem B.g0Ptr 4 B.Lk P E0 g

/-- All parts of the blocks, for the data `D`. -/
def SelBlocksDataAt (mem : ℕ → ℕ) (B : SelectBlocksLoc) (P : ℕ) (D : SelBlocksData)
    (pLast : ℕ := 0) : Prop :=
  (∀ j ≤ B.d, SelPartF mem B j (D.F j)) ∧
  (∀ j ≤ B.d, SelPartPhi mem B P j (D.V j) (D.φ j)) ∧
  (∀ j ≤ B.d, SelPartLen mem B P j (D.E j) (D.len j) pLast) ∧
  (∀ j < B.d, SelPartEmb mem B j (D.coreE j) (D.emb j)) ∧
  SelPartLast mem B D.Gd ∧
  SelPartG0 mem B P D.E0 D.g

/-- **The blocks as parts.** `SelectBlocksAt` is `SelBlocksDataAt` of the data of the chain. -/
theorem selectBlocksAt_iff_data {mem : ℕ → ℕ} {B : SelectBlocksLoc} {P pLast : ℕ} {C : TreeChain}
    {g ℓ : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} :
    SelectBlocksAt mem B P C g ℓ φ pLast ↔
      SelBlocksDataAt mem B P (SelBlocksData.ofChain C B.d g ℓ φ) pLast := by
  constructor
  · rintro ⟨hV, hE, hF, hPhi, hLen, hEmb, hLastG, hg0⟩
    exact ⟨hF, fun j hj => ⟨hV j hj, hPhi j hj⟩, fun j hj => ⟨hE j hj, hLen j hj⟩, hEmb,
      hLastG, ⟨hE 0 (Nat.zero_le _), hg0⟩⟩
  · rintro ⟨hF, hPhi, hLen, hEmb, hLastG, ⟨_, hg0⟩⟩
    exact ⟨fun j hj => (hPhi j hj).1, fun j hj => (hLen j hj).1, hF, fun j hj => (hPhi j hj).2,
      fun j hj => (hLen j hj).2, hEmb, hLastG, hg0⟩

/-! ## 2. The regions -/

namespace SelectBlocksLoc

/-- The words of the forest of level `j`. -/
def regF (B : SelectBlocksLoc) (j a : ℕ) : Prop := B.fPtr j ≤ a ∧ a < B.phiPtr j

/-- The words of the potentials of level `j`. -/
def regPhi (B : SelectBlocksLoc) (j a : ℕ) : Prop := B.phiPtr j ≤ a ∧ a < B.lenPtr j

/-- The words of the core lengths of level `j`. -/
def regLen (B : SelectBlocksLoc) (j a : ℕ) : Prop := B.lenPtr j ≤ a ∧ a < B.embPtr j

/-- The words of the embedding table and the slots of level `j`. -/
def regEmb (B : SelectBlocksLoc) (j a : ℕ) : Prop :=
  B.embPtr j ≤ a ∧ a < B.fPtr j + B.levelSize

/-- The words of the last graph. -/
def regLast (B : SelectBlocksLoc) (a : ℕ) : Prop := B.lastGPtr ≤ a ∧ a < B.g0Ptr

/-- The words of `g` on `G_0`. -/
def regG0 (B : SelectBlocksLoc) (a : ℕ) : Prop := B.g0Ptr ≤ a ∧ a < B.endAddr

/-- The block of level `j`. -/
def regBlk (B : SelectBlocksLoc) (j a : ℕ) : Prop := B.fPtr j ≤ a ∧ a < B.fPtr j + B.levelSize

theorem phiPtr_eq (B : SelectBlocksLoc) (j : ℕ) :
    B.phiPtr j = B.fPtr j + dynGraphSize B.vCap B.eCap := rfl

theorem lenPtr_eq (B : SelectBlocksLoc) (j : ℕ) :
    B.lenPtr j = B.fPtr j + dynGraphSize B.vCap B.eCap + B.vCap * B.Lk := rfl

theorem embPtr_eq (B : SelectBlocksLoc) (j : ℕ) :
    B.embPtr j = B.fPtr j + dynGraphSize B.vCap B.eCap + B.vCap * B.Lk + B.eCap * B.Lk := rfl

theorem blkEnd_eq (B : SelectBlocksLoc) (j : ℕ) :
    B.fPtr j + B.levelSize = B.fPtr j + dynGraphSize B.vCap B.eCap + B.vCap * B.Lk +
      B.eCap * B.Lk + B.eCap + B.eCap * B.slot := by
  unfold levelSize; omega

/-- A block ends before the next one starts. -/
theorem blk_le_of_lt (B : SelectBlocksLoc) {j j' : ℕ} (h : j < j') :
    B.fPtr j + B.levelSize ≤ B.fPtr j' := by
  have := Nat.mul_le_mul_right B.levelSize (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at this
  unfold fPtr; omega

/-- Every block of a level `j ≤ d` ends before the last graph. -/
theorem blk_le_last (B : SelectBlocksLoc) {j : ℕ} (h : j ≤ B.d) :
    B.fPtr j + B.levelSize ≤ B.lastGPtr := by
  have : (j + 1) * B.levelSize ≤ (B.d + 1) * B.levelSize :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  unfold fPtr lastGPtr; omega

theorem regF_blk {B : SelectBlocksLoc} {j a : ℕ} (h : B.regF j a) : B.regBlk j a := by
  have h1 := B.blkEnd_eq j
  have h2 := B.phiPtr_eq j
  unfold regF at h; unfold regBlk; omega

theorem regPhi_blk {B : SelectBlocksLoc} {j a : ℕ} (h : B.regPhi j a) : B.regBlk j a := by
  have h1 := B.blkEnd_eq j
  have h2 := B.phiPtr_eq j
  have h3 := B.lenPtr_eq j
  unfold regPhi at h; unfold regBlk; omega

theorem regLen_blk {B : SelectBlocksLoc} {j a : ℕ} (h : B.regLen j a) : B.regBlk j a := by
  have h1 := B.blkEnd_eq j
  have h2 := B.lenPtr_eq j
  have h3 := B.embPtr_eq j
  unfold regLen at h; unfold regBlk; omega

theorem regEmb_blk {B : SelectBlocksLoc} {j a : ℕ} (h : B.regEmb j a) : B.regBlk j a := by
  have h3 := B.embPtr_eq j
  unfold regEmb at h; unfold regBlk; omega

/-- Two different levels have disjoint blocks. -/
theorem regBlk_disj {B : SelectBlocksLoc} {j j' a : ℕ} (hne : j ≠ j') (h : B.regBlk j a) :
    ¬ B.regBlk j' a := by
  unfold regBlk at *
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := B.blk_le_of_lt hlt; omega
  · have := B.blk_le_of_lt hlt; omega

/-- The blocks of the levels `j ≤ d` lie before the last graph. -/
theorem regBlk_not_last {B : SelectBlocksLoc} {j a : ℕ} (hj : j ≤ B.d) (h : B.regBlk j a) :
    ¬ B.regLast a := by
  have := B.blk_le_last hj
  unfold regBlk at h; unfold regLast; omega

theorem regBlk_not_g0 {B : SelectBlocksLoc} {j a : ℕ} (hj : j ≤ B.d) (h : B.regBlk j a) :
    ¬ B.regG0 a := by
  have := B.blk_le_last hj
  unfold regBlk at h; unfold regG0 g0Ptr; omega

theorem regLast_not_g0 {B : SelectBlocksLoc} {a : ℕ} (h : B.regLast a) : ¬ B.regG0 a := by
  unfold regLast at h; unfold regG0; omega

/-- Inside one block the four regions come in the order `F`, `φ`, core lengths, embeddings. Two
regions of one kind at different levels lie in different blocks. -/
theorem regF_not_phi {B : SelectBlocksLoc} {j j' a : ℕ} (h : B.regF j a) : ¬ B.regPhi j' a := by
  intro h'
  by_cases hj : j = j'
  · subst hj; unfold regF at h; unfold regPhi at h'; omega
  · exact regBlk_disj hj (regF_blk h) (regPhi_blk h')

theorem regF_not_len {B : SelectBlocksLoc} {j j' a : ℕ} (h : B.regF j a) : ¬ B.regLen j' a := by
  intro h'
  by_cases hj : j = j'
  · subst hj; have := B.lenPtr_eq j; have := B.phiPtr_eq j
    unfold regF at h; unfold regLen at h'; omega
  · exact regBlk_disj hj (regF_blk h) (regLen_blk h')

theorem regF_not_emb {B : SelectBlocksLoc} {j j' a : ℕ} (h : B.regF j a) : ¬ B.regEmb j' a := by
  intro h'
  by_cases hj : j = j'
  · subst hj; have := B.embPtr_eq j; have := B.phiPtr_eq j
    unfold regF at h; unfold regEmb at h'; omega
  · exact regBlk_disj hj (regF_blk h) (regEmb_blk h')

theorem regPhi_not_len {B : SelectBlocksLoc} {j j' a : ℕ} (h : B.regPhi j a) :
    ¬ B.regLen j' a := by
  intro h'
  by_cases hj : j = j'
  · subst hj; unfold regPhi at h; unfold regLen at h'; omega
  · exact regBlk_disj hj (regPhi_blk h) (regLen_blk h')

theorem regPhi_not_emb {B : SelectBlocksLoc} {j j' a : ℕ} (h : B.regPhi j a) :
    ¬ B.regEmb j' a := by
  intro h'
  by_cases hj : j = j'
  · subst hj; have := B.embPtr_eq j; have := B.lenPtr_eq j
    unfold regPhi at h; unfold regEmb at h'; omega
  · exact regBlk_disj hj (regPhi_blk h) (regEmb_blk h')

theorem regLen_not_emb {B : SelectBlocksLoc} {j j' a : ℕ} (h : B.regLen j a) :
    ¬ B.regEmb j' a := by
  intro h'
  by_cases hj : j = j'
  · subst hj; unfold regLen at h; unfold regEmb at h'; omega
  · exact regBlk_disj hj (regLen_blk h) (regEmb_blk h')

theorem regF_disj {B : SelectBlocksLoc} {j j' a : ℕ} (hne : j ≠ j') (h : B.regF j a) :
    ¬ B.regF j' a := fun h' => regBlk_disj hne (regF_blk h) (regF_blk h')

theorem regPhi_disj {B : SelectBlocksLoc} {j j' a : ℕ} (hne : j ≠ j') (h : B.regPhi j a) :
    ¬ B.regPhi j' a := fun h' => regBlk_disj hne (regPhi_blk h) (regPhi_blk h')

theorem regLen_disj {B : SelectBlocksLoc} {j j' a : ℕ} (hne : j ≠ j') (h : B.regLen j a) :
    ¬ B.regLen j' a := fun h' => regBlk_disj hne (regLen_blk h) (regLen_blk h')

theorem regEmb_disj {B : SelectBlocksLoc} {j j' a : ℕ} (hne : j ≠ j') (h : B.regEmb j a) :
    ¬ B.regEmb j' a := fun h' => regBlk_disj hne (regEmb_blk h) (regEmb_blk h')

end SelectBlocksLoc

open SelectBlocksLoc

/-! ## 3. Each part depends only on its region -/

private theorem mul_add_lt_mul' {v c L i : ℕ} (hv : v < c) (hi : i < L) : v * L + i < c * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at this
  omega

theorem SelPartF.of_agree {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {j : ℕ} {F : MGraph}
    (h : SelPartF mem B j F) (hag : ∀ a, B.regF j a → mem' a = mem a) : SelPartF mem' B j F :=
  DynGraphAt.of_agree h fun a h1 h2 => hag a ⟨h1, h2⟩

theorem SelPartPhi.of_agree {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P j : ℕ} {V : Finset ℕ}
    {φj : ℕ → ℝ} (h : SelPartPhi mem B P j V φj) (hag : ∀ a, B.regPhi j a → mem' a = mem a) :
    SelPartPhi mem' B P j V φj := by
  refine ⟨h.1, EdgeValuesAt.congr h.2 fun v hv i hi => hag _ ⟨by omega, ?_⟩⟩
  have := mul_add_lt_mul' (h.1 v hv) hi
  unfold lenPtr; omega

theorem SelPartLen.of_agree {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P j pLast : ℕ}
    {E : Finset ℕ} {lenj : ℕ → ℝ} (h : SelPartLen mem B P j E lenj pLast)
    (hag : ∀ a, B.regLen j a → mem' a = mem a) :
    SelPartLen mem' B P j E lenj pLast := by
  refine ⟨h.1, EdgeValuesAt.congr h.2 fun e he i hi => hag _ ⟨by omega, ?_⟩⟩
  have := mul_add_lt_mul' (h.1 e he) hi
  unfold embPtr; omega

theorem SelPartEmb.of_agree {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {j : ℕ} {E : Finset ℕ}
    {emb : Embedding} (h : SelPartEmb mem B j E emb)
    (hag : ∀ a, B.regEmb j a → mem' a = mem a) : SelPartEmb mem' B j E emb := by
  intro e he
  obtain ⟨h1, h2, h3, h4⟩ := h e he
  have hend := B.blkEnd_eq j
  have hemb := B.embPtr_eq j
  refine ⟨h1, ?_, h3, fun i hi => ?_⟩
  · rw [hag _ ⟨by omega, by omega⟩]; exact h2
  · have hi' : i < B.slot := lt_of_lt_of_le hi h3
    have := mul_add_lt_mul' h1 hi'
    rw [hag _ ⟨by unfold slotPtr; omega, by unfold slotPtr; omega⟩]
    exact h4 i hi

theorem SelPartLast.of_agree {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {Gd : MGraph}
    (h : SelPartLast mem B Gd) (hag : ∀ a, B.regLast a → mem' a = mem a) :
    SelPartLast mem' B Gd :=
  DynGraphAt.of_agree h fun a h1 h2 => hag a ⟨h1, by unfold g0Ptr; omega⟩

theorem SelPartG0.of_agree {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P : ℕ} {E0 : Finset ℕ}
    {g : ℕ → ℝ} (h : SelPartG0 mem B P E0 g) (hag : ∀ a, B.regG0 a → mem' a = mem a) :
    SelPartG0 mem' B P E0 g := by
  refine ⟨h.1, EdgeValuesAt.congr h.2 fun e he i hi => hag _ ⟨by omega, ?_⟩⟩
  have := mul_add_lt_mul' (h.1 e he) hi
  unfold endAddr; omega

/-! ## 4. Writing one region keeps the other parts -/

/-- All parts hold at `mem'` if `mem'` agrees with `mem` on every region of the blocks. -/
theorem SelBlocksDataAt.of_agree {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P pLast : ℕ}
    {D : SelBlocksData} (h : SelBlocksDataAt mem B P D pLast)
    (hag : ∀ a, B.base ≤ a → a < B.endAddr → mem' a = mem a) :
    SelBlocksDataAt mem' B P D pLast := by
  have hb : ∀ j a, B.regBlk j a → B.base ≤ a := fun j a h => by
    unfold regBlk fPtr at h; omega
  have he : ∀ j a, j ≤ B.d → B.regBlk j a → a < B.endAddr := fun j a hj h => by
    have := B.blk_le_last hj
    unfold regBlk at h; unfold endAddr g0Ptr; omega
  obtain ⟨hF, hPhi, hLen, hEmb, hLast, hG0⟩ := h
  refine ⟨fun j hj => (hF j hj).of_agree fun a ha => hag a (hb j a (regF_blk ha))
      (he j a hj (regF_blk ha)),
    fun j hj => (hPhi j hj).of_agree fun a ha => hag a (hb j a (regPhi_blk ha))
      (he j a hj (regPhi_blk ha)),
    fun j hj => (hLen j hj).of_agree fun a ha => hag a (hb j a (regLen_blk ha))
      (he j a hj (regLen_blk ha)),
    fun j hj => (hEmb j hj).of_agree fun a ha => hag a (hb j a (regEmb_blk ha))
      (he j a hj.le (regEmb_blk ha)),
    hLast.of_agree fun a ha => hag a ?_ ?_, hG0.of_agree fun a ha => hag a ?_ ha.2⟩
  · unfold regLast lastGPtr at ha; omega
  · unfold regLast at ha; unfold endAddr; omega
  · unfold regG0 g0Ptr lastGPtr at ha; omega

/-- **The forest of level `j`.** Writing only the words of `F_j`, with a new forest `F'` there,
keeps the other parts. -/
theorem SelBlocksDataAt.setF {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P j pLast : ℕ}
    {D : SelBlocksData} {F' : MGraph} (h : SelBlocksDataAt mem B P D pLast) (hj : j ≤ B.d)
    (hag : ∀ a, ¬ B.regF j a → mem' a = mem a) (hF : SelPartF mem' B j F') :
    SelBlocksDataAt mem' B P { D with F := Function.update D.F j F' } pLast := by
  obtain ⟨hF0, hPhi, hLen, hEmb, hLast, hG0⟩ := h
  refine ⟨fun j' hj' => ?_, fun j' hj' => (hPhi j' hj').of_agree fun a ha =>
      hag a fun h' => regF_not_phi h' ha,
    fun j' hj' => (hLen j' hj').of_agree fun a ha => hag a fun h' => regF_not_len h' ha,
    fun j' hj' => (hEmb j' hj').of_agree fun a ha => hag a fun h' => regF_not_emb h' ha,
    hLast.of_agree fun a ha => hag a fun h' => regBlk_not_last hj (regF_blk h') ha,
    hG0.of_agree fun a ha => hag a fun h' => regBlk_not_g0 hj (regF_blk h') ha⟩
  by_cases hjj : j' = j
  · subst hjj; simpa using hF
  · simp only [Function.update_of_ne hjj]
    exact (hF0 j' hj').of_agree fun a ha => hag a fun h' => regF_disj (Ne.symm hjj) h' ha

/-- **The potentials of level `j`.** Writing only the words of `φ_j`, with new vertices `V'` and
potentials `φj'` there, keeps the other parts. -/
theorem SelBlocksDataAt.setPhi {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P j pLast : ℕ}
    {D : SelBlocksData} {V' : Finset ℕ} {φj' : ℕ → ℝ} (h : SelBlocksDataAt mem B P D pLast)
    (hj : j ≤ B.d) (hag : ∀ a, ¬ B.regPhi j a → mem' a = mem a)
    (hPhi' : SelPartPhi mem' B P j V' φj') :
    SelBlocksDataAt mem' B P
      { D with V := Function.update D.V j V', φ := Function.update D.φ j φj' } pLast := by
  obtain ⟨hF, hPhi, hLen, hEmb, hLast, hG0⟩ := h
  refine ⟨fun j' hj' => (hF j' hj').of_agree fun a ha => hag a fun h' => regF_not_phi ha h',
    fun j' hj' => ?_,
    fun j' hj' => (hLen j' hj').of_agree fun a ha => hag a fun h' => regPhi_not_len h' ha,
    fun j' hj' => (hEmb j' hj').of_agree fun a ha => hag a fun h' => regPhi_not_emb h' ha,
    hLast.of_agree fun a ha => hag a fun h' => regBlk_not_last hj (regPhi_blk h') ha,
    hG0.of_agree fun a ha => hag a fun h' => regBlk_not_g0 hj (regPhi_blk h') ha⟩
  by_cases hjj : j' = j
  · subst hjj; simpa using hPhi'
  · simp only [Function.update_of_ne hjj]
    exact (hPhi j' hj').of_agree fun a ha => hag a fun h' => regPhi_disj (Ne.symm hjj) h' ha

/-- **The core lengths of level `j`.** Writing only the words of the core lengths of level `j`,
with new edges `E'` and lengths `lenj'` there, keeps the other parts. -/
theorem SelBlocksDataAt.setLen {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P j pLast : ℕ}
    {D : SelBlocksData} {E' : Finset ℕ} {lenj' : ℕ → ℝ} (h : SelBlocksDataAt mem B P D pLast)
    (hj : j ≤ B.d) (hag : ∀ a, ¬ B.regLen j a → mem' a = mem a)
    (hLen' : SelPartLen mem' B P j E' lenj' pLast) :
    SelBlocksDataAt mem' B P
      { D with E := Function.update D.E j E', len := Function.update D.len j lenj' } pLast := by
  obtain ⟨hF, hPhi, hLen, hEmb, hLast, hG0⟩ := h
  refine ⟨fun j' hj' => (hF j' hj').of_agree fun a ha => hag a fun h' => regF_not_len ha h',
    fun j' hj' => (hPhi j' hj').of_agree fun a ha => hag a fun h' => regPhi_not_len ha h',
    fun j' hj' => ?_,
    fun j' hj' => (hEmb j' hj').of_agree fun a ha => hag a fun h' => regLen_not_emb h' ha,
    hLast.of_agree fun a ha => hag a fun h' => regBlk_not_last hj (regLen_blk h') ha,
    hG0.of_agree fun a ha => hag a fun h' => regBlk_not_g0 hj (regLen_blk h') ha⟩
  by_cases hjj : j' = j
  · subst hjj; simpa using hLen'
  · simp only [Function.update_of_ne hjj]
    exact (hLen j' hj').of_agree fun a ha => hag a fun h' => regLen_disj (Ne.symm hjj) h' ha

/-- **The embedding slots of level `j < d`.** Writing only the words of the embedding table and
the slots of level `j`, with new edges `E'` and walks `emb'` there, keeps the other parts. -/
theorem SelBlocksDataAt.setEmb {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P j pLast : ℕ}
    {D : SelBlocksData} {E' : Finset ℕ} {emb' : Embedding} (h : SelBlocksDataAt mem B P D pLast)
    (hj : j < B.d) (hag : ∀ a, ¬ B.regEmb j a → mem' a = mem a)
    (hEmb' : SelPartEmb mem' B j E' emb') :
    SelBlocksDataAt mem' B P
      { D with coreE := Function.update D.coreE j E', emb := Function.update D.emb j emb' } pLast := by
  obtain ⟨hF, hPhi, hLen, hEmb, hLast, hG0⟩ := h
  refine ⟨fun j' hj' => (hF j' hj').of_agree fun a ha => hag a fun h' => regF_not_emb ha h',
    fun j' hj' => (hPhi j' hj').of_agree fun a ha => hag a fun h' => regPhi_not_emb ha h',
    fun j' hj' => (hLen j' hj').of_agree fun a ha => hag a fun h' => regLen_not_emb ha h',
    fun j' hj' => ?_,
    hLast.of_agree fun a ha => hag a fun h' => regBlk_not_last hj.le (regEmb_blk h') ha,
    hG0.of_agree fun a ha => hag a fun h' => regBlk_not_g0 hj.le (regEmb_blk h') ha⟩
  by_cases hjj : j' = j
  · subst hjj; simpa using hEmb'
  · simp only [Function.update_of_ne hjj]
    exact (hEmb j' hj').of_agree fun a ha => hag a fun h' => regEmb_disj (Ne.symm hjj) h' ha

/-- **The last graph.** Writing only the words of the last graph, with a new graph `Gd'` there,
keeps the other parts. -/
theorem SelBlocksDataAt.setLast {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P pLast : ℕ}
    {D : SelBlocksData} {Gd' : MGraph} (h : SelBlocksDataAt mem B P D pLast)
    (hag : ∀ a, ¬ B.regLast a → mem' a = mem a) (hLast' : SelPartLast mem' B Gd') :
    SelBlocksDataAt mem' B P { D with Gd := Gd' } pLast := by
  obtain ⟨hF, hPhi, hLen, hEmb, _, hG0⟩ := h
  exact ⟨fun j' hj' => (hF j' hj').of_agree fun a ha =>
      hag a (regBlk_not_last hj' (regF_blk ha)),
    fun j' hj' => (hPhi j' hj').of_agree fun a ha => hag a (regBlk_not_last hj' (regPhi_blk ha)),
    fun j' hj' => (hLen j' hj').of_agree fun a ha => hag a (regBlk_not_last hj' (regLen_blk ha)),
    fun j' hj' => (hEmb j' hj').of_agree fun a ha =>
      hag a (regBlk_not_last hj'.le (regEmb_blk ha)),
    hLast', hG0.of_agree fun a ha => hag a fun h' => regLast_not_g0 h' ha⟩

/-- **The gradient on `G_0`.** Writing only the words of `g` on `G_0`, with new edges `E0'` and
values `g'` there, keeps the other parts. -/
theorem SelBlocksDataAt.setG0 {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P pLast : ℕ}
    {D : SelBlocksData} {E0' : Finset ℕ} {g' : ℕ → ℝ} (h : SelBlocksDataAt mem B P D pLast)
    (hag : ∀ a, ¬ B.regG0 a → mem' a = mem a) (hG0' : SelPartG0 mem' B P E0' g') :
    SelBlocksDataAt mem' B P { D with E0 := E0', g := g' } pLast := by
  obtain ⟨hF, hPhi, hLen, hEmb, hLast, _⟩ := h
  exact ⟨fun j' hj' => (hF j' hj').of_agree fun a ha => hag a (regBlk_not_g0 hj' (regF_blk ha)),
    fun j' hj' => (hPhi j' hj').of_agree fun a ha => hag a (regBlk_not_g0 hj' (regPhi_blk ha)),
    fun j' hj' => (hLen j' hj').of_agree fun a ha => hag a (regBlk_not_g0 hj' (regLen_blk ha)),
    fun j' hj' => (hEmb j' hj').of_agree fun a ha =>
      hag a (regBlk_not_g0 hj'.le (regEmb_blk ha)),
    hLast.of_agree fun a ha => hag a (regLast_not_g0 ha), hG0'⟩

end MinCostFlow.MinRatio
