module

public import MinCostFlow.SparseCore.Program.ReadRecord
public import MinCostFlow.SparseCore.Program.ReadTree
public import WordRAM.DataStructure

/-!
# The representation of the readout data of a branch

This file fixes how the data of one branch (`ReadView`) lives in memory, as a representation
`readRep` in the sense of `WordRAM.DSRep`, and proves that it is local (`readRep_local`).

**The record.** The record at handle `r` has `11` words. The first nine are those of
`ReadRecAt` (`ReadRecord.lean`): pointers to `T`, `F`, the root bits, the stretch descriptor, the
limb count `L_w`, pointers to `S` and to the copy of `G`, and the two stretch tables. The words
`r + 9` and `r + 10` point to two more graphs: the live part `liveT G T` (caps `vCap`, `eCap`) and
the frozen part `frozenT G T` (caps `vCap`, `tCap`) of the tree (`ReadTree.lean`). An update needs
them to split `T` at a cost that the input and a potential pay.

**The blocks** lie in a fixed order after the record (`ReadLayout`): `T`, `F`, the root bits, `S`,
`G`, the numerator table, the denominator table, the live part, the frozen part. Gaps between the
blocks are allowed. So any two blocks are disjoint, which `omega` sees from the chain of
inequalities.

**What the record keeps true** (`ReadKeep`): the tree has the vertices of `G` and the ends of `G`
on its edges that are edges of `G`, and the forest is a subgraph of `G` with the vertices of `G`.
The blocks give the rest that an update needs (valid graphs within the caps). These facts hold
after each single update of a batch, while `ReadView.Inv` (one root per component) holds only
after the whole update. So the batch walk keeps the representation itself as its invariant.

**The concrete state** (`ReadConc`) holds the pointers and the view. The potential is
`readPotMul · treePot G T` (`treePot`, `ReadTree.lean`): a tag-`3` split of `T` pays the smaller of
the moved live ends and the frozen ends from it (`split_amortized`). A restart changes only `S`,
so it keeps the potential, and the initialization pays it from `treePot_le`.

The two readouts of `ReadRecord.lean` give the readout clauses of `ReadBranchAt` for this
representation (`readRep_readLSF`, `readRep_readS`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## The representation -/

/-- The concrete state of the data of a branch: the pointers of the record (`q`), the blocks of
the live part (`live`) and of the frozen part (`frz`) of the tree, and the view, which the
potential reads. -/
structure ReadConc where
  q : ReadPtrs
  live : ℕ
  frz : ℕ
  view : ReadView

/-- The number of words of the full record. -/
def readFullWords : ℕ := 11

/-- The blocks follow the record in a fixed order: `T`, `F`, the root bits, `S`, `G`, the
numerator table, the denominator table, the live part, the frozen part. -/
def ReadLayout (r vCap eCap tCap L_w : ℕ) (y : ReadConc) : Prop :=
  r + readFullWords ≤ y.q.t ∧ y.q.t + dynGraphSize vCap tCap ≤ y.q.f ∧
  y.q.f + dynGraphSize vCap tCap ≤ y.q.roots ∧ y.q.roots + vCap ≤ y.q.s ∧
  y.q.s + dynGraphSize vCap eCap ≤ y.q.g ∧ y.q.g + dynGraphSize vCap eCap ≤ y.q.num ∧
  y.q.num + eCap * L_w ≤ y.q.den ∧ y.q.den + eCap * L_w ≤ y.live ∧
  y.live + dynGraphSize vCap eCap ≤ y.frz

/-- What the data keep true between and during updates: the tree has the vertices of `G` and the
ends of `G` on its edges that are edges of `G`, and the forest has the vertices of `G` and is a
subgraph of `G`. -/
def ReadKeep (v : ReadView) : Prop :=
  v.lsf.T.V = v.G.V ∧
  (∀ e ∈ v.lsf.T.E, e ∈ v.G.E → v.lsf.T.tail e = v.G.tail e ∧ v.lsf.T.head e = v.G.head e) ∧
  v.lsf.F.F.V = v.G.V ∧ v.G.IsSubgraph v.lsf.F.F

/-- The record at `r` holds the view `v` with the concrete state `y`: the view is the one of `y`,
the blocks are in order, `v` meets `ReadKeep`, the first nine words and their blocks hold `v`
(`ReadRecAt`), and the words `r + 9`, `r + 10` point to the live and the frozen part of the tree. -/
def ReadRepAt (vCap eCap tCap L_w P r : ℕ) (v : ReadView) (y : ReadConc) (mem : ℕ → ℕ) :
    Prop :=
  y.view = v ∧ ReadLayout r vCap eCap tCap L_w y ∧ ReadKeep v ∧
  ReadRecAt mem r vCap eCap tCap L_w P v y.q ∧ mem (r + 9) = y.live ∧ mem (r + 10) = y.frz ∧
  DynGraphAt mem y.live vCap eCap (liveT v.G v.lsf.T) ∧
  DynGraphAt mem y.frz vCap tCap (frozenT v.G v.lsf.T)

/-- The cells of the data: the `11` words of the record, the blocks of `ReadRecFoot`, and the
blocks of the live and the frozen part. -/
def readFoot (vCap eCap tCap L_w r : ℕ) (y : ReadConc) (a : ℕ) : Prop :=
  (r ≤ a ∧ a < r + readFullWords) ∨ ReadRecFoot r vCap eCap tCap L_w y.q a ∨
  (y.live ≤ a ∧ a < y.live + dynGraphSize vCap eCap) ∨
  (y.frz ≤ a ∧ a < y.frz + dynGraphSize vCap tCap)

/-- The factor of the potential: it pays a constant per moved end of a split of `T`. -/
def readPotMul : ℕ := 1000

/-- **The representation of the readout data of a branch**, for vertex names below `vCap`, edge
names of `G` and `S` below `eCap`, tree edge names below `tCap`, and stretch tables of `L_w` limbs
of `4` bits at precision `P`. -/
def readRep (vCap eCap tCap L_w P : ℕ) : DSRep ReadView where
  τ := ReadConc
  rep r v y mem := ReadRepAt vCap eCap tCap L_w P r v y mem
  phi _ y _ := readPotMul * treePot y.view.G y.view.lsf.T
  foot r y := readFoot vCap eCap tCap L_w r y

theorem readRep_rep {vCap eCap tCap L_w P r : ℕ} {v : ReadView} {y : ReadConc}
    {mem : ℕ → ℕ} :
    (readRep vCap eCap tCap L_w P).rep r v y mem ↔ ReadRepAt vCap eCap tCap L_w P r v y mem :=
  Iff.rfl

theorem readRep_phi {vCap eCap tCap L_w P r : ℕ} {y : ReadConc} {mem : ℕ → ℕ} :
    (readRep vCap eCap tCap L_w P).phi r y mem = readPotMul * treePot y.view.G y.view.lsf.T :=
  rfl

theorem readRep_foot {vCap eCap tCap L_w P r : ℕ} {y : ReadConc} {a : ℕ} :
    (readRep vCap eCap tCap L_w P).foot r y a ↔ readFoot vCap eCap tCap L_w r y a :=
  Iff.rfl

/-! ## Locality -/

/-- The copy of `G` in a record. -/
theorem ReadRecAt.gGraph {mem : ℕ → ℕ} {r vCap eCap tCap L_w P : ℕ} {v : ReadView}
    {q : ReadPtrs} (hrec : ReadRecAt mem r vCap eCap tCap L_w P v q) :
    DynGraphAt mem q.g vCap eCap v.G :=
  hrec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- If a memory `out` agrees with `mem` on the cells of a record (`ReadRecFoot`), the record holds
the same data in `out`. -/
theorem ReadRecAt.of_foot {mem out : ℕ → ℕ} {r vCap eCap tCap L_w P : ℕ} {v : ReadView}
    {q : ReadPtrs} (hrec : ReadRecAt mem r vCap eCap tCap L_w P v q)
    (hagree : ∀ a, ReadRecFoot r vCap eCap tCap L_w q a → out a = mem a)
    (hdom : ∀ e ∈ v.G.E, e < eCap) :
    ReadRecAt out r vCap eCap tCap L_w P v q := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hT, hF, hR, hS, hPr, hSc, hG⟩ := hrec
  have hw (i : ℕ) (hi : i < readRecWords) : out (r + i) = mem (r + i) :=
    hagree _ (Or.inl ⟨by omega, by omega⟩)
  have hblk (b n : ℕ) (hb : ∀ a, b ≤ a → a < b + n → ReadRecFoot r vCap eCap tCap L_w q a) :
      ∀ a, b ≤ a → a < b + n → out a = mem a :=
    fun a ha1 ha2 => hagree a (hb a ha1 ha2)
  have hnum (e : ℕ) (he : e ∈ v.G.E) (i : ℕ) (hi : i < L_w) :
      out (q.num + e * L_w + i) = mem (q.num + e * L_w + i) := by
    have heC := hdom e he
    have hlt : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right _ (by omega)
    exact hblk q.num (eCap * L_w)
      (fun a h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))
      _ (by omega) (by rw [Nat.add_mul, one_mul] at hlt; omega)
  have hden (e : ℕ) (he : e ∈ v.G.E) (i : ℕ) (hi : i < L_w) :
      out (q.den + e * L_w + i) = mem (q.den + e * L_w + i) := by
    have heC := hdom e he
    have hlt : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right _ (by omega)
    exact hblk q.den (eCap * L_w)
      (fun a h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))))))
      _ (by omega) (by rw [Nat.add_mul, one_mul] at hlt; omega)
  have hnP : out (r + 7) = q.num := (hw 7 (by decide)).trans h7
  have hdP : out (r + 7 + 1) = q.den := (hw 8 (by decide)).trans h8
  have hnP' : mem (r + 7) = q.num := h7
  have hdP' : mem (r + 7 + 1) = q.den := h8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show r = r + 0 from rfl, hw 0 (by decide)]; exact h0
  · rw [hw 1 (by decide)]; exact h1
  · rw [hw 2 (by decide)]; exact h2
  · rw [hw 3 (by decide)]; exact h3
  · rw [hw 4 (by decide)]; exact h4
  · rw [hw 5 (by decide)]; exact h5
  · rw [hw 6 (by decide)]; exact h6
  · rw [hw 7 (by decide)]; exact h7
  · rw [hw 8 (by decide)]; exact h8
  · exact hT.of_agree (hblk q.t _ fun a h1 h2 => Or.inr (Or.inl ⟨h1, h2⟩))
  · exact hF.of_agree (hblk q.f _ fun a h1 h2 => Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
  · refine ⟨hR.1, fun x hx => ?_⟩
    have := hblk q.roots vCap (fun a h1 h2 => Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
      (q.roots + x) (by omega) (by omega)
    rw [this]; exact hR.2 x hx
  · intro e he
    obtain ⟨hvN, hvD, hpos, hval⟩ := hS e he
    rw [hnP'] at hvN
    rw [hdP'] at hvD hpos
    rw [hnP', hdP'] at hval
    rw [hnP, hdP]
    refine ⟨fun i hi => (hnum e he i hi).trans_lt (hvN i hi),
      fun i hi => (hden e he i hi).trans_lt (hvD i hi), ?_, ?_⟩
    · simpa only [Num.fixVal, Num.intVal_congr (hden e he)] using hpos
    · simpa only [Num.fixVal, Num.intVal_congr (hnum e he), Num.intVal_congr (hden e he)]
        using hval
  · intro e he
    obtain ⟨hN, hD⟩ := hPr e he
    rw [hnP'] at hN
    rw [hdP'] at hD
    rw [hnP, hdP, Num.intVal_congr (hnum e he), Num.intVal_congr (hden e he)]
    exact ⟨hN, hD⟩
  · exact hSc.of_agree (hblk q.s _ fun a h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h1, h2⟩)))))
  · exact hG.of_agree (hblk q.g _ fun a h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h1, h2⟩))))))

/-- If a memory `out` agrees with `mem` on the cells of the data, the record holds the same data
in `out`. -/
theorem ReadRepAt.of_foot {vCap eCap tCap L_w P r : ℕ} {v : ReadView} {y : ReadConc}
    {mem out : ℕ → ℕ} (hrep : ReadRepAt vCap eCap tCap L_w P r v y mem)
    (hagree : ∀ a, readFoot vCap eCap tCap L_w r y a → out a = mem a) :
    ReadRepAt vCap eCap tCap L_w P r v y out := by
  obtain ⟨hv, hlay, hinv, hrec, h9, h10, hlive, hfrz⟩ := hrep
  have hdom : ∀ e ∈ v.G.E, e < eCap := hrec.gGraph.2.2.1
  refine ⟨hv, hlay, hinv, hrec.of_foot (fun a ha => hagree a (Or.inr (Or.inl ha))) hdom, ?_, ?_,
    ?_, ?_⟩
  · rw [hagree _ (Or.inl ⟨by omega, by simp [readFullWords]⟩)]; exact h9
  · rw [hagree _ (Or.inl ⟨by omega, by simp [readFullWords]⟩)]; exact h10
  · exact hlive.of_agree fun a h1 h2 => hagree a (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
  · exact hfrz.of_agree fun a h1 h2 => hagree a (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))

/-- **The representation is local**: the data and the potential depend only on the cells of the
footprint. The potential does not read memory. -/
theorem readRep_local (vCap eCap tCap L_w P : ℕ) : (readRep vCap eCap tCap L_w P).Local := by
  intro r v y mem mem' hag
  exact ⟨fun hrep => ReadRepAt.of_foot hrep fun a ha => (hag a ha).symm, rfl⟩

/-- If the cells of the data are below `h` and `out` agrees with `mem` below `h`, the record
holds the same data in `out`. -/
theorem ReadRepAt.of_below {vCap eCap tCap L_w P r h : ℕ} {v : ReadView} {y : ReadConc}
    {mem out : ℕ → ℕ} (hrep : ReadRepAt vCap eCap tCap L_w P r v y mem)
    (hfoot : ∀ a, readFoot vCap eCap tCap L_w r y a → a < h)
    (hagree : ∀ a < h, out a = mem a) : ReadRepAt vCap eCap tCap L_w P r v y out :=
  hrep.of_foot fun a ha => hagree a (hfoot a ha)

/-! ## Facts for the operations -/

/-- A view that meets `ReadView.Inv` meets `ReadKeep`. -/
theorem ReadView.Inv.keep {vCap eCap tCap : ℕ} {v : ReadView} (h : v.Inv vCap eCap tCap) :
    ReadKeep v :=
  ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1⟩

/-- `ReadKeep` does not read `S`, so a restart (which changes only `S`) keeps it. -/
theorem ReadKeep.with_S {v : ReadView} (h : ReadKeep v) (S' : MGraph) :
    ReadKeep { v with S := S' } := h

/-- The tree agrees with `G` (`TreeAgree`) when both are valid and `ReadKeep` holds. -/
theorem ReadKeep.treeAgree {v : ReadView} (h : ReadKeep v) (hG : v.G.IsValid)
    (hT : v.lsf.T.IsValid) : TreeAgree v.G v.lsf.T :=
  ⟨hG, hT, h.1, h.2.1⟩

/-- A cell of the data lies in the record or in one of its blocks, all between `r` and the end of
the frozen part. -/
theorem readFoot_bounds {vCap eCap tCap L_w r : ℕ} {y : ReadConc}
    (hlay : ReadLayout r vCap eCap tCap L_w y) {a : ℕ}
    (ha : readFoot vCap eCap tCap L_w r y a) : r ≤ a ∧ a < y.frz + dynGraphSize vCap tCap := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hlay
  simp only [readFullWords] at h1
  rcases ha with ha | ha | ha | ha
  · simp only [readFullWords] at ha
    omega
  · simp only [ReadRecFoot, readRecWords] at ha
    omega
  · omega
  · omega

/-! ## The readouts -/

/-- **Readout `2` for `readRep`.** If `p` has `readLSFStmt` at `f` and `80 ≤ mul`, the call
`[r, h]` meets its clause of `ReadBranchAt`. -/
theorem readRep_readLSF {w vCap eCap tCap L_w P mul f : ℕ} {p : Program}
    (hp : p.procs[f]? = some readLSFStmt) (hmul : 80 ≤ mul)
    (r h : ℕ) (v : ReadView) (y : ReadConc) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hrep : (readRep vCap eCap tCap L_w P).rep r v y mem)
    (hfoot : ∀ a, (readRep vCap eCap tCap L_w P).foot r y a → a < h) (hz : ZeroFrom mem h)
    (hroom : h + 5 < 2 ^ w) :
    ReadCallEnds (readRep vCap eCap tCap L_w P) w p f [r, h] mem pos ω r y h v
      (fun mem' => ReadLSFOut mem' h L_w P v) 5 mul
      ((readRep vCap eCap tCap L_w P).phi r y mem) := by
  have hrec := hrep.2.2.2.1
  have hdom : ∀ e ∈ v.G.E, e < eCap := hrec.gGraph.2.2.1
  obtain ⟨o, st, c, hrun, ho, hout, hbelow, habove, hc⟩ :=
    readLSF_runs (w := w) p ω hrec (fun a ha => hfoot a (Or.inr (Or.inl ha))) hdom hroom
  refine ⟨readLSFStmt, hp, o, st, c, y, hrun, hrep.of_below hfoot hbelow, hout, ?_, ?_, ?_,
    fun a ha _ => hbelow a ha, fun a ha => Or.inl ha, ?_⟩
  · omega
  · omega
  · intro a ha
    rw [habove a (by omega)]
    exact hz a (by omega)
  · simp only [readRep_phi]
    omega

/-- **Readout `3` for `readRep`.** If `p` has `readSStmt` at `f` and `20 ≤ mul`, the call `[r, h]`
meets its clause of `ReadBranchAt`. -/
theorem readRep_readS {w vCap eCap tCap L_w P mul f : ℕ} {p : Program}
    (hp : p.procs[f]? = some readSStmt) (hmul : 20 ≤ mul)
    (r h : ℕ) (v : ReadView) (y : ReadConc) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hrep : (readRep vCap eCap tCap L_w P).rep r v y mem)
    (hfoot : ∀ a, (readRep vCap eCap tCap L_w P).foot r y a → a < h) (hz : ZeroFrom mem h)
    (hroom : h + 1 < 2 ^ w) :
    ReadCallEnds (readRep vCap eCap tCap L_w P) w p f [r, h] mem pos ω r y h v
      (fun mem' => ReadSOut mem' h v) 1 mul ((readRep vCap eCap tCap L_w P).phi r y mem) := by
  have hrec := hrep.2.2.2.1
  have hdom : ∀ e ∈ v.G.E, e < eCap := hrec.gGraph.2.2.1
  obtain ⟨o, st, c, hrun, ho, hout, hbelow, habove, hc⟩ :=
    readS_runs (w := w) p ω hrec (fun a ha => hfoot a (Or.inr (Or.inl ha))) hdom hroom
  refine ⟨readSStmt, hp, o, st, c, y, hrun, hrep.of_below hfoot hbelow, hout, ?_, ?_, ?_,
    fun a ha _ => hbelow a ha, fun a ha => Or.inl ha, ?_⟩
  · omega
  · omega
  · intro a ha
    rw [habove a (by omega)]
    exact hz a (by omega)
  · simp only [readRep_phi]
    omega

end MinCostFlow.SparseCore.Program.Read
