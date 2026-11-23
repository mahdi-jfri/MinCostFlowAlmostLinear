module

public import MinCostFlow.LastLevelProgram.LiftBitsCall
public import MinCostFlow.LastLevelProgram.ClimbTogetherCall
public import MinCostFlow.LastLevelProgram.OrientDepth
public import MinCostFlow.LastLevelProgram.AncestorSemantics
import WordRAM.Tactic

/-!
# Ancestor query with a known depth difference

Lift the deeper vertex, then find the first meeting of the two parent
walks. The query reads the table and leaves it available for later edges.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM LSF

/-- Register nine holds the shallower vertex while register three climbs
the depth difference in register four. -/
def ancestorQuery : Stmt :=
  climbBitsLoop ;;
  .assign 4 (.reg 9) ;;
  alignedAncestor

/-- Given the depth difference and a bound on the first meeting after
alignment, the mixed-depth query returns that meeting in logarithmic time. -/
theorem ancestorQuery_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (base n count u v delta : ℕ) (parent : ℕ → ℕ)
    (hword : 2 < 2^w) (hcount : count < 2^w) (hrows : 0 < count)
    (hu : u < n) (hv : v < n) (hdw : delta < 2^w) (hd : delta < 2^count)
    (hroom : base+count*n < 2^w) (hparent : ∀ x < n, parent x < n)
    (htable : ∀ i < count, ∀ x < n, mem (base+i*n+x) = ancestorJump parent i x)
    (hroot : (parent^[2^count]) ((parent^[delta]) u) = (parent^[2^count]) v) :
    let x := (parent^[delta]) u
    let d := Nat.find (show ∃ k, (parent^[k]) x = (parent^[k]) v from ⟨2^count,hroot⟩)
    Triple w p (fun st => st.regs 0 = base ∧ st.regs 1 = n ∧ st.regs 2 = count ∧
        st.regs 3 = u ∧ st.regs 4 = delta ∧ st.regs 9 = v ∧ st.mem = mem)
      ancestorQuery (fun o st => o = .returned ((parent^[d]) x) ∧ st.mem = mem)
      (fun _ => 86*count+28) := by
  intro x d st ω hs
  obtain ⟨o,mid,c,hr,hpost,hcost⟩ :=
    climbBitsLoop_triple (p := p) mem base n count u delta v parent
      hword hcount hu hdw hroom hparent htable st ω hs
  cases o with
  | returned => exact False.elim hpost
  | normal =>
    obtain ⟨hm,h0,h1,h2,h9,hx,h3⟩ := hpost
    rw [climbBits_exact parent hd] at h3
    let next := { mid with regs := Function.update mid.regs 4 v }
    have ha : Runs w p ω (.assign 4 (.reg 9)) mid .normal next 2 :=
      runs_assign_iff.mpr ⟨v,by simp [Expr.eval,h9],rfl,rfl,rfl⟩
    obtain ⟨o,out,t,hrt,hout,htime⟩ :=
      alignedAncestor_triple (p := p) mem base n count x v parent
        (by omega) hcount hrows (by change (parent^[delta]) u < n; simpa only [← h3] using hx) hv hroom hparent htable hroot next ω
        ⟨h0,h1,h2,h3,by simp [next],hm⟩
    refine ⟨o,out,c+(2+t+1)+1,?_,hout,?_⟩
    exact runs_seq_iff.mpr (Or.inr ⟨mid,c,2+t+1,hr,
      runs_seq_iff.mpr (Or.inr ⟨next,2,t,ha,hrt,rfl⟩),rfl⟩)
    change c+(2+t+1)+1 ≤ 86*count+28
    change c ≤ 41*count+7 at hcost
    change t ≤ 45*count+17 at htime
    omega

/-- Read the endpoint depths, align them, and return their common ancestor. -/
def depthTableAncestorQuery : Stmt :=
  prepareAncestorQuery ;; ancestorQuery

/-- A query given the raw endpoints and both tables costs at most
`86 * count + 55` steps and leaves the tables intact. -/
theorem depthTableAncestorQuery_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (base n count u v depthBase : ℕ) (parent depth : ℕ → ℕ)
    (hword : 2 < 2^w) (hcount : count < 2^w) (hrows : 0 < count)
    (hu : u < n) (hv : v < n) (hdu : depth u < 2^w) (hdv : depth v < 2^w)
    (hdepthRoom : depthBase+n < 2^w)
    (hdepth : ∀ x < n, mem (depthBase+x) = depth x)
    (hroom : base+count*n < 2^w) (hparent : ∀ x < n, parent x < n)
    (htable : ∀ i < count, ∀ x < n, mem (base+i*n+x) = ancestorJump parent i x)
    (hgap : (if depth u < depth v then depth v-depth u else depth u-depth v) < 2^count)
    (hroot : (parent^[2^count])
      ((parent^[if depth u < depth v then depth v-depth u else depth u-depth v])
        (if depth u < depth v then v else u)) =
      (parent^[2^count]) (if depth u < depth v then u else v)) :
    let a := if depth u < depth v then v else u
    let b := if depth u < depth v then u else v
    let gap := if depth u < depth v then depth v-depth u else depth u-depth v
    let x := (parent^[gap]) a
    let d := Nat.find (show ∃ k, (parent^[k]) x = (parent^[k]) b from ⟨2^count,hroot⟩)
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = base ∧ st.regs 1 = n ∧
        st.regs 2 = count ∧ st.regs 3 = u ∧ st.regs 4 = v ∧ st.regs 10 = depthBase)
      depthTableAncestorQuery (fun o st => o = .returned ((parent^[d]) x) ∧ st.mem = mem)
      (fun _ => 86*count+55) := by
  intro a b gap x d
  have ha : a < n := by dsimp [a]; split <;> assumption
  have hb : b < n := by dsimp [b]; split <;> assumption
  have hgw : gap < 2^w := by
    dsimp [gap]
    split
    · exact (Nat.sub_le ..).trans_lt hdv
    · exact (Nat.sub_le ..).trans_lt hdu
  refine Triple.seq_normal
    (prepareAncestorQuery_triple mem base n count u v depthBase depth
      (by omega) hu hv hdepthRoom hdepth hdu hdv)
    ((ancestorQuery_triple mem base n count a b gap parent hword hcount hrows
      ha hb hgw hgap hroom hparent htable hroot).conseq ?_ (fun _ _ h => h) (fun _ _ => le_rfl))
    (fun _ _ _ _ => by omega)
  intro st hs
  obtain ⟨hm,h0,h1,h2,h3,h9,h4⟩ := hs
  exact ⟨h0,h1,h2,h3,h4,h9,hm⟩

/-- On a compact rooted tree, the table query returns the same LCA as the
forest-path definition used to compute stretch. -/
theorem rootedTreeAncestorQuery_triple {w : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hT : LSF.IsRootedTree T r) (mem : ℕ → ℕ) (base n count u v depthBase : ℕ)
    (hvertices : ∀ x, x ∈ T.V ↔ x < n)
    (hword : 2 < 2^w) (hcount : count < 2^w) (hrows : 0 < count)
    (hu : u < n) (hv : v < n)
    (hdepth : ∀ x < n, LSF.depth T r x < 2^count ∧ LSF.depth T r x < 2^w)
    (hdepthRoom : depthBase+n < 2^w)
    (hdepthTable : ∀ x < n, mem (depthBase+x) = LSF.depth T r x)
    (hroom : base+count*n < 2^w)
    (htable : ∀ i < count, ∀ x < n, mem (base+i*n+x) = ancestorJump (LSF.parent T r) i x) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = base ∧ st.regs 1 = n ∧
        st.regs 2 = count ∧ st.regs 3 = u ∧ st.regs 4 = v ∧ st.regs 10 = depthBase)
      depthTableAncestorQuery (fun o st => o = .returned (LSF.lca T r u v) ∧ st.mem = mem)
      (fun _ => 86*count+55) := by
  let a := if depth T r u < depth T r v then v else u
  let b := if depth T r u < depth T r v then u else v
  let gap := if depth T r u < depth T r v then depth T r v - depth T r u
    else depth T r u - depth T r v
  let x := (parent T r)^[gap] a
  have huv := (hvertices u).2 hu
  have hvv := (hvertices v).2 hv
  have ha : a < n := by dsimp [a]; split <;> assumption
  have hb : b < n := by dsimp [b]; split <;> assumption
  have hav := (hvertices a).2 ha
  have hbv := (hvertices b).2 hb
  have horder : depth T r b ≤ depth T r a := by
    dsimp [a,b]
    split <;> omega
  have hgap : gap = depth T r a - depth T r b := by simp [gap,a,b]; split <;> rfl
  have hgl : gap < 2^count := hgap ▸ (Nat.sub_le ..).trans_lt (hdepth a ha).1
  have halign := lca_eq_lca_lifted hT hav hbv horder
  rw [← hgap] at halign
  have hxv := isAncestor_mem hT hav (parentIterate_spec hT hav gap).1
  have hmeet : (parent T r)^[2^count] x = (parent T r)^[2^count] b := by
    rw [parentIterate_eq_root hT hxv ((hdepth x ((hvertices x).1 hxv)).1.le),
      parentIterate_eq_root hT hbv (hdepth b hb).1.le]
  have hpa (y : ℕ) (hy : y < n) : parent T r y < n :=
    (hvertices _).1 (parent_mem hT ((hvertices _).2 hy))
  have hrun := depthTableAncestorQuery_triple (p := p) mem base n count u v depthBase
    (parent T r) (depth T r) hword hcount hrows hu hv (hdepth u hu).2 (hdepth v hv).2
    hdepthRoom hdepthTable hroom hpa htable hgl hmeet
  let k := depth T r x - depth T r (lca T r x b)
  obtain ⟨hkx,hkb,hmin⟩ := parentIterate_firstMeeting hT hxv hbv halign.1
  let hex : ∃ j, (parent T r)^[j] x = (parent T r)^[j] b := ⟨2^count,hmeet⟩
  have hk : Nat.find hex = k :=
    Nat.le_antisymm (Nat.find_min' hex (hkx.trans hkb.symm))
      (Nat.le_of_not_gt fun hh => hmin _ hh (Nat.find_spec hex))
  have hab : lca T r a b = lca T r u v := by
    dsimp [a,b]
    split
    · exact lca_comm hT hvv huv
    · rfl
  refine hrun.conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st ⟨ho,hm⟩
  change o = .returned ((parent T r)^[Nat.find hex] x) at ho
  rw [hk,hkx,halign.2,hab] at ho
  exact ⟨ho,hm⟩

/-- Callable query with arguments `[base, width, rows, u, v, depthBase]`. -/
def rootedTreeAncestorBody : Stmt :=
  .assign 10 (.reg 5) ;; depthTableAncestorQuery

/-- A call reads the two tables for a compact rooted tree and returns its LCA. -/
def rootedTreeAncestorContract (w : ℕ) (T : MGraph) (r : ℕ) : Contract where
  pre args mem := ∃ base n count u v depthBase,
    args = [base,n,count,u,v,depthBase] ∧ (∀ x, x ∈ T.V ↔ x < n) ∧
    2 < 2^w ∧ 0 < count ∧ u < n ∧ v < n ∧
    (∀ x < n, depth T r x < 2^count ∧ depth T r x < 2^w) ∧
    depthBase+n < 2^w ∧ (∀ x < n, mem (depthBase+x) = depth T r x) ∧
    base+count*n < 2^w ∧
    (∀ i < count, ∀ x < n, mem (base+i*n+x) = ancestorJump (parent T r) i x)
  post args mem result out :=
    result = lca T r (args[3]?.getD 0) (args[4]?.getD 0) ∧ out = mem
  cost args _ := 86*(args[2]?.getD 0)+58

/-- The rooted tree query can be called from the edge stretch procedure. -/
theorem rootedTreeAncestor_meetsContract {w entry : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (he : p.procs[entry]? = some rootedTreeAncestorBody) :
    MeetsContract w p entry (rootedTreeAncestorContract w T r) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨base,n,count,u,v,depthBase,rfl,hvertices,hword,hrows,hu,hv,hdepth,
    hdepthRoom,hdepthTable,hroom,htable⟩ := hpre
  have hc := hwords count (by simp)
  let st := startState [base,n,count,u,v,depthBase] mem pos
  let mid := { st with regs := Function.update st.regs 10 depthBase }
  have ha : Runs w p ω (.assign 10 (.reg 5)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨depthBase,rfl,rfl,rfl,rfl⟩
  obtain ⟨o,out,c,hr,⟨ho,hm⟩,ht⟩ :=
    rootedTreeAncestorQuery_triple (p := p) hT mem base n count u v depthBase
      hvertices hword hc hrows hu hv hdepth hdepthRoom hdepthTable hroom htable mid ω
      (by simp [mid,st,startState])
  refine ⟨o,out,2+c+1,runs_seq_iff.mpr (Or.inr ⟨mid,2,c,ha,hr,rfl⟩),?_,?_⟩
  · subst o
    exact ⟨rfl,hm⟩
  · change c ≤ 86*count+55 at ht
    change 2+c+1 ≤ 86*count+58
    omega

end MinCostFlow.LastLevelProgram
