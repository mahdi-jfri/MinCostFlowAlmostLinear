module

public import MinCostFlow.LastLevelProgram.RootDistanceCall
import WordRAM.Tactic

/-!
# Computing root distances in parent-first order

For each nonroot vertex, locate its parent, its parent edge, and its
destination block, then call the child-distance update.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- Read the next child from the traversal order in register zero.
Registers one and two give the parent and parent-edge tables. -/
def distanceVisitChild : Stmt :=
  .assign 9 (.load (.bin .add (.reg 0) (.reg 8)))

/-- Use the selected child to address the parent distance, parent-edge
length, and child distance. Registers three and four give the two block
arrays, register five the limb count, and register six the heap cursor. -/
def distanceVisitArgs : List Expr :=
  [.bin .add (.reg 3) (.bin .mul (.load (.bin .add (.reg 1) (.reg 9))) (.reg 5)),
   .bin .add (.reg 4) (.bin .mul (.load (.bin .add (.reg 2) (.reg 9))) (.reg 5)),
   .bin .add (.reg 3) (.bin .mul (.reg 9) (.reg 5)), .reg 5, .reg 6]

/-- Process the nonroot vertices in the input traversal order. -/
def rootDistancePass (step : ℕ) : Stmt :=
  forRange 8 (.const 0) (.reg 7) (distanceVisitChild ;; .call 6 step distanceVisitArgs)

/-- Selecting the next child changes only its register. -/
theorem distanceVisitChild_runs {w : ℕ} {p : Program} (st : State) (ω : ℕ → Bool)
    (order i child : ℕ) (h0 : st.regs 0 = order) (h8 : st.regs 8 = i)
    (hcell : st.mem (order+i) = child) (hroom : order+i < 2^w) :
    Runs w p ω distanceVisitChild st .normal
      { st with regs := Function.update st.regs 9 child } 5 :=
  runs_assign_iff.mpr ⟨child,by eval_expr,rfl,rfl,rfl⟩

/-- The lookup forms exact block addresses inside the two allocated arrays. -/
theorem distanceVisitArgs_eval {w : ℕ} {st : State}
    (parents edges lengths dist L heap n m child par edge : ℕ)
    (h1 : st.regs 1 = parents) (h2 : st.regs 2 = edges)
    (h3 : st.regs 3 = dist) (h4 : st.regs 4 = lengths)
    (h5 : st.regs 5 = L) (h6 : st.regs 6 = heap) (h9 : st.regs 9 = child)
    (hpar : st.mem (parents+child) = par) (hedge : st.mem (edges+child) = edge)
    (hc : child < n) (hp : par < n) (he : edge < m)
    (hparents : parents+n < 2^w) (hedges : edges+n < 2^w)
    (hdist : dist+n*L < 2^w) (hlen : lengths+m*L < 2^w) :
    evalArgs w st distanceVisitArgs =
      some [dist+par*L,lengths+edge*L,dist+child*L,L,heap] := by
  have haddrP : parents+child < 2^w := by omega
  have haddrE : edges+child < 2^w := by omega
  have hparmul := Nat.mul_le_mul_right L hp.le
  have hedgemul := Nat.mul_le_mul_right L he.le
  have hchildmul := Nat.mul_le_mul_right L hc.le
  have hparW : par*L < 2^w := by omega
  have hedgeW : edge*L < 2^w := by omega
  have hchildW : child*L < 2^w := by omega
  have hsrc : dist+par*L < 2^w := by omega
  have hlen' : lengths+edge*L < 2^w := by omega
  have hdest : dist+child*L < 2^w := by omega
  unfold distanceVisitArgs
  eval_expr

/-- One visit reads the next child and writes its distance. The heap
cursor and the child register are the only registers it changes. -/
theorem distanceVisit_runs {w h step : ℕ} {p : Program}
    (hs : MeetsContract w p step (rootDistanceStepContract w h))
    (st : State) (ω : ℕ → Bool)
    (order parents edges lengths dist L heap n m i child par edge : ℕ)
    (h0 : st.regs 0 = order) (h1 : st.regs 1 = parents) (h2 : st.regs 2 = edges)
    (h3 : st.regs 3 = dist) (h4 : st.regs 4 = lengths)
    (h5 : st.regs 5 = L) (h6 : st.regs 6 = heap) (h8 : st.regs 8 = i)
    (hchild : st.mem (order+i) = child) (hpar : st.mem (parents+child) = par)
    (hedge : st.mem (edges+child) = edge)
    (hc : child < n) (hp : par < n) (he : edge < m)
    (horder : order+i < 2^w)
    (hparents : parents+n < 2^w) (hedges : edges+n < 2^w)
    (hdist : dist+n*L < 2^w) (hlen : lengths+m*L < 2^w)
    (hargs : ∀ a ∈ [dist+par*L,lengths+edge*L,dist+child*L,L,heap], a < 2^w)
    (hpre : (rootDistanceStepContract w h).pre
      [dist+par*L,lengths+edge*L,dist+child*L,L,heap] st.mem) :
    ∃ out c, Runs w p ω (distanceVisitChild ;; .call 6 step distanceVisitArgs) st .normal out c ∧
      (rootDistanceStepContract w h).post
        [dist+par*L,lengths+edge*L,dist+child*L,L,heap] st.mem (out.regs 6) out.mem ∧
      (∀ j, j ≠ 6 → j ≠ 9 → out.regs j = st.regs j) ∧ c ≤ 55*L+66 := by
  let mid := { st with regs := Function.update st.regs 9 child }
  have hread := distanceVisitChild_runs (p := p) st ω order i child h0 h8 hchild horder
  have heval := distanceVisitArgs_eval (st := mid) parents edges lengths dist L heap n m
    child par edge h1 h2 h3 h4 h5 h6 (by simp [mid]) hpar hedge
    hc hp he hparents hedges hdist hlen
  obtain ⟨out,c,ret,hr,hpost,hret,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 6) hs heval hargs hpre ω
  refine ⟨out,5+c+1,runs_seq_iff.mpr (Or.inr ⟨mid,5,c,hread,hr,rfl⟩),?_,?_,?_⟩
  · rwa [hret]
  · intro j hj6 hj9
    simpa [mid,Function.update_of_ne hj9] using hregs j hj6
  · change c ≤ argsSize distanceVisitArgs + (55*L+34) + 1 at hcost
    simp [distanceVisitArgs,argsSize,Expr.size] at hcost
    omega

/-- Given a parent-first enumeration, each visit produces the indicated
distance and keeps the earlier blocks and the input tables intact. -/
theorem rootDistancePass_triple {w h step : ℕ} {p : Program}
    (hs : MeetsContract w p step (rootDistanceStepContract w h))
    (mem : ℕ → ℕ) (pos order parents edges dist lengths L heap k n m root : ℕ)
    (child par edge : ℕ → ℕ) (distance : ℕ → ℤ)
    (hw : 1 < 2^w) (hL : L < 2^w) (hk : k < 2^w)
    (hr : root < n)
    (hO : order+k ≤ dist) (hP : parents+n ≤ dist) (hE : edges+n ≤ dist)
    (hLen : lengths+m*L ≤ dist) (hD : dist+n*L ≤ heap)
    (hroom : heap+k*L < 2^w) (hzero : ZeroFrom mem heap)
    (hinit : Valid mem (dist+root*L) h L ∧ intVal mem (dist+root*L) h L = distance root)
    (hvisit : ∀ i < k, child i < n ∧ par i < n ∧ edge i < m ∧
      mem (order+i) = child i ∧ mem (parents+child i) = par i ∧ mem (edges+child i) = edge i)
    (hfirst : ∀ i < k, par i = root ∨ ∃ j < i, child j = par i)

    (hvalue : ∀ i < k, Valid mem (lengths+edge i*L) h L ∧ Fits h L (distance (child i)) ∧
      distance (child i) = distance (par i) + intVal mem (lengths+edge i*L) h L) :
    Triple w p (fun st => st = startState [order,parents,edges,dist,lengths,L,heap,k] mem pos)
      (rootDistancePass step) (normalPost fun st =>
        st.regs 6 = heap+k*L ∧ ZeroFrom st.mem (st.regs 6) ∧
        (∀ a < dist, st.mem a = mem a) ∧
        ∀ v, (v = root ∨ ∃ j < k, child j = v) →
          Valid st.mem (dist+v*L) h L ∧ intVal st.mem (dist+v*L) h L = distance v)
      (fun _ => (55*L+75)*k+7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = order ∧ st.regs 1 = parents ∧ st.regs 2 = edges ∧ st.regs 3 = dist ∧
    st.regs 4 = lengths ∧ st.regs 5 = L ∧ st.regs 6 = heap+i*L ∧ st.regs 7 = k ∧
    st.regs 8 = i ∧ ZeroFrom st.mem (st.regs 6) ∧ (∀ a < dist, st.mem a = mem a) ∧
    ∀ v, (v = root ∨ ∃ j < i, child j = v) →
      Valid st.mem (dist+v*L) h L ∧ intVal st.mem (dist+v*L) h L = distance v
  have loop := Triple.forRange_const (p := p) (r := 8) (lo := .const 0) (hi := .reg 7)
    (body := distanceVisitChild ;; .call 6 step distanceVisitArgs) (Inv := Inv)
    (P := fun st => st = startState [order,parents,edges,dist,lengths,L,heap,k] mem pos)
    (55*L+66) 0 k (Nat.zero_le _) hw (fun _ => hk)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [Inv,startState,hzero,hinit]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ h => by
      have hh : st.regs 7 = k := h.2.2.2.2.2.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,hz,hframe,hdone⟩
      let cur := heap+i*L
      have hmul := Nat.mul_le_mul_right L hi
      rw [Nat.succ_mul] at hmul
      have hspace : cur+L < 2^w := by dsimp [cur]; omega
      have hcur : heap ≤ cur := Nat.le_add_right _ _
      obtain ⟨hc,hp,he,ho,hpar,hedge⟩ := hvisit i hi
      have hblock (b d q bound : ℕ) (hb : b+d*L ≤ bound) (hq : q < d) : b+q*L+L ≤ bound := by
        have hh := Nat.mul_le_mul_right L hq
        rw [Nat.succ_mul] at hh
        omega
      have hpB := hblock dist n (par i) heap hD hp
      have hcB := hblock dist n (child i) heap hD hc
      have heB := hblock lengths m (edge i) heap (hLen.trans (Nat.le_add_right _ _ |>.trans hD)) he
      have heD := hblock lengths m (edge i) dist hLen he
      obtain ⟨hvp,hvpVal⟩ := hdone _ (hfirst i hi)
      obtain ⟨hve,hfit,heq⟩ := hvalue i hi
      have hcopy (j : ℕ) (hj : j < L) :
          st.mem (lengths+edge i*L+j) = mem (lengths+edge i*L+j) :=
        hframe _ (by omega)
      have heVal := intVal_congr (h := h) hcopy
      have hargs : ∀ a ∈ [dist+par i*L,lengths+edge i*L,dist+child i*L,L,cur], a < 2^w := by
        intro a ha
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl|rfl|rfl <;> omega
      have hpre : (rootDistanceStepContract w h).pre
          [dist+par i*L,lengths+edge i*L,dist+child i*L,L,cur] st.mem :=
        ⟨_,_,_,_,_,rfl,hw,hpB.trans hcur,heB.trans hcur,hcB.trans hcur,hspace,
          hvp,fun j hj => (hcopy j hj).trans_lt (hve j hj),
          by change ZeroFrom st.mem (heap+i*L); rwa [h6] at hz,
          by rwa [hvpVal,heVal,← heq]⟩
      obtain ⟨out,c,hrun,hpost,hregs,hcost⟩ := distanceVisit_runs hs st ω order parents edges
        lengths dist L cur n m i (child i) (par i) (edge i) h0 h1 h2 h3 h4 h5 h6 h8
        ((hframe _ (by omega)).trans ho) ((hframe _ (by omega)).trans hpar)
        ((hframe _ (by omega)).trans hedge) hc hp he
        (by omega) (by omega) (by omega) (by omega) (by omega) hargs hpre
      obtain ⟨hret,hvalid,hval,hf,htail⟩ := hpost
      change out.regs 6 = cur+L at hret
      change intVal out.mem (dist+child i*L) h L =
        intVal st.mem (dist+par i*L) h L + intVal st.mem (lengths+edge i*L) h L at hval
      change ∀ a < cur, a < dist+child i*L ∨ dist+child i*L+L ≤ a → out.mem a = st.mem a at hf
      have hnew : out.regs 6 = heap+(i+1)*L := by
        rw [Nat.succ_mul]
        simpa only [cur,Nat.add_assoc] using hret
      refine ⟨.normal,out,c,hrun,⟨?_,(hregs 8 (by decide) (by decide)).trans h8⟩,hcost⟩
      refine ⟨(hregs 0 (by decide) (by decide)).trans h0,(hregs 1 (by decide) (by decide)).trans h1,
        (hregs 2 (by decide) (by decide)).trans h2,(hregs 3 (by decide) (by decide)).trans h3,
        (hregs 4 (by decide) (by decide)).trans h4,(hregs 5 (by decide) (by decide)).trans h5,
        hnew,(hregs 7 (by decide) (by decide)).trans h7,by simp,htail,?_,?_⟩
      · intro a ha
        exact (hf a (by omega) (Or.inl (by omega))).trans (hframe a ha)
      · intro v hv
        by_cases hv' : v = child i
        · subst v
          exact ⟨hvalid,by simpa only [hvpVal,heVal,heq] using hval⟩
        · have hvold : v = root ∨ ∃ j < i, child j = v := by
            rcases hv with h | ⟨j,hj,hjv⟩
            · exact Or.inl h
            · have hji : j ≠ i := fun h => hv' (h ▸ hjv).symm
              exact Or.inr ⟨j,by omega,hjv⟩
          have hvn : v < n := by
            rcases hvold with rfl | ⟨j,hj,rfl⟩
            · exact hr
            · exact (hvisit j (hj.trans hi)).1
          obtain ⟨hvv,hvalv⟩ := hdone v hvold
          have hb := hblock dist n v heap hD hvn
          have hsame (j : ℕ) (hj : j < L) :
              out.mem (dist+v*L+j) = st.mem (dist+v*L+j) := by
            apply hf _ (by omega)
            by_cases hlt : v < child i
            · have hmul' := Nat.mul_le_mul_right L hlt
              rw [Nat.succ_mul] at hmul'
              exact Or.inl (by omega)
            · have hmul' := Nat.mul_le_mul_right L (show child i+1 ≤ v by omega)
              rw [Nat.succ_mul] at hmul'
              exact Or.inr (by omega)
          exact ⟨fun j hj => (hsame j hj).trans_lt (hvv j hj), (intVal_congr hsame).trans hvalv⟩)
  refine loop.conseq (fun _ h => h) ?_ (by intro _ _; simp [Expr.size,Nat.mul_comm,Nat.add_assoc])
  intro o st h
  cases o with
  | returned => exact h
  | normal =>
    obtain ⟨_,_,_,_,_,_,hc,_,_,hz,hf,hdone⟩ := h
    exact ⟨hc,hz,hf,hdone⟩

end MinCostFlow.LastLevelProgram
