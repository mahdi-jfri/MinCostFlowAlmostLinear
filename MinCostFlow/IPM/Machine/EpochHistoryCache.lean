module

public import MinCostFlow.IPM.Machine.EpochCacheMovement
public import MinCostFlow.IPM.Machine.HistoryIteration
import MinCostFlow.IPM.Machine.EpochMaterialization
import MinCostFlow.IPM.Machine.DetectRefreshFrame
import MinCostFlow.IPM.Machine.DetectRefreshOutput
import MinCostFlow.IPM.Machine.DetectRefreshUnreportedFlow
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.Num.IPM.FixedPointFacts

import MinCostFlow.IPM.Machine.EpochConditions

/-!
# The coordinate associated with each coefficient stage

An odd Detect stage still presents the old coefficient arrays, even
for a just-reported edge. Its cached coordinate is the last report as
of the preceding even stage. An even Update stage presents the newly
refreshed arrays. The last report now includes the intervening Detect.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM.Machine

/-- The exact base-plus-implicit flow at the last report which has
already been used to refresh the supplied coefficients. -/
def epochHistoryCache (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (t : ℕ)
    (base : Fin I.m → ℝ) (e : Fin I.m) : ℝ :=
  epochHistoryFlow I A D eta op (minRatioLast A.eraseFailure D eta op (2*(t/2)) e) base e

/-- For a loop point at an even stage under `P`, Query at the actual last report
identifies the stored coordinate with the history cache. -/
theorem epochHistoryCache_eq_cache_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (L : EpochLayout) (q i : ℕ) (mem : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ t≤2*i,D.G t=namedInstance I)
    (hPD : ∀ j ≤ 2*i, P (D.G j) (D.ℓ j))
    (e : Fin I.m)
    (hcache : reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    epochVector F I mem L.flow e=
      epochHistoryCache I A D eta op (2*i) (epochVector F I mem L.base) e := by
  let t := minRatioLast A.eraseFailure D eta op (2*i) e
  have ht : t≤2*i := minRatioLast_le A.eraseFailure D eta op (2*i) e
  have he : e.val∈(D.G t).E := by rw [hG t ht]; exact Finset.mem_range.mpr e.isLt
  have hq := (hA D eta op (2*i) hv (namedHistory_bounded hG) hPD).1.1 t ht e he
  have hindex : 2*(2*i/2)=2*i := by omega
  rw [epochHistoryCache,hindex,epochHistoryFlow]
  exact hcache.2.1.trans (congrArg (epochVector F I mem L.base e+·) hq)

/-- For a loop point at an even stage, Query at the actual last report
identifies the stored coordinate with the history cache. -/
theorem epochHistoryCache_eq_cache_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (L : EpochLayout) (q i : ℕ) (mem : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ t≤2*i,D.G t=namedInstance I)
    (e : Fin I.m)
    (hcache : reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    epochVector F I mem L.flow e=
      epochHistoryCache I A D eta op (2*i) (epochVector F I mem L.base) e :=
  epochHistoryCache_eq_cache_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    L q i mem D eta op hv hG (fun _ _ => trivial) e hcache

/-- For a loop point at an even stage, Query at the actual last report
identifies the stored coordinate with the history cache. -/
theorem epochHistoryCache_eq_cache {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (L : EpochLayout) (q i : ℕ) (mem : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ t≤2*i,D.G t=namedInstance I)
    (e : Fin I.m)
    (hcache : reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    epochVector F I mem L.flow e=
      epochHistoryCache I A D eta op (2*i) (epochVector F I mem L.base) e :=
  epochHistoryCache_eq_cache_upTo F A I κ α Ψ eps (hA.upTo I.m I.n)
    L q i mem D eta op hv hG e hcache

/-- Appending the next pair preserves the coordinates associated with
the inputs of every earlier stage. -/
theorem epochHistoryCache_past (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ) (base : Fin I.m → ℝ)
    (t : ℕ) (ht : t≤T) :
    epochHistoryCache I A (appendHistoryIteration D T es g l)
      (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T) t base=
      epochHistoryCache I A D eta op t base := by
  funext e
  have hindex : 2*(t/2)≤T := by omega
  have hlast := minRatioLast_le A.eraseFailure D eta op (2*(t/2)) e
  unfold epochHistoryCache epochHistoryFlow
  have heq : minRatioLast A.eraseFailure (appendHistoryIteration D T es g l)
      (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T) (2*(t/2)) e=
      minRatioLast A.eraseFailure D eta op (2*(t/2)) e := by
    unfold appendHistoryIteration appendHistoryIterationEta appendHistoryIterationOp
    rw [appendHistoryStage_past_last _ _ _ _ (T+1) _ _ _ _ true _ _ (by omega),
      appendHistoryStage_past_last _ _ _ _ T _ _ _ 0 false _ _ hindex]
  rw [heq,appendHistoryIteration_past_flow _ _ _ _ _ _ _ _ _ _ _ (hlast.trans hindex)]

/-- The new odd-stage Detect still has the old cached coordinates.
No coefficients are changed by the call itself. -/
theorem epochHistoryCache_detect (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (i : ℕ)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ) (base : Fin I.m → ℝ) :
    epochHistoryCache I A (appendHistoryIteration D (2*i) es g l)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) (2*i+1) base=
      epochHistoryCache I A D eta op (2*i) base := by
  have hindex : 2*((2*i+1)/2)=2*(2*i/2) := by omega
  unfold epochHistoryCache
  rw [hindex]
  exact epochHistoryCache_past I A D eta op (2*i) es g l actual base (2*i) le_rfl

/-- On the even-stage Update input, the cache has the current flow on
the exact Detect set and the previous held coordinate elsewhere. -/
theorem epochHistoryCache_update (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (i : ℕ)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ) (base : Fin I.m → ℝ) (e : Fin I.m) :
    epochHistoryCache I A (appendHistoryIteration D (2*i) es g l)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) (2*i+1+1) base e=
    if e.val∈(A.detect (minRatioState A.eraseFailure D eta op (2*i))).1 then
      epochHistoryFlow I A D eta op (2*i) base e
    else epochHistoryCache I A D eta op (2*i) base e := by
  have hindex : 2*((2*i+1+1)/2)=2*i+1+1 := by omega
  have heven : 2*(2*i/2)=2*i := by omega
  unfold epochHistoryCache epochHistoryFlow
  rw [hindex,heven,appendHistoryIteration_last_flow]
  rw [show A.eraseFailure.detect=A.detect from rfl]
  split_ifs <;> rfl

/-- When no edge is inserted from the odd Detect to the next even
Update, the cached coordinate of that edge stays constant. -/
theorem epochHistoryCache_update_of_notInserted (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (i : ℕ)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ) (base : Fin I.m → ℝ) (e : Fin I.m)
    (hset : es.toFinset=(A.detect (minRatioState A.eraseFailure D eta op (2*i))).1)
    (hne : (appendHistoryIteration D (2*i) es g l).NotInsertedBetween e (2*i+1) (2*i+1+1)) :
    epochHistoryCache I A (appendHistoryIteration D (2*i) es g l)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) (2*i+1+1) base e=
    epochHistoryCache I A (appendHistoryIteration D (2*i) es g l)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) (2*i+1) base e := by
  rw [epochHistoryCache_detect,epochHistoryCache_update]
  apply ite_eq_right
  intro he
  have hm : e.val∈es := List.mem_toFinset.mp (hset ▸ he)
  obtain ⟨u,hu,hi⟩ := (refreshEdges_inserts (D.G (2*i)) es e).mpr hm
  exact hne (2*i+1+1) (by omega) le_rfl u
    (by simpa only [appendHistoryIteration,appendHistoryStage,Function.update_self] using hu) hi

/-- The newly refreshed table under `P` is exactly the cache for the even-stage
Update input. The identity holds independently of whether Update succeeds. -/
theorem epochHistoryCache_eq_refreshed_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    (L : EpochLayout) (q K heap v i : ℕ) (x : R.τ) (mem refreshed : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ t≤2*i,D.G t=namedInstance I)
    (hPD : ∀ j ≤ 2*i, P (D.G j) (D.ℓ j))
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) x q K L.sourceEnd L.tableEnd).pre
      ((L.packet F I heap).take 20) mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) x q K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v refreshed)
    (haccept : refreshed (v-1)=1) (hbase : L.base+I.m*F.limbs≤L.flow)
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    epochVector F I refreshed L.flow=
      epochHistoryCache I A (appendHistoryIteration D (2*i) es g l)
        (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) (2*i+1+1)
        (epochVector F I mem L.base) := by
  funext e
  rw [epochHistoryCache_update]
  by_cases hmem : e.val∈(A.detect (minRatioState A.eraseFailure D eta op (2*i))).1
  · rw [ite_eq_left hmem]
    have hcr := (detectRefresh_output F A (namedInstance I) I.m κ α rate allocation R hpre hout).2.2.2.2
      haccept e.val hmem
    have he : e.val∈(D.G (2*i)).E := by rw [hG _ le_rfl]; exact Finset.mem_range.mpr e.isLt
    have hf := reportedCachePost_detect_flow_upTo_on F A κ α Ψ eps hA D eta op (2*i) hv
      (namedHistory_bounded hG) hPD he hcr
    have hframe := detectRefresh_frame F A (namedInstance I) I.m κ α rate allocation R hpre hout
    have hsame := Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe
      ((reported_entry_end L.base F.limbs e.val I.m e.isLt).trans hbase)
    rw [hsame] at hf
    exact hf
  · rw [ite_eq_right hmem]
    have heq := detectRefresh_unreported_flow F A (namedInstance I) I.m κ α rate allocation R hpre hout e.isLt hmem
    have hf : epochVector F I refreshed L.flow e=epochVector F I mem L.flow e := by
      unfold epochVector Num.fixVal
      rw [Num.intVal_congr heq]
    exact hf.trans (epochHistoryCache_eq_cache_upTo_on F A I κ α Ψ eps hA L q i mem D eta op hv hG hPD e
      (hcache e.val e.isLt))

/-- The newly refreshed table is exactly the cache for the even-stage
Update input. The identity holds independently of whether Update succeeds. -/
theorem epochHistoryCache_eq_refreshed_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    (L : EpochLayout) (q K heap v i : ℕ) (x : R.τ) (mem refreshed : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ t≤2*i,D.G t=namedInstance I)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) x q K L.sourceEnd L.tableEnd).pre
      ((L.packet F I heap).take 20) mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) x q K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v refreshed)
    (haccept : refreshed (v-1)=1) (hbase : L.base+I.m*F.limbs≤L.flow)
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    epochVector F I refreshed L.flow=
      epochHistoryCache I A (appendHistoryIteration D (2*i) es g l)
        (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) (2*i+1+1)
        (epochVector F I mem L.base) :=
  epochHistoryCache_eq_refreshed_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    rate allocation R L q K heap v i x mem refreshed D eta op es g l actual
    hv hG (fun _ _ => trivial) hpre hout haccept hbase hcache

/-- The newly refreshed table is exactly the cache for the even-stage
Update input. The identity holds independently of whether Update succeeds. -/
theorem epochHistoryCache_eq_refreshed {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    (L : EpochLayout) (q K heap v i : ℕ) (x : R.τ) (mem refreshed : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ t≤2*i,D.G t=namedInstance I)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) x q K L.sourceEnd L.tableEnd).pre
      ((L.packet F I heap).take 20) mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) x q K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v refreshed)
    (haccept : refreshed (v-1)=1) (hbase : L.base+I.m*F.limbs≤L.flow)
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    epochVector F I refreshed L.flow=
      epochHistoryCache I A (appendHistoryIteration D (2*i) es g l)
        (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) (2*i+1+1)
        (epochVector F I mem L.base) :=
  epochHistoryCache_eq_refreshed_upTo F A I κ α Ψ eps (hA.upTo I.m I.n)
    rate allocation R L q K heap v i x mem refreshed D eta op es g l actual
    hv hG hpre hout haccept hbase hcache

end MinCostFlow.IPM.Machine
