module

public import MinCostFlow.IPM.Machine.ConnectedPairOrder
import MinCostFlow.IPM.Machine.InitialLayoutRead
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Scaling.SolverInputLayout
import WordRAM.Tactic

/-!
# Appending the two zero-deficit edge blocks

After the original Lemma 4.12 records, two scans append the hub edge
in each direction at each zero deficit. The final pointer determines
the corrected edge count, so the scans need no extra counters.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- Arguments `[input,incoming,outgoing,penalty,heap]`. -/
def connectedRecordAssemblyBody (assemble forward backward : ℕ) : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  .call 6 assemble [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4] ;;
  .call 7 forward [.reg 1,.reg 2,.reg 5,.reg 3,.reg 6] ;;
  .call 8 backward [.reg 1,.reg 2,.reg 5,.reg 3,.reg 7] ;;
  .store (.bin .add (.reg 4) (.const 1))
    (.bin .div (.bin .sub (.reg 8) (.bin .add (.reg 4) (.const 2))) (.const 5)) ;;
  .ret (.reg 8)

/-- The original assembly and the two pair scans. -/
def connectedRecordAssemblyModule (b : ℕ) : List Stmt :=
  [connectedRecordAssemblyBody (b+1) (b+6) (b+9)] ++
    (initialRecordAssemblyModule (b+1) ++
      (connectedPairScanModule false (b+6) ++ connectedPairScanModule true (b+9)))

/-- With the exact midpoint totals, assembly writes the connected graph
in the circulation encoding. Its cost and reservation are linear. -/
def connectedRecordAssemblyContract (w : ℕ) (J : Circulation) : Contract :=
  let graph := fun (args : List ℕ) => connectedInitialInstance J.toInstance (args.getD 3 0 : ℕ)
  let C := heapContract w
    (fun args mem => ∃ a inc out penalty heap, args = [a,inc,out,penalty,heap] ∧
      ListAt mem a J.solverWords ∧ a+J.solverWords.length ≤ heap ∧
      (∀ x ∈ J.solverWords, x < 2^w) ∧ (∀ e, 1 ≤ J.capacity e) ∧
      ∀ i < J.n, inc+i < heap ∧ out+i < heap ∧
        mem (inc+i) = incomingCapacity J i ∧ mem (out+i) = outgoingCapacity J i ∧
        mem (inc+i) < 2^w ∧ mem (out+i) < 2^w)
    (fun args _ mem' => ZeroLowerAt mem' (heapArg args) (graph args))
    (fun _ _ => 100*J.m+800*J.n+800) (fun _ _ => 2+5*J.m+15*J.n)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      v = heapArg args+2+5*(graph args).m }

/-- The connected assembly uses no random instructions. -/
theorem connectedRecordAssemblyModule_noRand (b : ℕ) :
    ∀ body ∈ connectedRecordAssemblyModule b, body.NoRand := by
  intro body hb
  simp only [connectedRecordAssemblyModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb | hb
  · simp [connectedRecordAssemblyBody,Stmt.NoRand]
  · exact initialRecordAssemblyModule_noRand _ body hb
  · exact connectedPairScanModule_noRand _ _ body hb
  · exact connectedPairScanModule_noRand _ _ body hb

/-- The full assembly writes the connected graph using linear time and space. -/
theorem connectedRecordAssembly_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b (connectedRecordAssemblyModule b)) (J : Circulation) :
    MeetsContract w p b (connectedRecordAssemblyContract w J) := by
  have hrest : p.HasAt (b+1) (initialRecordAssemblyModule (b+1) ++
      (connectedPairScanModule false (b+6) ++ connectedPairScanModule true (b+9))) :=
    Num.hasAt_append_right hp
  have hscan : p.HasAt (b+6) (connectedPairScanModule false (b+6) ++
      connectedPairScanModule true (b+9)) := Num.hasAt_append_right hrest
  have hback : p.HasAt (b+9) (connectedPairScanModule true (b+9)) :=
    Num.hasAt_append_right hscan
  have hA := initialRecordAssembly_meetsContract hw (Num.hasAt_append_left hrest) J
  have hF := connectedPairScan_meetsContract false hw (Num.hasAt_append_left hscan)
  have hB := connectedPairScan_meetsContract true hw hback
  apply meetsContract_of_runs hp.head
  intro args mem pos tape hwords hpre
  obtain ⟨⟨a,inc,out,penalty,heap,rfl,hat,hend,hinput,hpCap,htables⟩,hzero,hspace⟩ := hpre
  change heap+(2+5*J.m+15*J.n) < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hn := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).1
  have hnw : J.n < 2^w := hinput _ List.mem_cons_self
  have htw : ∀ i < J.n, inc+i < heap ∧ out+i < heap ∧
      mem (inc+i) < 2^w ∧ mem (out+i) < 2^w := fun i hi =>
    ⟨(htables i hi).1,(htables i hi).2.1,(htables i hi).2.2.2.2⟩
  have ha : a < 2^w := hwords _ (by simp)
  have hi : inc < 2^w := hwords _ (by simp)
  have ho : out < 2^w := hwords _ (by simp)
  have hk : penalty < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  let old := initialInstance J.toInstance (penalty : ℤ)
  let aug := connectedInitialInstance J.toInstance (penalty : ℤ)
  let rows := (zeroLowerWords old).drop 2
  let forward := connectedPairPrefix false (incomingCapacity J) (outgoingCapacity J) J.n penalty J.n
  let backward := connectedPairPrefix true (incomingCapacity J) (outgoingCapacity J) J.n penalty J.n
  have hrlen : rows.length = 5*old.m := by
    change ((zeroLowerWords old).drop 2).length = _
    rw [List.length_drop, zeroLowerWords_length old
      (initialInstance_valid J.toInstance penalty J.toInstance_valid)]
    omega
  have hfLen : forward.length ≤ 5*J.n := connectedPairPrefix_length_le _ _ _ _ _ _
  have hbLen : backward.length ≤ 5*J.n := connectedPairPrefix_length_le _ _ _ _ _ _
  have hcount : aug.m = old.m + (zeroDeficitVertices J.toInstance).card +
      (zeroDeficitVertices J.toInstance).card := by
    dsimp only [aug,old,connectedInitialInstance,initialInstance]
    rw [instanceOfArrays_m, instanceOfArrays_m]
    omega
  have hrecords (mem' : ℕ → ℕ) (hframe : ∀ x < heap, mem' x = mem x)
      (reverse : Bool) :
      connectedPairPrefix reverse (fun i => mem' (inc+i)) (fun i => mem' (out+i)) J.n penalty J.n =
        connectedPairPrefix reverse (incomingCapacity J) (outgoingCapacity J) J.n penalty J.n := by
    apply connectedPairPrefix_congr
    · intro i hi
      exact (hframe _ (htables i hi).1).trans (htables i hi).2.2.1
    · intro i hi
      exact (hframe _ (htables i hi).2.1).trans (htables i hi).2.2.2.1
  apply runs_start_le
  unfold connectedRecordAssemblyBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_call_le hA (vs := [a,inc,out,penalty,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨a,inc,out,penalty,heap,rfl,hat,hend,hinput,htw⟩,hzero,
      by change heap+(2+5*J.m+5*J.n) < 2^w; omega⟩
  · intro v1 mem1 pos1 hpost1
    obtain ⟨⟨hlo1,hhi1,hframe1,hzero1,hwords1⟩,hv1⟩ := hpost1
    change ∀ x < heap, mem1 x = mem x at hframe1
    change v1 ≤ heap+(2+5*J.m+5*J.n) at hhi1
    change heap ≤ v1 at hlo1
    change ListAt mem1 heap (initialAssemblyWords J (fun i => mem (inc+i))
      (fun i => mem (out+i)) penalty) at hwords1
    have haux := initialAuxiliaryPrefix_congr (fun i => mem (inc+i)) (fun i => mem (out+i))
      (incomingCapacity J) (outgoingCapacity J) J.n penalty J.n
      (fun i hi => (htables i hi).2.2.1) (fun i hi => (htables i hi).2.2.2.1)
    have hrewrite : initialAssemblyWords J (fun i => mem (inc+i)) (fun i => mem (out+i)) penalty =
        zeroLowerWords old := by
      unfold initialAssemblyWords
      rw [haux]
      exact initialAssemblyWords_eq_initialInstance J hpCap penalty
    rw [hrewrite] at hwords1
    have hv1' : v1 = heap+2+5*old.m := by
      change v1 = heap+2+5*J.m+
        (initialAuxiliaryPrefix (fun i => mem (inc+i)) (fun i => mem (out+i)) J.n penalty J.n).length at hv1
      rw [haux, initialAuxiliaryPrefix_length_deficit] at hv1
      have hfree : (freeEdges J.toInstance).card = J.m := by
        rw [freeEdges_circulation J hpCap,Finset.card_univ,Fintype.card_fin,Circulation.toInstance_m]
      simpa only [old, initialInstance_m, hfree, Nat.mul_add, Nat.add_assoc] using hv1
    have hv1w : v1 < 2^w := by omega
    have hsource (atHeap : ℕ) (hatHeap : heap ≤ atHeap) (mem' : ℕ → ℕ)
        (hframe : ∀ x < heap, mem' x = mem x) :
        ∀ i < J.n, inc+i < atHeap ∧ out+i < atHeap ∧
          mem' (inc+i) < 2^w ∧ mem' (out+i) < 2^w := by
      intro i hi
      obtain ⟨hia,hoa,hiw,how⟩ := htw i hi
      exact ⟨hia.trans_le hatHeap,hoa.trans_le hatHeap,
        by simpa only [hframe _ hia] using hiw, by simpa only [hframe _ hoa] using how⟩
    refine runs_seq_call_le hF (vs := [inc,out,J.n,penalty,v1]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_,_,_,_,_,rfl,hsource v1 hlo1 mem1 hframe1⟩,hzero1,
        by change v1+5*J.n < 2^w; omega⟩
    · intro v2 mem2 pos2 hpost2
      obtain ⟨⟨hlo2,hhi2,hframe2,hzero2,hwords2⟩,hv2⟩ := hpost2
      change v1 ≤ v2 at hlo2
      change v2 ≤ v1+5*J.n at hhi2
      change ∀ x < v1, mem2 x = mem1 x at hframe2
      have hfEq := hrecords mem1 hframe1 false
      change ListAt mem2 v1 (connectedPairPrefix false (fun i => mem1 (inc+i))
        (fun i => mem1 (out+i)) J.n penalty J.n) at hwords2
      change v2 = v1+(connectedPairPrefix false (fun i => mem1 (inc+i))
        (fun i => mem1 (out+i)) J.n penalty J.n).length at hv2
      rw [hfEq] at hv2 hwords2
      have hframe02 : ∀ x < heap, mem2 x = mem x := fun x hx =>
        (hframe2 x (hx.trans_le hlo1)).trans (hframe1 x hx)
      have hv2w : v2 < 2^w := by omega
      refine runs_seq_call_le hB (vs := [inc,out,J.n,penalty,v2]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_,_,_,_,_,rfl,hsource v2 (hlo1.trans hlo2) mem2 hframe02⟩,hzero2,
          by change v2+5*J.n < 2^w; omega⟩
      · intro v3 mem3 pos3 hpost3
        obtain ⟨⟨hlo3,hhi3,hframe3,hzero3,hwords3⟩,hv3⟩ := hpost3
        change v2 ≤ v3 at hlo3
        change v3 ≤ v2+5*J.n at hhi3
        change ∀ x < v2, mem3 x = mem2 x at hframe3
        change ListAt mem3 v2 (connectedPairPrefix true (fun i => mem2 (inc+i))
          (fun i => mem2 (out+i)) J.n penalty J.n) at hwords3
        change v3 = v2+(connectedPairPrefix true (fun i => mem2 (inc+i))
          (fun i => mem2 (out+i)) J.n penalty J.n).length at hv3
        have hbEq := hrecords mem2 hframe02 true
        rw [hbEq] at hv3 hwords3
        have hfl : forward.length = 5*(zeroDeficitVertices J.toInstance).card :=
          connectedPairPrefix_length_eq J penalty false
        have hbl : backward.length = 5*(zeroDeficitVertices J.toInstance).card :=
          connectedPairPrefix_length_eq J penalty true
        change v2 = v1+forward.length at hv2
        change v3 = v2+backward.length at hv3
        have hfinal : v3 = heap+2+5*aug.m := by omega
        have hcount' : (v3-(heap+2))/5 = aug.m := by omega
        have hv3w : v3 < 2^w := by omega
        have hh2 : heap+2 < 2^w := by omega
        have hdiff : v3-(heap+2) < 2^w := by omega
        have hcntw : (v3-(heap+2))/5 < 2^w := by omega
        have hn1 : mem3 heap = J.n+1 := by
          exact (hframe3 _ (by omega)).trans ((hframe2 _ (by omega)).trans (hwords1 0 (by
            simp [zeroLowerWords])))
        have hrows : ListAt mem3 (heap+2) rows := by
          intro i hi
          have h := hwords1.drop 2 i hi
          rw [hrlen] at hi
          exact (hframe3 _ (by omega)).trans ((hframe2 _ (by omega)).trans h)
        have hbody : ListAt mem3 (heap+2) (rows ++ forward ++ backward) := by
          apply listAt_append.mpr
          constructor
          · apply listAt_append.mpr
            refine ⟨hrows, ?_⟩
            rw [hrlen, ← hv1']
            intro i hi
            exact (hframe3 _ (by omega)).trans (hwords2 i hi)
          · rw [List.length_append, hrlen]
            have hbase : heap+2+(5*old.m+forward.length) = v2 := by omega
            rw [hbase]
            exact hwords3
        wram_step
        refine runs_ret_le (v := v3) (by eval_expr) ?_ ?_
        · let resultMem := Function.update mem3 (heap+1) ((v3-(heap+2))/5)
          change (heap ≤ v3 ∧ v3 ≤ heap+(2+5*J.m+15*J.n) ∧
            (∀ x < heap,resultMem x = mem x) ∧ ZeroFrom resultMem v3 ∧
            ZeroLowerAt resultMem heap aug) ∧ v3 = heap+2+5*aug.m
          refine ⟨⟨by omega,by omega,?_,?_,?_,?_,?_⟩,hfinal⟩
          · intro x hx
            dsimp only [resultMem]
            rw [Function.update_of_ne (by omega : x ≠ heap+1), hframe3 _ (by omega)]
            exact hframe02 x hx
          · intro x hx
            dsimp only [resultMem]
            rw [Function.update_of_ne (by omega : x ≠ heap+1)]
            exact hzero3 x hx
          · exact (connectedInitialInstance_zeroLower J hpCap penalty).1
          · exact (connectedInitialInstance_zeroLower J hpCap penalty).2
          · change ListAt resultMem heap (zeroLowerWords (connectedInitialInstance J.toInstance (penalty : ℤ)))
            rw [zeroLowerWords_connected]
            simp only [List.cons_append, List.nil_append]
            apply listAt_cons.mpr
            refine ⟨by simpa [resultMem] using hn1, ?_⟩
            apply listAt_cons.mpr
            refine ⟨by simpa [resultMem, aug] using hcount', ?_⟩
            intro i hi
            have hword := hbody i (by simpa only [List.append_assoc] using hi)
            change resultMem (heap+1+1+i) = _
            rw [show heap+1+1+i = heap+2+i by omega]
            simpa only [resultMem, Function.update_of_ne (by omega : heap+2+i ≠ heap+1),
              List.append_assoc] using hword
        · simp only [connectedRecordAssemblyContract,initialRecordAssemblyContract,
            connectedPairScanContract,heapContract,Expr.size_bin,Expr.size_reg,Expr.size_const,
            Expr.size_load,argsSize_cons,argsSize_nil,List.getD_cons_zero,List.getD_cons_succ]
          omega

end MinCostFlow.IPM.Machine
