module

public import MinCostFlow.IPM.Machine.RefreshScan
public import MinCostFlow.IPM.Machine.RefreshLayout
public import MinCostFlow.IPM.Machine.GraphCoefficientRead
public import MinCostFlow.IPM.NamedInstance
import WordRAM.Memory

/-!
# Connecting changed-edge memory to the model update batch

The reported names may occur in any order. Shared instance lookups
identify every endpoint read by the scan, and its exact output is the
body of the model's delete/reinsert batch. Input validity supplies all
word and address premises of the actual scan.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- An actual reported-name array and shared graph encode exactly the
model's delete/reinsert records, with their original edge names. -/
theorem refreshScanWords_namedInstance (I : Instance) (hI : I.IsValid)
    (mem : ℕ → ℕ) (a names : ℕ) (es : List ℕ)
    (hgraph : ListAt mem a (zeroLowerWords I)) (hnames : ListAt mem names es)
    (hes : ∀ e ∈ es,e < I.m) :
    refreshScanWords mem (a+2) names es.length=
      es.flatMap (fun e => [1,e,0,e,(namedInstance I).tail e,(namedInstance I).head e]) := by
  have hlist : (List.range es.length).map (fun i => mem (names+i))=es := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map,List.getElem_range]
      exact hnames i hi'
  unfold refreshScanWords
  conv_rhs => rw [← hlist,List.flatMap_map]
  apply List.flatMap_congr
  intro i hi
  have hin : i < es.length := List.mem_range.mp hi
  have hname := hnames i hin
  have he : mem (names+i) < I.m := by rw [hname]; exact hes _ (List.getElem_mem hin)
  have hp := zeroLower_endpoints_at I hI mem a hgraph ⟨mem (names+i),he⟩
  simp only [namedInstance,he,↓reduceDIte]
  rw [show a+2+1+5*mem (names+i)=a+3+5*mem (names+i) by omega]
  rw [hp.1,hp.2]

/-- The scan's address and word-fit premises follow from an actual
shared instance and a below-heap list of existing edge names. -/
theorem refreshScan_pre_from_instance (I : Instance) (hI : I.IsValid)
    {w a names heap : ℕ} {mem : ℕ → ℕ} (es : List ℕ)
    (hgraph : ListAt mem a (zeroLowerWords I)) (hnames : ListAt mem names es)
    (hes : ∀ e ∈ es,e < I.m)
    (hgraphEnd : a+(zeroLowerWords I).length ≤ heap)
    (hnamesEnd : names+es.length ≤ heap)
    (hinput : ∀ x ∈ zeroLowerWords I,x < 2^w)
    (hz : ZeroFrom mem heap) (hspace : heap+6*es.length < 2^w) :
    (refreshScanContract w).pre [a+2,names,es.length,heap] mem := by
  have hlen := zeroLowerWords_length I hI
  have hh := zeroLower_header_at I hI mem a hgraph
  have hm : I.m < 2^w := by
    rw [← hh.2]
    exact hgraph.words_lt hinput (i:=1) (by rw [hlen]; omega)
  have hn : I.n < 2^w := by
    rw [← hh.1]
    simpa only [Nat.add_zero] using hgraph.words_lt hinput (i:=0) (by rw [hlen]; omega)
  have hgEnd : a+(2+5*I.m) ≤ heap := by simpa only [hlen] using hgraphEnd
  refine ⟨⟨a+2,names,es.length,heap,rfl,?_⟩,hz,hspace⟩
  intro i hi
  have he : mem (names+i) < I.m := by
    rw [hnames i hi]
    exact hes _ (List.getElem_mem hi)
  have hp := zeroLower_endpoints_at I hI mem a hgraph ⟨mem (names+i),he⟩
  have hv := hI.1 (I.edge ⟨mem (names+i),he⟩) (List.getElem_mem he)
  refine ⟨by omega,he.trans hm,by omega,?_,?_⟩
  · rw [hp.1]
    exact hv.1.trans hn
  · rw [show a+2+1+5*mem (names+i)=a+3+5*mem (names+i) by omega,hp.2]
    exact hv.2.trans hn

end MinCostFlow.IPM.Machine
