module

public import MinCostFlow.LSF.Program.WScan
public import MinCostFlow.LSF.Program.RefineMath

/-!
# The `W` block is `refineDecomp`

`wBlock_bridge`: after the scan, the `W` block holds `refineDecomp W_T F₀`, for the forest
`F₀ = forestGivenRoots T₀ r₀ R π`. The scan read the kept indices sorted by a key `K` that is
equal exactly when the label `lab` and the root `rt` are equal. So each group of the scan is the
set `keyClass x` of the kept indices with the key of its first element `x`, and by
`RefineMath.lean` its vertices are `keyPiece x` and its edges are the `F₀` edges inside it.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF

@[expose] public section

/-- In a list whose entries strictly increase under `f`, two entries with the same value are
equal. -/
lemma pairwise_lt_inj {α : Type*} {G : List α} {f : α → ℕ}
    (h : G.Pairwise (fun p q => f p < f q)) {p q : α} (hp : p ∈ G) (hq : q ∈ G)
    (he : f p = f q) : p = q := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
  rcases lt_trichotomy i j with hij | rfl | hij
  · have := List.pairwise_iff_getElem.mp h i j hi hj hij; omega
  · rfl
  · have := List.pairwise_iff_getElem.mp h j i hj hi hij; omega

lemma getElem_flatten_start' (L : List (List ℕ)) {i t m : ℕ} (hi : i < L.length)
    (ht : t < L[i].length) (hm : ((L.take i).map List.length).sum = m) :
    ∃ h : m + t < L.flatten.length, L.flatten[m + t] = L[i][t] := by
  subst hm; exact getElem_flatten_start L hi ht

lemma eStart_le_total (G : List (List ℕ × List ℕ)) (i : ℕ) : eStart G i ≤ eStart G G.length := by
  simp only [eStart, List.take_length]
  rw [List.map_take]
  conv_rhs => rw [← List.take_append_drop i (G.map (·.1.length))]
  rw [List.sum_append]
  omega

variable {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ} {fid tl hd par pe dep : ℕ → ℕ}
  {R : Finset ℕ} {π inR piv mp own rt : ℕ → ℕ} {W_T : Finset (Finset ℕ)} {lab : ℕ → ℕ × ℕ}

/-- The facts of `wT_spec` give `WLabels` for the label pairs `(labY x, labB x)`. -/
lemma wLabels_of_spec {G₀ : MGraph} {k : ℝ} {labY labB : ℕ → ℕ}
    (hspec : IsTreeDecompSpec G₀ T₀ k W_T)
    (hlab : ∀ x < vList.length, x ≠ r → ∀ x' < vList.length, x' ≠ r →
      ((labY x = labY x' ∧ labB x = labB x') ↔ ∃ P ∈ W_T,
        parentEdge T₀ (vList.getD r 0) (vList.getD x 0) ∈ inducedEdges T₀ P ∧
        parentEdge T₀ (vList.getD r 0) (vList.getD x' 0) ∈ inducedEdges T₀ P)) :
    WLabels T₀ vList r W_T (fun x => (labY x, labB x)) where
  hconv := hspec.1
  hdisj := hspec.2.1
  hcov := hspec.2.2.1
  hlab := fun x hx hxr x' hx' hxr' => by
    rw [Prod.mk.injEq]; exact hlab x hx hxr x' hx' hxr'

/-- The `W` block after the scan holds `refineDecomp W_T F₀`. -/
theorem wBlock_bridge (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (h : RootPassIdx T₀ vList tM r fid par pe R π inR piv mp own rt)
    (hW : WLabels T₀ vList r W_T lab) {K s lY lB : ℕ → ℕ} {cnt n0 wPtr : ℕ} {mem' : ℕ → ℕ}
    (hlab : ∀ y, lab y = (lY y, lB y))
    (hSnd : ((List.range cnt).map s).Nodup)
    (hSmem : ∀ y, y ∈ (List.range cnt).map s ↔ y < vList.length ∧ y ≠ r ∧ own (pe y) = 0)
    (hKok : WKeyOK K s lY lB rt cnt) (hcn : cnt ≤ n0)
    (h0 : mem' (wPtr + wOffNumPieces) = (wGroups K s par cnt).length)
    (h1 : mem' (wPtr + wOffVertOffPtr) = wVertOffBase wPtr)
    (h2 : mem' (wPtr + wOffVertsPtr) = wVertsBase wPtr n0)
    (h3 : mem' (wPtr + wOffEdgeOffPtr) = wEdgeOffBase wPtr n0)
    (h4 : mem' (wPtr + wOffEdgesPtr) = wEdgesBase wPtr n0)
    (h5 : mem' (wPtr + wOffTotalVerts) = vTotal (wGroups K s par cnt))
    (h6 : mem' (wPtr + wOffTotalEdges) = cnt)
    (hVO : ∀ i ≤ (wGroups K s par cnt).length,
      mem' (wVertOffBase wPtr + i) = vStart (wGroups K s par cnt) i)
    (hEO : ∀ i ≤ (wGroups K s par cnt).length,
      mem' (wEdgeOffBase wPtr n0 + i) = eStart (wGroups K s par cnt) i)
    (hVS : ListAt mem' (wVertsBase wPtr n0)
      ((flatV (wGroups K s par cnt)).map (fun y => vList.getD y 0)))
    (hES : ∀ j < cnt, mem' (wEdgesBase wPtr n0 + j) = fid (pe (s j))) :
    WBlockAt mem' wPtr n0 (refineDecomp W_T (forestGivenRoots T₀ (vList.getD r 0) R π))
      (forestGivenRoots T₀ (vList.getD r 0) R π) := by
  classical
  obtain ⟨G, hG⟩ : ∃ G, wGroups K s par cnt = G := ⟨_, rfl⟩
  rw [hG] at h0 h5 hVO hEO hVS
  have GI : GroupsInv K s par cnt G := hG ▸ groupsInv_of_le hKok.1 cnt le_rfl
  have hGl : G.length ≤ cnt := length_le GI
  have hGv : vTotal G ≤ 2 * cnt := vTotal_le GI
  have hEG : eStart G G.length = cnt := eStart_length GI
  set S := (List.range cnt).map s with hS
  -- the elements of the groups are the entries of `S`
  have hinS : ∀ q ∈ G, ∀ y ∈ q.1, y ∈ S := fun q hq y hy => by
    rw [hS, ← GI.hflat]
    exact List.mem_flatten.mpr ⟨q.1, List.mem_map_of_mem hq, hy⟩
  have hpos : ∀ y ∈ S, ∃ j < cnt, s j = y := fun y hy => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    exact ⟨j, List.mem_range.mp hj, rfl⟩
  -- equal keys on `S` are equal labels and roots
  have hKeq : ∀ y ∈ S, ∀ y' ∈ S, (K y = K y' ↔ lab y = lab y' ∧ rt y = rt y') := by
    intro y hy y' hy'
    obtain ⟨j, hj, rfl⟩ := hpos y hy
    obtain ⟨j', hj', rfl⟩ := hpos y' hy'
    rw [hKok.2 j hj j' hj', hlab, hlab, Prod.mk.injEq, and_assoc]
  -- each group is the key class of its first element
  have hclass : ∀ q ∈ G, ∀ y, y ∈ q.1 ↔
      y ∈ keyClass vList.length r own pe rt lab (q.1.headD 0) := by
    intro q hq y
    have hx0 := headD_mem' (GI.hne q hq)
    have hx0S := hinS q hq _ hx0
    simp only [keyClass, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hy
      have hyS := hinS q hq y hy
      obtain ⟨a, b, c⟩ := (hSmem y).mp hyS
      exact ⟨a, b, c, ((hKeq y hyS _ hx0S).mp (GI.hkey q hq y hy)).1,
        ((hKeq y hyS _ hx0S).mp (GI.hkey q hq y hy)).2⟩
    · rintro ⟨a, b, c, hl, ht⟩
      have hyS : y ∈ S := (hSmem y).mpr ⟨a, b, c⟩
      rw [hS, ← GI.hflat] at hyS
      obtain ⟨l, hl', hyl⟩ := List.mem_flatten.mp hyS
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hl'
      have hx0' := headD_mem' (GI.hne q' hq')
      have hKy : K y = K (q.1.headD 0) := (hKeq y (hinS q' hq' y hyl) _ hx0S).mpr ⟨hl, ht⟩
      have hqq : q' = q := pairwise_lt_inj GI.hlt hq' hq (by
        rw [← GI.hkey q' hq' y hyl, hKy])
      rw [hqq] at hyl
      exact hyl
  have hkept : ∀ q ∈ G, q.1.headD 0 < vList.length ∧ q.1.headD 0 ≠ r ∧
      own (pe (q.1.headD 0)) = 0 := fun q hq =>
    (hSmem _).mp (hinS q hq _ (headD_mem' (GI.hne q hq)))
  have hidx : ∀ q ∈ G, ∀ z ∈ q.1, z < vList.length ∧ z ≠ r ∧ own (pe z) = 0 := fun q hq z hz =>
    (hSmem z).mp (hinS q hq z hz)
  have hGnd : G.Nodup := GI.hlt.imp fun hab he => by rw [he] at hab; exact lt_irrefl _ hab
  have hflatS : (G.map Prod.fst).flatten = S := GI.hflat
  dsimp only [WBlockAt]
  rw [h0, h5, h6]
  refine ⟨h1, h2, h3, h4, by omega, by omega, by omega,
    by rw [hVO 0 (Nat.zero_le _)]; simp [vStart], by rw [hVO _ le_rfl]; rfl,
    by rw [hEO 0 (Nat.zero_le _)]; simp [eStart], by rw [hEO _ le_rfl, hEG],
    G.map (fun q => keyPiece vList r own pe rt par lab (q.1.headD 0)), by simp, ?_, ?_, ?_⟩
  · refine List.Nodup.map_on (fun q hq q' hq' he => ?_) hGnd
    obtain ⟨a, b, c⟩ := hkept q hq
    obtain ⟨a', b', c'⟩ := hkept q' hq'
    have := (keyPiece_eq_iff hI h hW a b c a' b' c').mp he
    exact pairwise_lt_inj GI.hlt hq hq'
      ((hKeq _ (hinS q hq _ (headD_mem' (GI.hne q hq))) _
        (hinS q' hq' _ (headD_mem' (GI.hne q' hq')))).mpr this)
  · intro P
    rw [refine_mem_iff hI h hW P, List.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨_, (hkept q hq).1, (hkept q hq).2.1, (hkept q hq).2.2, rfl⟩
    · rintro ⟨x, hx, hxr, hxo, rfl⟩
      have hxS : x ∈ S := (hSmem x).mpr ⟨hx, hxr, hxo⟩
      rw [← hflatS] at hxS
      obtain ⟨l, hl', hxl⟩ := List.mem_flatten.mp hxS
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl'
      have hxc := (hclass q hq x).mp hxl
      simp only [keyClass, Finset.mem_filter, Finset.mem_range] at hxc
      obtain ⟨a, b, c⟩ := hkept q hq
      exact ⟨q, hq, (keyPiece_eq_iff hI h hW a b c hx hxr hxo).mpr
        ⟨hxc.2.2.2.1.symm, hxc.2.2.2.2.symm⟩⟩
  · intro i hi
    simp only [List.length_map] at hi
    have hq : G[i] ∈ G := List.getElem_mem hi
    obtain ⟨a, b, c⟩ := hkept _ hq
    rw [hVO i hi.le, hVO (i + 1) hi, hEO i hi.le, hEO (i + 1) hi]
    have hvs : vStart G (i + 1) = vStart G i + G[i].2.length := start_succ _ G hi
    have hes : eStart G (i + 1) = eStart G i + G[i].1.length := start_succ _ G hi
    have hvle := vStart_le_vTotal G (i := i + 1)
    have hele := eStart_le_total G (i + 1)
    simp only [List.getElem_map]
    refine ⟨by omega, hvle, by omega, by omega, G[i].2.map (fun y => vList.getD y 0),
      by simp [hvs], ?_, ?_, ?_, G[i].1.map (fun y => fid (pe y)), by simp [hes], ?_, ?_, ?_⟩
    · refine List.Nodup.map_on (fun y hy y' hy' he => ?_) (GI.hvert _ hq).1
      have hlt : ∀ y ∈ G[i].2, y < vList.length := fun y hy => by
        obtain ⟨z, hz, hyz | hyz⟩ := ((GI.hvert _ hq).2 y).mp hy
        · rw [hyz]; exact (hidx _ hq z hz).1
        · rw [hyz]; exact (hI.step (hidx _ hq z hz).1 (hidx _ hq z hz).2.1).1
      exact hI.getD_inj (hlt y hy) (hlt y' hy') he
    · intro x
      simp only [List.mem_map, keyPiece, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hyz | hyz⟩ := ((GI.hvert _ hq).2 y).mp hy
        · exact Or.inl ⟨z, (hclass _ hq z).mp hz, by rw [hyz]⟩
        · exact Or.inr ⟨z, (hclass _ hq z).mp hz, by rw [hyz]⟩
      · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
        · exact ⟨z, ((GI.hvert _ hq).2 z).mpr ⟨z, (hclass _ hq z).mpr hz, Or.inl rfl⟩, rfl⟩
        · exact ⟨par z, ((GI.hvert _ hq).2 _).mpr ⟨z, (hclass _ hq z).mpr hz, Or.inr rfl⟩, rfl⟩
    · intro t ht
      simp only [List.length_map] at ht
      have hsum : (((G.map Prod.snd).take i).map List.length).sum = vStart G i := by
        simp [vStart, List.map_take, Function.comp_def]
      obtain ⟨hb, hval⟩ := getElem_flatten_start' (G.map Prod.snd) (i := i) (t := t)
        (by simpa using hi) (by simpa using ht) hsum
      have hlen : vStart G i + t < ((flatV G).map (fun y => vList.getD y 0)).length := by
        rw [List.length_map]; exact hb
      rw [Nat.add_assoc, hVS _ hlen]
      simp only [List.getElem_map, flatV]
      rw [hval]
      simp
    · have hnd1 : G[i].1.Nodup := by
        rw [← hflatS] at hSnd
        exact (List.nodup_flatten.mp hSnd).1 _ (List.mem_map_of_mem hq)
      refine List.Nodup.map_on (fun y hy y' hy' he => ?_) hnd1
      obtain ⟨ya, yb, -⟩ := hidx _ hq y hy
      obtain ⟨ya', yb', -⟩ := hidx _ hq y' hy'
      obtain ⟨-, -, -, -, e1⟩ := hI.step ya yb
      obtain ⟨-, -, -, -, e2⟩ := hI.step ya' yb'
      have hne1 : vList.getD y 0 ≠ vList.getD r 0 := fun he' => yb (hI.getD_inj ya hI.hr he')
      have hne2 : vList.getD y' 0 ≠ vList.getD r 0 := fun he' => yb' (hI.getD_inj ya' hI.hr he')
      exact hI.getD_inj ya ya' (parentEdge_inj hI.hT (hI.getD_mem ya) (hI.getD_mem ya') hne1
        hne2 (by rw [e1, e2]; exact he))
    · intro e
      rw [ind_keyPiece hI h hW a b c]
      simp only [List.mem_map, Finset.mem_image, hclass _ hq]
    · intro t ht
      simp only [List.length_map] at ht
      have hsum : (((G.map Prod.fst).take i).map List.length).sum = eStart G i := by
        simp [eStart, List.map_take, Function.comp_def]
      obtain ⟨hb, hval⟩ := getElem_flatten_start' (G.map Prod.fst) (i := i) (t := t)
        (by simpa using hi) (by simpa using ht) hsum
      simp only [hflatS, hS, List.length_map, List.length_range] at hb
      simp only [hflatS, hS, List.getElem_map, List.getElem_range] at hval
      rw [Nat.add_assoc, hES _ hb]
      simp only [List.getElem_map, ← hval]

end

end MinCostFlow.LSF.Program
