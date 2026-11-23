module

public import MinCostFlow.LSF.Program.WAddV

/-!
# The groups of the scan in memory

The scan of `WScan.lean` keeps the groups `G` (`WScanMath.lean`) in four arrays: the vertex
offsets at `VO`, the edge offsets at `EO`, the vertex list at `VS` and the stamps at `ST`.
`WMem` says that memory holds `G` this way. This file proves that the three kinds of steps of
the scan keep `WMem`:

* `WMem.newGroup`: writing the two offsets of a new group;
* `WMem.addElem`: adding an element to the last group (the memory does not change);
* `WMem.addVert`: adding a vertex with `wAddVProc`.

`wGroups_succ_split` writes one step of `wGroups` as these three steps.
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-- Adds the element `x` to a group. -/
def eAdd (x : ℕ) (p : List ℕ × List ℕ) : List ℕ × List ℕ := (p.1 ++ [x], p.2)

/-- Adds the vertex `y` to a group, unless it is there. -/
def vAdd (y : ℕ) (p : List ℕ × List ℕ) : List ℕ × List ℕ := (p.1, addNew p.2 y)

lemma pushLast_pushLast (f g : List ℕ × List ℕ → List ℕ × List ℕ) (G : List (List ℕ × List ℕ)) :
    pushLast f (pushLast g G) = pushLast (f ∘ g) G := by
  simp [pushLast]

/-- One step of `wGroups` as a new group (at a boundary), an element and two vertices. -/
lemma wGroups_succ_split (K s pa : ℕ → ℕ) (k : ℕ) :
    wGroups K s pa (k + 1) = pushLast (vAdd (pa (s k))) (pushLast (vAdd (s k))
      (pushLast (eAdd (s k))
        (if IsBoundary K s k then wGroups K s pa k ++ [([], [])] else wGroups K s pa k))) := by
  rw [pushLast_pushLast, pushLast_pushLast, wGroups]
  rfl

lemma pushLast_ne_nil (f : List ℕ × List ℕ → List ℕ × List ℕ) (G : List (List ℕ × List ℕ)) :
    pushLast f G ≠ [] := by
  simp [pushLast]

lemma pushLast_length (f : List ℕ × List ℕ → List ℕ × List ℕ) {G : List (List ℕ × List ℕ)}
    (hG : G ≠ []) : (pushLast f G).length = G.length := by
  rw [pushLast_of_ne_nil f hG]
  simp only [List.length_append, List.length_dropLast, List.length_singleton]
  have := List.length_pos_iff.mpr hG
  omega

lemma pushLast_getLast (f : List ℕ × List ℕ → List ℕ × List ℕ) {G : List (List ℕ × List ℕ)}
    (hG : G ≠ []) : (pushLast f G).getLast (pushLast_ne_nil f G) = f (G.getLast hG) := by
  simp only [pushLast_of_ne_nil f hG, List.getLast_append_of_ne_nil, List.getLast_singleton]
  · simp

/-- The first `i < G.length` groups do not change when the last group changes. -/
lemma take_pushLast (f : List ℕ × List ℕ → List ℕ × List ℕ) {G : List (List ℕ × List ℕ)}
    (hG : G ≠ []) {i : ℕ} (hi : i < G.length) : (pushLast f G).take i = G.take i := by
  have hlen := List.length_pos_iff.mpr hG
  rw [pushLast_of_ne_nil f hG, List.take_append_of_le_length (by simp; omega)]
  conv_rhs => rw [← List.dropLast_append_getLast hG]
  rw [List.take_append_of_le_length (by simp; omega)]

/-- The vertices of all groups, in order. -/
def flatV (G : List (List ℕ × List ℕ)) : List ℕ := (G.map Prod.snd).flatten

lemma vTotal_eq (G : List (List ℕ × List ℕ)) : vTotal G = (flatV G).length := by
  simp [vTotal, vStart, flatV, List.length_flatten, Function.comp_def]

lemma flatV_append_nil (G : List (List ℕ × List ℕ)) : flatV (G ++ [([], [])]) = flatV G := by
  simp [flatV]

lemma flatV_pushLast_eAdd (x : ℕ) {G : List (List ℕ × List ℕ)} (hG : G ≠ []) :
    flatV (pushLast (eAdd x) G) = flatV G := by
  obtain ⟨D, q, rfl⟩ : ∃ D q, G = D ++ [q] := ⟨_, _, (List.dropLast_append_getLast hG).symm⟩
  simp [flatV, eAdd, pushLast]

lemma flatV_pushLast_vAdd (y : ℕ) {G : List (List ℕ × List ℕ)} (hG : G ≠ []) :
    flatV (pushLast (vAdd y) G) =
      if y ∈ (G.getLast hG).2 then flatV G else flatV G ++ [y] := by
  obtain ⟨D, q, rfl⟩ : ∃ D q, G = D ++ [q] := ⟨_, _, (List.dropLast_append_getLast hG).symm⟩
  simp only [pushLast, List.dropLast_concat, List.getLastD_eq_getLast?, List.getLast?_concat,
    Option.getD_some, List.getLast_concat]
  simp only [flatV, vAdd, addNew, List.map_append, List.map_singleton, List.flatten_append,
    List.flatten_singleton]
  split_ifs <;> simp

/-- A layout of the four arrays: offsets at `VO` and `EO` (`N + 1` cells), vertices at `VS`
(`2N` cells), edges at `ES` (`N` cells), and the `n` stamps at `ST` away from all of them. -/
def WLay (VO VS EO ES ST n N : ℕ) : Prop :=
  VO + (N + 1) ≤ VS ∧ VS + 2 * N ≤ EO ∧ EO + (N + 1) ≤ ES ∧ (ST + n ≤ VO ∨ ES + N ≤ ST)

/-- Memory holds the groups `G`. -/
def WMem (mem : ℕ → ℕ) (VO VS EO ST n : ℕ) (vL : ℕ → ℕ) (G : List (List ℕ × List ℕ)) : Prop :=
  (∀ i < G.length, mem (VO + i) = vStart G i) ∧ (∀ i < G.length, mem (EO + i) = eStart G i) ∧
  ListAt mem VS ((flatV G).map vL) ∧
  ∀ y < n, mem (ST + y) ≤ G.length ∧ ∀ hG : G ≠ [], (mem (ST + y) = G.length ↔ y ∈ (G.getLast hG).2)

lemma wMem_nil (mem : ℕ → ℕ) (VO VS EO ST n : ℕ) (vL : ℕ → ℕ)
    (hz : ∀ y < n, mem (ST + y) = 0) : WMem mem VO VS EO ST n vL [] := by
  refine ⟨by simp, by simp, by simp [ListAt, flatV], fun y hy => ⟨by simp [hz y hy], ?_⟩⟩
  intro h; exact absurd rfl h

lemma vStart_append_nil (G : List (List ℕ × List ℕ)) {i : ℕ} (hi : i ≤ G.length) :
    vStart (G ++ [([], [])]) i = vStart G i := by
  simp [vStart, List.take_append_of_le_length hi]

lemma eStart_append_nil (G : List (List ℕ × List ℕ)) {i : ℕ} (hi : i ≤ G.length) :
    eStart (G ++ [([], [])]) i = eStart G i := by
  simp [eStart, List.take_append_of_le_length hi]

lemma vStart_length (G : List (List ℕ × List ℕ)) : vStart G G.length = vTotal G := rfl

/-- `WMem` only reads the first `N` offsets, the first `2N` vertices and the stamps. -/
lemma WMem.congr {mem mem' : ℕ → ℕ} {VO VS EO ST n N : ℕ} {vL : ℕ → ℕ}
    {G : List (List ℕ × List ℕ)} (h : WMem mem VO VS EO ST n vL G) (hlen : G.length ≤ N)
    (htot : vTotal G ≤ 2 * N)
    (hag : ∀ a, (VO ≤ a ∧ a < VO + N) ∨ (EO ≤ a ∧ a < EO + N) ∨ (VS ≤ a ∧ a < VS + 2 * N) ∨
      (ST ≤ a ∧ a < ST + n) → mem' a = mem a) :
    WMem mem' VO VS EO ST n vL G := by
  obtain ⟨hVO, hEO, hVS, hST⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, fun y hy => ?_⟩
  · rw [hag _ (Or.inl ⟨by omega, by omega⟩)]; exact hVO i hi
  · rw [hag _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hEO i hi
  · have hj' : j < vTotal G := by rw [vTotal_eq]; simpa using hj
    rw [hag _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]; exact hVS j hj
  · rw [hag _ (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))]; exact hST y hy

/-- `wAddVProc` changes only the stamp of `y` and the cell `vsPtr + tv`. -/
lemma wAddVMem_other {mem : ℕ → ℕ} {stPtr vListPtr vsPtr y g tv a : ℕ} (h1 : a ≠ stPtr + y)
    (h2 : a ≠ vsPtr + tv) : wAddVMem mem stPtr vListPtr vsPtr y g tv a = mem a := by
  unfold wAddVMem
  split_ifs
  · rfl
  · rw [Function.update_of_ne h2, Function.update_of_ne h1]

/-- Writing the offsets of a new, empty group. -/
lemma WMem.newGroup {mem : ℕ → ℕ} {VO VS EO ES ST n N : ℕ} {vL : ℕ → ℕ}
    {G : List (List ℕ × List ℕ)} (h : WMem mem VO VS EO ST n vL G) (hlay : WLay VO VS EO ES ST n N)
    (hlen : G.length ≤ N) (htot : vTotal G ≤ 2 * N) :
    WMem (Function.update (Function.update mem (VO + G.length) (vTotal G)) (EO + G.length)
      (eStart G G.length)) VO VS EO ST n vL (G ++ [([], [])]) := by
  obtain ⟨hVO, hEO, hVS, hST⟩ := h
  obtain ⟨l1, l2, l3, l4⟩ := hlay
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, fun y hy => ?_⟩
  · simp only [List.length_append, List.length_singleton] at hi
    rw [Function.update_of_ne (by omega), vStart_append_nil G (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Function.update_of_ne (by omega)]; exact hVO i hi
    · rw [Function.update_self]; rfl
  · simp only [List.length_append, List.length_singleton] at hi
    rw [eStart_append_nil G (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hEO i hi
    · rw [Function.update_self]
  · rw [flatV_append_nil]
    intro j hj
    have hj' : j < vTotal G := by rw [vTotal_eq]; simpa using hj
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hVS j hj
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    obtain ⟨hle, -⟩ := hST y hy
    refine ⟨by simp; omega, fun _ => ⟨fun h => by simp at h; omega, fun h => by simp at h⟩⟩

/-- Adding an element to the last group does not change the memory. -/
lemma WMem.addElem {mem : ℕ → ℕ} {VO VS EO ST n : ℕ} {vL : ℕ → ℕ}
    {G : List (List ℕ × List ℕ)} (h : WMem mem VO VS EO ST n vL G) (hG : G ≠ []) (x : ℕ) :
    WMem mem VO VS EO ST n vL (pushLast (eAdd x) G) := by
  obtain ⟨hVO, hEO, hVS, hST⟩ := h
  have hl := pushLast_length (eAdd x) hG
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, fun y hy => ?_⟩
  · rw [hl] at hi
    rw [hVO i hi]; simp only [vStart, take_pushLast _ hG hi]
  · rw [hl] at hi
    rw [hEO i hi]; simp only [eStart, take_pushLast _ hG hi]
  · rw [flatV_pushLast_eAdd x hG]; exact hVS
  · rw [hl]
    refine ⟨(hST y hy).1, fun hG' => ?_⟩
    rw [pushLast_getLast _ hG]
    exact (hST y hy).2 hG

/-- Adding a vertex with `wAddVProc` keeps `WMem`, and the new count is the new total. -/
lemma WMem.addVert {mem : ℕ → ℕ} {VO VS EO ES ST n N vListPtr : ℕ} {vL : ℕ → ℕ}
    {G : List (List ℕ × List ℕ)} (h : WMem mem VO VS EO ST n vL G) (hG : G ≠ [])
    (hlay : WLay VO VS EO ES ST n N) (hlen : G.length ≤ N) {y : ℕ} (hy : y < n) (hvL : mem (vListPtr + y) = vL y)
    (hroom : y ∉ (G.getLast hG).2 → vTotal G < 2 * N) :
    WMem (wAddVMem mem ST vListPtr VS y G.length (vTotal G)) VO VS EO ST n vL
        (pushLast (vAdd y) G) ∧
      (if mem (ST + y) = G.length then vTotal G else vTotal G + 1) =
        vTotal (pushLast (vAdd y) G) := by
  obtain ⟨hVO, hEO, hVS, hST⟩ := h
  obtain ⟨l1, l2, l3, l4⟩ := hlay
  have hl := pushLast_length (vAdd y) hG
  have hiff := (hST y hy).2 hG
  have hlast := pushLast_getLast (vAdd y) hG
  by_cases hin : y ∈ (G.getLast hG).2
  · have hs : mem (ST + y) = G.length := hiff.mpr hin
    have hflat : flatV (pushLast (vAdd y) G) = flatV G := by
      rw [flatV_pushLast_vAdd y hG, if_pos hin]
    simp only [wAddVMem, hs, if_true]
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_, fun z hz => ?_⟩, ?_⟩
    · rw [hl] at hi
      rw [hVO i hi]; simp only [vStart, take_pushLast _ hG hi]
    · rw [hl] at hi
      rw [hEO i hi]; simp only [eStart, take_pushLast _ hG hi]
    · rw [hflat]; exact hVS
    · rw [hl]
      refine ⟨(hST z hz).1, fun hG' => ?_⟩
      rw [hlast, (hST z hz).2 hG]
      simp only [_root_.MinCostFlow.LSF.Program.vAdd, mem_addNew]
      constructor
      · exact Or.inl
      · rintro (h | rfl)
        · exact h
        · exact hin
    · rw [vTotal_eq, vTotal_eq, hflat]
  · have hs : mem (ST + y) ≠ G.length := fun he => hin (hiff.mp he)
    have hflat : flatV (pushLast (vAdd y) G) = flatV G ++ [y] := by
      rw [flatV_pushLast_vAdd y hG, if_neg hin]
    have hroom' := hroom hin
    have htot : vTotal G = (flatV G).length := vTotal_eq G
    simp only [wAddVMem, hs, if_false]
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_, fun z hz => ?_⟩, ?_⟩
    · rw [hl] at hi
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hVO i hi]
      simp only [vStart, take_pushLast _ hG hi]
    · rw [hl] at hi
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hEO i hi]
      simp only [eStart, take_pushLast _ hG hi]
    · rw [hflat]
      intro j hj
      simp only [List.map_append, List.length_append, List.length_map, List.map_singleton,
        List.length_singleton] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hVS j
          (by simpa using hj)]
        simp only [List.map_append, List.map_singleton]
        rw [List.getElem_append_left (by simpa using hj)]
      · simp only [← htot, Function.update_self, hvL]
        simp [htot]
    · rw [hl]
      have hST' := hST z hz
      by_cases hzy : z = y
      · subst hzy
        rw [Function.update_of_ne (by omega), Function.update_self]
        refine ⟨le_rfl, fun hG' => ?_⟩
        rw [hlast]
        simp [_root_.MinCostFlow.LSF.Program.vAdd, mem_addNew]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        refine ⟨hST'.1, fun hG' => ?_⟩
        rw [hlast, hST'.2 hG]
        simp [_root_.MinCostFlow.LSF.Program.vAdd, mem_addNew, hzy]
    · rw [vTotal_eq, vTotal_eq, hflat]
      simp

end

end MinCostFlow.LSF.Program
