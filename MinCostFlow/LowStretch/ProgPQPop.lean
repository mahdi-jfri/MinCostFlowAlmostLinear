module

public import MinCostFlow.LowStretch.ProgPQ

/-!
# The pop procedure of the class queues

`pqPop` removes a least entry of all the lists and writes it to two given cells
(`pqPop_spec`). When the list of that entry becomes empty, its first and last-plus-one positions go
back to `0`, so a list never needs more space than the entries pushed since it was last empty.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

theorem upd2_in {f : ℕ → ℕ} {R D S k1 k2 a : ℕ} (hR : R + 2 ≤ D ∨ D + S ≤ R) (ha0 : D ≤ a)
    (ha : a < D + S) : Function.update (Function.update f R k1) (R + 1) k2 a = f a := by
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem pqE_succ {D J A c i : ℕ} : pqE D J A c (i + 1) = pqE D J A c i + 2 := by
  unfold pqE; ring

theorem R_ne {R D S x : ℕ} (hR : R + 2 ≤ D ∨ D + S ≤ R) (h1 : D ≤ x) (h2 : x < D + S) :
    R ≠ x ∧ R + 1 ≠ x := by
  constructor <;> omega

theorem pqT_bounds {D J A c : ℕ} (hc : c < J) :
    D + 3 + 2 * J ≤ pqT D J c ∧ D ≤ pqT D J c ∧ pqT D J c < D + pqSize J A := by
  unfold pqT pqSize
  refine ⟨by omega, by omega, ?_⟩
  have : 0 ≤ 2 * J * A := Nat.zero_le _
  omega

theorem pqT_ne_pqH {D J c c' : ℕ} (hc : c < J) (hc' : c' < J) : pqT D J c ≠ pqH D J c' := by
  unfold pqT pqH; omega

theorem pqT_ne {D J c c' : ℕ} (h : c ≠ c') : pqT D J c ≠ pqT D J c' := by
  unfold pqT; omega

theorem pqH_bounds {D J A c : ℕ} (hc : c < J) :
    D + 3 + 2 * J ≤ pqH D J c ∧ pqH D J c < D + 3 + 3 * J ∧ pqH D J c < D + pqSize J A := by
  unfold pqH pqSize
  refine ⟨by omega, by omega, ?_⟩
  have : 0 ≤ 2 * J * A := Nat.zero_le _
  omega

/-- `pqPop [D, J, A, INF, R]`: if some list is not empty, remove a least entry, write its key at
`R` and its vertex at `R + 1`, and return `1`; otherwise return `0`. If the list of the entry becomes empty, its two
positions go back to `0`. -/
def pqPop (bTT : ℕ) : Stmt :=
  .seq (.assign 5 (.load (.bin .add (.reg 0) (.const 4))))
  (.cond (.bin .lt (.bin .div (.reg 5) (.reg 1)) (.reg 3))
    (.seq (.assign 6 (.bin .mod (.reg 5) (.reg 1)))
    (.seq (.assign 7 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 3))
      (.bin .add (.reg 1) (.reg 1))) (.reg 6)))
    (.seq (.assign 8 (.load (.reg 7)))
    (.seq (.assign 9 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 0) (.const 3))
      (.bin .add (.reg 1) (.reg 1))) (.bin .add (.reg 1) (.reg 1)))
      (.bin .mul (.const 2) (.bin .add (.bin .mul (.reg 6) (.reg 2)) (.reg 8)))))
    (.seq (.assign 11 (.load (.reg 9)))
    (.seq (.assign 12 (.load (.bin .add (.reg 9) (.const 1))))
    (.seq (.assign 13 (.load (.bin .add (.reg 9) (.const 2))))
    (.seq (.assign 14 (.load (.bin .add (.reg 7) (.reg 1))))
    (.seq (.store (.reg 4) (.reg 11))
    (.seq (.store (.bin .add (.reg 4) (.const 1)) (.reg 12))
    (.seq (.store (.reg 7) (.bin .add (.reg 8) (.const 1)))
    (.seq (.cond (.bin .lt (.bin .add (.reg 8) (.const 1)) (.reg 14))
        (.call 10 bTT [.bin .add (.reg 0) (.const 3), .reg 1, .reg 6,
          .bin .add (.bin .mul (.reg 13) (.reg 1)) (.reg 6)])
        (.seq (.store (.reg 7) (.const 0))
        (.seq (.store (.bin .add (.reg 7) (.reg 1)) (.const 0))
        (.call 10 bTT [.bin .add (.reg 0) (.const 3), .reg 1, .reg 6,
          .bin .add (.bin .mul (.reg 3) (.reg 1)) (.reg 6)]))))
    (.ret (.const 1))))))))))))))
    (.ret (.const 0)))

theorem pqPop_noRand (bTT : ℕ) : (pqPop bTT).NoRand := by simp [pqPop, Stmt.NoRand]

/-- The contract of `pqPop`. -/
def pqPopC (w : ℕ) : Contract where
  pre args mem := ∃ D J A INF qs R, args = [D, J, A, INF, R] ∧
    PQRep mem D J A INF qs ∧ PQFits w D J A INF ∧ (R + 2 ≤ D ∨ D + pqSize J A ≤ R) ∧
    R + 1 < 2 ^ w
  post args mem v mem' := ∀ D J A INF qs R, args = [D, J, A, INF, R] →
    PQRep mem D J A INF qs →
    (v = 0 ∧ (∀ c, qs c = []) ∧ mem' = mem) ∨
    (v = 1 ∧ ∃ c < J, c = mem (D + 4) % J ∧ ∃ rest, qs c = (mem' R, mem' (R + 1)) :: rest ∧
      (∀ e ∈ pqAll J qs, mem' R ≤ e.1) ∧ PQRep mem' D J A INF (Function.update qs c rest) ∧
      (∀ c' < J, mem' (pqT D J c') ≤ mem (pqT D J c')) ∧ (rest = [] → mem' (pqT D J c) = 0) ∧
      ∀ a, (a < D + 3 ∨ D + pqSize J A ≤ a) → a ≠ R → a ≠ R + 1 → mem' a = mem a)
  cost args _ := 50 * (Nat.log 2 (args.getD 1 0) + 2) + 250

theorem pqPop_spec {w : ℕ} {p : Program} {b bTT : ℕ} (hp : p.HasAt b [pqPop bTT])
    (hTT : MeetsContract w p bTT (ttUpdateC w)) : MeetsContract w p b (pqPopC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨D, J, A, INF, qs, R, rfl, hrep, ⟨hfit1, hfit2, hw2⟩, hR, hR2⟩ := hpre
  have hproc : p.procs[b]? = some (pqPop bTT) := hp 0 (by simp)
  have hJ1 := hrep.J_pos
  have hRs : R + 2 ≤ D ∨ D + pqSize J A ≤ R := hR
  have hRtt : (R ≤ D + 3 ∨ D + 3 + 2 * J ≤ R) ∧ (R + 1 ≤ D + 3 ∨ D + 3 + 2 * J ≤ R + 1) := by
    unfold pqSize at hR; constructor <;> omega
  unfold pqSize at hfit1 hR
  have hfit1' : D + 3 + 4 * J + 2 * (J * A) < 2 ^ w := by
    have : 2 * J * A = 2 * (J * A) := by ring
    omega
  clear hR
  have hfit2' : INF * J + J < 2 ^ w := hfit2
  clear hfit1
  have hD : D < 2 ^ w := by omega
  have hroot := hrep.root_spec
  have htrip : Triple w p (fun st => st = startState [D, J, A, INF, R] mem pos) (pqPop bTT)
      (fun o st' => (o.value = 0 ∧ (∀ c, qs c = []) ∧ st'.mem = mem) ∨
        (o.value = 1 ∧ ∃ c < J, c = mem (D + 4) % J ∧ ∃ rest, qs c = (st'.mem R, st'.mem (R + 1)) :: rest ∧
          (∀ e ∈ pqAll J qs, st'.mem R ≤ e.1) ∧
          PQRep st'.mem D J A INF (Function.update qs c rest) ∧
          (∀ c' < J, st'.mem (pqT D J c') ≤ mem (pqT D J c')) ∧ (rest = [] → st'.mem (pqT D J c) = 0) ∧
          ∀ a, (a < D + 3 ∨ D + pqSize J A ≤ a) → a ≠ R → a ≠ R + 1 → st'.mem a = mem a))
      (fun _ => 50 * (Nat.log 2 J + 2) + 250) := by
    wram_enter
    · subst hpre
      dsimp only [pqPop]
      have e4 : D + 3 + 1 = D + 4 := rfl
      rw [e4] at hroot
      -- the root is a leaf, so it is a word
      have hrw : mem (D + 4) < 2 ^ w := by
        obtain ⟨c0, hc0, h0⟩ := hrep.tt.root_mem hJ1
        rw [← e4, h0, hrep.leaf c0 hc0]
        cases hq0 : qs c0 with
        | nil => simp only [leafv]; omega
        | cons f l =>
          simp only [leafv]
          have := hrep.lt c0 f (by rw [hq0]; exact List.mem_cons_self)
          have : f.1 * J ≤ INF * J := Nat.mul_le_mul_right _ (by omega)
          omega
      by_cases hne : mem (D + 4) / J < INF
      · obtain ⟨e, rest, hq, hek, hc0, hmin⟩ := hroot.1 hne
        have hhd := hrep.head_eq hc0 hq
        have hbd := hrep.bounds (mem (D + 4) % J) hc0
        have hcA : (mem (D + 4) % J) * A + A ≤ J * A := by nlinarith
        have hH : D + 3 + (J + J) + (mem (D + 4) % J) = pqH D J (mem (D + 4) % J) := by unfold pqH; ring
        have hT : D + 3 + (J + J) + (mem (D + 4) % J) + J = pqT D J (mem (D + 4) % J) := by unfold pqT; ring
        have hE : D + 3 + (J + J) + (J + J) + 2 * ((mem (D + 4) % J) * A + mem (pqH D J (mem (D + 4) % J))) =
            pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) := by unfold pqE; ring
        have hHv : mem (D + 3 + (J + J) + mem (D + 4) % J) = mem (pqH D J (mem (D + 4) % J)) := by rw [hH]
        have hTv : mem (D + 3 + (J + J) + mem (D + 4) % J + J) = mem (pqT D J (mem (D + 4) % J)) := by rw [hT]
        have hEv : D + 3 + (J + J) + (J + J) + 2 * (mem (D + 4) % J * A +
            mem (D + 3 + (J + J) + mem (D + 4) % J)) = pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) := by
          rw [hHv]; exact hE
        have hcA' : mem (D + 4) % J * A + A ≤ J * A := hcA
        have hpb := pqH_bounds (A := A) (D := D) hc0
        have hR1 : R ≠ pqH D J (mem (D + 4) % J) ∧ R + 1 ≠ pqH D J (mem (D + 4) % J) :=
          R_ne hRs (by omega) hpb.2.2
        -- after the three stores
        have hM1 : ∀ a, D ≤ a → a < D + pqSize J A → Function.update (Function.update (Function.update mem R
            (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J)))))) (R + 1)
            (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1))) (pqH D J (mem (D + 4) % J)) (mem (pqH D J (mem (D + 4) % J)) + 1) a =
            Function.update mem (pqH D J (mem (D + 4) % J)) (mem (pqH D J (mem (D + 4) % J)) + 1) a := by
          intro a ha0 ha
          by_cases hah : a = pqH D J (mem (D + 4) % J)
          · subst hah; simp
          · rw [Function.update_of_ne hah, Function.update_of_ne hah, upd2_in hRs ha0 ha]
        have hTT1 : ∀ a, D + 3 + 1 ≤ a → a < D + 3 + 2 * J →
            Function.update (Function.update (Function.update mem R
            (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J)))))) (R + 1)
            (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1))) (pqH D J (mem (D + 4) % J)) (mem (pqH D J (mem (D + 4) % J)) + 1) a =
            mem a := by
          intro a h1 h2
          rw [hM1 a (by omega) (by omega), Function.update_of_ne (by omega)]
        have hout : ∀ a, (a < D + 3 ∨ D + pqSize J A ≤ a) → a ≠ R → a ≠ R + 1 →
            Function.update (Function.update (Function.update mem R
            (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J)))))) (R + 1)
            (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1))) (pqH D J (mem (D + 4) % J)) (mem (pqH D J (mem (D + 4) % J)) + 1) a =
            mem a := by
          intro a ha h1 h2
          rw [Function.update_of_ne (by omega), Function.update_of_ne h2,
            Function.update_of_ne h1]
        have he := hhd.2.1
        -- the final memory, from the repair of the tree
        have hfin : rest ≠ [] → ∀ mem' : ℕ → ℕ,
            TTOk mem' (D + 3) J →
            mem' (D + 3 + J + (mem (D + 4) % J)) = leafv INF J (mem (D + 4) % J) rest →
            (∀ j' < J, j' ≠ (mem (D + 4) % J) → mem' (D + 3 + J + j') = Function.update (Function.update
              (Function.update mem R (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J)))))) (R + 1)
              (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1))) (pqH D J (mem (D + 4) % J)) (mem (pqH D J (mem (D + 4) % J)) + 1)
                (D + 3 + J + j')) →
            (∀ a, a ≤ D + 3 ∨ D + 3 + 2 * J ≤ a → mem' a = Function.update (Function.update
              (Function.update mem R (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J)))))) (R + 1)
              (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1))) (pqH D J (mem (D + 4) % J)) (mem (pqH D J (mem (D + 4) % J)) + 1)
                a) →
            ∃ c < J, c = mem (D + 4) % J ∧ ∃ rest', qs c = (mem' R, mem' (R + 1)) :: rest' ∧
              (∀ e ∈ pqAll J qs, mem' R ≤ e.1) ∧
              PQRep mem' D J A INF (Function.update qs c rest') ∧
              (∀ c' < J, mem' (pqT D J c') ≤ mem (pqT D J c')) ∧ (rest' = [] → mem' (pqT D J c) = 0) ∧
              ∀ a, (a < D + 3 ∨ D + pqSize J A ≤ a) → a ≠ R → a ≠ R + 1 → mem' a = mem a := by
          intro hne mem' htt' hleaf' hother' hfr'
          have hmR : mem' R = mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J)))) := by
            rw [hfr' R hRtt.1, Function.update_of_ne hR1.1,
              Function.update_of_ne (by omega), Function.update_self]
          have hmR1 : mem' (R + 1) = mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1) := by
            rw [hfr' (R + 1) hRtt.2, Function.update_of_ne hR1.2,
              Function.update_self]
          refine ⟨(mem (D + 4) % J), hc0, rfl, rest, by rw [hq, hmR, hmR1, ← he], fun e' he' => ?_, ?_,
            fun c' hc' => ?_, fun h => absurd h hne, fun a ha h1 h2 => ?_⟩
          · have := congrArg Prod.fst he
            simp only at this
            rw [hmR, ← this]
            exact hmin e' he'
          · refine hrep.pop hc0 hq (fun a ha1 ha2 ha3 => ?_) htt' fun c' hc' => ?_
            · rw [hfr' a (by omega), hM1 a ha1 ha2]
            · by_cases hcc : c' = (mem (D + 4) % J)
              · subst hcc; rw [if_pos rfl]; exact hleaf'
              · rw [if_neg hcc, hother' c' hc' hcc, hTT1 _ (by omega) (by omega)]
          · have hb := pqT_bounds (A := A) (D := D) hc'
            rw [hfr' _ (by omega), Function.update_of_ne (pqT_ne_pqH hc' hc0),
              upd2_in hRs (by omega) hb.2.2]
          · rw [hfr' a (by unfold pqSize at ha; omega), hout a ha h1 h2]
        by_cases hnx : rest = []
        · have hlast : mem (pqH D J (mem (D + 4) % J)) + 1 = mem (pqT D J (mem (D + 4) % J)) := hhd.2.2.1.mp hnx
          subst hnx
          have hHT : pqH D J (mem (D + 4) % J) + J = pqT D J (mem (D + 4) % J) := by
            unfold pqH pqT; ring
          have hTb : D + 3 + 2 * J ≤ pqT D J (mem (D + 4) % J) ∧
              pqT D J (mem (D + 4) % J) < D + pqSize J A := by
            rw [← hHT]; have := hpb.2.2; have := hpb.1
            constructor
            · omega
            · unfold pqH pqSize at *; omega
          have hR2' : R ≠ pqT D J (mem (D + 4) % J) ∧ R + 1 ≠ pqT D J (mem (D + 4) % J) :=
            R_ne hRs (by omega) hTb.2
          have hM0 : ∀ a, D ≤ a → a < D + pqSize J A → Function.update (Function.update (Function.update (Function.update (Function.update mem R
              (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J)))))) (R + 1)
              (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1))) (pqH D J (mem (D + 4) % J)) (mem (pqH D J (mem (D + 4) % J)) + 1)) (pqH D J (mem (D + 4) % J)) 0) (pqT D J (mem (D + 4) % J)) 0 a =
              Function.update (Function.update mem (pqH D J (mem (D + 4) % J)) 0) (pqT D J (mem (D + 4) % J)) 0 a := by
            intro a ha0 ha
            by_cases hat : a = pqT D J (mem (D + 4) % J)
            · subst hat; simp
            · rw [Function.update_of_ne hat, Function.update_of_ne hat]
              by_cases hah : a = pqH D J (mem (D + 4) % J)
              · subst hah; simp
              · rw [Function.update_of_ne hah, Function.update_of_ne hah, Function.update_of_ne hah,
                  upd2_in hRs ha0 ha]
          have hTT0 : ∀ a, D + 3 + 1 ≤ a → a < D + 3 + 2 * J → Function.update (Function.update (Function.update (Function.update (Function.update mem R
              (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J)))))) (R + 1)
              (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1))) (pqH D J (mem (D + 4) % J)) (mem (pqH D J (mem (D + 4) % J)) + 1)) (pqH D J (mem (D + 4) % J)) 0) (pqT D J (mem (D + 4) % J)) 0 a = mem a := by
            intro a h1 h2
            rw [hM0 a (by omega) (by unfold pqSize; omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
          have hout0 : ∀ a, (a < D + 3 ∨ D + pqSize J A ≤ a) → a ≠ R → a ≠ R + 1 → Function.update (Function.update (Function.update (Function.update (Function.update mem R
              (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J)))))) (R + 1)
              (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1))) (pqH D J (mem (D + 4) % J)) (mem (pqH D J (mem (D + 4) % J)) + 1)) (pqH D J (mem (D + 4) % J)) 0) (pqT D J (mem (D + 4) % J)) 0 a = mem a := by
            intro a ha h1 h2
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hout a ha h1 h2]
          have hfin0 : ∀ mem' : ℕ → ℕ,
              TTOk mem' (D + 3) J →
              mem' (D + 3 + J + (mem (D + 4) % J)) = leafv INF J (mem (D + 4) % J) [] →
              (∀ j' < J, j' ≠ (mem (D + 4) % J) → mem' (D + 3 + J + j') = Function.update (Function.update (Function.update (Function.update (Function.update mem R
              (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J)))))) (R + 1)
              (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1))) (pqH D J (mem (D + 4) % J)) (mem (pqH D J (mem (D + 4) % J)) + 1)) (pqH D J (mem (D + 4) % J)) 0) (pqT D J (mem (D + 4) % J)) 0 (D + 3 + J + j')) →
              (∀ a, a ≤ D + 3 ∨ D + 3 + 2 * J ≤ a → mem' a = Function.update (Function.update (Function.update (Function.update (Function.update mem R
              (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J)))))) (R + 1)
              (mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1))) (pqH D J (mem (D + 4) % J)) (mem (pqH D J (mem (D + 4) % J)) + 1)) (pqH D J (mem (D + 4) % J)) 0) (pqT D J (mem (D + 4) % J)) 0 a) →
              ∃ c < J, c = mem (D + 4) % J ∧ ∃ rest', qs c = (mem' R, mem' (R + 1)) :: rest' ∧
                (∀ e ∈ pqAll J qs, mem' R ≤ e.1) ∧
                PQRep mem' D J A INF (Function.update qs c rest') ∧
                (∀ c' < J, mem' (pqT D J c') ≤ mem (pqT D J c')) ∧
                (rest' = [] → mem' (pqT D J c) = 0) ∧
                ∀ a, (a < D + 3 ∨ D + pqSize J A ≤ a) → a ≠ R → a ≠ R + 1 → mem' a = mem a := by
            intro mem' htt' hleaf' hother' hfr'
            have hmR : mem' R = mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J)))) := by
              rw [hfr' R hRtt.1, Function.update_of_ne hR2'.1, Function.update_of_ne hR1.1,
                Function.update_of_ne hR1.1, Function.update_of_ne (by omega), Function.update_self]
            have hmR1 : mem' (R + 1) = mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1) := by
              rw [hfr' (R + 1) hRtt.2, Function.update_of_ne hR2'.2, Function.update_of_ne hR1.2,
                Function.update_of_ne hR1.2, Function.update_self]
            refine ⟨(mem (D + 4) % J), hc0, rfl, [], by rw [hq, hmR, hmR1, ← he], fun e' he' => ?_, ?_,
              fun c' hc' => ?_, fun _ => ?_, fun a ha h1 h2 => ?_⟩
            · have := congrArg Prod.fst he
              simp only at this
              rw [hmR, ← this]
              exact hmin e' he'
            · refine hrep.popLast hc0 hq (fun a ha1 ha2 ha3 => ?_) htt' fun c' hc' => ?_
              · rw [hfr' a (by omega), hM0 a ha1 ha2]
              · by_cases hcc : c' = (mem (D + 4) % J)
                · subst hcc; rw [if_pos rfl]; exact hleaf'
                · rw [if_neg hcc, hother' c' hc' hcc, hTT0 _ (by omega) (by omega)]
            · have hb := pqT_bounds (A := A) (D := D) hc'
              rw [hfr' _ (by omega)]
              by_cases hcc : c' = mem (D + 4) % J
              · subst hcc; rw [Function.update_self]; omega
              · rw [Function.update_of_ne (pqT_ne hcc), Function.update_of_ne (pqT_ne_pqH hc' hc0),
                  Function.update_of_ne (pqT_ne_pqH hc' hc0), upd2_in hRs (by omega) hb.2.2]
            · rw [hfr' _ (Or.inr hTb.1), Function.update_self]
            · rw [hfr' a (by unfold pqSize at ha; omega), hout0 a ha h1 h2]
          wram_run
          · refine ⟨D + 3, J, mem (D + 4) % J, INF * J + mem (D + 4) % J, rfl, hc0, by omega, hw2, ?_⟩
            dsimp only [startState]
            rw [hEv, hHv, hH, hHT]
            exact hrep.tt.congr fun a h1 h2 => hTT0 a (by omega) (by omega)
          · intro v mem' pos' hpost
            dsimp only [startState] at hpost hcond
            rw [hEv, hHv, hH, hHT] at hpost
            obtain ⟨htt', hleaf', hother', hfr'⟩ := hpost
            simp only [List.getD_cons_zero, List.getD_cons_succ] at htt' hleaf' hother' hfr'
            wram_run
            · right
              exact ⟨rfl, hfin0 mem' htt' hleaf' hother' hfr'⟩
            · simp only [ttUpdateC, List.getD_cons_succ, List.getD_cons_zero] at *
              wram_cost
          all_goals done
        · obtain ⟨f, rest', rfl⟩ := List.exists_cons_of_ne_nil hnx
          have hf := hhd.2.2.2 f rest' rfl
          have hlt' : mem (pqH D J (mem (D + 4) % J)) + 1 < mem (pqT D J (mem (D + 4) % J)) := by
            have hi1 := hhd.2.2.1
            have hi2 := hhd.1
            by_contra hc
            exact List.cons_ne_nil f rest' (hi1.mpr (by omega))
          have hfk : f.1 < INF := hrep.lt (mem (D + 4) % J) f (by rw [hq]; simp)
          have hfJ : f.1 * J ≤ INF * J := Nat.mul_le_mul_right _ hfk.le
          have hf' : mem (D + 3 + (J + J) + (J + J) + 2 * (mem (D + 4) % J * A +
              mem (D + 3 + (J + J) + mem (D + 4) % J)) + 2) = f.1 := by
            rw [hEv, hf, pqE_succ]
          have hfJ' : mem (D + 3 + (J + J) + (J + J) + 2 * (mem (D + 4) % J * A +
              mem (D + 3 + (J + J) + mem (D + 4) % J)) + 2) * J ≤ INF * J := by rw [hf']; exact hfJ
          have hlt'' : mem (D + 3 + (J + J) + mem (D + 4) % J) + 1 <
              mem (D + 3 + (J + J) + mem (D + 4) % J + J) := by rw [hHv, hTv]; exact hlt'
          wram_run
          · refine ⟨D + 3, J, mem (D + 4) % J, _, rfl, hc0, by omega, hw2, ?_⟩
            dsimp only [startState]
            rw [hEv, hHv, hH]
            exact hrep.tt.congr fun a h1 h2 => hTT1 a (by omega) (by omega)
          · intro v mem' pos' hpost
            dsimp only [startState] at hpost hcond
            rw [hEv, hHv, hH] at hpost
            obtain ⟨htt', hleaf', hother', hfr'⟩ := hpost
            simp only [List.getD_cons_zero, List.getD_cons_succ] at htt' hleaf' hother' hfr'
            wram_run
            · right
              exact ⟨rfl, hfin hnx mem' htt' hleaf' hother' hfr'⟩
            · simp only [ttUpdateC, List.getD_cons_succ, List.getD_cons_zero] at *
              wram_cost
          all_goals done
      · have hall := hroot.2 (by omega)
        wram_run
        · left
          exact ⟨rfl, hall, rfl⟩
        · wram_cost
  obtain ⟨o, st', c', hrun, hpost, hcost⟩ := htrip (startState [D, J, A, INF, R] mem pos) ω rfl
  refine ⟨pqPop bTT, hproc, o, st', c', hrun, fun D' J' A' INF' qs' R' he hrep' => ?_,
    by simpa [pqPopC] using hcost⟩
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
  obtain ⟨-, -, -, rfl⟩ := hrep.uniq hrep'
  exact hpost

end MinCostFlow.LowStretch
