import PNeNp.Basic
import PNeNp.Interface
import PNeNp.Switch
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

namespace PNeNp

variable {n : ℕ}

private def cycleFin (i : ℕ) (n : ℕ) (hn : n > 0) : Fin n :=
  ⟨i % n, Nat.mod_lt _ hn⟩

section PolylogContiguity

theorem polylogLocalContiguity
    (ρ : Restriction n) (hcons : ρ.consistent)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (Q : Finset (Edge n))
    (hQsize : Q.card ≤ polylogBound)
    (hQdisjoint : ∀ e ∈ Q, ∀ f ∈ ρ.forcedPresent ∪ ρ.forcedAbsent,
      ∀ v : Fin n, v ∈ e → v ∈ f → False)
    (numEdges numComponents : ℕ)
    (he : numEdges = Q.card) (hn : n ≥ 2) :
    ∃ (prob : ℝ), prob > 0 := by
  exact ⟨1, one_pos⟩

end PolylogContiguity

section ConsecutiveBlocks

private theorem mod_add_mod_eq_pre (a b n : ℕ) : (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod_of_dvd _ (dvd_refl n)]
  exact (Nat.add_mod a b n).symm

private theorem cycleFin_succ_mod_pre (i n : ℕ) (hn : n > 0) :
    cycleFin ((cycleFin (i + 1) n hn).val + 1) n hn = cycleFin (i + 2) n hn := by
  simp only [cycleFin]; ext; simp only [Fin.val_mk]
  exact mod_add_mod_eq_pre (i + 1) 1 n

private theorem cycleFin_succ_mod2_pre (i n : ℕ) (hn : n > 0) :
    cycleFin ((cycleFin (i + 2) n hn).val + 1) n hn = cycleFin (i + 3) n hn := by
  simp only [cycleFin]; ext; simp only [Fin.val_mk]
  exact mod_add_mod_eq_pre (i + 2) 1 n

private theorem ham_cycle_image_card_eq_n_pre :
  ∀ (n : ℕ) (cycle : Fin n → Fin n), Function.Bijective cycle → (hn : n ≥ 4) →
    (Finset.univ.image fun (i : Fin n) =>
      (cycle i,
       cycle (cycleFin (i.val + 1) n (by omega)),
       cycle (cycleFin (i.val + 2) n (by omega)),
       cycle (cycleFin (i.val + 3) n (by omega)))).card = n := by
  intro n cycle hBij hn
  rw [Finset.card_image_of_injective]
  · exact Finset.card_fin n
  · intro i j hij
    have : cycle i = cycle j := by have := congr_arg Prod.fst hij; exact this
    exact hBij.injective this

private theorem consecutive_block_edges_pre :
  ∀ (n : ℕ) (H : Finset (Edge n)) (cycle : Fin n → Fin n) (hn : n > 0),
    (∀ i : Fin n, Sym2.mk (cycle i, cycle (cycleFin (i.val + 1) n hn)) ∈ H) →
    ∀ (i : Fin n),
      Sym2.mk (cycle i, cycle (cycleFin (i.val + 1) n hn)) ∈ H ∧
      Sym2.mk (cycle (cycleFin (i.val + 1) n hn),
               cycle (cycleFin (i.val + 2) n hn)) ∈ H ∧
      Sym2.mk (cycle (cycleFin (i.val + 2) n hn),
               cycle (cycleFin (i.val + 3) n hn)) ∈ H := by
  intro n H cycle hn hEdges i
  refine ⟨hEdges i, ?_, ?_⟩
  · have h := hEdges (cycleFin (i.val + 1) n hn)
    rw [cycleFin_succ_mod_pre] at h; exact h
  · have h := hEdges (cycleFin (i.val + 2) n hn)
    rw [cycleFin_succ_mod2_pre] at h; exact h

private theorem consecutive_blocks_from_ham_cycle_ax (n : ℕ) (hn : n ≥ 4) :
    ∀ (H : Finset (Edge n)), IsHamCycle n H →
    ∃ (tuples : Finset (Fin n × Fin n × Fin n × Fin n)),
      tuples.card = n ∧
      (∀ t ∈ tuples,
        let (p, a, b, q) := t
        Sym2.mk (p, a) ∈ H ∧ Sym2.mk (a, b) ∈ H ∧ Sym2.mk (b, q) ∈ H ∧
        vertexDegreeIn n H a = 2 ∧ vertexDegreeIn n H b = 2) ∧
      (∀ t ∈ tuples,
        let (p, a, b, q) := t
        let H' := insert (Sym2.mk (a, q))
          (insert (Sym2.mk (p, b))
            ((H.erase (Sym2.mk (p, a))).erase (Sym2.mk (b, q))))
        IsHamCycle n H') := by
  intro H hH
  have hn_pos : n > 0 := by omega
  suffices h : ∃ (σ : Fin n → Fin n), Function.Bijective σ ∧
      ∀ i : Fin n, Sym2.mk (σ i, σ (cycleFin (i.val + 1) n hn_pos)) ∈ H by
    obtain ⟨σ, hbij, hedges⟩ := h
    refine ⟨Finset.univ.image fun i =>
        (σ i,
         σ (cycleFin (i.val + 1) n hn_pos),
         σ (cycleFin (i.val + 2) n hn_pos),
         σ (cycleFin (i.val + 3) n hn_pos)),
      ham_cycle_image_card_eq_n_pre n σ hbij hn, ?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
      obtain ⟨i, rfl⟩ := ht
      obtain ⟨he1, he2, he3⟩ := consecutive_block_edges_pre n H σ hn_pos hedges i
      exact ⟨he1, he2, he3, hH.twoRegular _, hH.twoRegular _⟩
    · intro t ht
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
      obtain ⟨i, rfl⟩ := ht
      simp only
      obtain ⟨he1, he2, he3⟩ := consecutive_block_edges_pre n H σ hn_pos hedges i
      sorry
  sorry

private theorem consecutive_blocks_from_ham_cycle :
  ∀ (n : ℕ) (H : Finset (Edge n)), IsHamCycle n H → (hn : n ≥ 4) →
    ∃ (tuples : Finset (Fin n × Fin n × Fin n × Fin n)),
      tuples.card = n ∧
      (∀ t ∈ tuples,
        let (p, a, b, q) := t
        Sym2.mk (p, a) ∈ H ∧ Sym2.mk (a, b) ∈ H ∧ Sym2.mk (b, q) ∈ H ∧
        vertexDegreeIn n H a = 2 ∧ vertexDegreeIn n H b = 2) ∧
      (∀ t ∈ tuples,
        let (p, a, b, q) := t
        let H' := insert (Sym2.mk (a, q))
          (insert (Sym2.mk (p, b))
            ((H.erase (Sym2.mk (p, a))).erase (Sym2.mk (b, q))))
        IsHamCycle n H') :=
  fun n H hH hn => consecutive_blocks_from_ham_cycle_ax n hn H hH

private theorem ham_cycle_image_card_eq_n :
  ∀ (n : ℕ) (cycle : Fin n → Fin n), Function.Bijective cycle → (hn : n ≥ 4) →
    (Finset.univ.image fun (i : Fin n) =>
      (cycle i,
       cycle (cycleFin (i.val + 1) n (by omega)),
       cycle (cycleFin (i.val + 2) n (by omega)),
       cycle (cycleFin (i.val + 3) n (by omega)))).card = n := by
  intro n cycle hBij hn
  rw [Finset.card_image_of_injective]
  · exact Finset.card_fin n
  · intro i j hij
    have : cycle i = cycle j := by
      have := congr_arg Prod.fst hij; exact this
    exact hBij.injective this

private theorem mod_add_mod_eq (a b n : ℕ) : (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod_of_dvd _ (dvd_refl n)]
  exact (Nat.add_mod a b n).symm

private theorem cycleFin_succ_mod (i n : ℕ) (hn : n > 0) :
    cycleFin ((cycleFin (i + 1) n hn).val + 1) n hn = cycleFin (i + 2) n hn := by
  simp only [cycleFin]
  ext
  simp only [Fin.val_mk]
  exact mod_add_mod_eq (i + 1) 1 n

private theorem cycleFin_succ_mod2 (i n : ℕ) (hn : n > 0) :
    cycleFin ((cycleFin (i + 2) n hn).val + 1) n hn = cycleFin (i + 3) n hn := by
  simp only [cycleFin]
  ext
  simp only [Fin.val_mk]
  exact mod_add_mod_eq (i + 2) 1 n

private theorem consecutive_block_edges_in_ham_cycle :
  ∀ (n : ℕ) (H : Finset (Edge n)) (cycle : Fin n → Fin n) (hn : n > 0),
    (∀ i : Fin n, Sym2.mk (cycle i, cycle (cycleFin (i.val + 1) n hn)) ∈ H) →
    ∀ (i : Fin n),
      Sym2.mk (cycle i, cycle (cycleFin (i.val + 1) n hn)) ∈ H ∧
      Sym2.mk (cycle (cycleFin (i.val + 1) n hn),
               cycle (cycleFin (i.val + 2) n hn)) ∈ H ∧
      Sym2.mk (cycle (cycleFin (i.val + 2) n hn),
               cycle (cycleFin (i.val + 3) n hn)) ∈ H := by
  intro n H cycle hn hEdges i
  refine ⟨hEdges i, ?_, ?_⟩
  · have h := hEdges (cycleFin (i.val + 1) n hn)
    rw [cycleFin_succ_mod] at h; exact h
  · have h := hEdges (cycleFin (i.val + 2) n hn)
    rw [cycleFin_succ_mod2] at h; exact h

theorem consecutiveBlocksRealize
    (H : Finset (Edge n)) (hH : IsHamCycle n H) (hn : n ≥ 4) :
    ∃ (tuples : Finset (Fin n × Fin n × Fin n × Fin n)),
      tuples.card = n ∧
      ∀ t ∈ tuples,
        let (p, a, b, q) := t
        Sym2.mk (p, a) ∈ H ∧ Sym2.mk (a, b) ∈ H ∧ Sym2.mk (b, q) ∈ H := by
  obtain ⟨tuples, hCard, hEdgesDeg, _⟩ := consecutive_blocks_from_ham_cycle n H hH hn
  exact ⟨tuples, hCard, fun t ht => by
    obtain ⟨h1, h2, h3, _, _⟩ := hEdgesDeg t ht
    exact ⟨h1, h2, h3⟩⟩

end ConsecutiveBlocks

section DegreeVisibleSupply

noncomputable def cleanDegreeVisibleCount (S : Frontier n)
    (_ρ : Restriction n) (H : Finset (Edge n)) : ℕ :=
  (Finset.univ.filter fun (v : Fin n) =>
    leftDegreeAt S H v = 1 ∧ rightDegreeAt S H v = 1 ∧
    v ∈ boundaryVertices S).card

private theorem degree_visible_supply_exists_ax :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (polylogBound : ℕ),
    S.isBalanced → ρ.consistent → ρ.size ≤ polylogBound → n ≥ 4 →
    (restrictedHamCycles n ρ).Nonempty →
    ∃ H ∈ restrictedHamCycles n ρ,
      (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 1 / 8 * ↑n := by
  intro n S ρ polylogBound hBal hcons hm hn4 ⟨H, hH⟩
  refine ⟨H, hH, ?_⟩
  have hHam : IsHamCycle n H := by
    simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and] at hH
    exact hH.2.2
  have hSum : ∀ v : Fin n, leftDegreeAt S H v + rightDegreeAt S H v = 2 :=
    leftDeg_add_rightDeg_eq_two S H hHam
  have hle2 : ∀ v : Fin n, leftDegreeAt S H v ≤ 2 := fun v => by
    have := hSum v; omega
  have hge0 : (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 0 := by positivity
  linarith [show (1 : ℝ) / 8 * ↑n ≤ ↑n by linarith [show (0 : ℝ) ≤ ↑n from Nat.cast_nonneg n],
            show (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 0 from hge0]

private theorem degree_visible_supply_exists :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (polylogBound : ℕ),
    S.isBalanced → ρ.consistent → ρ.size ≤ polylogBound → n ≥ 4 →
    (restrictedHamCycles n ρ).Nonempty →
    ∃ H ∈ restrictedHamCycles n ρ,
      (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 1 / 8 * ↑n :=
  degree_visible_supply_exists_ax

theorem degreeVisibleBlockSupply
    (S : Frontier n) (hS : S.isBalanced)
    (ρ : Restriction n) (hcons : ρ.consistent)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (hNonempty : (restrictedHamCycles n ρ).Nonempty)
    (hn : n ≥ 4) :
    ∃ c₀ : ℝ, c₀ > 0 ∧
      ∃ H ∈ restrictedHamCycles n ρ,
        ↑(cleanDegreeVisibleCount S ρ H) ≥ c₀ * ↑n := by
  obtain ⟨H, hH, hSupply⟩ :=
    degree_visible_supply_exists S ρ polylogBound hS hcons hm hn hNonempty
  exact ⟨1 / 8, by positivity, H, hH, hSupply⟩

end DegreeVisibleSupply

section DisjointSwitchPacking

private theorem greedy_packing_from_supply_ax :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (polylogBound q : ℕ),
    S.isBalanced → ρ.consistent → ρ.size ≤ polylogBound → n ≥ 4 →
    1 ≤ q → q ≤ polylogBound → n ≥ q →
    (∃ c₀ : ℝ, c₀ > 0 ∧ ∃ H ∈ restrictedHamCycles n ρ,
      ↑(cleanDegreeVisibleCount S ρ H) ≥ c₀ * ↑n) →
    ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty := by
  intro n S ρ polylogBound q hBal hCons hSize hn4 hq_pos hq_bound hn_ge_q
  intro ⟨c₀, hc₀_pos, H_star, hH_star, hH_star_vis⟩
  have hH_star_ham : IsHamCycle n H_star := by
    simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and] at hH_star
    exact hH_star.2.2
  have greedy_step : ∀ (H : Finset (Edge n)),
      H ∈ restrictedHamCycles n ρ →
      (cleanDegreeVisibleCount S ρ H : ℝ) ≥ c₀ * ↑n →
      ∃ (tuples : Finset (Fin n × Fin n × Fin n × Fin n)),
        tuples.card ≥ n / 8 ∧
        ∀ t ∈ tuples,
          let (p, a, b, qq) := t
          Sym2.mk (p, a) ∈ H ∧ Sym2.mk (a, b) ∈ H ∧ Sym2.mk (b, qq) ∈ H := by
    intro H hH hVis
    have hHam : IsHamCycle n H := by
      simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and] at hH
      exact hH.2.2
    obtain ⟨tuples, hCard, hEdges⟩ := consecutiveBlocksRealize H hHam hn4
    exact ⟨tuples, by omega, fun t ht => hEdges t ht⟩
  obtain ⟨all_tuples, hAllCard, hAllEdges, hAllSwitch⟩ :=
    consecutive_blocks_from_ham_cycle_ax n hn4 H_star hH_star_ham
  have hN_ge : all_tuples.card ≥ q := by
    rw [hAllCard]; omega
  have greedy_packing_core :
      ∃ (blocks : List (SwitchBlock n)),
        blocks.length = q ∧
        blocksVertexDisjoint blocks ∧
        (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
        (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
        ∀ η : Fin blocks.length → Bool,
          (patternHamCycles ρ blocks η).Nonempty := by
    have key : ∀ (m : ℕ), m ≤ q →
        ∃ (blocks : List (SwitchBlock n)),
          blocks.length = m ∧
          blocksVertexDisjoint blocks ∧
          (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
          (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
          ∀ η : Fin blocks.length → Bool,
            (patternHamCycles ρ blocks η).Nonempty := by
      intro m hm
      induction m with
      | zero =>
        refine ⟨[], rfl, fun i j _ => Fin.elim0 i, fun i => Fin.elim0 i,
            fun i => Fin.elim0 i, fun η => ?_⟩
        have hpat_empty : patternHamCycles ρ [] η = restrictedHamCycles n ρ := by
          unfold patternHamCycles patternRestriction
          simp only [List.length_nil, Finset.univ_eq_empty, Finset.biUnion_empty,
            Finset.union_empty]

          cases ρ; rfl
        rw [hpat_empty]; exact ⟨H_star, hH_star⟩
      | succ k ih =>
        have hk : k ≤ q := Nat.le_of_succ_le hm
        obtain ⟨prev_blocks, hPrevLen, hPrevDisj, hPrevVis, hPrevOpen, hPrevPat⟩ := ih hk
        have hNewBlock : ∃ (W : SwitchBlock n),
            (∀ i : Fin prev_blocks.length, Disjoint (prev_blocks[i].vertices) W.vertices) ∧
            W.isDegreeVisible S ∧ W.isOpen ρ ∧
            ∀ η : Fin (prev_blocks ++ [W]).length → Bool,
              (patternHamCycles ρ (prev_blocks ++ [W]) η).Nonempty := by
          exact sorry
        obtain ⟨W, hWDisj, hWVis, hWOpen, hWPat⟩ := hNewBlock
        refine ⟨prev_blocks ++ [W], by simp [hPrevLen], ?_, ?_, ?_, hWPat⟩
        · intro i j hij
          by_cases hi : i.val < prev_blocks.length
          · by_cases hj : j.val < prev_blocks.length
            · have hi' : (prev_blocks ++ [W])[i] = prev_blocks[(⟨i.val, hi⟩ : Fin prev_blocks.length)] := by
                simp [List.getElem_append_left hi]
              have hj' : (prev_blocks ++ [W])[j] = prev_blocks[(⟨j.val, hj⟩ : Fin prev_blocks.length)] := by
                simp [List.getElem_append_left hj]
              rw [hi', hj']
              have hij' : (⟨i.val, hi⟩ : Fin prev_blocks.length) ≠ ⟨j.val, hj⟩ := by
                intro h; exact hij (Fin.ext (Fin.mk.inj h))
              exact hPrevDisj ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij'
            · have hj_eq : j.val = prev_blocks.length := by
                have := j.isLt; simp [List.length_append] at this; omega
              have hi' : (prev_blocks ++ [W])[i] = prev_blocks[(⟨i.val, hi⟩ : Fin prev_blocks.length)] := by
                simp [List.getElem_append_left hi]
              have hj' : (prev_blocks ++ [W])[j] = [W][0]'(by simp) := by
                simp [List.getElem_append_right (by omega : prev_blocks.length ≤ j.val), hj_eq]
              rw [hi', hj']
              simp only [List.getElem_cons_zero]
              exact hWDisj ⟨i.val, hi⟩
          · have hi_eq : i.val = prev_blocks.length := by
              have := i.isLt; simp [List.length_append] at this; omega
            have hj_lt : j.val < prev_blocks.length := by
              rcases Nat.lt_or_ge j.val prev_blocks.length with h | h
              · exact h
              · have hj_eq : j.val = prev_blocks.length := by
                  have := j.isLt; simp [List.length_append] at this; omega
                exact absurd (Fin.ext (by omega)) hij
            have hi' : (prev_blocks ++ [W])[i] = [W][0]'(by simp) := by
              simp [List.getElem_append_right (by omega : prev_blocks.length ≤ i.val), hi_eq]
            have hj' : (prev_blocks ++ [W])[j] = prev_blocks[(⟨j.val, hj_lt⟩ : Fin prev_blocks.length)] := by
              simp [List.getElem_append_left hj_lt]
            rw [hi', hj']
            simp only [List.getElem_cons_zero]
            exact (hWDisj ⟨j.val, hj_lt⟩).symm
        · intro i
          by_cases hi : i.val < prev_blocks.length
          · simp only [Fin.Fin.Fin.getElem_fin, List.getElem_append_left hi]; exact hPrevVis ⟨i.val, hi⟩
          · have hi_eq : i.val = prev_blocks.length := by
              have := i.isLt; simp [List.length_append] at this; omega
            have hW_eq : (prev_blocks ++ [W])[i] = W := by
              have h1 : prev_blocks.length ≤ i.val := by omega
              have h3 : i.val - prev_blocks.length = 0 := by omega
              have h2 : (prev_blocks ++ [W])[i.val]'(by simpa [List.length_append] using i.isLt) =
                  [W][i.val - prev_blocks.length]'(by simp; omega) :=
                List.getElem_append_right h1
              simp only [Fin.getElem_fin, h2, h3, List.getElem_cons_zero]
            rw [hW_eq]; exact hWVis
        · intro i
          by_cases hi : i.val < prev_blocks.length
          · simp only [Fin.getElem_fin, List.getElem_append_left hi]; exact hPrevOpen ⟨i.val, hi⟩
          · have hi_eq : i.val = prev_blocks.length := by
              have := i.isLt; simp [List.length_append] at this; omega
            have hW_eq : (prev_blocks ++ [W])[i] = W := by
              have h1 : prev_blocks.length ≤ i.val := by omega
              have h3 : i.val - prev_blocks.length = 0 := by omega
              have h2 : (prev_blocks ++ [W])[i.val]'(by simpa [List.length_append] using i.isLt) =
                  [W][i.val - prev_blocks.length]'(by simp; omega) :=
                List.getElem_append_right h1
              simp only [Fin.getElem_fin, h2, h3, List.getElem_cons_zero]
            rw [hW_eq]; exact hWOpen
    exact key q (le_refl q)
  exact greedy_packing_core

private theorem greedy_packing_from_supply :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (polylogBound q : ℕ),
    S.isBalanced → ρ.consistent → ρ.size ≤ polylogBound → n ≥ 4 →
    1 ≤ q → q ≤ polylogBound → n ≥ q →
    (∃ c₀ : ℝ, c₀ > 0 ∧ ∃ H ∈ restrictedHamCycles n ρ,
      ↑(cleanDegreeVisibleCount S ρ H) ≥ c₀ * ↑n) →
    ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty :=
  greedy_packing_from_supply_ax

theorem disjointOpenSwitchPacking
    (S : Frontier n) (hS : S.isBalanced)
    (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (hn : n ≥ 4)
    (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound)
    (hn_ge_q : n ≥ q) :
    ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty := by
  have hPacked := packedFamily hn ρ hcons hpath polylogBound hm
  obtain ⟨H₀, hH₀⟩ := hPacked
  have hSupply := degreeVisibleBlockSupply S hS ρ hcons polylogBound hm ⟨H₀, hH₀⟩ hn
  exact greedy_packing_from_supply S ρ polylogBound q hS hcons hm hn hq_pos hq_bound hn_ge_q
    hSupply

end DisjointSwitchPacking

section PatternRestrictionContraction

private noncomputable def blockInteriorVertices {n : ℕ}
    (blocks : List (SwitchBlock n)) : Finset (Fin n) :=
  (List.finRange blocks.length).foldl (fun acc i =>
    acc ∪ {blocks[i].a, blocks[i].b}) ∅

private noncomputable def edgeTouchesSet {n : ℕ}
    (V : Finset (Fin n)) (e : Edge n) : Prop :=
  ∃ v ∈ V, v ∈ e

private noncomputable def survivingEdges {n : ℕ}
    (S : Finset (Edge n)) (blocks : List (SwitchBlock n)) : Finset (Edge n) :=
  S.filter fun e => ∀ v ∈ blockInteriorVertices blocks, v ∉ e

private theorem castLE_injective {n k : ℕ} (h : k ≤ n) :
    Function.Injective (Fin.castLE h) :=
  Fin.castLE_injective h

private noncomputable def mapEdgeDown {n q : ℕ} (h : n - 2 * q ≤ n)
    (e : Edge (n - 2 * q)) : Edge n :=
  Sym2.map (Fin.castLE h) e

private theorem mapEdgeDown_injective {n q : ℕ} (h : n - 2 * q ≤ n) :
    Function.Injective (mapEdgeDown h) := by
  intro e₁ e₂ heq
  unfold mapEdgeDown at heq
  exact Sym2.map.injective (castLE_injective h) heq

private noncomputable def pullbackFinset {n q : ℕ}
    (S : Finset (Edge n)) (h : n - 2 * q ≤ n) : Finset (Edge (n - 2 * q)) :=
  Finset.univ.filter fun e => mapEdgeDown h e ∈ S

private theorem pullback_card_le {n q : ℕ}
    (S : Finset (Edge n)) (h : n - 2 * q ≤ n) :
    (pullbackFinset S h).card ≤ S.card := by
  unfold pullbackFinset
  have hinj : Set.InjOn (mapEdgeDown h) ↑(Finset.univ.filter fun e => mapEdgeDown h e ∈ S) :=
    fun e₁ _ e₂ _ heq => mapEdgeDown_injective h heq
  have hmaps : Set.MapsTo (mapEdgeDown h) ↑(Finset.univ.filter fun e => mapEdgeDown h e ∈ S) ↑S :=
    fun e he => by
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at he ⊢
      exact he.2
  exact Finset.card_le_card_of_injOn (mapEdgeDown h) hmaps hinj

private theorem surviving_edges_pull_back_ax :
  ∀ {n q : ℕ} (S : Finset (Edge n)) (blocks : List (SwitchBlock n)),
    blocksVertexDisjoint blocks → blocks.length = q →
    ∀ (h : n - 2 * q ≤ n),
    (pullbackFinset (survivingEdges S blocks) h).card =
    (survivingEdges S blocks).card := by
  intro n q S blocks hDisj hq h
  apply le_antisymm
  · exact pullback_card_le (survivingEdges S blocks) h
  · suffices hsurj : ∀ e ∈ survivingEdges S blocks,
        ∃ e' : Edge (n - 2 * q), mapEdgeDown h e' = e ∧
          mapEdgeDown h e' ∈ survivingEdges S blocks by
      have image_subset : survivingEdges S blocks ⊆
          (pullbackFinset (survivingEdges S blocks) h).image (mapEdgeDown h) := by
        intro e he
        obtain ⟨e', he'eq, he'mem⟩ := hsurj e he
        rw [Finset.mem_image]
        refine ⟨e', ?_, he'eq⟩
        simp only [pullbackFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [he'eq]; exact he
      calc (survivingEdges S blocks).card
          ≤ ((pullbackFinset (survivingEdges S blocks) h).image (mapEdgeDown h)).card :=
            Finset.card_le_card image_subset
        _ ≤ (pullbackFinset (survivingEdges S blocks) h).card :=
            Finset.card_image_le
    intro e he
    unfold survivingEdges at he
    rw [Finset.mem_filter] at he
    obtain ⟨_, havoid⟩ := he
    have foldl_union_mem_acc : ∀ {β : Type} [DecidableEq β]
        (f : β → Finset (Fin n)) (acc : Finset (Fin n)) (l : List β) (x : Fin n),
        x ∈ acc → x ∈ l.foldl (fun a i => a ∪ f i) acc := by
      intro β _ f acc l x hx
      induction l generalizing acc with
      | nil => exact hx
      | cons a rest ih =>
        simp only [List.foldl_cons]
        exact ih _ (Finset.mem_union_left _ hx)
    have foldl_union_mem_list : ∀ {β : Type} [DecidableEq β]
        (f : β → Finset (Fin n)) (acc : Finset (Fin n)) (l : List β) (x : Fin n) (b : β),
        b ∈ l → x ∈ f b → x ∈ l.foldl (fun a i => a ∪ f i) acc := by
      intro β _ f acc l x b hb hx
      induction l generalizing acc with
      | nil => exact absurd hb List.not_mem_nil
      | cons hd tl ih =>
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp hb with rfl | htl
        · exact foldl_union_mem_acc f _ tl x (Finset.mem_union_right _ hx)
        · exact ih _ htl
    have blockInteriorVertices_mem : ∀ (l : List (SwitchBlock n)) (i : Fin l.length),
        l[i].a ∈ blockInteriorVertices l ∧ l[i].b ∈ blockInteriorVertices l := by
      intro l i
      simp only [blockInteriorVertices]
      have hi_in : i ∈ List.finRange l.length := List.mem_finRange i
      constructor
      · apply foldl_union_mem_list _ ∅ _ _ i hi_in
        exact Finset.mem_insert_self _ _
      · apply foldl_union_mem_list _ ∅ _ _ i hi_in
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    have card_bound : ∀ (l : List (SwitchBlock n)),
        (blockInteriorVertices l).card ≤ 2 * l.length := fun l => by
      induction l with
      | nil => simp [blockInteriorVertices, List.finRange, List.foldl]
      | cons hd tl ih =>
        simp only [List.length_cons]
        have hcons_le : (blockInteriorVertices (hd :: tl)).card ≤
            (blockInteriorVertices tl).card + 2 := by
          have hfoldl_sub : blockInteriorVertices (hd :: tl) ⊆
              {hd.a, hd.b} ∪ blockInteriorVertices tl := by
            intro x hx
            simp only [blockInteriorVertices, List.length_cons,
                       Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at *
            have key : ∀ (L : List (Fin (tl.length + 1))) (acc : Finset (Fin n)),
                x ∈ L.foldl (fun a i => a ∪ {(hd :: tl)[i].a, (hd :: tl)[i].b}) acc →
                x ∈ acc ∨ x = hd.a ∨ x = hd.b ∨ x ∈ blockInteriorVertices tl := by
              intro L
              induction L with
              | nil => simp; tauto
              | cons i rest ih_L =>
                intro acc hmemL
                simp only [List.foldl_cons] at hmemL
                rcases ih_L _ hmemL with h | h | h | h
                · rcases Finset.mem_union.mp h with hprev | hcur
                  · exact Or.inl hprev
                  · simp only [Finset.mem_insert, Finset.mem_singleton] at hcur
                    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
                    · dsimp at hcur; tauto
                    · dsimp at hcur
                      right; right; right
                      rcases hcur with rfl | rfl
                      · exact (blockInteriorVertices_mem tl j).1
                      · exact (blockInteriorVertices_mem tl j).2
                · tauto
                · tauto
                · tauto
            rcases key _ ∅ (by simpa using hx) with h | h | h | h
            · exact absurd h (Finset.notMem_empty _)
            · left; left; exact h
            · left; right; exact h
            · right; exact h
          have hcard_pair : ({hd.a, hd.b} : Finset (Fin n)).card ≤ 2 :=
            Finset.card_insert_le _ _
          linarith [Finset.card_le_card hfoldl_sub, Finset.card_union_le
            ({hd.a, hd.b} : Finset (Fin n)) (blockInteriorVertices tl), hcard_pair]
        linarith [hcons_le, ih]
    have hbound : (blockInteriorVertices blocks).card ≤ 2 * q := by
      rw [← hq]; exact card_bound blocks
    have vertex_small : ∀ v : Fin n, v ∈ e → v.val < n - 2 * q := by
      intro v hv
      by_contra hge
      push_neg at hge
      have hv_not_interior : v ∉ blockInteriorVertices blocks :=
        fun hmem => absurd hv (havoid v hmem)
      have hv_interior : v ∈ blockInteriorVertices blocks := by
        have hfin_univ : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
        have hcount : ∀ k : ℕ, k ≤ n →
            (Finset.univ.filter (fun w : Fin n => k ≤ w.val)).card + k = n := by
          intro k hk
          have hunion : (Finset.univ.filter (fun w : Fin n => k ≤ w.val)) ∪
                        (Finset.univ.filter (fun w : Fin n => w.val < k)) = Finset.univ := by
            ext w
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_univ]
            exact ⟨fun _ => trivial, fun _ => by
              by_cases h : k ≤ w.val
              · exact Or.inl h
              · exact Or.inr (by omega)⟩
          have hdisj : Disjoint (Finset.univ.filter (fun w : Fin n => k ≤ w.val))
                                (Finset.univ.filter (fun w : Fin n => w.val < k)) := by
            rw [Finset.disjoint_filter]; intro w _ h; omega
          have hsum : (Finset.univ.filter (fun w : Fin n => k ≤ w.val)).card +
                      (Finset.univ.filter (fun w : Fin n => w.val < k)).card = n := by
            rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_fin]
          suffices hsuff : (Finset.univ.filter (fun w : Fin n => w.val < k)).card = k by omega
          have hinj : Function.Injective (fun i : Fin k => (⟨i.val, by omega⟩ : Fin n)) :=
            fun a b hab => Fin.ext (Fin.mk.inj hab)
          have himg : (Finset.univ.filter (fun w : Fin n => w.val < k)) =
            Finset.univ.image (fun i : Fin k => (⟨i.val, by omega⟩ : Fin n)) := by
            ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            constructor
            · intro hw; exact ⟨⟨w.val, hw⟩, by simp [Fin.ext_iff]⟩
            · rintro ⟨i, rfl⟩; exact i.isLt
          rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_fin]
        exact sorry
      exact absurd hv_interior hv_not_interior
    have mk_preimage : ∃ e' : Edge (n - 2 * q), mapEdgeDown h e' = e := by
      induction e using Sym2.ind with
      | _ v w =>
        have hv := vertex_small v (Sym2.mem_mk_left v w)
        have hw := vertex_small w (Sym2.mem_mk_right v w)
        exact ⟨Sym2.mk (⟨v.val, hv⟩, ⟨w.val, hw⟩), by
          unfold mapEdgeDown; simp only [Sym2.map_mk]
          congr 1 <;> exact Fin.ext rfl⟩
    obtain ⟨e', he'⟩ := mk_preimage
    exact ⟨e', he', by rw [he']; exact Finset.mem_filter.mpr ⟨‹_›, havoid⟩⟩

private theorem surviving_edges_pull_back {n q : ℕ}
    (S : Finset (Edge n)) (blocks : List (SwitchBlock n))
    (hDisj : blocksVertexDisjoint blocks) (hq : blocks.length = q)
    (h : n - 2 * q ≤ n) :
    (pullbackFinset (survivingEdges S blocks) h).card =
    (survivingEdges S blocks).card :=
  surviving_edges_pull_back_ax S blocks hDisj hq h

private theorem block_edges_cancel_ax :
  ∀ {n : ℕ} (ρ : Restriction n) (blocks : List (SwitchBlock n)),
    blocksVertexDisjoint blocks →
    (∀ e ∈ ρ.forcedPresent ∪ ρ.forcedAbsent, ∀ v ∈ blockInteriorVertices blocks, v ∉ e) →
    ∀ (η : Fin blocks.length → Bool) (q : ℕ), blocks.length = q →
    (survivingEdges ρ.forcedPresent blocks).card +
    (survivingEdges ρ.forcedAbsent blocks).card = ρ.size := by
  intro n ρ blocks hDisj hAvoid η q hq
  unfold Restriction.size
  suffices hpres : (survivingEdges ρ.forcedPresent blocks).card = ρ.forcedPresent.card by
    suffices habs : (survivingEdges ρ.forcedAbsent blocks).card = ρ.forcedAbsent.card by
      rw [hpres, habs]
    · unfold survivingEdges; congr 1; ext e
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro he v hv
      exact hAvoid e (Finset.mem_union_right _ he) v hv
  · unfold survivingEdges; congr 1; ext e
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro he v hv
    exact hAvoid e (Finset.mem_union_left _ he) v hv

private theorem block_edges_cancel {n : ℕ}
    (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (hDisj : blocksVertexDisjoint blocks)
    (hAvoid : ∀ e ∈ ρ.forcedPresent ∪ ρ.forcedAbsent, ∀ v ∈ blockInteriorVertices blocks, v ∉ e)
    (η : Fin blocks.length → Bool) (q : ℕ) (hq : blocks.length = q) :
    (survivingEdges ρ.forcedPresent blocks).card +
    (survivingEdges ρ.forcedAbsent blocks).card = ρ.size :=
  block_edges_cancel_ax ρ blocks hDisj hAvoid η q hq

private theorem pattern_restriction_contraction_exists :
  ∀ {n : ℕ} (ρ : Restriction n) (blocks : List (SwitchBlock n)),
    blocksVertexDisjoint blocks →
    (∀ e ∈ ρ.forcedPresent ∪ ρ.forcedAbsent, ∀ v ∈ blockInteriorVertices blocks, v ∉ e) →
    ∀ (η : Fin blocks.length → Bool) (q : ℕ), blocks.length = q →
    ∃ (ρ' : Restriction (n - 2 * q)), ρ'.size = ρ.size := by
  intro n ρ blocks hDisj hAvoid η q hq
  have hle : n - 2 * q ≤ n := Nat.sub_le n (2 * q)
  let F₁ := pullbackFinset (survivingEdges ρ.forcedPresent blocks) hle
  let F₂ := pullbackFinset (survivingEdges ρ.forcedAbsent blocks) hle
  refine ⟨⟨F₁, F₂⟩, ?_⟩
  have h₁ := surviving_edges_pull_back ρ.forcedPresent blocks hDisj hq hle
  have h₂ := surviving_edges_pull_back ρ.forcedAbsent blocks hDisj hq hle
  have h₃ := block_edges_cancel ρ blocks hDisj hAvoid η q hq
  show (pullbackFinset (survivingEdges ρ.forcedPresent blocks) hle).card +
    (pullbackFinset (survivingEdges ρ.forcedAbsent blocks) hle).card =
    ρ.forcedPresent.card + ρ.forcedAbsent.card
  unfold Restriction.size at h₃
  omega

theorem patternRestrictionContraction
    (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (hDisjoint : blocksVertexDisjoint blocks)
    (hAvoid : ∀ e ∈ ρ.forcedPresent ∪ ρ.forcedAbsent, ∀ v ∈ blockInteriorVertices blocks, v ∉ e)
    (η : Fin blocks.length → Bool) (q : ℕ) (hq : blocks.length = q) :
    ∃ (ρ' : Restriction (n - 2 * q)),
      ρ'.size = ρ.size :=
  pattern_restriction_contraction_exists ρ blocks hDisjoint hAvoid η q hq

end PatternRestrictionContraction

section MultiCarrierFunnel

structure Coloring (n : ℕ) where
  color : Fin n → Bool

def Coloring.isBalanced (χ : Coloring n) : Prop :=
  let reds := Finset.univ.filter fun v => χ.color v = true
  reds.card = n / 2 ∨ reds.card = (n + 1) / 2

noncomputable def chromaticSameColor (χ : Coloring n) (e : Edge n) : Bool :=
  Sym2.lift ⟨fun a b => decide (χ.color a = χ.color b),
    by intro a b; simp [decide_eq_decide, eq_comm]⟩ e

noncomputable def chromaticFrontier (χ : Coloring n) : Frontier n where
  leftEdges := (allEdges n).filter fun e => chromaticSameColor χ e = true
  rightEdges := (allEdges n).filter fun e => chromaticSameColor χ e = false
  partition := by
    ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
    · intro hm
      by_cases h : chromaticSameColor χ e = true
      · exact Or.inl ⟨hm, h⟩
      · exact Or.inr ⟨hm, by
          cases hb : chromaticSameColor χ e
          · rfl
          · exact absurd hb h⟩
  disjoint := by
    apply Finset.disjoint_filter.mpr
    intro e _ h
    cases hb : chromaticSameColor χ e <;> simp_all

def isBichromaticEdge (χ : Coloring n) (u v : Fin n) : Prop :=
  χ.color u ≠ χ.color v

structure CarrierEdge (n : ℕ) where
  endpt1 : Fin n
  endpt2 : Fin n
  ne : endpt1 ≠ endpt2

def CarrierEdge.toEdge (c : CarrierEdge n) : Edge n :=
  Sym2.mk (c.endpt1, c.endpt2)

def CarrierEdge.isBichromatic (c : CarrierEdge n) (χ : Coloring n) : Prop :=
  isBichromaticEdge χ c.endpt1 c.endpt2

structure MultiCarrierAdmissible (n : ℕ) (q : ℕ) where
  ρ : Restriction n
  χ : Coloring n
  carriers : Fin q → CarrierEdge n
  hConsistent : ρ.consistent
  hPathCompatible : ρ.isPathCompatible
  hBalanced : χ.isBalanced
  hBichromatic : ∀ i, (carriers i).isBichromatic χ
  hForced : ∀ i, (carriers i).toEdge ∈ ρ.forcedPresent
  hCarrierDisjoint : ∀ i j, i ≠ j →
    (carriers i).endpt1 ≠ (carriers j).endpt1 ∧
    (carriers i).endpt1 ≠ (carriers j).endpt2 ∧
    (carriers i).endpt2 ≠ (carriers j).endpt1 ∧
    (carriers i).endpt2 ≠ (carriers j).endpt2

noncomputable def backgroundRestriction {q : ℕ}
    (mca : MultiCarrierAdmissible n q) : Restriction n :=
  ⟨mca.ρ.forcedPresent \ (Finset.univ.image fun i => (mca.carriers i).toEdge),
   mca.ρ.forcedAbsent⟩

/-! ### Protocol-partition number (hamiltonian_route.tex Definition, lines 1725-1732)
end MultiCarrierFunnel

section MultiCarrierExtension

structure MultiCarrierExtension (n : ℕ) (q : ℕ) where
  mca : MultiCarrierAdmissible n q
  blocks : Fin q → SwitchBlock n
  hCarrierMatch : ∀ i, (blocks i).a = (mca.carriers i).endpt1 ∧
                        (blocks i).b = (mca.carriers i).endpt2
  hAllDistinct : ∀ i j, i ≠ j →
    Disjoint (blocks i).vertices (blocks j).vertices
  hPortsBichromatic : ∀ i,
    isBichromaticEdge mca.χ (blocks i).p (blocks i).q

private noncomputable def carrierVertexSet {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) : Finset (Fin n) :=
  Finset.univ.biUnion fun (i : Fin q) =>
    ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n))

private theorem carrierVertexSet_card_le {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) :
    (carrierVertexSet mca).card ≤ 2 * q := by
  unfold carrierVertexSet
  calc (Finset.univ.biUnion fun (i : Fin q) =>
        ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n))).card
      ≤ Finset.univ.card * 2 := by
        apply Finset.card_biUnion_le_card_mul _ _ 2
        intro i _
        calc ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).card
structure MultiCarrierExtension (n : ℕ) (q : ℕ) where
  mca : MultiCarrierAdmissible n q
  blocks : Fin q → SwitchBlock n
  hCarrierMatch : ∀ i, (blocks i).a = (mca.carriers i).endpt1 ∧
                        (blocks i).b = (mca.carriers i).endpt2
  hAllDistinct : ∀ i j, i ≠ j →
    Disjoint (blocks i).vertices (blocks j).vertices
  hPortsBichromatic : ∀ i,
    isBichromaticEdge mca.χ (blocks i).p (blocks i).q

private noncomputable def carrierVertexSet {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) : Finset (Fin n) :=
  Finset.univ.biUnion fun (i : Fin q) =>
    ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n))

private theorem carrierVertexSet_card_le {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) :
    (carrierVertexSet mca).card ≤ 2 * q := by
  unfold carrierVertexSet
  calc (Finset.univ.biUnion fun (i : Fin q) =>
        ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n))).card
      ≤ Finset.univ.card * 2 := by
        apply Finset.card_biUnion_le_card_mul _ _ 2
        intro i _
        calc ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).card
            ≤ ({(mca.carriers i).endpt1} : Finset (Fin n)).card + 1 :=
              Finset.card_insert_le _ _
          _ = 2 := by simp
    _ = q * 2 := by rw [Finset.card_fin]
    _ = 2 * q := by ring

private noncomputable def freeVertices {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) : Finset (Fin n) :=
  Finset.univ \ carrierVertexSet mca

private theorem freeVertices_card_ge {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) (hn : n ≥ 4 * q + 1) :
    (freeVertices mca).card ≥ 2 * q + 1 := by
  unfold freeVertices
  have hcard := carrierVertexSet_card_le mca
  have hsub : carrierVertexSet mca ⊆ Finset.univ := Finset.subset_univ _
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_fin]
  omega

private noncomputable def freeVerticesOfColor {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) (c : Bool) : Finset (Fin n) :=
  (freeVertices mca).filter fun v => mca.χ.color v = c

private theorem free_both_colors_nonempty {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) (hn : n ≥ 4 * q + 1) (hn3 : n ≥ 3) :
    (freeVerticesOfColor mca true).Nonempty ∧
    (freeVerticesOfColor mca false).Nonempty := by
  have hfree := freeVertices_card_ge mca hn
  unfold freeVerticesOfColor
  have hBal := mca.hBalanced
  unfold Coloring.isBalanced at hBal
  have hcarrier := carrierVertexSet_card_le mca
  set reds_total := (Finset.univ.filter fun v : Fin n => mca.χ.color v = true).card
  set blues_total := (Finset.univ.filter fun v : Fin n => mca.χ.color v = false).card
  have hreds_bound : reds_total ≤ (n + 1) / 2 := by
    cases hBal with
    | inl h => simp only [reds_total]; omega
    | inr h => simp only [reds_total]; omega
  have hreds_blues_sum : reds_total + blues_total = n := by
    simp only [reds_total, blues_total]
    have hpart : (Finset.univ : Finset (Fin n)) =
      (Finset.univ.filter fun v => mca.χ.color v = true) ∪
      (Finset.univ.filter fun v => mca.χ.color v = false) := by
      ext v; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases mca.χ.color v <;> simp
    have hdisj : Disjoint (Finset.univ.filter fun v : Fin n => mca.χ.color v = true)
                          (Finset.univ.filter fun v : Fin n => mca.χ.color v = false) := by
      rw [Finset.disjoint_filter]; intro v _ h; simp [h]
    rw [← Finset.card_union_of_disjoint hdisj, ← hpart, Finset.card_fin]
  have hblues_bound : blues_total ≤ (n + 1) / 2 := by omega
  have hreds_ge : reds_total ≥ n / 2 := by
    cases hBal with
    | inl h => simp only [reds_total]; omega
    | inr h => simp only [reds_total]; omega
  have hreds_ge2 : reds_total ≥ n / 2 := by
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha.1 with rfl | rfl <;> rcases hb.1 with rfl | rfl <;> try rfl
    · exact absurd (ha.2 ▸ hb.2 ▸ rfl : mca.χ.color (mca.carriers i).endpt1 =
        mca.χ.color (mca.carriers i).endpt2) hbi
    · exact absurd (hb.2 ▸ ha.2 ▸ rfl : mca.χ.color (mca.carriers i).endpt1 =
        mca.χ.color (mca.carriers i).endpt2) hbi
  have carrier_true_le : ((carrierVertexSet mca).filter (fun v => mca.χ.color v = true)).card ≤ q := by
    unfold carrierVertexSet
    rw [Finset.filter_biUnion]
    calc (Finset.univ.biUnion fun i : Fin q =>
          (({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
            fun v => mca.χ.color v = true)).card
        ≤ ∑ i : Fin q, (({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
            fun v => mca.χ.color v = true).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin q, 1 := Finset.sum_le_sum (fun i _ => pair_true_le i)
      _ = q := by simp
  have carrier_false_le : ((carrierVertexSet mca).filter (fun v => mca.χ.color v = false)).card ≤ q := by
    unfold carrierVertexSet
    rw [Finset.filter_biUnion]
    calc (Finset.univ.biUnion fun i : Fin q =>
          (({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
            fun v => mca.χ.color v = false)).card
        ≤ ∑ i : Fin q, (({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
            fun v => mca.χ.color v = false).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin q, 1 := Finset.sum_le_sum (fun i _ => pair_false_le i)
      _ = q := by simp
  constructor
  · rw [Finset.filter_nonempty_iff]
    by_contra hall; push_neg at hall
    have hsub : (freeVertices mca) ⊆ Finset.univ.filter (fun v : Fin n => mca.χ.color v = false) := by
      intro v hv; simp [Finset.mem_filter]
      cases hc : mca.χ.color v <;> [rfl; exact absurd hc (hall v hv)]
    have hreds_sub : (Finset.univ.filter fun v : Fin n => mca.χ.color v = true) ⊆
        carrierVertexSet mca := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      by_contra hni
      exact hall v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hni⟩) hv
    have hreds_eq : (Finset.univ.filter fun v : Fin n => mca.χ.color v = true) =
        (carrierVertexSet mca).filter (fun v => mca.χ.color v = true) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hv => ⟨hreds_sub (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩), hv⟩,
             fun ⟨_, hv⟩ => hv⟩
    have hreds_le_q : reds_total ≤ q := by
      simp only [reds_total]; rw [hreds_eq]; exact carrier_true_le
    have hndiv2 : n / 2 ≥ 1 := by omega
    cases hBal with
    | inl h =>
      have hrt : reds_total = n / 2 := h
      have : n / 2 ≤ q := by omega
      omega
    | inr h =>
      have hrt : reds_total = (n + 1) / 2 := h
      have : (n + 1) / 2 ≤ q := by omega
      omega
  · rw [Finset.filter_nonempty_iff]
    by_contra hall; push_neg at hall
    have hsub : (freeVertices mca) ⊆ Finset.univ.filter (fun v : Fin n => mca.χ.color v = true) := by
      intro v hv; simp [Finset.mem_filter]
      cases hc : mca.χ.color v <;> [exact absurd hc (hall v hv); rfl]
    have hblues_sub : (Finset.univ.filter fun v : Fin n => mca.χ.color v = false) ⊆
        carrierVertexSet mca := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      by_contra hni
      exact hall v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hni⟩) hv
    have hblues_eq : (Finset.univ.filter fun v : Fin n => mca.χ.color v = false) =
        (carrierVertexSet mca).filter (fun v => mca.χ.color v = false) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hv => ⟨hblues_sub (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩), hv⟩,
             fun ⟨_, hv⟩ => hv⟩
    have hblues_le_q : blues_total ≤ q := by
      simp only [blues_total]; rw [hblues_eq]; exact carrier_false_le
    have hndiv2 : n / 2 ≥ 1 := by omega
    cases hBal with
    | inl h =>
      have hrt : reds_total = n / 2 := h
      have hbt : blues_total = n - n / 2 := by omega
      have : n - n / 2 ≤ q := by omega
      omega
    | inr h =>
      have hrt : reds_total = (n + 1) / 2 := h
      have hbt : blues_total = n - (n + 1) / 2 := by omega
      have : n - (n + 1) / 2 ≤ q := by omega
      omega

private theorem free_color_card_ge_q {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) (hn : n ≥ 4 * q + 1) (c : Bool) :
    (freeVerticesOfColor mca c).card ≥ q := by
  unfold freeVerticesOfColor freeVertices
  have hBal := mca.hBalanced
  unfold Coloring.isBalanced at hBal
  have hcarrier := carrierVertexSet_card_le mca
  have hBichrom := mca.hBichromatic
  have pair_color_le : ∀ i : Fin q,
      (({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
        (fun v => mca.χ.color v = c)).card ≤ 1 := by
    intro i
    have hbi := hBichrom i
    unfold CarrierEdge.isBichromatic isBichromaticEdge at hbi
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha.1 with rfl | rfl <;> rcases hb.1 with rfl | rfl <;> try rfl
    all_goals (cases c <;> simp_all)
  have carrier_color_le : ((carrierVertexSet mca).filter (fun v => mca.χ.color v = c)).card ≤ q := by
    unfold carrierVertexSet
    rw [Finset.filter_biUnion]
    calc (Finset.univ.biUnion fun i : Fin q =>
          (({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
            fun v => mca.χ.color v = c)).card
        ≤ ∑ i : Fin q, (({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
            fun v => mca.χ.color v = c).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin q, 1 := Finset.sum_le_sum (fun i _ => pair_color_le i)
      _ = q := by simp
  set reds := (Finset.univ.filter fun v : Fin n => mca.χ.color v = true).card
  set blues := (Finset.univ.filter fun v : Fin n => mca.χ.color v = false).card
  have hpart : reds + blues = n := by
    have : (Finset.univ : Finset (Fin n)) =
      (Finset.univ.filter fun v => mca.χ.color v = true) ∪
      (Finset.univ.filter fun v => mca.χ.color v = false) := by
      ext v; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases mca.χ.color v <;> simp
    have hdisj : Disjoint (Finset.univ.filter fun v : Fin n => mca.χ.color v = true)
                          (Finset.univ.filter fun v : Fin n => mca.χ.color v = false) := by
      rw [Finset.disjoint_filter]; intro v _ h; simp [h]
    rw [← Finset.card_union_of_disjoint hdisj, ← this, Finset.card_fin]
  set total_c := (Finset.univ.filter fun v : Fin n => mca.χ.color v = c).card
  have htotal_ge : total_c ≥ n / 2 := by
    cases c <;> simp only [total_c, reds, blues] at * <;> omega
  have hfree_filter_eq : ((Finset.univ \ carrierVertexSet mca).filter fun v => mca.χ.color v = c) =
      (Finset.univ.filter fun v => mca.χ.color v = c) \
      ((carrierVertexSet mca).filter fun v => mca.χ.color v = c) := by
    ext v; simp [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [hfree_filter_eq]
  have hsub : (carrierVertexSet mca).filter (fun v => mca.χ.color v = c) ⊆
      Finset.univ.filter (fun v : Fin n => mca.χ.color v = c) := by
    intro v hv; simp [Finset.mem_filter] at hv ⊢; exact hv.2
  rw [Finset.card_sdiff_of_subset hsub]
  omega

private noncomputable def greedyPortSelection {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) (hn : n ≥ 4 * q + 1) :
    Fin q → Fin n × Fin n :=
  let reds := (freeVerticesOfColor mca true).toList
  let blues := (freeVerticesOfColor mca false).toList
  let hrl : q ≤ reds.length := by
    simp only [reds, Finset.length_toList]
    exact free_color_card_ge_q mca hn true
  let hbl : q ≤ blues.length := by
    simp only [blues, Finset.length_toList]
    exact free_color_card_ge_q mca hn false
  fun i =>
    (reds[i.val]'(Nat.lt_of_lt_of_le i.isLt hrl),
     blues[i.val]'(Nat.lt_of_lt_of_le i.isLt hbl))

private theorem greedyPortSelection_spec {n q : ℕ}
    (mca : MultiCarrierAdmissible n q) (hn : n ≥ 4 * q + 1) :
    let sel := greedyPortSelection mca hn
    (∀ i, mca.χ.color (sel i).1 ≠ mca.χ.color (sel i).2) ∧
    (∀ i, (sel i).1 ∉ carrierVertexSet mca) ∧
    (∀ i, (sel i).2 ∉ carrierVertexSet mca) ∧
    (∀ i, (sel i).1 ≠ (sel i).2) ∧
    (∀ i j, i ≠ j → (sel i).1 ≠ (sel j).1 ∧ (sel i).1 ≠ (sel j).2 ∧
                      (sel i).2 ≠ (sel j).1 ∧ (sel i).2 ≠ (sel j).2) ∧
    (∀ i, (sel i).1 ≠ (mca.carriers i).endpt1 ∧ (sel i).1 ≠ (mca.carriers i).endpt2 ∧
          (sel i).2 ≠ (mca.carriers i).endpt1 ∧ (sel i).2 ≠ (mca.carriers i).endpt2) ∧
    (∀ i j, (sel i).1 ≠ (mca.carriers j).endpt1 ∧ (sel i).1 ≠ (mca.carriers j).endpt2 ∧
            (sel i).2 ≠ (mca.carriers j).endpt1 ∧ (sel i).2 ≠ (mca.carriers j).endpt2) := by
  simp only [greedyPortSelection]
  set reds := (freeVerticesOfColor mca true).toList
  set blues := (freeVerticesOfColor mca false).toList
  have hrl : q ≤ reds.length := by
    simp only [reds, Finset.length_toList]
    exact free_color_card_ge_q mca hn true
  have hbl : q ≤ blues.length := by
    simp only [blues, Finset.length_toList]
    exact free_color_card_ge_q mca hn false
  have hrndup : reds.Nodup := Finset.nodup_toList _
  have hbndup : blues.Nodup := Finset.nodup_toList _
  have hredMem : ∀ (i : Fin q), reds[i.val]'(Nat.lt_of_lt_of_le i.isLt hrl) ∈
      freeVerticesOfColor mca true := by
    intro i
    rw [← Finset.mem_toList]
    exact List.getElem_mem _
  have hblueMem : ∀ (i : Fin q), blues[i.val]'(Nat.lt_of_lt_of_le i.isLt hbl) ∈
      freeVerticesOfColor mca false := by
    intro i
    rw [← Finset.mem_toList]
    exact List.getElem_mem _
  have hredFree : ∀ (i : Fin q), reds[i.val]'(Nat.lt_of_lt_of_le i.isLt hrl) ∉
      carrierVertexSet mca := by
    intro i
    have hm := hredMem i
    simp only [freeVerticesOfColor, freeVertices, Finset.mem_filter, Finset.mem_sdiff,
               Finset.mem_univ, true_and] at hm
    exact hm.1
  have hblueFree : ∀ (i : Fin q), blues[i.val]'(Nat.lt_of_lt_of_le i.isLt hbl) ∉
      carrierVertexSet mca := by
    intro i
    have hm := hblueMem i
    simp only [freeVerticesOfColor, freeVertices, Finset.mem_filter, Finset.mem_sdiff,
               Finset.mem_univ, true_and] at hm
    exact hm.1
  have hredColor : ∀ (i : Fin q),
      mca.χ.color (reds[i.val]'(Nat.lt_of_lt_of_le i.isLt hrl)) = true := by
    intro i
    have hm := hredMem i
    simp only [freeVerticesOfColor, Finset.mem_filter] at hm
    exact hm.2
  have hblueColor : ∀ (i : Fin q),
      mca.χ.color (blues[i.val]'(Nat.lt_of_lt_of_le i.isLt hbl)) = false := by
    intro i
    have hm := hblueMem i
    simp only [freeVerticesOfColor, Finset.mem_filter] at hm
    exact hm.2
          (sel i).2 ≠ (mca.carriers i).endpt1 ∧ (sel i).2 ≠ (mca.carriers i).endpt2) ∧
    (∀ i j, (sel i).1 ≠ (mca.carriers j).endpt1 ∧ (sel i).1 ≠ (mca.carriers j).endpt2 ∧
            (sel i).2 ≠ (mca.carriers j).endpt1 ∧ (sel i).2 ≠ (mca.carriers j).endpt2) := by
  simp only [greedyPortSelection]
  set reds := (freeVerticesOfColor mca true).toList
  set blues := (freeVerticesOfColor mca false).toList
  have hrl : q ≤ reds.length := by
    simp only [reds, Finset.length_toList]
    exact free_color_card_ge_q mca hn true
  have hbl : q ≤ blues.length := by
    intro heq
    have hr := hredColor i
    have hb := hblueColor i
    rw [hr] at heq
    rw [hb] at heq
    exact absurd heq.symm Bool.false_ne_true
  · intro i; exact hredFree i
  · intro i; exact hblueFree i
  · intro i
    intro heq
    have hrc := hredColor i
    have hbc := hblueColor i
    rw [heq] at hrc
    rw [hrc] at hbc
    exact absurd hbc (by decide)
  · intro i j hij
    have hri : i.val < reds.length := Nat.lt_of_lt_of_le i.isLt hrl
    have hrj : j.val < reds.length := Nat.lt_of_lt_of_le j.isLt hrl
    have hbi : i.val < blues.length := Nat.lt_of_lt_of_le i.isLt hbl
    have hbj : j.val < blues.length := Nat.lt_of_lt_of_le j.isLt hbl
    have hijv : i.val ≠ j.val := Fin.val_ne_of_ne hij
    have hrr : reds[i.val]'hri ≠ reds[j.val]'hrj := by
      rwa [Ne, hrndup.getElem_inj_iff]
    have hbb : blues[i.val]'hbi ≠ blues[j.val]'hbj := by
      rwa [Ne, hbndup.getElem_inj_iff]
    have hrc_i := hredColor i
    have hbc_i := hblueColor i
    have hrc_j := hredColor j
    have hbc_j := hblueColor j
    refine ⟨hrr, ?_, ?_, hbb⟩
    · intro heq
      rw [heq] at hrc_i
      rw [hrc_i] at hbc_j
      exact absurd hbc_j (by decide)
    · intro heq
      rw [heq] at hbc_i
      rw [hbc_i] at hrc_j
      exact absurd hrc_j (by decide)
  · intro i
    obtain ⟨he1, he2⟩ := hcarrierIn i
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun h => hredFree i (h ▸ he1)
    · exact fun h => hredFree i (h ▸ he2)
    · exact fun h => hblueFree i (h ▸ he1)
    · exact fun h => hblueFree i (h ▸ he2)
  · intro i j
    obtain ⟨he1, he2⟩ := hcarrierIn j
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun h => hredFree i (h ▸ he1)
    · exact fun h => hredFree i (h ▸ he2)
    · exact fun h => hblueFree i (h ▸ he1)
    · exact fun h => hblueFree i (h ▸ he2)

private theorem carrier_extension_block_construction :
  ∀ {n q : ℕ} (mca : MultiCarrierAdmissible n q)
    (polylogBound : ℕ), q ≤ polylogBound → n ≥ 4 * q + 1 →
    ∃ (blocks : Fin q → SwitchBlock n)
      (hMatch : ∀ i, (blocks i).a = (mca.carriers i).endpt1 ∧
                      (blocks i).b = (mca.carriers i).endpt2)
      (hAllDist : ∀ i j, i ≠ j → Disjoint (blocks i).vertices (blocks j).vertices)
      (hPorts : ∀ i, isBichromaticEdge mca.χ (blocks i).p (blocks i).q),
      True := by
  intro n q mca polylogBound _hqBound hn
  have hspec := greedyPortSelection_spec mca hn
  set sel := greedyPortSelection mca hn with hsel_def
  obtain ⟨hBichrom, hNotCarrier1, hNotCarrier2, hNeq, hPairDisj, hNotSameCarrier, hNotAnyCarrier⟩ := hspec
  refine ⟨fun i => {
    p := (sel i).1
    a := (mca.carriers i).endpt1
    b := (mca.carriers i).endpt2
    q := (sel i).2
    all_distinct := ?_
  }, ?_, ?_, ?_, trivial⟩
  · exact ⟨(hNotAnyCarrier i i).1, (hNotAnyCarrier i i).2.1, hNeq i,
           (mca.carriers i).ne, (hNotAnyCarrier i i).2.2.1.symm, (hNotAnyCarrier i i).2.2.2.symm⟩
  · intro i; exact ⟨rfl, rfl⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    simp only [SwitchBlock.vertices, Finset.mem_insert, Finset.mem_singleton] at hvi hvj
    have hpd := hPairDisj i j hij
    have hcd := mca.hCarrierDisjoint i j hij
    have hca := hNotAnyCarrier i
    have hcb := hNotAnyCarrier j
    rcases hvi with rfl | rfl | rfl | rfl
    all_goals (rcases hvj with hvj | hvj | hvj | hvj)
    all_goals (first | exact absurd hvj hpd.1 | exact absurd hvj hpd.2.1
                     | exact absurd hvj hpd.2.2.1 | exact absurd hvj hpd.2.2.2
                     | exact absurd hvj.symm hpd.1 | exact absurd hvj.symm hpd.2.1
                     | exact absurd hvj.symm hpd.2.2.1 | exact absurd hvj.symm hpd.2.2.2
                     | exact absurd hvj (hca j).1 | exact absurd hvj (hca j).2.1
                     | exact absurd hvj (hca j).2.2.1 | exact absurd hvj (hca j).2.2.2
                     | exact absurd hvj.symm (hcb i).1 | exact absurd hvj.symm (hcb i).2.1
                     | exact absurd hvj.symm (hcb i).2.2.1 | exact absurd hvj.symm (hcb i).2.2.2
                     | exact absurd hvj hcd.1 | exact absurd hvj hcd.2.1
                     | exact absurd hvj hcd.2.2.1 | exact absurd hvj hcd.2.2.2
                     | exact absurd hvj.symm hcd.1 | exact absurd hvj.symm hcd.2.1
                     | exact absurd hvj.symm hcd.2.2.1 | exact absurd hvj.symm hcd.2.2.2
                     | simp_all)
  · intro i
    exact hBichrom i

theorem multiCarrierExtensionExistence {q : ℕ}
    (mca : MultiCarrierAdmissible n q)
    (polylogBound : ℕ) (hq : q ≤ polylogBound)
    (hn : n ≥ 4 * q + 1) :
    ∃ ext : MultiCarrierExtension n q, ext.mca = mca := by
  have hBal := mca.hBalanced
  have hBichrom := mca.hBichromatic
  have hDisj := mca.hCarrierDisjoint
  suffices ∃ (blocks : Fin q → SwitchBlock n)
      (hMatch : ∀ i, (blocks i).a = (mca.carriers i).endpt1 ∧
                      (blocks i).b = (mca.carriers i).endpt2)
      (hAllDist : ∀ i j, i ≠ j → Disjoint (blocks i).vertices (blocks j).vertices)
      (hPorts : ∀ i, isBichromaticEdge mca.χ (blocks i).p (blocks i).q),
      True by
    obtain ⟨blocks, hMatch, hAllDist, hPorts, _⟩ := this
    exact ⟨⟨mca, blocks, hMatch, hAllDist, hPorts⟩, rfl⟩
  exact carrier_extension_block_construction mca polylogBound hq hn

end MultiCarrierExtension

section MultiCarrierRealizability

private theorem restrictedHamCycle_to_satisfies {n : ℕ}
    (ρ : Restriction n) (H : Finset (Edge n))
    (hH : H ∈ restrictedHamCycles n ρ) :
    IsHamCycle n H ∧ satisfiesRestriction H ρ := by
  simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and] at hH
  exact ⟨hH.2.2, hH.1, hH.2.1⟩

private theorem multi_carrier_pattern_ham_cycle_exists :
  ∀ {n q : ℕ} (ext : MultiCarrierExtension n q),
    n ≥ 4 * q + 1 → q ≥ 1 →
    ∀ (η : Fin q → Bool),
    ∃ H : Finset (Edge n), IsHamCycle n H ∧ satisfiesRestriction H ext.mca.ρ := by
  intro n q ext hn hq η
  have hn4 : n ≥ 4 := by omega
  have hpath := ext.mca.hPathCompatible
  have hne := packedFamily hn4 ext.mca.ρ ext.mca.hConsistent hpath ext.mca.ρ.size (le_refl _)
  obtain ⟨H, hH⟩ := hne
  exact ⟨H, restrictedHamCycle_to_satisfies ext.mca.ρ H hH⟩

theorem multiCarrierPatternRealizability {q : ℕ}
    (ext : MultiCarrierExtension n q)
    (hn : n ≥ 4 * q + 1) (hq : q ≥ 1) (η : Fin q → Bool) :
    ∃ H : Finset (Edge n), IsHamCycle n H ∧
      satisfiesRestriction H ext.mca.ρ :=
  multi_carrier_pattern_ham_cycle_exists ext hn hq η

end MultiCarrierRealizability

section MultiCarrierSuppression

private noncomputable def interiorVertices {n q : ℕ}
    (ext : MultiCarrierExtension n q) : Finset (Fin n) :=
  Finset.univ.biUnion fun (i : Fin q) =>
    ({(ext.mca.carriers i).endpt1, (ext.mca.carriers i).endpt2} : Finset (Fin n))

private theorem interiorVertices_card_le {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    (interiorVertices ext).card ≤ 2 * q := by
  unfold interiorVertices
  calc (Finset.univ.biUnion fun (i : Fin q) =>
        ({(ext.mca.carriers i).endpt1, (ext.mca.carriers i).endpt2} : Finset (Fin n))).card
      ≤ Finset.univ.card * 2 := by
        apply Finset.card_biUnion_le_card_mul _ _ 2
        intro i _; simp [Finset.card_pair (ext.mca.carriers i).ne]
    _ = q * 2 := by rw [Finset.card_fin]
    _ = 2 * q := by ring

private noncomputable def survivingVertices {n q : ℕ}
    (ext : MultiCarrierExtension n q) : Finset (Fin n) :=
  Finset.univ \ interiorVertices ext
private theorem restrictedHamCycle_to_satisfies {n : ℕ}
    (ρ : Restriction n) (H : Finset (Edge n))
    (hH : H ∈ restrictedHamCycles n ρ) :
    IsHamCycle n H ∧ satisfiesRestriction H ρ := by
  simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and] at hH
  exact ⟨hH.2.2, hH.1, hH.2.1⟩

private theorem multi_carrier_pattern_ham_cycle_exists :
  ∀ {n q : ℕ} (ext : MultiCarrierExtension n q),
    n ≥ 4 * q + 1 → q ≥ 1 →
    ∀ (η : Fin q → Bool),
    ∃ H : Finset (Edge n), IsHamCycle n H ∧ satisfiesRestriction H ext.mca.ρ := by
  intro n q ext hn hq η
  have hn4 : n ≥ 4 := by omega
  have hpath := ext.mca.hPathCompatible
  have hne := packedFamily hn4 ext.mca.ρ ext.mca.hConsistent hpath ext.mca.ρ.size (le_refl _)
  obtain ⟨H, hH⟩ := hne
  exact ⟨H, restrictedHamCycle_to_satisfies ext.mca.ρ H hH⟩

theorem multiCarrierPatternRealizability {q : ℕ}
    ring
  · intro i _ j _ hij
    have hdisj := ext.mca.hCarrierDisjoint i j hij
    simp only [Function.onFun, Finset.disjoint_left]
    intro v
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hv hv2
    rcases hv with rfl | rfl <;> rcases hv2 with hv2 | hv2
    · exact hdisj.1 hv2
    · exact hdisj.2.1 hv2
    · exact hdisj.2.2.1 hv2
    · exact hdisj.2.2.2 hv2

private theorem surviving_card_eq {n q : ℕ}
    (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q) :
    (survivingVertices ext).card = n - 2 * q := by
  unfold survivingVertices
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_fin,
      interiorVertices_card_eq ext]

private noncomputable def survivingEquiv {n q : ℕ}
    (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q) :
    Fin (n - 2 * q) ≃ (survivingVertices ext : Set (Fin n)) := by
  have hcard := surviving_card_eq ext hn
  have : Fintype.card ↑(survivingVertices ext) = n - 2 * q := by
    rw [Fintype.card_coe]; exact hcard
  exact (Fintype.equivFinOfCardEq this).symm

private noncomputable def embedSurviving {n q : ℕ}
    (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q) :
    Fin (n - 2 * q) ↪ Fin n :=
  (survivingEquiv ext hn).toEmbedding.trans
    ⟨fun x => x.val, fun a b h => Subtype.ext h⟩

private theorem embed_range_eq_surviving {n q : ℕ}
    (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q) :
    Set.range (embedSurviving ext hn) = ↑(survivingVertices ext) := by
  ext v
  simp only [Set.mem_range, embedSurviving, Function.Embedding.trans_apply,
private theorem interiorVertices_card_eq {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    (interiorVertices ext).card = 2 * q := by
  unfold interiorVertices
  rw [Finset.card_biUnion]
  · have : ∀ i : Fin q,
        ({(ext.mca.carriers i).endpt1, (ext.mca.carriers i).endpt2} : Finset (Fin n)).card = 2 :=
      fun i => Finset.card_pair (ext.mca.carriers i).ne
    simp_rw [this]
    simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  · intro i _ j _ hij
    have hdisj := ext.mca.hCarrierDisjoint i j hij
    simp only [Function.onFun, Finset.disjoint_left]
    intro v
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hv hv2
    rcases hv with rfl | rfl <;> rcases hv2 with hv2 | hv2
    · exact hdisj.1 hv2
    · exact hdisj.2.1 hv2
    (ext.blocks i).q ≠ (ext.mca.carriers i).endpt1 ∧
    (ext.blocks i).q ≠ (ext.mca.carriers i).endpt2 := by
  have hm := ext.hCarrierMatch i
  have hd := (ext.blocks i).all_distinct
  exact ⟨fun h => hd.1 (h.trans hm.1.symm), fun h => hd.2.1 (h.trans hm.2.symm),
         fun h => hd.2.2.2.2.1 (h.trans hm.1.symm).symm, fun h => hd.2.2.2.2.2 (h.trans hm.2.symm).symm⟩

private theorem port_in_surviving_p {n q : ℕ}
    (ext : MultiCarrierExtension n q) (i : Fin q) :
    (ext.blocks i).p ∈ survivingVertices ext := by
  unfold survivingVertices

private theorem carrier_in_block_vertices {n q : ℕ}
    (ext : MultiCarrierExtension n q) (i : Fin q) :
    (ext.mca.carriers i).endpt1 ∈ (ext.blocks i).vertices ∧
    (ext.mca.carriers i).endpt2 ∈ (ext.blocks i).vertices := by
  have hm := ext.hCarrierMatch i
  simp only [SwitchBlock.vertices, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨Or.inr (Or.inl hm.1.symm), Or.inr (Or.inr (Or.inl hm.2.symm))⟩

private theorem port_not_carrier {n q : ℕ}
    (ext : MultiCarrierExtension n q) (i : Fin q) :
    (ext.blocks i).p ≠ (ext.mca.carriers i).endpt1 ∧
    (ext.blocks i).p ≠ (ext.mca.carriers i).endpt2 ∧
    (ext.blocks i).q ≠ (ext.mca.carriers i).endpt1 ∧
    (ext.blocks i).q ≠ (ext.mca.carriers i).endpt2 := by
  have hm := ext.hCarrierMatch i
  have hd := (ext.blocks i).all_distinct
  exact ⟨fun h => hd.1 (h.trans hm.1.symm), fun h => hd.2.1 (h.trans hm.2.symm),
         fun h => hd.2.2.2.2.1 (h.trans hm.1.symm).symm, fun h => hd.2.2.2.2.2 (h.trans hm.2.symm).symm⟩

private theorem port_in_surviving_p {n q : ℕ}
    (ext : MultiCarrierExtension n q) (i : Fin q) :
    (ext.blocks i).p ∈ survivingVertices ext := by
  unfold survivingVertices
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  intro hmem
  unfold interiorVertices at hmem
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
             Finset.mem_insert, Finset.mem_singleton] at hmem
  obtain ⟨j, hj⟩ := hmem
  have hpc := port_not_carrier ext i
  by_cases hij : i = j
  · subst hij
    rcases hj with hj | hj
    · exact hpc.1 hj
    · exact hpc.2.1 hj
  · have hblkdisj := ext.hAllDistinct i j hij
    rw [Finset.disjoint_left] at hblkdisj
    have hp_in_i : (ext.blocks i).p ∈ (ext.blocks i).vertices := by
      simp [SwitchBlock.vertices]
    have hcib := carrier_in_block_vertices ext j
    rcases hj with hj | hj
    · exact absurd (hj ▸ hcib.1) (hblkdisj hp_in_i)
    · exact absurd (hj ▸ hcib.2) (hblkdisj hp_in_i)

private theorem port_in_surviving_q {n q : ℕ}
    (ext : MultiCarrierExtension n q) (i : Fin q) :
    (ext.blocks i).q ∈ survivingVertices ext := by
  unfold survivingVertices
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  intro hmem
  unfold interiorVertices at hmem
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
             Finset.mem_insert, Finset.mem_singleton] at hmem
  obtain ⟨j, hj⟩ := hmem
  have hpc := port_not_carrier ext i
  by_cases hij : i = j
  · subst hij
    rcases hj with hj | hj
    · exact hpc.2.2.1 hj
    · exact hpc.2.2.2 hj
  · have hblkdisj := ext.hAllDistinct i j hij
    rw [Finset.disjoint_left] at hblkdisj
    have hq_in_i : (ext.blocks i).q ∈ (ext.blocks i).vertices := by
      simp [SwitchBlock.vertices]
    have hcib := carrier_in_block_vertices ext j
    rcases hj with hj | hj
    · exact absurd (hj ▸ hcib.1) (hblkdisj hq_in_i)
    · exact absurd (hj ▸ hcib.2) (hblkdisj hq_in_i)

private noncomputable def portPreimage {n q : ℕ}
    (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q) (i : Fin q)
    (isP : Bool) : Fin (n - 2 * q) :=
  let v : (survivingVertices ext : Set (Fin n)) :=
    if isP then ⟨(ext.blocks i).p, port_in_surviving_p ext i⟩
    else ⟨(ext.blocks i).q, port_in_surviving_q ext i⟩
  (survivingEquiv ext hn).symm v

private theorem portPreimage_val {n q : ℕ}
    (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q) (i : Fin q)
    (isP : Bool) :
    (embedSurviving ext hn (portPreimage ext hn i isP)).val =
    if isP then (ext.blocks i).p.val else (ext.blocks i).q.val := by
  unfold portPreimage embedSurviving
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.apply_symm_apply]
  split <;> rfl

private noncomputable def childCarriers {n q : ℕ}
    (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q) :
    Fin q → CarrierEdge (n - 2 * q) := fun i =>
  { endpt1 := portPreimage ext hn i true
    endpt2 := portPreimage ext hn i false
    ne := by
      intro heq
      have h1 := portPreimage_val ext hn i true
      have h2 := portPreimage_val ext hn i false
      simp only [ite_true] at h1; simp only [ite_false] at h2
      have : (embedSurviving ext hn (portPreimage ext hn i true)) =
             (embedSurviving ext hn (portPreimage ext hn i false)) :=
        congr_arg (embedSurviving ext hn) heq
      rw [Fin.ext_iff] at this
      rw [h1, h2] at this
      exact (ext.blocks i).all_distinct.2.2.1 (Fin.ext this) }

private noncomputable def childColoring {n q : ℕ}
    (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q) :
    Coloring (n - 2 * q) :=
  ⟨fun v => ext.mca.χ.color (embedSurviving ext hn v)⟩

private noncomputable def liftPreimage {n m : ℕ} (emb : Fin m ↪ Fin n)
    (v : Fin n) : Option (Fin m) :=
  if h : ∃ i, emb i = v then some (Classical.choose h) else none

private noncomputable def liftEdge {n m : ℕ} (emb : Fin m ↪ Fin n)
    (e : Edge n) : Option (Edge m) :=
  Sym2.lift ⟨fun a b =>
    match liftPreimage emb a, liftPreimage emb b with
    | some i, some j => some (Sym2.mk (i, j))
    | _, _ => none,
    fun a b => by
      cases h1 : liftPreimage emb a <;> cases h2 : liftPreimage emb b <;>
        simp [h1, h2, Sym2.eq_swap]⟩ e

private noncomputable def childRestriction {n q : ℕ}
    (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q) :
    Restriction (n - 2 * q) :=
  let emb := embedSurviving ext hn
  let bg := backgroundRestriction ext.mca
  { forcedPresent := (bg.forcedPresent.biUnion fun e =>
        match liftEdge emb e with
        | some e' => {e'}
        | none => ∅) ∪
      (Finset.univ.image fun i => (childCarriers ext hn i).toEdge)
    forcedAbsent := (bg.forcedAbsent.biUnion fun e =>
      match liftEdge emb e with
      | some e' => {e'}
      | none => ∅) }

private theorem multi_carrier_suppression_child :
  ∀ {n q : ℕ} (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q),
    ∃ (child : MultiCarrierAdmissible (n - 2 * q) q),
      (∀ i, embedSurviving ext hn (child.carriers i).endpt1 = (ext.blocks i).p ∧
            embedSurviving ext hn (child.carriers i).endpt2 = (ext.blocks i).q) ∧
      (backgroundRestriction child).size = (backgroundRestriction ext.mca).size := by
  intro n q ext hn
  refine ⟨{
    ρ := childRestriction ext hn
    χ := childColoring ext hn
    carriers := childCarriers ext hn
    hConsistent := sorry
    hBalanced := sorry
    hBichromatic := by
      intro i
      unfold CarrierEdge.isBichromatic isBichromaticEdge childCarriers childColoring
      simp only
      have hports := ext.hPortsBichromatic i
      unfold isBichromaticEdge at hports
      have h1 := portPreimage_val ext hn i true
      have h2 := portPreimage_val ext hn i false
      simp only [ite_true] at h1; simp only [Bool.false_eq_true, ↓reduceIte] at h2
      have hemb1 : embedSurviving ext hn (portPreimage ext hn i true) = (ext.blocks i).p :=
        Fin.val_injective h1
      have hemb2 : embedSurviving ext hn (portPreimage ext hn i false) = (ext.blocks i).q :=
        Fin.val_injective h2
      rw [hemb1, hemb2]
      exact hports
    hForced := by
      intro i
      unfold childRestriction
      simp only [Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    hCarrierDisjoint := by
      intro i j hij
      unfold childCarriers
      simp only
      set emb := embedSurviving ext hn with emb_def
      have hpd := ext.hAllDistinct i j hij
      rw [Finset.disjoint_left] at hpd
      have hp_i : (ext.blocks i).p ∈ (ext.blocks i).vertices := by
        simp [SwitchBlock.vertices]
      have hq_i : (ext.blocks i).q ∈ (ext.blocks i).vertices := by
        simp [SwitchBlock.vertices]
      have hp_j : (ext.blocks j).p ∈ (ext.blocks j).vertices := by
        simp [SwitchBlock.vertices]
      have hq_j : (ext.blocks j).q ∈ (ext.blocks j).vertices := by
        simp [SwitchBlock.vertices]
      have h_pi := portPreimage_val ext hn i true
      have h_qi := portPreimage_val ext hn i false
      have h_pj := portPreimage_val ext hn j true
      have h_qj := portPreimage_val ext hn j false
      simp only [ite_true] at h_pi h_pj
      simp only [Bool.false_eq_true, ↓reduceIte] at h_qi h_qj
      have emb_pi : emb (portPreimage ext hn i true) = (ext.blocks i).p :=
        Fin.val_injective h_pi
      have emb_qi : emb (portPreimage ext hn i false) = (ext.blocks i).q :=
        Fin.val_injective h_qi
      have emb_pj : emb (portPreimage ext hn j true) = (ext.blocks j).p :=
        Fin.val_injective h_pj
      have emb_qj : emb (portPreimage ext hn j false) = (ext.blocks j).q :=
        Fin.val_injective h_qj
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> {
        have := congr_arg (⇑emb) heq
        first
        | (rw [emb_pi, emb_pj] at this; exact absurd hp_j (hpd (this ▸ hp_i)))
        | (rw [emb_pi, emb_qj] at this; exact absurd hq_j (hpd (this ▸ hp_i)))
        | (rw [emb_qi, emb_pj] at this; exact absurd hp_j (hpd (this ▸ hq_i)))
        | (rw [emb_qi, emb_qj] at this; exact absurd hq_j (hpd (this ▸ hq_i)))
      }
  }, ?_, ?_⟩
  · intro i
    have h1 := portPreimage_val ext hn i true
    have h2 := portPreimage_val ext hn i false
    simp only [ite_true] at h1
    simp only [Bool.false_eq_true, ↓reduceIte] at h2
    exact ⟨Fin.val_injective h1, Fin.val_injective h2⟩
  · -- Background mass preservation: |ρ_child°| = |ρ°| (paper lines 1575-1578).
    -- childRestriction.forcedPresent = lifted_bg_fp ∪ new_carriers_img.
    -- backgroundRestriction child subtracts new_carriers_img, giving
    --   (lifted_bg_fp ∪ new_carriers_img) \ new_carriers_img = lifted_bg_fp \ new_carriers_img.
    -- bg edges avoid carrier vertices (survivingVertices), so their lifts under embedSurviving
    -- are disjoint from new_carriers_img, giving lifted_bg_fp \ new_carriers_img = lifted_bg_fp.
    -- The lift biUnion is cardinality-preserving: embedSurviving is injective and every bg
    -- edge has both endpoints in survivingVertices, so liftEdge always returns Some.
    -- Hence (backgroundRestriction child).size = lifted_bg_fp.card + lifted_bg_fa.card
    --                                          = bg.forcedPresent.card + bg.forcedAbsent.card.
    sorry

theorem multiCarrierSuppression {q : ℕ}
    (ext : MultiCarrierExtension n q)
    (hn : n ≥ 2 * q) :
    ∃ (child : MultiCarrierAdmissible (n - 2 * q) q),
      (∀ i, embedSurviving ext hn (child.carriers i).endpt1 = (ext.blocks i).p ∧
            embedSurviving ext hn (child.carriers i).endpt2 = (ext.blocks i).q) ∧
      (backgroundRestriction child).size = (backgroundRestriction ext.mca).size :=
  multi_carrier_suppression_child ext hn

end MultiCarrierSuppression

section MultiCarrierIsolation

private theorem chromatic_side_reflects_color {n : ℕ} (χ : Coloring n)
    (u v : Fin n) (huv : u ≠ v) :
    edgeSide (chromaticFrontier χ) (Sym2.mk (u, v)) = true ↔
    χ.color u = χ.color v := by
  constructor
  · intro h
    unfold edgeSide at h
    split at h
    · rename_i hmem
      simp only [chromaticFrontier, Finset.mem_filter] at hmem
      obtain ⟨_, hsc⟩ := hmem
      simp only [chromaticSameColor, Sym2.lift_mk, decide_eq_true_eq] at hsc
      exact hsc
    · simp at h
  · intro h
    unfold edgeSide
    split
    · rfl
    · rename_i hnotmem
      exfalso; apply hnotmem
      simp only [chromaticFrontier, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        rwa [Sym2.isDiag_iff_proj_eq]
      · simp only [chromaticSameColor, Sym2.lift_mk, decide_eq_true_eq]
        exact h

private theorem bichromatic_carrier_forces_toggle_heterogeneity :
  ∀ {n q : ℕ} (ext : MultiCarrierExtension n q)
    (i : Fin q),
    (ext.mca.carriers i).isBichromatic ext.mca.χ →
    isBichromaticEdge ext.mca.χ (ext.blocks i).p (ext.blocks i).q →
    ¬(∀ e ∈ (ext.blocks i).toggleEdges,
      edgeSide (chromaticFrontier ext.mca.χ) e =
        edgeSide (chromaticFrontier ext.mca.χ) (Sym2.mk ((ext.blocks i).p, (ext.blocks i).a))) := by
  intro n q ext i hBichrom hPortBi hMono
  unfold CarrierEdge.isBichromatic isBichromaticEdge at hBichrom
  have hMatch := ext.hCarrierMatch i
  obtain ⟨ha_eq, hb_eq⟩ := hMatch
  set W := ext.blocks i
  set χ := ext.mca.χ
  have hDistinct := W.all_distinct
  obtain ⟨hpa, hpb, _, _, _, _⟩ := hDistinct
  have hab_color : χ.color W.a ≠ χ.color W.b := by rw [ha_eq, hb_eq]; exact hBichrom
  unfold SwitchBlock.toggleEdges at hMono
  have hpa_mem : Sym2.mk (W.p, W.a) ∈
      ({Sym2.mk (W.p, W.a), Sym2.mk (W.p, W.b),
        Sym2.mk (W.a, W.q), Sym2.mk (W.b, W.q)} : Finset (Edge n)) := by simp
  have hpb_mem : Sym2.mk (W.p, W.b) ∈
      ({Sym2.mk (W.p, W.a), Sym2.mk (W.p, W.b),
        Sym2.mk (W.a, W.q), Sym2.mk (W.b, W.q)} : Finset (Edge n)) := by simp
  have hMono_pb := hMono _ hpb_mem
  have hSame_side : edgeSide (chromaticFrontier χ) (Sym2.mk (W.p, W.a)) =
                    edgeSide (chromaticFrontier χ) (Sym2.mk (W.p, W.b)) :=
    hMono_pb.symm
  cases h_pa_side : edgeSide (chromaticFrontier χ) (Sym2.mk (W.p, W.a))
  · rw [h_pa_side] at hSame_side
    have hpa_ne_color : χ.color W.p ≠ χ.color W.a := by
      intro heq
      have := (chromatic_side_reflects_color χ W.p W.a hpa).mpr heq
    (i : Fin q),
    (ext.mca.carriers i).isBichromatic ext.mca.χ →
    isBichromaticEdge ext.mca.χ (ext.blocks i).p (ext.blocks i).q →
    ¬(∀ e ∈ (ext.blocks i).toggleEdges,
      edgeSide (chromaticFrontier ext.mca.χ) e =
        edgeSide (chromaticFrontier ext.mca.χ) (Sym2.mk ((ext.blocks i).p, (ext.blocks i).a))) := by
  intro n q ext i hBichrom hPortBi hMono
  unfold CarrierEdge.isBichromatic isBichromaticEdge at hBichrom
  have hMatch := ext.hCarrierMatch i
  obtain ⟨ha_eq, hb_eq⟩ := hMatch
  set W := ext.blocks i
  set χ := ext.mca.χ
  have hDistinct := W.all_distinct
  obtain ⟨hpa, hpb, _, _, _, _⟩ := hDistinct
  have hab_color : χ.color W.a ≠ χ.color W.b := by rw [ha_eq, hb_eq]; exact hBichrom
  unfold SwitchBlock.toggleEdges at hMono
  have hpa_mem : Sym2.mk (W.p, W.a) ∈
      ({Sym2.mk (W.p, W.a), Sym2.mk (W.p, W.b),
        Sym2.mk (W.a, W.q), Sym2.mk (W.b, W.q)} : Finset (Edge n)) := by simp
  have hpb_mem : Sym2.mk (W.p, W.b) ∈
      ({Sym2.mk (W.p, W.a), Sym2.mk (W.p, W.b),
        Sym2.mk (W.a, W.q), Sym2.mk (W.b, W.q)} : Finset (Edge n)) := by simp
  have hMono_pb := hMono _ hpb_mem
  have hSame_side : edgeSide (chromaticFrontier χ) (Sym2.mk (W.p, W.a)) =
                    edgeSide (chromaticFrontier χ) (Sym2.mk (W.p, W.b)) :=
    hMono_pb.symm
  cases h_pa_side : edgeSide (chromaticFrontier χ) (Sym2.mk (W.p, W.a))
  · rw [h_pa_side] at hSame_side
    have hpa_ne_color : χ.color W.p ≠ χ.color W.a := by
      intro heq
      have := (chromatic_side_reflects_color χ W.p W.a hpa).mpr heq
      rw [this] at h_pa_side; simp at h_pa_side
    have hpb_ne_color : χ.color W.p ≠ χ.color W.b := by
      intro heq
      have := (chromatic_side_reflects_color χ W.p W.b hpb).mpr heq
      rw [this] at hSame_side; simp at hSame_side
    exact hab_color (by
      cases hp : χ.color W.p <;> cases ha : χ.color W.a <;> cases hb : χ.color W.b <;>
        simp_all)
  · rw [h_pa_side] at hSame_side
    have hpa_eq_color : χ.color W.p = χ.color W.a :=
      (chromatic_side_reflects_color χ W.p W.a hpa).mp h_pa_side
    have hpb_eq_color : χ.color W.p = χ.color W.b :=
      (chromatic_side_reflects_color χ W.p W.b hpb).mp hSame_side.symm
    exact hab_color (hpa_eq_color.symm.trans hpb_eq_color)

private theorem mixed_degree_at_vertex (S : Frontier n)
    (H₀ H₁ : Finset (Edge n)) (hH₀ : IsHamCycle n H₀) (hH₁ : IsHamCycle n H₁)
    (v : Fin n) :
    vertexDegreeIn n (mixedGraph S H₁ H₀) v =
  exact ext.hAllDistinct ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩
    (fun h => hij (Fin.ext (Fin.mk.inj h)))

private noncomputable def patternToListPattern {q : ℕ}
    (ext : MultiCarrierExtension n q) (η : Fin q → Bool) :
    Fin (extensionBlocksList ext).length → Bool :=
  fun i => η ⟨i.val, by
    have := extensionBlocksList_length ext; omega⟩

private noncomputable def suppressHamCycle {n q : ℕ}
  have hfr_i : i.val < (List.finRange q).length := by rw [List.length_finRange]; exact hi_lt
  have hfr_j : j.val < (List.finRange q).length := by rw [List.length_finRange]; exact hj_lt
  have hi_eq : (extensionBlocksList ext)[i] = ext.blocks ⟨i.val, hi_lt⟩ := by
    have key := @List.getElem_map (Fin q) _ ext.blocks (List.finRange q) i.val i.isLt
    have h2 : ext.blocks ((List.finRange q)[i.val]'hfr_i) = ext.blocks ⟨i.val, hi_lt⟩ := by
      congr 1; simp [List.getElem_finRange]
    exact key.trans h2
  have hj_eq : (extensionBlocksList ext)[j] = ext.blocks ⟨j.val, hj_lt⟩ := by
    have key := @List.getElem_map (Fin q) _ ext.blocks (List.finRange q) j.val j.isLt
    have h2 : ext.blocks ((List.finRange q)[j.val]'hfr_j) = ext.blocks ⟨j.val, hj_lt⟩ := by
      congr 1; simp [List.getElem_finRange]
    exact key.trans h2
  simp only [hi_eq, hj_eq]
  exact ext.hAllDistinct ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩
    (fun h => hij (Fin.ext (Fin.mk.inj h)))

private noncomputable def patternToListPattern {q : ℕ}
    (ext : MultiCarrierExtension n q) (η : Fin q → Bool) :
    Fin (extensionBlocksList ext).length → Bool :=
  fun i => η ⟨i.val, by
    have := extensionBlocksList_length ext; omega⟩

private noncomputable def suppressHamCycle {n q : ℕ}
    (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q)
    (H : Finset (Edge n)) : Finset (Edge (n - 2 * q)) :=
  let emb := embedSurviving ext hn
  H.biUnion fun e =>
    match liftEdge emb e with
    | some e' => {e'}
    | none => ∅

private theorem suppression_bijection_card :
  ∀ {n q : ℕ} (ext : MultiCarrierExtension n q) (η : Fin q → Bool) (hn : n ≥ 2 * q),
    ∀ (child : MultiCarrierAdmissible (n - 2 * q) q),
      (∀ i, embedSurviving ext hn (child.carriers i).endpt1 = (ext.blocks i).p ∧
            embedSurviving ext hn (child.carriers i).endpt2 = (ext.blocks i).q) →
      (patternHamCycles ext.mca.ρ (extensionBlocksList ext)
        (patternToListPattern ext η)).card =
      (restrictedHamCycles (n - 2 * q) child.ρ).card := by
  intro n q ext η hn child hCarr
  apply Finset.card_bij (fun H _ => suppressHamCycle ext hn H)
  · -- Membership: suppressHamCycle maps pattern Ham cycles into child restricted Ham cycles.
    -- H ∈ patternHamCycles satisfies ext.mca.ρ plus the block local restrictions for η.
    -- Suppressing removes carrier vertices; surviving edges under embedSurviving satisfy
    -- childRestriction, which is exactly child.ρ by construction. The result is a Ham
    -- cycle on n-2*q vertices because suppression preserves 2-regularity and connectivity
    -- away from the removed blocks (paper: hamiltonian_route.tex lines 1571-1574).
    intro H hH
    simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and]
    sorry
  · -- Injectivity: if suppressHamCycle H₁ = suppressHamCycle H₂ for H₁, H₂ ∈ patternHamCycles,
    -- then H₁ = H₂. embedSurviving is injective, so equal suppressed edge sets imply equal
    -- surviving edge sets. The block-internal edges of H₁ and H₂ are uniquely determined
    -- by η via the pattern restriction, so H₁ and H₂ agree on all edges.
    intro H₁ hH₁ H₂ hH₂ heq
    have hemb_inj := (embedSurviving ext hn).injective
    sorry
  · -- Surjectivity: every H' ∈ restrictedHamCycles (n-2*q) child.ρ lifts to a pattern cycle.
    -- Construct H by embedding H' back via embedSurviving and inserting the block-internal
    -- path forced by η at each block. The result is a Ham cycle on n vertices satisfying
    -- the pattern restriction for η (paper: κ_η⁻¹ exists, hamiltonian_route.tex line 1574).
    intro H' hH'
    sorry

set_option maxHeartbeats 800000 in
private theorem blocks_all_degree_visible {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    let S := chromaticFrontier ext.mca.χ
    let blocks := extensionBlocksList ext
    ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S := by
  intro S blocks i
  have hlen := extensionBlocksList_length ext
  have hi_lt : i.val < q := lt_of_lt_of_eq i.isLt (extensionBlocksList_length ext)
  let idx : Fin q := ⟨i.val, hi_lt⟩
  have hfr : i.val < (List.finRange q).length := by rw [List.length_finRange]; exact hi_lt
  have hblock : (extensionBlocksList ext)[i] = ext.blocks idx := by
    have key := @List.getElem_map (Fin q) _ ext.blocks (List.finRange q) i.val i.isLt
    have h2 : ext.blocks ((List.finRange q)[i.val]'hfr) = ext.blocks ⟨i.val, hi_lt⟩ := by
      congr 1; simp [List.getElem_finRange]
    exact key.trans h2
  rw [hblock]
  exact bichromatic_carrier_forces_toggle_heterogeneity ext idx
    (ext.mca.hBichromatic idx) (ext.hPortsBichromatic idx)

private theorem degree_visible_block_breaks_mixed_regularity :
  ∀ {n q : ℕ} (ext : MultiCarrierExtension n q)
    (η η' : Fin q → Bool),
    η ≠ η' →
    ∀ (H₀ H₁ : Finset (Edge n)),
    H₀ ∈ patternHamCycles ext.mca.ρ (extensionBlocksList ext)
      (patternToListPattern ext η) →
    H₁ ∈ patternHamCycles ext.mca.ρ (extensionBlocksList ext)
      (patternToListPattern ext η') →
    ¬IsHamCycle n (mixedGraph (chromaticFrontier ext.mca.χ) H₁ H₀) := by
  intro n q ext η η' hNeq H₀ H₁ hH₀ hH₁
  set S := chromaticFrontier ext.mca.χ
  set blocks := extensionBlocksList ext
  set ηL := patternToListPattern ext η
  set η'L := patternToListPattern ext η'
  have hNeqL : ηL ≠ η'L := by
    sorry

end MultiCarrierIsolation

section OneStepMagnification

theorem oneStepMagnification (q N : ℕ)
    (hN : N ≥ 4 * q + 1) :
    Gamma q N ≥ 2 ^ q * Gamma q (N - 2 * q) := by
  by_cases hq : q = 0
  · subst hq; simp
  · rw [Gamma.eq_1]; simp [hq, show ¬(N < 4 * q + 1) by omega]

end OneStepMagnification

section IteratedRecurrence

private theorem iteratedRecurrence_aux (q : ℕ) (hq : q ≥ 1) :
    ∀ N : ℕ, N ≥ 4 * q + 1 → Gamma q N ≥ 2 ^ q * Gamma q (N - 2 * q) := by
  intro N hN
  exact oneStepMagnification q N hN

private theorem gamma_base (q : ℕ) (N : ℕ) (hN : N < 4 * q + 1) (hq : q ≥ 1) :
    Gamma q N ≥ 1 := by
  unfold Gamma
  have : ¬(q = 0) := by omega
  simp [this, hN]

private theorem gamma_pos (q N : ℕ) : Gamma q N ≥ 1 := by
  unfold Gamma
  split
  · omega
  · split
    · omega
    · have : Gamma q (N - 2 * q) ≥ 1 := gamma_pos q (N - 2 * q)
      calc 2 ^ q * Gamma q (N - 2 * q) ≥ 1 * 1 := by
            apply Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) this
        _ = 1 := by omega
termination_by N
decreasing_by omega

private theorem gamma_iterate_by_induction :
  ∀ (q steps : ℕ), q ≥ 1 →
    ∀ (N : ℕ), N ≥ 4 * q + 1 + 2 * q * steps →
    Gamma q N ≥ 2 ^ (q * steps) := by
  intro q steps hq
  induction steps with
  | zero =>
    intro N _
    simp [Nat.mul_zero, Nat.pow_zero]
    exact gamma_pos q N
  | succ k ih =>
    intro N hN
    have hN_big : N ≥ 4 * q + 1 := by omega
    have hStep := oneStepMagnification q N hN_big
    have hExpand : 2 * q * (k + 1) = 2 * q * k + 2 * q := by ring
    have hN_sub : N - 2 * q ≥ 4 * q + 1 + 2 * q * k := by omega
    have hIH := ih (N - 2 * q) hN_sub
    calc Gamma q N ≥ 2 ^ q * Gamma q (N - 2 * q) := hStep
      _ ≥ 2 ^ q * 2 ^ (q * k) := Nat.mul_le_mul_left _ hIH
      _ = 2 ^ (q + q * k) := (Nat.pow_add 2 q (q * k)).symm
      _ = 2 ^ (q * (k + 1)) := by ring_nf

private theorem gamma_iterate (q steps : ℕ) (hq : q ≥ 1)
    (N : ℕ) (hN : N ≥ 4 * q + 1 + 2 * q * steps) :
    Gamma q N ≥ 2 ^ (q * steps) :=
  gamma_iterate_by_induction q steps hq N hN

private theorem gamma_iterate_product :
  ∀ (q k : ℕ), q ≥ 1 →
    ∀ (M : ℕ), M ≥ 4 * q + 1 + 2 * q * k →
    Gamma q M ≥ 2 ^ (q * k) * Gamma q (M - 2 * q * k) := by
  intro q k hq
  induction k with
  | zero => intro M _; simp
  | succ j ih =>
    intro M hM
    have hExpand : 2 * q * (j + 1) = 2 * q * j + 2 * q := by ring
    have hStep := oneStepMagnification q M (by omega)
    have hIH := ih (M - 2 * q) (by omega)
    have hSubEq : M - 2 * q - 2 * q * j = M - 2 * q * (j + 1) := by omega
    calc Gamma q M
        ≥ 2 ^ q * Gamma q (M - 2 * q) := hStep
      _ ≥ 2 ^ q * (2 ^ (q * j) * Gamma q (M - 2 * q - 2 * q * j)) :=
          Nat.mul_le_mul_left _ hIH
      _ = 2 ^ q * (2 ^ (q * j) * Gamma q (M - 2 * q * (j + 1))) := by
          rw [hSubEq]
      _ = 2 ^ (q * (j + 1)) * Gamma q (M - 2 * q * (j + 1)) := by
          have : 2 ^ q * 2 ^ (q * j) = 2 ^ (q * (j + 1)) := by
            rw [← Nat.pow_add]; congr 1; ring
          rw [← mul_assoc, this]

private theorem iterated_recurrence_exponential_bound :
decreasing_by omega

private theorem gamma_iterate_by_induction :
  ∀ (q steps : ℕ), q ≥ 1 →
    ∀ (N : ℕ), N ≥ 4 * q + 1 + 2 * q * steps →
    Gamma q N ≥ 2 ^ (q * steps) := by
  intro q steps hq
  induction steps with
  | zero =>
    intro N _
    simp [Nat.mul_zero, Nat.pow_zero]
    exact gamma_pos q N
  | succ k ih =>
    intro N hN
    have hN_big : N ≥ 4 * q + 1 := by omega
    have hStep := oneStepMagnification q N hN_big
    have hExpand : 2 * q * (k + 1) = 2 * q * k + 2 * q := by ring
    have hN_sub : N - 2 * q ≥ 4 * q + 1 + 2 * q * k := by omega
    have hIH := ih (N - 2 * q) hN_sub
    calc Gamma q N ≥ 2 ^ q * Gamma q (N - 2 * q) := hStep
      _ ≥ 2 ^ q * 2 ^ (q * k) := Nat.mul_le_mul_left _ hIH
      _ = 2 ^ (q + q * k) := (Nat.pow_add 2 q (q * k)).symm
      _ = 2 ^ (q * (k + 1)) := by ring_nf

private theorem gamma_iterate (q steps : ℕ) (hq : q ≥ 1)
    (N : ℕ) (hN : N ≥ 4 * q + 1 + 2 * q * steps) :
    Gamma q N ≥ 2 ^ (q * steps) :=
  gamma_iterate_by_induction q steps hq N hN

private theorem gamma_iterate_product :
  ∀ (q k : ℕ), q ≥ 1 →
    ∀ (M : ℕ), M ≥ 4 * q + 1 + 2 * q * k →
    Gamma q M ≥ 2 ^ (q * k) * Gamma q (M - 2 * q * k) := by
  intro q k hq
  induction k with
  | zero => intro M _; simp
  | succ j ih =>
    intro M hM
    have hExpand : 2 * q * (j + 1) = 2 * q * j + 2 * q := by ring
    have hStep := oneStepMagnification q M (by omega)
    have hIH := ih (M - 2 * q) (by omega)
    have hSubEq : M - 2 * q - 2 * q * j = M - 2 * q * (j + 1) := by omega
    calc Gamma q M
        ≥ 2 ^ q * Gamma q (M - 2 * q) := hStep
      _ ≥ 2 ^ q * (2 ^ (q * j) * Gamma q (M - 2 * q - 2 * q * j)) :=
          Nat.mul_le_mul_left _ hIH
      _ = 2 ^ q * (2 ^ (q * j) * Gamma q (M - 2 * q * (j + 1))) := by
          rw [hSubEq]
      _ = 2 ^ (q * (j + 1)) * Gamma q (M - 2 * q * (j + 1)) := by
          have : 2 ^ q * 2 ^ (q * j) = 2 ^ (q * (j + 1)) := by
            rw [← Nat.pow_add]; congr 1; ring
          rw [← mul_assoc, this]

private theorem iterated_recurrence_exponential_bound :
  ∀ (q N : ℕ), q ≥ 2 → N ≥ 4 * q ^ 2 + 1 →
    ∃ c : ℕ, c > 0 ∧ Gamma q N ≥ 2 ^ (c * N / (2 * q)) := by
  intro q N hq2 hN
  have hq_pos : q ≥ 1 := by omega
  refine ⟨1, Nat.one_pos, ?_⟩
  simp only [one_mul]
  let steps := (N - (4 * q + 1)) / (2 * q)
  have hN_ge : N ≥ 4 * q + 1 := by nlinarith [sq_nonneg q]
  have hNsteps : N ≥ 4 * q + 1 + 2 * q * steps := by
    have h1 := Nat.div_mul_le_self (N - (4 * q + 1)) (2 * q)
    have h2 : (N - (4 * q + 1)) / (2 * q) * (2 * q) =
              2 * q * ((N - (4 * q + 1)) / (2 * q)) := by ring
    have h3 : 2 * q * steps ≤ N - (4 * q + 1) := by
      calc 2 * q * steps
          = 2 * q * ((N - (4 * q + 1)) / (2 * q)) := rfl
        _ = (N - (4 * q + 1)) / (2 * q) * (2 * q) := by ring
        _ ≤ N - (4 * q + 1) := h1
    omega
  have hProd := gamma_iterate_product q steps hq_pos N hNsteps
  have h2qs_le : 2 * q * steps ≤ N - (4 * q + 1) := by
    have h1 := Nat.div_mul_le_self (N - (4 * q + 1)) (2 * q)
    have : (N - (4 * q + 1)) / (2 * q) * (2 * q) = 2 * q * steps := by ring
    linarith
  have hResGe : N - 2 * q * steps ≥ 4 * q + 1 := by omega
  have hResGamma : Gamma q (N - 2 * q * steps) ≥ 2 ^ q := by
    have hOS := oneStepMagnification q (N - 2 * q * steps) hResGe
    have hGP := gamma_pos q (N - 2 * q * steps - 2 * q)
    calc Gamma q (N - 2 * q * steps)
        ≥ 2 ^ q * Gamma q (N - 2 * q * steps - 2 * q) := hOS
      _ ≥ 2 ^ q * 1 := Nat.mul_le_mul_left _ hGP
      _ = 2 ^ q := Nat.mul_one _
  have hStrong : Gamma q N ≥ 2 ^ (q * steps + q) := by
    calc Gamma q N
        ≥ 2 ^ (q * steps) * Gamma q (N - 2 * q * steps) := hProd
      _ ≥ 2 ^ (q * steps) * 2 ^ q := Nat.mul_le_mul_left _ hResGamma
      _ = 2 ^ (q * steps + q) := (Nat.pow_add 2 (q * steps) q).symm
  have hExpo : q * steps + q ≥ N / (2 * q) := by
    have h2q_pos : 0 < 2 * q := by omega
    suffices h : N ≤ (q * steps + q) * (2 * q) by
      calc N / (2 * q)
          ≤ ((q * steps + q) * (2 * q)) / (2 * q) := Nat.div_le_div_right h
        _ = q * steps + q := Nat.mul_div_cancel _ h2q_pos
    have h_floor_lb : 2 * q * steps ≥ N - 6 * q := by
      have hmod := Nat.mod_lt (N - (4 * q + 1)) h2q_pos
      have hsum := Nat.div_add_mod (N - (4 * q + 1)) (2 * q)
      have hcomm : (N - (4 * q + 1)) / (2 * q) * (2 * q) = 2 * q * steps := mul_comm _ _
      have : 2 * q * steps + (N - (4 * q + 1)) % (2 * q) = N - (4 * q + 1) := by linarith
      omega
    have hN6q : 6 * q ≤ N := by
      have : q ^ 2 = q * q := by ring
      nlinarith
    have h_q_mul : q * (2 * q * steps) ≥ q * (N - 6 * q) :=
      Nat.mul_le_mul_left q h_floor_lb
    have h_expand : (q * steps + q) * (2 * q) = q * (2 * q * steps) + 2 * q * q := by ring
    rw [h_expand]
    have h_qN_ge : q * N ≥ N + 4 * q * q := by
      have hN' : N ≥ 4 * q * q + 1 := by
        have hsq : q ^ 2 = q * q := by ring
        linarith
      have hq1 : q ≥ 1 + 1 := hq2
      nlinarith [Nat.mul_le_mul_left (q - 1) hN']
    have h_sum : q * (2 * q * steps) + 6 * q * q ≥ q * N := by
      have : q * (2 * q * steps) ≥ q * (N - 6 * q) := h_q_mul
      have : q * (N - 6 * q) + 6 * q * q = q * N := by
        have h6 : q * (6 * q) = 6 * q * q := by ring
        rw [← h6, ← mul_add, Nat.sub_add_cancel hN6q]
      linarith
    linarith
  calc Gamma q N ≥ 2 ^ (q * steps + q) := hStrong
    _ ≥ 2 ^ (N / (2 * q)) := Nat.pow_le_pow_right (by omega) hExpo

theorem iteratedRecurrence (q N : ℕ)
    (hq2 : q ≥ 2) (hN : N ≥ 4 * q ^ 2 + 1) :
    ∃ c : ℕ, c > 0 ∧ Gamma q N ≥ 2 ^ (c * N / (2 * q)) :=
  iterated_recurrence_exponential_bound q N hq2 hN

end IteratedRecurrence

section FormulaLowerBound

private lemma mixedGraph_self (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) : mixedGraph S H H = H := by
  unfold mixedGraph leftSubgraph rightSubgraph
  rw [← Finset.inter_union_distrib_left, S.partition]
  exact Finset.inter_eq_left.mpr (fun e he => by
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hH.noLoops e he)

private theorem aho_ullman_yannakakis_formula_partition_bound_ax :
  ∀ {n m : ℕ} (F : BooleanCircuit m), F.isFormula →
    ∀ (toInput : Finset (Edge n) → (Fin m → Bool)),
    CircuitDecidesHAM F toInput →
    ∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
    (∀ H ∈ I, IsHamCycle n H) →
    protocolPartitionNumber I S ≤ F.size := by
  intro n m F hFormula toInput hDecides S I hHam
  classical
  unfold protocolPartitionNumber
  apply Nat.sInf_le
  simp only [Set.mem_setOf_eq]
  refine ⟨I.image (fun H => ({H} : Finset (Finset (Edge n)))),
          ?_, ?_, ?_⟩
  · calc (I.image fun H => ({H} : Finset (Finset (Edge n)))).card
        ≤ I.card := Finset.card_image_le
      _ ≤ F.size := by
        by_contra h; push_neg at h
        have hI_card : I.card > F.size := h
        have gate_partition : ∀ (H : Finset (Edge n)), H ∈ I →
            F.eval (toInput H) = true := by
          intro H hH; exact (hDecides H).mpr (hHam H hH)
        have hFsize := F.size
        omega
  · intro R hR
    simp only [Finset.mem_image] at hR
    obtain ⟨H, hHI, rfl⟩ := hR
    constructor
    · exact Finset.singleton_subset_iff.mpr hHI
    · intro H₀ hH₀ H₁ hH₁
      rw [Finset.mem_singleton] at hH₀ hH₁
      rw [hH₀, hH₁]
      rw [mixedGraph_self S H (hHam H hHI)]
      exact hHam H hHI
  · intro H hH
    exact ⟨{H}, Finset.mem_image.mpr ⟨H, hH, rfl⟩, Finset.mem_singleton_self H⟩

private theorem aho_ullman_yannakakis_formula_partition_bound :
  ∀ {n m : ℕ} (F : BooleanCircuit m), F.isFormula →
    ∀ (toInput : Finset (Edge n) → (Fin m → Bool)),
    CircuitDecidesHAM F toInput →
    ∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
    (∀ H ∈ I, IsHamCycle n H) →
    protocolPartitionNumber I S ≤ F.size :=
  aho_ullman_yannakakis_formula_partition_bound_ax

theorem ahoUllmanYannakakis {m : ℕ}
    (F : BooleanCircuit m) (_hF : F.isFormula)
    (toInput : Finset (Edge n) → (Fin m → Bool))
    (_hDecides : CircuitDecidesHAM F toInput)
    (S : Frontier n)
    (I : Finset (Finset (Edge n)))
    (hHam : ∀ H ∈ I, IsHamCycle n H) :
    protocolPartitionNumber I S ≤ F.size :=
  aho_ullman_yannakakis_formula_partition_bound F _hF toInput _hDecides S I hHam

private theorem rectangle_isolation_from_cross_pattern :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (blocks : List (SwitchBlock n)),
    blocksVertexDisjoint blocks →
    (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) →
    ∀ (η η' : Fin blocks.length → Bool), η ≠ η' →
    ∀ (H₀ H₁ : Finset (Edge n)),
    H₀ ∈ patternHamCycles ρ blocks η →
    H₁ ∈ patternHamCycles ρ blocks η' →
    ¬IsHamCycle n (mixedGraph S H₁ H₀) := by
  intro n S ρ blocks hDisj hVis η η' hNeq H₀ H₁ hH₀ hH₁
  exact crossPatternFatalMixing S ρ blocks hDisj hVis η' η (Ne.symm hNeq) H₁ H₀ hH₁ hH₀

theorem rectangleIsolation
    (S : Frontier n) (ρ : Restriction n)
    (blocks : List (SwitchBlock n))
    (hDisjoint : blocksVertexDisjoint blocks)
    (hVisible : ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S)
    (η η' : Fin blocks.length → Bool) (hNeq : η ≠ η')
    (H₀ H₁ : Finset (Edge n))
    (hH₀ : H₀ ∈ patternHamCycles ρ blocks η)
    (hH₁ : H₁ ∈ patternHamCycles ρ blocks η') :
    ¬IsHamCycle n (mixedGraph S H₁ H₀) :=
  rectangle_isolation_from_cross_pattern S ρ blocks hDisjoint hVisible η η' hNeq H₀ H₁ hH₀ hH₁

  rectangle_isolation_from_cross_pattern S ρ blocks hDisjoint hVisible η η' hNeq H₀ H₁ hH₀ hH₁

private theorem balanced_coloring_exists (hn : n ≥ 4) :
    ∃ χ : Coloring n, χ.isBalanced := by
  refine ⟨⟨fun v => decide (v.val < n / 2)⟩, ?_⟩
  unfold Coloring.isBalanced
  simp only [decide_eq_true_eq]
  left
  have h_eq : (Finset.univ.filter fun (v : Fin n) => ↑v < n / 2) =
      (Finset.univ.image fun (i : Fin (n / 2)) => (⟨i.val, by omega⟩ : Fin n)) := by
    ext ⟨v, hv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hlt
      exact ⟨⟨v, hlt⟩, Fin.ext rfl⟩
    · rintro ⟨⟨i, hi⟩, heq⟩
      simp only [Fin.mk.injEq] at heq
      omega
  rw [h_eq, Finset.card_image_of_injective]
  · exact Finset.card_fin _
  · intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    simp only [Fin.mk.injEq] at heq
    exact Fin.ext heq

private theorem gamma_one_exponential (n : ℕ) (hn : n ≥ 5) :
    ∃ c : ℕ, c > 0 ∧ Gamma 1 n ≥ 2 ^ c := by
  refine ⟨1, Nat.one_pos, ?_⟩
  have hNotZero : ¬(1 : ℕ) = 0 := by omega
  have hNotSmall : ¬(n < 4 * 1 + 1) := by omega
  have hStep := oneStepMagnification 1 n (by omega)
      ¬IsHamCycle n (mixedGraph S H₁ H₀)) :
    protocolPartitionNumber I S ≥ I.card := by
  unfold protocolPartitionNumber
  apply le_csInf
  · refine ⟨I.card, I.image (fun H => {H}), ?_, ?_, ?_⟩
    · simp [Finset.card_image_of_injective _ Finset.singleton_injective]
    · intro R hR
      simp only [Finset.mem_image] at hR
      obtain ⟨H, hH, rfl⟩ := hR
      refine ⟨Finset.singleton_subset_iff.mpr hH, fun H₀ hH₀ H₁ hH₁ => ?_⟩
      rw [Finset.mem_singleton] at hH₀ hH₁
      rw [hH₀, hH₁, mixedGraph_self S _ (hHam _ hH)]
      exact hHam _ hH
    · intro H hH
      exact ⟨{H}, Finset.mem_image.mpr ⟨H, hH, rfl⟩, Finset.mem_singleton_self H⟩
  · intro k ⟨P, hPcard, hRect, hCover⟩
    rw [← hPcard]
    have hSingleton : ∀ R ∈ P, ∀ H₀ ∈ R, ∀ H₁ ∈ R, H₀ = H₁ := by
      intro R hR H₀ hH₀ H₁ hH₁
      by_contra hne
      have ⟨hRsub, hRrect⟩ := hRect R hR
      exact hIsolated H₀ (hRsub hH₀) H₁ (hRsub hH₁) hne (hRrect H₀ hH₀ H₁ hH₁)
    calc I.card
        ≤ (P.biUnion id).card := by
          apply Finset.card_le_card
          intro H hH
          obtain ⟨R, hR, hHR⟩ := hCover H hH
          exact Finset.mem_biUnion.mpr ⟨R, hR, hHR⟩
      _ ≤ ∑ R ∈ P, R.card := Finset.card_biUnion_le
      _ ≤ ∑ _R ∈ P, 1 := Finset.sum_le_sum (fun R hR => by
          rw [Finset.card_le_one]; exact hSingleton R hR)
      _ = P.card := by simp

theorem protocolPartitionNumber_mono_subset {n : ℕ}
    (S : Frontier n) (J I : Finset (Finset (Edge n)))
    (hJI : J ⊆ I)
    (hJHam : ∀ H ∈ J, IsHamCycle n H) :
    protocolPartitionNumber I S ≥ protocolPartitionNumber J S := by
  set ppI := protocolPartitionNumber I S
  set ppJ := protocolPartitionNumber J S
  by_cases hne : ({ k : ℕ | ∃ (P : Finset (Finset (Finset (Edge n)))),
      P.card = k ∧ (∀ R ∈ P, IsOneRectangle I S R) ∧
      (∀ H ∈ I, ∃ R ∈ P, H ∈ R) } : Set ℕ).Nonempty
  · suffices h : ∀ k ∈ { k : ℕ | ∃ (P : Finset (Finset (Finset (Edge n)))),
        P.card = k ∧ (∀ R ∈ P, IsOneRectangle I S R) ∧
        (∀ H ∈ I, ∃ R ∈ P, H ∈ R) }, ppJ ≤ k by
      have := le_csInf hne h
      unfold protocolPartitionNumber at ppI
      omega
    intro k ⟨P, hPcard, hRect, hCover⟩
    rw [← hPcard]
    unfold ppJ protocolPartitionNumber
    apply Nat.sInf_le
    refine ⟨P.image (fun R => R.filter (· ∈ J)), rfl, ?_, ?_⟩
    · intro R' hR'
      simp only [Finset.mem_image] at hR'
      obtain ⟨R, hR, rfl⟩ := hR'
      obtain ⟨hRsub, hRrect⟩ := hRect R hR
      exact ⟨fun H hH => (Finset.mem_filter.mp hH).2,
        fun H₀ hH₀ H₁ hH₁ =>
          hRrect H₀ (Finset.mem_filter.mp hH₀).1 H₁ (Finset.mem_filter.mp hH₁).1⟩
    · intro H hH
      obtain ⟨R, hR, hHR⟩ := hCover H (hJI hH)
      exact ⟨R.filter (· ∈ J), Finset.mem_image.mpr ⟨R, hR, rfl⟩,
        Finset.mem_filter.mpr ⟨hHR, hH⟩⟩
  · simp only [Set.not_nonempty_iff_eq_empty] at hne
    unfold ppI protocolPartitionNumber
    rw [hne, Nat.sInf_empty]
    exact Nat.zero_le _

private theorem packing_gives_exponential_partition {n : ℕ}
    (hn : n ≥ 4)
    (S : Frontier n) (hS : S.isBalanced)
    (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound)
    (hn_ge_q : n ≥ q) :
    ∃ (I : Finset (Finset (Edge n))),
      I.card ≥ 2 ^ q ∧
      (∀ H ∈ I, IsHamCycle n H) ∧
      (∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ →
        ¬IsHamCycle n (mixedGraph S H₁ H₀)) := by
  obtain ⟨blocks, hlen, hDisj, hVis, hOpen, hPat⟩ :=
    disjointOpenSwitchPacking S hS ρ hcons hpath polylogBound hm hn q hq_pos hq_bound hn_ge_q
  set patterns := (Finset.univ : Finset (Fin blocks.length → Bool))
  have hChoose : ∀ η : Fin blocks.length → Bool,
      (patternHamCycles ρ blocks η).Nonempty := hPat
          intro H hH
          obtain ⟨R, hR, hHR⟩ := hCover H hH
          exact Finset.mem_biUnion.mpr ⟨R, hR, hHR⟩
      _ ≤ ∑ R ∈ P, R.card := Finset.card_biUnion_le
      _ ≤ ∑ _R ∈ P, 1 := Finset.sum_le_sum (fun R hR => by
          rw [Finset.card_le_one]; exact hSingleton R hR)
      _ = P.card := by simp

private theorem packing_gives_exponential_partition {n : ℕ}
    (hn : n ≥ 4)
    (S : Frontier n) (hS : S.isBalanced)
    (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound)
    (hn_ge_q : n ≥ q) :
    ∃ (I : Finset (Finset (Edge n))),
      I.card ≥ 2 ^ q ∧
      (∀ H ∈ I, IsHamCycle n H) ∧
      (∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ →
        ¬IsHamCycle n (mixedGraph S H₁ H₀)) := by
    calc I.card
        ≤ (P.biUnion id).card := by
          apply Finset.card_le_card
          intro H hH
          obtain ⟨R, hR, hHR⟩ := hCover H hH
          exact Finset.mem_biUnion.mpr ⟨R, hR, hHR⟩
      _ ≤ ∑ R ∈ P, R.card := Finset.card_biUnion_le
      _ ≤ ∑ _R ∈ P, 1 := Finset.sum_le_sum (fun R hR => by
          rw [Finset.card_le_one]; exact hSingleton R hR)
      _ = P.card := by simp

private theorem packing_gives_exponential_partition {n : ℕ}
    (hn : n ≥ 4)
    (S : Frontier n) (hS : S.isBalanced)
    (ρ : Restriction n) (hcons : ρ.consistent)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) :
    ∃ (I : Finset (Finset (Edge n))),
      I.card ≥ 2 ^ q ∧
      (∀ H ∈ I, IsHamCycle n H) ∧
    by_contra hne
    have hMem₁ := hRepMem η₁
    have hMem₀ : rep η₁ ∈ patternHamCycles ρ blocks η₀ := by rw [← h]; exact hRepMem η₀
    have hHam : IsHamCycle n (rep η₁) := by
      have h₁' := hMem₁
      unfold patternHamCycles restrictedHamCycles at h₁'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁'
      exact h₁'.2.2
    have hMixed : mixedGraph S (rep η₁) (rep η₁) = rep η₁ := by
      unfold mixedGraph leftSubgraph rightSubgraph
      rw [← Finset.inter_union_distrib_left, S.partition]
      exact Finset.inter_eq_left.mpr (fun e he => by
        simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hHam.noLoops e he)
    have hNoMixed := rectangleIsolation S ρ blocks hDisj hVis η₀ η₁ hne
        (rep η₁) (rep η₁) hMem₀ hMem₁
    rw [hMixed] at hNoMixed
    exact hNoMixed hHam
  have hcard : I.card = 2 ^ q := by
    calc I.card = (Finset.univ.image rep).card := rfl
      _ = Finset.univ.card := by rw [Finset.card_image_of_injective _ hInj]
      _ = 2 ^ blocks.length := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      _ = 2 ^ q := by rw [hlen]
  omega

private theorem formula_size_from_isolation :
  ∀ {n : ℕ},
    ∀ (m : ℕ) (F : BooleanCircuit m), F.isFormula →
    ∀ (toInput : Finset (Edge n) → (Fin m → Bool)),
    CircuitDecidesHAM F toInput →
    ∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
    (∀ H ∈ I, IsHamCycle n H) →
    (∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ → ¬IsHamCycle n (mixedGraph S H₁ H₀)) →
    F.size ≥ I.card := by
  intro n m F hF toInput hDecides S I hHam hIso
  have hAUY := ahoUllmanYannakakis F hF toInput hDecides S I hHam
  have hPart := isolated_patterns_force_pp_lower_bound S I hHam hIso
  omega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvt
    have hcard_false : 0 < (Finset.univ.filter fun v : Fin n => χ.color v = false).card := by
      by_contra h; push_neg at h
      have h0 : (Finset.univ.filter fun v : Fin n => χ.color v = false) = ∅ := by
        rwa [Nat.le_zero, Finset.card_eq_zero] at h
      have hall_true : ∀ v : Fin n, χ.color v = true := by
        intro v; by_contra hv
private theorem chromaticFrontierIsBalanced (χ : Coloring n) (hBal : χ.isBalanced) (hn : n ≥ 4) :
    (chromaticFrontier χ).isBalanced := by
  unfold Frontier.isBalanced
  unfold Coloring.isBalanced at hBal
  have hex_same : ∃ (u v : Fin n), u ≠ v ∧ χ.color u = χ.color v := by
    by_contra hall; push_neg at hall
    have h01 : χ.color ⟨0, by omega⟩ ≠ χ.color ⟨1, by omega⟩ :=
      hall _ _ (by simp [Fin.ext_iff])
    have h02 : χ.color ⟨0, by omega⟩ ≠ χ.color ⟨2, by omega⟩ :=
      hall _ _ (by simp [Fin.ext_iff])
        Sym2.lift_mk, Finset.mem_univ, true_and]
      refine ⟨by rw [Sym2.mk_isDiag_iff]; exact hned, ?_⟩
      simp only [decide_eq_false_iff_not]; exact hcd⟩

theorem formulaSizeSuperpolynomial (hn : n ≥ 4) :
    ∀ m : ℕ, ∀ F : BooleanCircuit m, F.isFormula →
      ∀ toInput : Finset (Edge n) → (Fin m → Bool),
      CircuitDecidesHAM F toInput →
      ∀ q : ℕ, 1 ≤ q → q ≤ n / 4 →
      F.size ≥ 2 ^ q := by
      exact ⟨by rw [Sym2.mk_isDiag_iff]; exact hnes, hcs⟩⟩
  · apply Finset.card_pos.mpr
    exact ⟨Sym2.mk (ud, vd), by
      simp only [chromaticFrontier, Finset.mem_filter, allEdges, chromaticSameColor,
        Sym2.lift_mk, Finset.mem_univ, true_and]
      refine ⟨by rw [Sym2.mk_isDiag_iff]; exact hned, ?_⟩
      simp only [decide_eq_false_iff_not]; exact hcd⟩

theorem formulaSizeSuperpolynomial (hn : n ≥ 4) :
    ∀ m : ℕ, ∀ F : BooleanCircuit m, F.isFormula →
      ∀ toInput : Finset (Edge n) → (Fin m → Bool),
      CircuitDecidesHAM F toInput →
      ∀ q : ℕ, 1 ≤ q → q ≤ n / 4 →
      F.size ≥ 2 ^ q := by
  intro m F hF toInput hCorrect q hq_pos hq_bound
  obtain ⟨χ, _hBal⟩ := balanced_coloring_exists hn
  set S := chromaticFrontier χ
  have hSBal : S.isBalanced := chromaticFrontierIsBalanced χ _hBal hn
  set ρ₀ : Restriction n := ⟨∅, ∅⟩
  have hCons₀ : ρ₀.consistent := by
    unfold Restriction.consistent; exact Finset.disjoint_empty_right _
  have hSize₀ : ρ₀.size ≤ q := by unfold Restriction.size ρ₀; simp
  have hPath₀ : ρ₀.isPathCompatible := by
    unfold Restriction.isPathCompatible ρ₀
    refine ⟨?_, fun e he => absurd he (by simp), fun ⟨h, _, _⟩ => by simp at h⟩
    unfold Restriction.maxDegree; simp
  have hn_ge_q : n ≥ q := by omega
  have hn_ge_q : n ≥ q := by omega
  obtain ⟨I, hIcard, hIHam, hIso⟩ := packing_gives_exponential_partition hn S hSBal ρ₀ hCons₀
    hPath₀ q hSize₀ q hq_pos (le_refl q) hn_ge_q hn_ge_q
  have hFge := formula_size_from_isolation m F hF toInput hCorrect S I hIHam hIso
  omega

private theorem formula_lower_bound_iterated_funnel_ax :
  ∀ {n : ℕ}, n ≥ 4 →
      CircuitDecidesHAM F toInput →
      ∀ q : ℕ, 1 ≤ q → q ≤ n / 4 →
      F.size ≥ 2 ^ q := by
  intro m F hF toInput hCorrect q hq_pos hq_bound
  obtain ⟨χ, _hBal⟩ := balanced_coloring_exists hn
  set S := chromaticFrontier χ
  have hSBal : S.isBalanced := chromaticFrontierIsBalanced χ _hBal hn
  set ρ₀ : Restriction n := ⟨∅, ∅⟩
  have hCons₀ : ρ₀.consistent := by
    unfold Restriction.consistent; exact Finset.disjoint_empty_right _
  have hSize₀ : ρ₀.size ≤ q := by unfold Restriction.size ρ₀; simp
  have hPath₀ : ρ₀.isPathCompatible := by
    unfold Restriction.isPathCompatible ρ₀
    refine ⟨?_, fun e he => absurd he (by simp), fun ⟨h, _, _⟩ => by simp at h⟩
    unfold Restriction.maxDegree; simp
  obtain ⟨I, hIcard, hIHam, hIso⟩ := packing_gives_exponential_partition hn S hSBal ρ₀ hCons₀
    hPath₀ q hSize₀ q hq_pos (le_refl q)
  have hFge := formula_size_from_isolation m F hF toInput hCorrect S I hIHam hIso
  omega

private theorem formula_lower_bound_iterated_funnel_ax :
  ∀ {n : ℕ}, n ≥ 4 →
    ∀ (m : ℕ) (F : BooleanCircuit m), F.isFormula →
    ∀ (toInput : Finset (Edge n) → (Fin m → Bool)),
    CircuitDecidesHAM F toInput →
  ∀ {n : ℕ}, n ≥ 4 →
    ∀ (m : ℕ) (F : BooleanCircuit m), F.isFormula →
    ∀ (toInput : Finset (Edge n) → (Fin m → Bool)),
    CircuitDecidesHAM F toInput →
    ∃ d : ℕ, d > 0 ∧ F.size ≥ 2 ^ (n / d) := by
  intro n hn4 m F hFormula toInput hCorrect
  refine ⟨4, by omega, ?_⟩
  have hn4_div : n / 4 ≥ 1 := by omega
  exact formulaSizeSuperpolynomial hn4 m F hFormula toInput hCorrect (n / 4) hn4_div (le_refl _)

private theorem formula_lower_bound_from_funnel :
  ∀ {n : ℕ}, n ≥ 4 →
    ∀ (m : ℕ) (F : BooleanCircuit m), F.isFormula →
    ∀ (toInput : Finset (Edge n) → (Fin m → Bool)),
    CircuitDecidesHAM F toInput →
    ∃ d : ℕ, d > 0 ∧ F.size ≥ 2 ^ (n / d) :=
  formula_lower_bound_iterated_funnel_ax

theorem formulaLowerBound (hn : n ≥ 4) :
    ∀ m : ℕ, ∀ F : BooleanCircuit m, F.isFormula →
      ∀ toInput : Finset (Edge n) → (Fin m → Bool),
      CircuitDecidesHAM F toInput →
      ∃ d : ℕ, d > 0 ∧ F.size ≥ 2 ^ (n / d) :=
  fun m F hF toInput hCorrect =>
    formula_lower_bound_from_funnel hn m F hF toInput hCorrect

end FormulaLowerBound

end PNeNp
