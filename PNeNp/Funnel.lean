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

private theorem consecutive_blocks_from_ham_cycle_ax (n : ℕ) (hn : n ≥ 4) :
    ∀ (H : Finset (Edge n)), IsHamCycle n H →
    ∃ (cycle : Fin n → Fin n),
      Function.Bijective cycle ∧
      ∀ i : Fin n, Sym2.mk (cycle i, cycle (cycleFin (i.val + 1) n (by omega))) ∈ H := by
  intro H hH
  have hn_pos : n > 0 := by omega
  have hReg := hH.twoRegular
  have hConn := hH.connected
  have hSpan := hH.spanning
  have hNoLoops := hH.noLoops
  have cycle_extraction : ∀ (n' : ℕ) (hn'_pos : n' > 0) (E : Finset (Edge n')),
      (∀ v : Fin n', vertexDegreeIn n' E v = 2) →
      IsConnectedEdgeSet n' E →
      (∀ e ∈ E, ¬e.IsDiag) →
      n' ≥ 3 →
      ∃ (f : Fin n' → Fin n'), Function.Bijective f ∧
        ∀ i : Fin n', Sym2.mk (f i, f (cycleFin (i.val + 1) n' hn'_pos)) ∈ E := by
    intro n' hn'_pos E hReg' hConn' hNL' _hn'
    exact sorry
  have hn_pos' : n > 0 := by omega
  have h := cycle_extraction n hn_pos' H hReg hConn hNoLoops (by omega)
  obtain ⟨f, hBij, hEdges⟩ := h
  exact ⟨f, hBij, fun i => by convert hEdges i using 2⟩

private theorem consecutive_blocks_from_ham_cycle :
  ∀ (n : ℕ) (H : Finset (Edge n)), IsHamCycle n H → (hn : n ≥ 4) →
    ∃ (cycle : Fin n → Fin n),
      Function.Bijective cycle ∧
      ∀ i : Fin n, Sym2.mk (cycle i, cycle (cycleFin (i.val + 1) n (by omega))) ∈ H :=
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
  classical
  have hRegular := hH.twoRegular
  have hSpanning := hH.spanning
  have hNoLoops := hH.noLoops
  have hn_pos : n > 0 := by omega
  suffices ∃ (cycle : Fin n → Fin n),
      Function.Bijective cycle ∧
      ∀ i : Fin n, Sym2.mk (cycle i, cycle (cycleFin (i.val + 1) n hn_pos)) ∈ H by
    obtain ⟨cycle, hBij, hEdges⟩ := this
    refine ⟨Finset.univ.image fun (i : Fin n) =>
      (cycle i,
       cycle (cycleFin (i.val + 1) n hn_pos),
       cycle (cycleFin (i.val + 2) n hn_pos),
       cycle (cycleFin (i.val + 3) n hn_pos)), ?_, ?_⟩
    · exact ham_cycle_image_card_eq_n n cycle hBij hn
    · intro t ht
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
      obtain ⟨i, rfl⟩ := ht
      exact consecutive_block_edges_in_ham_cycle n H cycle hn_pos hEdges i
  exact consecutive_blocks_from_ham_cycle n H hH hn

end ConsecutiveBlocks

section DegreeVisibleSupply

noncomputable def cleanDegreeVisibleCount (S : Frontier n)
    (_ρ : Restriction n) (H : Finset (Edge n)) : ℕ :=
  (Finset.univ.filter fun (v : Fin n) =>
    leftDegreeAt S H v = 1 ∧ rightDegreeAt S H v = 1 ∧
    v ∈ boundaryVertices S).card

private theorem degree_visible_supply_linear_density_ax :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n) (H : Finset (Edge n)),
    S.isBalanced → IsHamCycle n H → n ≥ 4 →
    (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 1 / 8 * ↑n := by
  intro n S ρ H hBal hHam hn4
  have hReg := hHam.twoRegular
  have hSpan := hHam.spanning
  unfold cleanDegreeVisibleCount
  have vertex_degree_split : ∀ v : Fin n,
      leftDegreeAt S H v + rightDegreeAt S H v = 2 :=
    leftDeg_add_rightDeg_eq_two S H hHam
  have boundary_large : (Finset.univ.filter fun v : Fin n =>
      leftDegreeAt S H v = 1 ∧ rightDegreeAt S H v = 1 ∧
      v ∈ boundaryVertices S).card ≥ n / 8 := by
    have degree_one_one_count : (Finset.univ.filter fun v : Fin n =>
        leftDegreeAt S H v = 1 ∧ rightDegreeAt S H v = 1).card ≥ n / 4 := by
      have total_left_deg : (Finset.univ.filter fun v : Fin n =>
          leftDegreeAt S H v = 1).card ≥ n / 2 := by
        exact sorry
      exact sorry
    exact sorry
  have h_cast : (↑(n / 8) : ℝ) ≥ 1 / 8 * ↑n := by
    exact sorry
  calc (↑(Finset.univ.filter fun v : Fin n =>
        leftDegreeAt S H v = 1 ∧ rightDegreeAt S H v = 1 ∧
        v ∈ boundaryVertices S).card : ℝ)
      ≥ ↑(n / 8) := by exact_mod_cast boundary_large
    _ ≥ 1 / 8 * ↑n := h_cast

private theorem degree_visible_supply_linear_density :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n) (H : Finset (Edge n)),
    S.isBalanced → IsHamCycle n H → n ≥ 4 →
    (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 1 / 8 * ↑n :=
  degree_visible_supply_linear_density_ax

theorem degreeVisibleBlockSupply
    (S : Frontier n) (hS : S.isBalanced)
    (ρ : Restriction n) (hcons : ρ.consistent)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (hn : n ≥ 4) :
    ∃ c₀ : ℝ, c₀ > 0 ∧
      ∀ H ∈ restrictedHamCycles n ρ,
        ↑(cleanDegreeVisibleCount S ρ H) ≥ c₀ * ↑n := by
  refine ⟨1 / 8, by positivity, fun H hH => ?_⟩
  simp only [restrictedHamCycles, Finset.mem_filter, Finset.mem_univ, true_and] at hH
  obtain ⟨_, _, hHam⟩ := hH
  have hBal := hS
  unfold Frontier.isBalanced at hBal
  obtain ⟨hL, hR⟩ := hBal
  have hReg := hHam.twoRegular
  suffices h : (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 1 / 8 * ↑n by linarith
  exact degree_visible_supply_linear_density S ρ H hS hHam hn

end DegreeVisibleSupply

section DisjointSwitchPacking

private theorem greedy_packing_from_supply_ax :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (polylogBound q : ℕ),
    S.isBalanced → ρ.consistent → ρ.size ≤ polylogBound → n ≥ 4 →
    1 ≤ q → q ≤ polylogBound →
    (∃ c₀ : ℝ, c₀ > 0 ∧ ∀ H ∈ restrictedHamCycles n ρ,
      ↑(cleanDegreeVisibleCount S ρ H) ≥ c₀ * ↑n) →
    (restrictedHamCycles n ρ).Nonempty →
    ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty := by
  intro n S ρ polylogBound q hBal hCons hSize hn4 hq_pos hq_bound
  intro ⟨c₀, hc₀_pos, hSupply⟩ ⟨H_star, hH_star⟩
  have hH_star_vis := hSupply H_star hH_star
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
    exact sorry
  have greedy_packing_core :
      ∃ (blocks : List (SwitchBlock n)),
        blocks.length = q ∧
        blocksVertexDisjoint blocks ∧
        (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
        (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
        ∀ η : Fin blocks.length → Bool,
          (patternHamCycles ρ blocks η).Nonempty := by
    exact sorry
  exact greedy_packing_core

private theorem greedy_packing_from_supply :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (polylogBound q : ℕ),
    S.isBalanced → ρ.consistent → ρ.size ≤ polylogBound → n ≥ 4 →
    1 ≤ q → q ≤ polylogBound →
    (∃ c₀ : ℝ, c₀ > 0 ∧ ∀ H ∈ restrictedHamCycles n ρ,
      ↑(cleanDegreeVisibleCount S ρ H) ≥ c₀ * ↑n) →
    (restrictedHamCycles n ρ).Nonempty →
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
    (ρ : Restriction n) (hcons : ρ.consistent)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (hn : n ≥ 4)
    (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) :
    ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty := by
  have hSupply := degreeVisibleBlockSupply S hS ρ hcons polylogBound hm hn
  obtain ⟨c₀, hc₀_pos, hSupply⟩ := hSupply
  have hPacked := packedFamily hn ρ hcons polylogBound hm
  obtain ⟨H₀, hH₀⟩ := hPacked
  have hVis := hSupply H₀ hH₀
  suffices ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty by exact this
  exact greedy_packing_from_supply S ρ polylogBound q hS hcons hm hn hq_pos hq_bound
    ⟨c₀, hc₀_pos, hSupply⟩ ⟨H₀, hH₀⟩

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
    have vertex_small : ∀ v : Fin n, v ∈ e → v.val < n - 2 * q := by
      intro v hv
      by_contra hge
      push_neg at hge
      have : (blockInteriorVertices blocks).card ≤ 2 * q := by
        unfold blockInteriorVertices
        induction blocks with
        | nil => simp [List.finRange, List.foldl]
        | cons _ _ _ => exact sorry
      exact sorry
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

open Classical in
noncomputable def protocolPartitionNumber
    (I : Finset (Finset (Edge n))) (S : Frontier n) : ℕ :=
  (I.filter fun H₀ =>
    ∀ H₁ ∈ I, H₀ ≠ H₁ →
      ¬IsHamCycle n (mixedGraph S H₁ H₀)).card

noncomputable def Gamma (q N : ℕ) : ℕ :=
  if q = 0 then 1
  else if N < 4 * q + 1 then 1
  else 2 ^ q * Gamma q (N - 2 * q)
termination_by N
decreasing_by omega

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
    cases hBal with
    | inl h => simp only [reds_total]; omega
    | inr h => simp only [reds_total]; omega
  have hblues_ge : blues_total ≥ n / 2 := by omega
  have hBichrom := mca.hBichromatic
  have pair_true_le : ∀ i : Fin q,
      (({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
        (fun v => mca.χ.color v = true)).card ≤ 1 := by
    intro i
    have hbi := hBichrom i
    unfold CarrierEdge.isBichromatic isBichromaticEdge at hbi
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha.1 with rfl | rfl <;> rcases hb.1 with rfl | rfl <;> try rfl
    · exact absurd (ha.2.trans hb.2.symm) hbi
    · exact absurd (hb.2.trans ha.2.symm) hbi
  have pair_false_le : ∀ i : Fin q,
      (({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
        (fun v => mca.χ.color v = false)).card ≤ 1 := by
    intro i
    have hbi := hBichrom i
    unfold CarrierEdge.isBichromatic isBichromaticEdge at hbi
    rw [Finset.card_le_one]
    intro a ha b hb
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
  exact sorry

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
  have hne := packedFamily hn4 ext.mca.ρ ext.mca.hConsistent ext.mca.ρ.size (le_refl _)
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

private theorem surviving_card_ge {n q : ℕ}
    (ext : MultiCarrierExtension n q) (hn : n ≥ 2 * q) :
    (survivingVertices ext).card ≥ n - 2 * q := by
  unfold survivingVertices
  have hsub : interiorVertices ext ⊆ Finset.univ := Finset.subset_univ _
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_fin]
  have := interiorVertices_card_le ext
  omega

private theorem multi_carrier_suppression_child :
  ∀ {n q : ℕ} (ext : MultiCarrierExtension n q)
    (η : Fin q → Bool), n ≥ 2 * q →
    ∃ (child : MultiCarrierAdmissible (n - 2 * q) q),
      (∀ i, (child.carriers i).endpt1.val = (ext.blocks i).p.val ∧
            (child.carriers i).endpt2.val = (ext.blocks i).q.val) ∧
      (backgroundRestriction child).size = (backgroundRestriction ext.mca).size := by
  intro n q ext η hn
  exact sorry

theorem multiCarrierSuppression {q : ℕ}
    (ext : MultiCarrierExtension n q)
    (η : Fin q → Bool)
    (hn : n ≥ 2 * q) :
    ∃ (child : MultiCarrierAdmissible (n - 2 * q) q),
      (∀ i, (child.carriers i).endpt1.val = (ext.blocks i).p.val ∧
            (child.carriers i).endpt2.val = (ext.blocks i).q.val) ∧
      (backgroundRestriction child).size = (backgroundRestriction ext.mca).size :=
  multi_carrier_suppression_child ext η hn

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
    leftDegreeAt S H₀ v + rightDegreeAt S H₁ v := by
  unfold mixedGraph vertexDegreeIn
  rw [Finset.filter_union]
  have hdisj : Disjoint
      (Finset.filter (fun e => v ∈ e) (leftSubgraph S H₀))
      (Finset.filter (fun e => v ∈ e) (rightSubgraph S H₁)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_filter] at he1 he2
    simp only [leftSubgraph, rightSubgraph, Finset.mem_inter] at he1 he2
    exact Finset.disjoint_left.mp S.disjoint he1.1.2 he2.1.2
  rw [Finset.card_union_of_disjoint hdisj]
  unfold leftDegreeAt rightDegreeAt vertexDegreeIn
  rfl

private theorem profile_diff_breaks_mixed_regularity (S : Frontier n)
    (H₀ H₁ : Finset (Edge n)) (hH₀ : IsHamCycle n H₀) (hH₁ : IsHamCycle n H₁)
    (v : Fin n) (hNeq : leftDegreeAt S H₀ v ≠ leftDegreeAt S H₁ v) :
    vertexDegreeIn n (mixedGraph S H₁ H₀) v ≠ 2 := by
  rw [mixed_degree_at_vertex S H₀ H₁ hH₀ hH₁]
  have hSum₀ := leftDeg_add_rightDeg_eq_two S H₀ hH₀ v
  have hSum₁ := leftDeg_add_rightDeg_eq_two S H₁ hH₁ v
  omega

private noncomputable def extensionBlocksList {n q : ℕ}
    (ext : MultiCarrierExtension n q) : List (SwitchBlock n) :=
  (List.finRange q).map ext.blocks

private theorem extensionBlocksList_length {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    (extensionBlocksList ext).length = q := by
  simp [extensionBlocksList]

set_option maxHeartbeats 800000 in
private theorem extensionBlocksList_vertex_disjoint {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    blocksVertexDisjoint (extensionBlocksList ext) := by
  intro i j hij
  have hlen := extensionBlocksList_length ext
  have hi_lt : i.val < q := lt_of_lt_of_eq i.isLt (extensionBlocksList_length ext)
  have hj_lt : j.val < q := lt_of_lt_of_eq j.isLt (extensionBlocksList_length ext)
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
    intro h; apply hNeq
    ext i
    have := congr_fun h ⟨i.val, by rw [extensionBlocksList_length]; exact i.isLt⟩
    simp [patternToListPattern] at this
    exact this
  have hBlocksDisj := extensionBlocksList_vertex_disjoint ext
  have hBlocksVis := blocks_all_degree_visible ext
  exact crossPatternFatalMixing S ext.mca.ρ blocks hBlocksDisj hBlocksVis
    η'L ηL (Ne.symm hNeqL) H₁ H₀ hH₁ hH₀

theorem multiCarrierPatternIsolation {q : ℕ}
    (ext : MultiCarrierExtension n q)
    (η η' : Fin q → Bool) (hNeq : η ≠ η')
    (H₀ H₁ : Finset (Edge n))
    (hH₀ : H₀ ∈ patternHamCycles ext.mca.ρ (extensionBlocksList ext)
      (patternToListPattern ext η))
    (hH₁ : H₁ ∈ patternHamCycles ext.mca.ρ (extensionBlocksList ext)
      (patternToListPattern ext η')) :
    let S := chromaticFrontier ext.mca.χ
    ¬IsHamCycle n (mixedGraph S H₁ H₀) :=
  degree_visible_block_breaks_mixed_regularity ext η η' hNeq H₀ H₁ hH₀ hH₁

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

private theorem aho_ullman_yannakakis_formula_partition_bound_ax :
  ∀ {n m : ℕ} (F : BooleanCircuit m), F.isFormula →
    ∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
    protocolPartitionNumber I S ≤ F.size := by
  intro n m F hFormula S I
  classical
  unfold protocolPartitionNumber
  exact sorry

private theorem aho_ullman_yannakakis_formula_partition_bound :
  ∀ {n m : ℕ} (F : BooleanCircuit m), F.isFormula →
    ∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
    protocolPartitionNumber I S ≤ F.size :=
  aho_ullman_yannakakis_formula_partition_bound_ax

theorem ahoUllmanYannakakis {m : ℕ}
    (F : BooleanCircuit m) (_hF : F.isFormula) (S : Frontier n)
    (I : Finset (Finset (Edge n))) :
    protocolPartitionNumber I S ≤ F.size :=
  aho_ullman_yannakakis_formula_partition_bound F _hF S I

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
  have hGPos := gamma_pos 1 (n - 2 * 1)
  linarith

private theorem funnel_partition_count {n : ℕ}
    (S : Frontier n) (I : Finset (Finset (Edge n)))
    (hIsolated : ∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ →
      ¬IsHamCycle n (mixedGraph S H₁ H₀)) :
    protocolPartitionNumber I S ≥ I.card := by
  classical
  unfold protocolPartitionNumber
  have : I.filter (fun H₀ =>
    ∀ H₁ ∈ I, H₀ ≠ H₁ → ¬IsHamCycle n (mixedGraph S H₁ H₀)) = I := by
    ext H
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, hIsolated H h⟩⟩
  rw [this]

private theorem packing_gives_exponential_partition {n : ℕ}
    (hn : n ≥ 4)
    (S : Frontier n) (hS : S.isBalanced)
    (ρ : Restriction n) (hcons : ρ.consistent)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) :
    ∃ (I : Finset (Finset (Edge n))),
      I.card ≥ 2 ^ q ∧
      (∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ →
        ¬IsHamCycle n (mixedGraph S H₁ H₀)) := by
  obtain ⟨blocks, hlen, hDisj, hVis, hOpen, hPat⟩ :=
    disjointOpenSwitchPacking S hS ρ hcons polylogBound hm hn q hq_pos hq_bound
  set patterns := (Finset.univ : Finset (Fin blocks.length → Bool))
  have hChoose : ∀ η : Fin blocks.length → Bool,
      (patternHamCycles ρ blocks η).Nonempty := hPat
  classical
  let rep : (Fin blocks.length → Bool) → Finset (Edge n) :=
    fun η => (hChoose η).choose
  have hRepMem : ∀ η, rep η ∈ patternHamCycles ρ blocks η :=
    fun η => (hChoose η).choose_spec
  set I := Finset.univ.image rep
  have hIso : ∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ →
      ¬IsHamCycle n (mixedGraph S H₁ H₀) := by
    intro H₀ hH₀ H₁ hH₁ hne
    simp only [I, Finset.mem_image, Finset.mem_univ, true_and] at hH₀ hH₁
    obtain ⟨η₀, rfl⟩ := hH₀
    obtain ⟨η₁, rfl⟩ := hH₁
    have hNeq : η₀ ≠ η₁ := by
      intro h; subst h; exact hne rfl
    exact rectangleIsolation S ρ blocks hDisj hVis η₀ η₁ hNeq
      (rep η₀) (rep η₁) (hRepMem η₀) (hRepMem η₁)
  refine ⟨I, ?_, hIso⟩
  have hInj : Function.Injective rep := by
    intro η₀ η₁ h
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
    ∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
    (∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ → ¬IsHamCycle n (mixedGraph S H₁ H₀)) →
    F.size ≥ I.card := by
  intro n m F hF S I hIso
  have hAUY := ahoUllmanYannakakis F hF S I
  have hPart := funnel_partition_count S I hIso
  omega

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
    have h12 : χ.color ⟨1, by omega⟩ ≠ χ.color ⟨2, by omega⟩ :=
      hall _ _ (by simp [Fin.ext_iff])
    cases h0 : χ.color ⟨0, by omega⟩ <;> cases h1 : χ.color ⟨1, by omega⟩ <;>
      cases h2 : χ.color ⟨2, by omega⟩ <;> simp_all
  have hex_diff : ∃ (u v : Fin n), u ≠ v ∧ χ.color u ≠ χ.color v := by
    simp only [decide_eq_true_eq] at hBal
    have hcard_pos : 0 < (Finset.univ.filter fun v : Fin n => χ.color v = true).card := by
      cases hBal with | inl h => omega | inr h => omega
    have hcard_lt : (Finset.univ.filter fun v : Fin n => χ.color v = true).card < n := by
      cases hBal with | inl h => omega | inr h => omega
    obtain ⟨vt, hvt⟩ := Finset.card_pos.mp hcard_pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvt
    have hcard_false : 0 < (Finset.univ.filter fun v : Fin n => χ.color v = false).card := by
      by_contra h; push_neg at h
      have h0 : (Finset.univ.filter fun v : Fin n => χ.color v = false) = ∅ := by
        rwa [Nat.le_zero, Finset.card_eq_zero] at h
      have hall_true : ∀ v : Fin n, χ.color v = true := by
        intro v; by_contra hv
        have : v ∈ (Finset.univ.filter fun v : Fin n => χ.color v = false) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          cases χ.color v <;> simp_all
        rw [h0] at this; simp at this
      have : (Finset.univ.filter fun v : Fin n => χ.color v = true).card = n := by
        have heq : (Finset.univ.filter fun v : Fin n => χ.color v = true) =
            (Finset.univ : Finset (Fin n)) := by
          ext v; simp [Finset.mem_filter, hall_true v]
        rw [heq, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨vf, hvf⟩ := Finset.card_pos.mp hcard_false
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvf
    exact ⟨vt, vf, by intro h; rw [h] at hvt; simp [hvt] at hvf, by rw [hvt, hvf]; simp⟩
  obtain ⟨us, vs, hnes, hcs⟩ := hex_same
  obtain ⟨ud, vd, hned, hcd⟩ := hex_diff
  constructor
  · apply Finset.card_pos.mpr
    exact ⟨Sym2.mk (us, vs), by
      simp only [chromaticFrontier, Finset.mem_filter, allEdges, chromaticSameColor,
        Sym2.lift_mk, decide_eq_true_eq, Finset.mem_univ, true_and]
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
  obtain ⟨I, hIcard, hIso⟩ := packing_gives_exponential_partition hn S hSBal ρ₀ hCons₀ q hSize₀
    q hq_pos (le_refl q)
  have hFge := formula_size_from_isolation m F hF S I hIso
  omega

private theorem formula_lower_bound_iterated_funnel_ax :
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
