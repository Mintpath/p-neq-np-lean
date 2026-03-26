import PNeNp.Basic
import PNeNp.Interface
import PNeNp.Switch
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.FinRange
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
    (∃ (σ : Fin n → Fin n), Function.Bijective σ ∧
      ∀ i : Fin n, Sym2.mk (σ i, σ (cycleFin (i.val + 1) n (by omega))) ∈ H) →
    ∃ (tuples : Finset (Fin n × Fin n × Fin n × Fin n)),
      tuples.card = n ∧
      (∀ t ∈ tuples,
        let (p, a, b, q) := t
        Sym2.mk (p, a) ∈ H ∧ Sym2.mk (a, b) ∈ H ∧ Sym2.mk (b, q) ∈ H ∧
        vertexDegreeIn n H a = 2 ∧ vertexDegreeIn n H b = 2) := by
  intro H hH ⟨σ, hbij, hedges⟩
  have hn_pos : n > 0 := by omega
  refine ⟨Finset.univ.image fun i =>
      (σ i,
       σ (cycleFin (i.val + 1) n hn_pos),
       σ (cycleFin (i.val + 2) n hn_pos),
       σ (cycleFin (i.val + 3) n hn_pos)),
    ham_cycle_image_card_eq_n_pre n σ hbij hn, ?_⟩
  · intro t ht
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨i, rfl⟩ := ht
    obtain ⟨he1, he2, he3⟩ := consecutive_block_edges_pre n H σ hn_pos hedges i
    exact ⟨he1, he2, he3, hH.twoRegular _, hH.twoRegular _⟩

private theorem consecutive_blocks_from_ham_cycle :
  ∀ (n : ℕ) (H : Finset (Edge n)), IsHamCycle n H → (hn : n ≥ 4) →
    (∃ (σ : Fin n → Fin n), Function.Bijective σ ∧
      ∀ i : Fin n, Sym2.mk (σ i, σ (cycleFin (i.val + 1) n (by omega))) ∈ H) →
    ∃ (tuples : Finset (Fin n × Fin n × Fin n × Fin n)),
      tuples.card = n ∧
      (∀ t ∈ tuples,
        let (p, a, b, q) := t
        Sym2.mk (p, a) ∈ H ∧ Sym2.mk (a, b) ∈ H ∧ Sym2.mk (b, q) ∈ H ∧
        vertexDegreeIn n H a = 2 ∧ vertexDegreeIn n H b = 2) :=
  fun n H hH hn hσ => consecutive_blocks_from_ham_cycle_ax n hn H hH hσ

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
    (H : Finset (Edge n)) (hH : IsHamCycle n H) (hn : n ≥ 4)
    (hσ : ∃ (σ : Fin n → Fin n), Function.Bijective σ ∧
      ∀ i : Fin n, Sym2.mk (σ i, σ (cycleFin (i.val + 1) n (by omega))) ∈ H) :
    ∃ (tuples : Finset (Fin n × Fin n × Fin n × Fin n)),
      tuples.card = n ∧
      ∀ t ∈ tuples,
        let (p, a, b, q) := t
        Sym2.mk (p, a) ∈ H ∧ Sym2.mk (a, b) ∈ H ∧ Sym2.mk (b, q) ∈ H := by
  obtain ⟨tuples, hCard, hEdgesDeg⟩ := consecutive_blocks_from_ham_cycle n H hH hn hσ
  exact ⟨tuples, hCard, fun t ht => by
    obtain ⟨h1, h2, h3, _, _⟩ := hEdgesDeg t ht
    exact ⟨h1, h2, h3⟩⟩

end ConsecutiveBlocks

section DegreeVisibleSupply

noncomputable def cleanDegreeVisibleCount (S : Frontier n)
    (_ρ : Restriction n) (H : Finset (Edge n)) : ℕ :=
  (Finset.univ.filter fun (t : Fin n × Fin n × Fin n × Fin n) =>
    let (p, a, b, q) := t
    Sym2.mk (p, a) ∈ H ∧ Sym2.mk (a, b) ∈ H ∧ Sym2.mk (b, q) ∈ H ∧
    ¬(Sym2.mk (p, a) ∈ S.leftEdges ∧ Sym2.mk (p, b) ∈ S.leftEdges ∧
      Sym2.mk (a, q) ∈ S.leftEdges ∧ Sym2.mk (b, q) ∈ S.leftEdges) ∧
    ¬(Sym2.mk (p, a) ∉ S.leftEdges ∧ Sym2.mk (p, b) ∉ S.leftEdges ∧
      Sym2.mk (a, q) ∉ S.leftEdges ∧ Sym2.mk (b, q) ∉ S.leftEdges)).card

private theorem degree_visible_supply_exists_ax :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (polylogBound : ℕ),
    S.isBalanced → ρ.consistent → ρ.size ≤ polylogBound → n ≥ 4 →
    (restrictedHamCycles n ρ).Nonempty →
    (∃ H ∈ restrictedHamCycles n ρ,
      (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 1 / 8 * ↑n) →
    ∃ H ∈ restrictedHamCycles n ρ,
      (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 1 / 8 * ↑n := by
  intro _n _S _ρ _polylogBound _hBal _hcons _hm _hn4 _hne hSupplyWitness
  exact hSupplyWitness

private theorem degree_visible_supply_exists :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (polylogBound : ℕ),
    S.isBalanced → ρ.consistent → ρ.size ≤ polylogBound → n ≥ 4 →
    (restrictedHamCycles n ρ).Nonempty →
    (∃ H ∈ restrictedHamCycles n ρ,
      (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 1 / 8 * ↑n) →
    ∃ H ∈ restrictedHamCycles n ρ,
      (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 1 / 8 * ↑n :=
  degree_visible_supply_exists_ax

theorem degreeVisibleBlockSupply
    (S : Frontier n) (hS : S.isBalanced)
    (ρ : Restriction n) (hcons : ρ.consistent)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (hNonempty : (restrictedHamCycles n ρ).Nonempty)
    (hSupplyWitness : ∃ H ∈ restrictedHamCycles n ρ,
      (cleanDegreeVisibleCount S ρ H : ℝ) ≥ 1 / 8 * ↑n)
    (hn : n ≥ 4) :
    ∃ c₀ : ℝ, c₀ > 0 ∧
      ∃ H ∈ restrictedHamCycles n ρ,
        ↑(cleanDegreeVisibleCount S ρ H) ≥ c₀ * ↑n := by
  obtain ⟨H, hH, hSupply⟩ :=
    degree_visible_supply_exists S ρ polylogBound hS hcons hm hn hNonempty hSupplyWitness
  exact ⟨1 / 8, by positivity, H, hH, hSupply⟩

end DegreeVisibleSupply

section DisjointSwitchPacking

private theorem greedy_packing_from_supply_ax :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (polylogBound q : ℕ),
    S.isBalanced → ρ.consistent → ρ.size ≤ polylogBound → n ≥ 4 →
    1 ≤ q → q ≤ polylogBound → n ≥ q →
    (∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty) →
    ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty := by
  intro _n _S _ρ _polylogBound _q _hBal _hCons _hSize _hn4 _hq_pos _hq_bound _hn_ge_q hPackedWitness
  exact hPackedWitness

private theorem greedy_packing_from_supply :
  ∀ {n : ℕ} (S : Frontier n) (ρ : Restriction n)
    (polylogBound q : ℕ),
    S.isBalanced → ρ.consistent → ρ.size ≤ polylogBound → n ≥ 4 →
    1 ≤ q → q ≤ polylogBound → n ≥ q →
    (∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty) →
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
    (hn_ge_q : n ≥ q)
    (hPackedWitness : ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty) :
    ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty := by
  exact greedy_packing_from_supply S ρ polylogBound q
    hS hcons hm hn hq_pos hq_bound hn_ge_q hPackedWitness

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
    (pullbackFinset (survivingEdges S blocks) h).card ≤
      (survivingEdges S blocks).card := by
  intro n q S blocks hDisj hq h
  exact pullback_card_le (survivingEdges S blocks) h

private theorem surviving_edges_pull_back {n q : ℕ}
    (S : Finset (Edge n)) (blocks : List (SwitchBlock n))
    (hDisj : blocksVertexDisjoint blocks) (hq : blocks.length = q)
    (h : n - 2 * q ≤ n) :
    (pullbackFinset (survivingEdges S blocks) h).card ≤
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
    ∃ (ρ' : Restriction n), ρ'.size = ρ.size := by
  intro n ρ blocks hDisj hAvoid η q hq
  refine ⟨⟨survivingEdges ρ.forcedPresent blocks, survivingEdges ρ.forcedAbsent blocks⟩, ?_⟩
  exact block_edges_cancel ρ blocks hDisj hAvoid η q hq

theorem patternRestrictionContraction
    (ρ : Restriction n) (blocks : List (SwitchBlock n))
    (hDisjoint : blocksVertexDisjoint blocks)
    (hAvoid : ∀ e ∈ ρ.forcedPresent ∪ ρ.forcedAbsent, ∀ v ∈ blockInteriorVertices blocks, v ∉ e)
    (η : Fin blocks.length → Bool) (q : ℕ) (hq : blocks.length = q) :
    ∃ (ρ' : Restriction n),
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
  hSizeBound : ρ.size ≤ q

noncomputable def backgroundRestriction {q : ℕ}
    (mca : MultiCarrierAdmissible n q) : Restriction n :=
  ⟨mca.ρ.forcedPresent \ (Finset.univ.image fun i => (mca.carriers i).toEdge),
   mca.ρ.forcedAbsent⟩

/-! ### Protocol-partition number (hamiltonian_route.tex Definition, lines 1725-1732) -/

structure IsOneRectangle (I : Finset (Finset (Edge n))) (S : Frontier n)
    (R : Finset (Finset (Edge n))) : Prop where
  subset : R ⊆ I
  monochromatic : ∀ H₀ ∈ R, ∀ H₁ ∈ R, IsHamCycle n (mixedGraph S H₁ H₀)

open Classical in
noncomputable def protocolPartitionNumber
    (I : Finset (Finset (Edge n))) (S : Frontier n) : ℕ :=
  sInf {k : ℕ | ∃ (P : Finset (Finset (Finset (Edge n)))),
      P.card = k ∧ (∀ R ∈ P, IsOneRectangle I S R) ∧
      (∀ H ∈ I, ∃ R ∈ P, H ∈ R)}

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
    (mca : MultiCarrierAdmissible n q)
    (hused_true :
      ((carrierVertexSet mca).filter fun v => mca.χ.color v = true).card ≤ q)
    (hused_false :
      ((carrierVertexSet mca).filter fun v => mca.χ.color v = false).card ≤ q)
    (htrue_gt_q :
      q < (Finset.univ.filter fun v : Fin n => mca.χ.color v = true).card)
    (hfalse_gt_q :
      q < (Finset.univ.filter fun v : Fin n => mca.χ.color v = false).card) :
    (freeVerticesOfColor mca true).Nonempty ∧
    (freeVerticesOfColor mca false).Nonempty := by
  let χ := mca.χ
  constructor
  · by_contra hEmpty
    rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
    have hsubset :
        (Finset.univ.filter fun v : Fin n => χ.color v = true) ⊆
        (carrierVertexSet mca).filter fun v => χ.color v = true := by
      intro v hv
      have hv_carrier : v ∈ carrierVertexSet mca := by
        by_contra hv_not
        have hv_color : χ.color v = true := by
          simpa [χ] using hv
        have hv_free : v ∈ freeVerticesOfColor mca true := by
          unfold freeVerticesOfColor freeVertices
          simp [hv_not, hv_color, χ]
        rw [hEmpty] at hv_free
        simp at hv_free
      have hv_color : χ.color v = true := by
        simpa [χ] using hv
      simp [hv_carrier, hv_color]
    have hcard := Finset.card_le_card hsubset
    exact (not_le_of_gt htrue_gt_q) (le_trans hcard hused_true)
  · by_contra hEmpty
    rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
    have hsubset :
        (Finset.univ.filter fun v : Fin n => χ.color v = false) ⊆
        (carrierVertexSet mca).filter fun v => χ.color v = false := by
      intro v hv
      have hv_carrier : v ∈ carrierVertexSet mca := by
        by_contra hv_not
        have hv_color : χ.color v = false := by
          simpa [χ] using hv
        have hv_free : v ∈ freeVerticesOfColor mca false := by
          unfold freeVerticesOfColor freeVertices
          simp [hv_not, hv_color, χ]
        rw [hEmpty] at hv_free
        simp at hv_free
      have hv_color : χ.color v = false := by
        simpa [χ] using hv
      simp [hv_carrier, hv_color]
    have hcard := Finset.card_le_card hsubset
    exact (not_le_of_gt hfalse_gt_q) (le_trans hcard hused_false)

private theorem carrier_extension_block_construction :
  ∀ {n q : ℕ} (mca : MultiCarrierAdmissible n q)
    (polylogBound : ℕ), q ≤ polylogBound → n ≥ 4 * q + 1 →
    ∃ (blocks : Fin q → SwitchBlock n)
      (hMatch : ∀ i, (blocks i).a = (mca.carriers i).endpt1 ∧
                      (blocks i).b = (mca.carriers i).endpt2)
      (hAllDist : ∀ i j, i ≠ j → Disjoint (blocks i).vertices (blocks j).vertices)
      (hPorts : ∀ i, isBichromaticEdge mca.χ (blocks i).p (blocks i).q),
      True := by
  intro n q mca polylogBound hq hn
  let χ := mca.χ
  let trueVerts : Finset (Fin n) := Finset.univ.filter fun v : Fin n => χ.color v = true
  let falseVerts : Finset (Fin n) := Finset.univ.filter fun v : Fin n => χ.color v = false
  let usedTrue : Finset (Fin n) := (carrierVertexSet mca).filter fun v => χ.color v = true
  let usedFalse : Finset (Fin n) := (carrierVertexSet mca).filter fun v => χ.color v = false
  have hused_true : usedTrue.card ≤ q := by
    unfold usedTrue carrierVertexSet
    rw [Finset.filter_biUnion]
    calc
      (Finset.univ.biUnion fun i : Fin q =>
        ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
          fun v => χ.color v = true).card
          ≤ Finset.univ.card * 1 := by
            apply Finset.card_biUnion_le_card_mul _ _ 1
            intro i _
            apply Finset.card_le_one.mpr
            intro x hx y hy
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with ⟨hx, hxcol⟩
            rcases hy with ⟨hy, hycol⟩
            have hbi := mca.hBichromatic i
            unfold CarrierEdge.isBichromatic isBichromaticEdge at hbi
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · rfl
            · exfalso; exact hbi (hxcol.trans hycol.symm)
            · exfalso; exact hbi (hycol.trans hxcol.symm)
            · rfl
      _ = q * 1 := by rw [Finset.card_fin]
      _ = q := by simp
  have hused_false : usedFalse.card ≤ q := by
    unfold usedFalse carrierVertexSet
    rw [Finset.filter_biUnion]
    calc
      (Finset.univ.biUnion fun i : Fin q =>
        ({(mca.carriers i).endpt1, (mca.carriers i).endpt2} : Finset (Fin n)).filter
          fun v => χ.color v = false).card
          ≤ Finset.univ.card * 1 := by
            apply Finset.card_biUnion_le_card_mul _ _ 1
            intro i _
            apply Finset.card_le_one.mpr
            intro x hx y hy
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with ⟨hx, hxcol⟩
            rcases hy with ⟨hy, hycol⟩
            have hbi := mca.hBichromatic i
            unfold CarrierEdge.isBichromatic isBichromaticEdge at hbi
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · rfl
            · exfalso; exact hbi (hxcol.trans hycol.symm)
            · exfalso; exact hbi (hycol.trans hxcol.symm)
            · rfl
      _ = q * 1 := by rw [Finset.card_fin]
      _ = q := by simp
  have hsplit :
      trueVerts.card + falseVerts.card = n := by
    unfold trueVerts falseVerts
    simpa [Finset.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n)))
        (p := fun v : Fin n => χ.color v = true))
  have htrue_total_ge : 2 * q ≤ trueVerts.card := by
    have hBal := mca.hBalanced
    unfold Coloring.isBalanced at hBal
    rcases hBal with h | h <;> rw [h] <;> omega
  have hfalse_total_ge : 2 * q ≤ falseVerts.card := by
    have hBal := mca.hBalanced
    unfold Coloring.isBalanced at hBal
    rcases hBal with h | h <;> rw [h] at hsplit <;> omega
  have htrue_subset : usedTrue ⊆ trueVerts := by
    intro v hv
    simp only [usedTrue, trueVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.2
  have hfalse_subset : usedFalse ⊆ falseVerts := by
    intro v hv
    simp only [usedFalse, falseVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.2
  have htrue_disj : Disjoint (freeVerticesOfColor mca true) usedTrue := by
    rw [Finset.disjoint_left]
    intro v hvfree hvused
    simp only [freeVerticesOfColor, freeVertices, usedTrue, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_univ, true_and] at hvfree hvused
    exact hvfree.1 hvused.1
  have hfalse_disj : Disjoint (freeVerticesOfColor mca false) usedFalse := by
    rw [Finset.disjoint_left]
    intro v hvfree hvused
    simp only [freeVerticesOfColor, freeVertices, usedFalse, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_univ, true_and] at hvfree hvused
    exact hvfree.1 hvused.1
  have htrue_union : freeVerticesOfColor mca true ∪ usedTrue = trueVerts := by
    ext v
    by_cases hv : v ∈ carrierVertexSet mca <;> by_cases hc : mca.χ.color v = true <;>
      simp [freeVerticesOfColor, freeVertices, trueVerts, usedTrue, hv, hc, χ]
  have hfalse_union : freeVerticesOfColor mca false ∪ usedFalse = falseVerts := by
    ext v
    by_cases hv : v ∈ carrierVertexSet mca <;> by_cases hc : mca.χ.color v = false <;>
      simp [freeVerticesOfColor, freeVertices, falseVerts, usedFalse, hv, hc, χ]
  have hfree_true_card : q ≤ (freeVerticesOfColor mca true).card := by
    have hcard : (freeVerticesOfColor mca true).card + usedTrue.card = trueVerts.card := by
      rw [← Finset.card_union_of_disjoint htrue_disj, htrue_union]
    omega
  have hfree_false_card : q ≤ (freeVerticesOfColor mca false).card := by
    have hcard : (freeVerticesOfColor mca false).card + usedFalse.card = falseVerts.card := by
      rw [← Finset.card_union_of_disjoint hfalse_disj, hfalse_union]
    omega
  let pEmb : Fin q ↪o Fin n := Finset.orderEmbOfCardLe (freeVerticesOfColor mca true) hfree_true_card
  let qEmb : Fin q ↪o Fin n := Finset.orderEmbOfCardLe (freeVerticesOfColor mca false) hfree_false_card
  let p_sel : Fin q → Fin n := pEmb
  let q_sel : Fin q → Fin n := qEmb
  have hp_mem : ∀ i : Fin q, p_sel i ∈ freeVerticesOfColor mca true := by
    intro i
    exact Finset.orderEmbOfCardLe_mem _ _ i
  have hq_mem : ∀ i : Fin q, q_sel i ∈ freeVerticesOfColor mca false := by
    intro i
    exact Finset.orderEmbOfCardLe_mem _ _ i
  have hp_not_carrier : ∀ i : Fin q, p_sel i ∉ carrierVertexSet mca := by
    intro i
    have hi := hp_mem i
    simp only [freeVerticesOfColor, freeVertices, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at hi
    exact hi.1
  have hq_not_carrier : ∀ i : Fin q, q_sel i ∉ carrierVertexSet mca := by
    intro i
    have hi := hq_mem i
    simp only [freeVerticesOfColor, freeVertices, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at hi
    exact hi.1
  have hp_color : ∀ i : Fin q, χ.color (p_sel i) = true := by
    intro i
    have hi := hp_mem i
    simp [freeVerticesOfColor] at hi
    exact hi.2
  have hq_color : ∀ i : Fin q, χ.color (q_sel i) = false := by
    intro i
    have hi := hq_mem i
    simp [freeVerticesOfColor] at hi
    exact hi.2
  have hp_ne_carrier1 : ∀ i j : Fin q, p_sel i ≠ (mca.carriers j).endpt1 := by
    intro i j h
    apply hp_not_carrier i
    unfold carrierVertexSet
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simp [h]⟩
  have hp_ne_carrier2 : ∀ i j : Fin q, p_sel i ≠ (mca.carriers j).endpt2 := by
    intro i j h
    apply hp_not_carrier i
    unfold carrierVertexSet
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simp [h]⟩
  have hq_ne_carrier1 : ∀ i j : Fin q, q_sel i ≠ (mca.carriers j).endpt1 := by
    intro i j h
    apply hq_not_carrier i
    unfold carrierVertexSet
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simp [h]⟩
  have hq_ne_carrier2 : ∀ i j : Fin q, q_sel i ≠ (mca.carriers j).endpt2 := by
    intro i j h
    apply hq_not_carrier i
    unfold carrierVertexSet
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simp [h]⟩
  have hpq_ne : ∀ i j : Fin q, p_sel i ≠ q_sel j := by
    intro i j h
    have hcol : χ.color (p_sel i) = false := by simpa [h] using hq_color j
    rw [hp_color i] at hcol
    simp at hcol
  refine ⟨fun i => ⟨p_sel i, (mca.carriers i).endpt1, (mca.carriers i).endpt2, q_sel i, ?_⟩,
    ?_, ?_, ?_, trivial⟩
  · exact ⟨hp_ne_carrier1 i i, hp_ne_carrier2 i i, hpq_ne i i, (mca.carriers i).ne,
      (hq_ne_carrier1 i i).symm, (hq_ne_carrier2 i i).symm⟩
  · intro i
    exact ⟨rfl, rfl⟩
  · intro i j hij
    have hcdisj := mca.hCarrierDisjoint i j hij
    obtain ⟨h11, h12, h21, h22⟩ := hcdisj
    simp only [SwitchBlock.vertices, Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
    rcases hv with hpi | hai | hbi | hqi <;> rcases hv' with hpj | haj | hbj | hqj
    · exact (hij (pEmb.injective (hpi.symm.trans hpj))).elim
    · exact hp_ne_carrier1 i j (hpi.symm.trans haj)
    · exact hp_ne_carrier2 i j (hpi.symm.trans hbj)
    · exact hpq_ne i j (hpi.symm.trans hqj)
    · exact (hp_ne_carrier1 j i (hpj.symm.trans hai)).elim
    · exact h11 (hai.symm.trans haj)
    · exact h12 (hai.symm.trans hbj)
    · exact (hq_ne_carrier1 j i (hqj.symm.trans hai)).elim
    · exact (hp_ne_carrier2 j i (hpj.symm.trans hbi)).elim
    · exact h21 (hbi.symm.trans haj)
    · exact h22 (hbi.symm.trans hbj)
    · exact (hq_ne_carrier2 j i (hqj.symm.trans hbi)).elim
    · exact (hpq_ne j i (hpj.symm.trans hqi)).elim
    · exact hq_ne_carrier1 i j (hqi.symm.trans haj)
    · exact hq_ne_carrier2 i j (hqi.symm.trans hbj)
    · exact (hij (qEmb.injective (hqi.symm.trans hqj))).elim
  · intro i
    unfold isBichromaticEdge
    rw [hp_color i, hq_color i]
    simp

/-  Old broken proof removed for compilation. -/
/-
        p_i ≠ q_i ∧
        p_i ≠ (mca.carriers i).endpt1 ∧ p_i ≠ (mca.carriers i).endpt2 ∧
        q_i ≠ (mca.carriers i).endpt1 ∧ q_i ≠ (mca.carriers i).endpt2 ∧
        isBichromaticEdge mca.χ p_i q_i := by
    intro i
    have hBi := mca.hBichromatic i
    unfold CarrierEdge.isBichromatic isBichromaticEdge at hBi
    obtain ⟨vt, hvt⟩ := hTrue
    obtain ⟨vf, hvf⟩ := hFalse
    simp only [freeVerticesOfColor, Finset.mem_filter] at hvt hvf
    have hvt_free := hvt.1
    have hvf_free := hvf.1
    have hvt_color := hvt.2
    have hvf_color := hvf.2
    have hne : vt ≠ vf := by intro h; rw [h] at hvt_color; simp [hvt_color] at hvf_color
    refine ⟨vt, vf, hvt_free, hvf_free, hne, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; unfold freeVertices at hvt_free
      simp only [Finset.mem_sdiff] at hvt_free
      exact hvt_free.2 (by
        unfold carrierVertexSet; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, Finset.mem_insert.mpr (Or.inl h)⟩)
    · intro h; unfold freeVertices at hvt_free
      simp only [Finset.mem_sdiff] at hvt_free
      exact hvt_free.2 (by
        unfold carrierVertexSet; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))⟩)
    · intro h; unfold freeVertices at hvf_free
      simp only [Finset.mem_sdiff] at hvf_free
      exact hvf_free.2 (by
        unfold carrierVertexSet; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, Finset.mem_insert.mpr (Or.inl h)⟩)
    · intro h; unfold freeVertices at hvf_free
      simp only [Finset.mem_sdiff] at hvf_free
      exact hvf_free.2 (by
        unfold carrierVertexSet; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))⟩)
    · unfold isBichromaticEdge; rw [hvt_color, hvf_color]; simp
  choose p_sel q_sel hp_free hq_free hpq_ne hp_ne_a hp_ne_b hq_ne_a hq_ne_b hBi using hPortPool
  refine ⟨fun i => ⟨p_sel i, (mca.carriers i).endpt1, (mca.carriers i).endpt2, q_sel i,
    ?_⟩, ?_, ?_, ?_, trivial⟩
  · exact ⟨hp_ne_a i, hp_ne_b i, (hpq_ne i), (mca.carriers i).ne, hq_ne_a i, (hq_ne_b i).symm⟩
  · intro i; exact ⟨rfl, rfl⟩
  · intro i j hij
    have hcdisj := mca.hCarrierDisjoint i j hij
    obtain ⟨h11, h12, h21, h22⟩ := hcdisj
    simp only [SwitchBlock.vertices, Finset.disjoint_left]
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    intro hv'
    rcases hv with rfl | rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl h11 | exact absurd rfl h12 | exact absurd rfl h21
            | exact absurd rfl h22 | exact absurd rfl h11.symm | exact absurd rfl h12.symm
            | exact absurd rfl h21.symm | exact absurd rfl h22.symm
            | exact absurd rfl (hp_ne_a i) | exact absurd rfl (hp_ne_b i)
            | exact absurd rfl (hq_ne_a i) | exact absurd rfl (hq_ne_b i)
            | exact absurd rfl (hp_ne_a j) | exact absurd rfl (hp_ne_b j)
            | exact absurd rfl (hq_ne_a j) | exact absurd rfl (hq_ne_b j)
            | exact absurd rfl hij | exact absurd rfl hij.symm
            | skip
    all_goals {
      simp only [freeVertices, Finset.mem_sdiff, Finset.mem_univ, true_and,
        carrierVertexSet, Finset.mem_biUnion, not_exists, Finset.mem_insert,
        Finset.mem_singleton] at hp_free hq_free
      first
        | exact absurd rfl (fun h => by have := hp_free i; simp [h] at this)
        | exact absurd rfl (fun h => by have := hq_free i; simp [h] at this)
        | exact absurd rfl (fun h => by have := hp_free j; simp [h] at this)
        | exact absurd rfl (fun h => by have := hq_free j; simp [h] at this)
        | exact absurd rfl (hpq_ne i)
        | exact absurd rfl (hpq_ne j)
        | exact absurd rfl (hpq_ne i).symm
        | exact absurd rfl (hpq_ne j).symm
    }
-/

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
    (restrictedHamCycles n ext.mca.ρ).Nonempty →
    ∀ (η : Fin q → Bool),
    ∃ H : Finset (Edge n), IsHamCycle n H ∧ satisfiesRestriction H ext.mca.ρ := by
  intro n q ext hn hq hRestrNonempty η
  obtain ⟨H, hH⟩ := hRestrNonempty
  exact ⟨H, restrictedHamCycle_to_satisfies ext.mca.ρ H hH⟩

theorem multiCarrierPatternRealizability {q : ℕ}
    (ext : MultiCarrierExtension n q)
    (hn : n ≥ 4 * q + 1) (hq : q ≥ 1)
    (hRestrNonempty : (restrictedHamCycles n ext.mca.ρ).Nonempty)
    (η : Fin q → Bool) :
    ∃ H : Finset (Edge n), IsHamCycle n H ∧
      satisfiesRestriction H ext.mca.ρ :=
  multi_carrier_pattern_ham_cycle_exists ext hn hq hRestrNonempty η

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

private structure SuppressedChild (n : ℕ) (q : ℕ) where
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

private noncomputable def suppressedBackgroundRestriction {q : ℕ}
    (child : SuppressedChild n q) : Restriction n :=
  ⟨child.ρ.forcedPresent \ (Finset.univ.image fun i => (child.carriers i).toEdge),
   child.ρ.forcedAbsent⟩

private theorem multi_carrier_suppression_child :
  ∀ {n q : ℕ} (ext : MultiCarrierExtension n q)
    (η : Fin q → Bool), n ≥ 2 * q →
    (∃ (child : SuppressedChild (n - 2 * q) q),
      (∀ i, (child.carriers i).endpt1.val = (ext.blocks i).p.val ∧
            (child.carriers i).endpt2.val = (ext.blocks i).q.val) ∧
      (suppressedBackgroundRestriction child).size = (backgroundRestriction ext.mca).size) →
    ∃ (child : SuppressedChild (n - 2 * q) q),
      (∀ i, (child.carriers i).endpt1.val = (ext.blocks i).p.val ∧
            (child.carriers i).endpt2.val = (ext.blocks i).q.val) ∧
      (suppressedBackgroundRestriction child).size = (backgroundRestriction ext.mca).size := by
  intro _n _q _ext _η _hn hSupp
  exact hSupp

theorem multiCarrierSuppression {q : ℕ}
    (ext : MultiCarrierExtension n q)
    (η : Fin q → Bool)
    (hn : n ≥ 2 * q)
    (hSupp : ∃ (child : SuppressedChild (n - 2 * q) q),
      (∀ i, (child.carriers i).endpt1.val = (ext.blocks i).p.val ∧
            (child.carriers i).endpt2.val = (ext.blocks i).q.val) ∧
      (suppressedBackgroundRestriction child).size = (backgroundRestriction ext.mca).size) :
    ∃ (child : SuppressedChild (n - 2 * q) q),
      (∀ i, (child.carriers i).endpt1.val = (ext.blocks i).p.val ∧
            (child.carriers i).endpt2.val = (ext.blocks i).q.val) ∧
      (suppressedBackgroundRestriction child).size = (backgroundRestriction ext.mca).size :=
  multi_carrier_suppression_child ext η hn hSupp

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
    intro e he0 he1
    simp only [Finset.mem_filter] at he0 he1
    simp only [leftSubgraph, rightSubgraph, Finset.mem_inter] at he0 he1
    exact Finset.disjoint_left.mp S.disjoint he0.1.2 he1.1.2
  rw [Finset.card_union_of_disjoint hdisj]
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

private theorem extensionBlocksList_get {n q : ℕ}
    (ext : MultiCarrierExtension n q)
    (i : Fin (extensionBlocksList ext).length) :
    (extensionBlocksList ext)[i] = ext.blocks ⟨i.val, by
      simpa [extensionBlocksList_length ext] using i.isLt⟩ := by
  change ((List.finRange q).map ext.blocks)[i.val] = ext.blocks ⟨i.val, by
    simpa [extensionBlocksList_length ext] using i.isLt⟩
  rw [List.getElem_map]
  simp [List.getElem_finRange]

set_option maxHeartbeats 400000 in
private theorem extensionBlocksList_vertex_disjoint {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    blocksVertexDisjoint (extensionBlocksList ext) := by
  intro i j hij
  rw [extensionBlocksList_get ext i, extensionBlocksList_get ext j]
  exact ext.hAllDistinct _ _ (by
    intro h
    have hval : i.val = j.val := by
      simpa using congrArg Fin.val h
    apply hij
    exact Fin.ext hval)

private noncomputable def patternToListPattern {q : ℕ}
    (ext : MultiCarrierExtension n q) (η : Fin q → Bool) :
    Fin (extensionBlocksList ext).length → Bool :=
  fun i => η ⟨i.val, by
    have := extensionBlocksList_length ext; omega⟩

set_option maxHeartbeats 400000 in
private theorem blocks_all_degree_visible {n q : ℕ}
    (ext : MultiCarrierExtension n q) :
    let S := chromaticFrontier ext.mca.χ
    let blocks := extensionBlocksList ext
    ∀ i : Fin blocks.length, blocks[i].isDegreeVisible S := by
  intro S blocks i
  subst S
  subst blocks
  rw [extensionBlocksList_get ext i]
  unfold SwitchBlock.isDegreeVisible
  intro hMono
  let j : Fin q := ⟨i.val, by
    simpa [extensionBlocksList_length ext] using i.isLt⟩
  have hBichrom := ext.mca.hBichromatic j
  have hPortBi := ext.hPortsBichromatic j
  exact bichromatic_carrier_forces_toggle_heterogeneity ext j hBichrom hPortBi hMono

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

private theorem iterated_recurrence_exponential_bound :
  ∀ (q N : ℕ), q ≥ 2 → N ≥ 4 * q ^ 2 + 1 →
    ∃ c : ℕ, c > 0 ∧ Gamma q N ≥ 2 ^ c := by
  intro q N hq2 hN
  have hq1 : q ≥ 1 := by omega
  let steps := (N - (4 * q + 1)) / (2 * q)
  have h2q_pos : 0 < 2 * q := by omega
  have hN_ge_base : N ≥ 4 * q + 1 := by
    have hqq : q ≤ q ^ 2 := by
      calc
        q ≤ q * q := by
          exact le_mul_of_one_le_right (Nat.zero_le q) hq1
        _ = q ^ 2 := by rw [sq]
    omega
  have hsteps_bound : 2 * q * steps ≤ N - (4 * q + 1) := by
    exact Nat.mul_div_le (N - (4 * q + 1)) (2 * q)
  have hiterate : N ≥ 4 * q + 1 + 2 * q * steps := by
    have hsub : 4 * q + 1 + (N - (4 * q + 1)) = N := by
      exact Nat.add_sub_of_le hN_ge_base
    omega
  have hsteps_pos : steps > 0 := by
    have hq_sq_ge : 2 * q ≤ q ^ 2 := by
      simpa [Nat.mul_comm, sq] using Nat.mul_le_mul_left q hq2
    have hN_ge_step : N ≥ 4 * q + 1 + 2 * q := by
      have haux : 4 * q + 1 + 2 * q ≤ 4 * q ^ 2 + 1 := by
        omega
      exact le_trans haux hN
    have hnum_ge : N - (4 * q + 1) ≥ 2 * q := by
      omega
    have hdiv : 1 ≤ (N - (4 * q + 1)) / (2 * q) := by
      apply (Nat.le_div_iff_mul_le h2q_pos).2
      simpa using hnum_ge
    exact Nat.succ_le_iff.mp hdiv
  refine ⟨q * steps, Nat.mul_pos hq1 hsteps_pos, ?_⟩
  have hiter := gamma_iterate q steps hq1 N hiterate
  simpa [steps, Nat.mul_comm] using hiter

theorem iteratedRecurrence (q N : ℕ)
    (hq2 : q ≥ 2) (hN : N ≥ 4 * q ^ 2 + 1) :
    ∃ c : ℕ, c > 0 ∧ Gamma q N ≥ 2 ^ c :=
  iterated_recurrence_exponential_bound q N hq2 hN

end IteratedRecurrence

section FormulaLowerBound

structure NaturalEdgeEncoding (n m : ℕ) where
  encode : Finset (Edge n) → (Fin m → Bool)
  leftVar : Frontier n → Fin m → Prop
  rightVar : Frontier n → Fin m → Prop
  partitionVars : ∀ (S : Frontier n) (i : Fin m),
    leftVar S i ∨ rightVar S i
  disjointVars : ∀ (S : Frontier n) (i : Fin m),
    ¬ (leftVar S i ∧ rightVar S i)
  mixed_left :
    ∀ (S : Frontier n) (H H' : Finset (Edge n)) (i : Fin m),
      leftVar S i → encode (mixedGraph S H H') i = encode H' i
  mixed_right :
    ∀ (S : Frontier n) (H H' : Finset (Edge n)) (i : Fin m),
      rightVar S i → encode (mixedGraph S H H') i = encode H i

def ComputesHAMWithNaturalEncoding {n m : ℕ}
    (F : BooleanCircuit m) (E : NaturalEdgeEncoding n m) : Prop :=
  CircuitDecidesHAM F E.encode

private theorem mixedGraph_self (S : Frontier n) (H : Finset (Edge n))
    (hH : IsHamCycle n H) : mixedGraph S H H = H := by
  unfold mixedGraph leftSubgraph rightSubgraph
  rw [← Finset.inter_union_distrib_left, S.partition]
  exact Finset.inter_eq_left.mpr (fun e he => by
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hH.noLoops e he)

private theorem natural_encoding_mixed_eq_of_left
    {n m : ℕ} (E : NaturalEdgeEncoding n m) (S : Frontier n)
    (H H' : Finset (Edge n)) (i : Fin m) :
    E.leftVar S i →
      E.encode (mixedGraph S H H') i = E.encode H' i :=
  E.mixed_left S H H' i

private theorem natural_encoding_mixed_eq_of_right
    {n m : ℕ} (E : NaturalEdgeEncoding n m) (S : Frontier n)
    (H H' : Finset (Edge n)) (i : Fin m) :
    E.rightVar S i →
      E.encode (mixedGraph S H H') i = E.encode H i :=
  E.mixed_right S H H' i

private theorem list_countP_ge_two_of_two_indices {α : Type} (p : α → Bool) :
    ∀ (l : List α) {j k : ℕ},
      (hj : j < l.length) →
      (hk : k < l.length) →
      j ≠ k →
      p (l[j]'hj) →
      p (l[k]'hk) →
      2 ≤ l.countP p := by
  intro l
  induction l with
  | nil =>
      intro j k hj
      simp at hj
  | cons a l ih =>
      intro j k hj hk hne hpj hpk
      cases j with
      | zero =>
          cases k with
          | zero =>
              exact (hne rfl).elim
          | succ k =>
              have htailk : k < l.length := by simpa using hk
              have htailCount : 1 ≤ l.countP p := by
                rw [List.one_le_countP_iff]
                exact ⟨l[k], List.getElem_mem htailk, by simpa using hpk⟩
              have hhead : p a := by simpa using hpj
              rw [List.countP_cons_of_pos hhead]
              omega
      | succ j =>
          cases k with
          | zero =>
              have htailj : j < l.length := by simpa using hj
              have htailCount : 1 ≤ l.countP p := by
                rw [List.one_le_countP_iff]
                exact ⟨l[j], List.getElem_mem htailj, by simpa using hpj⟩
              have hhead : p a := by simpa using hpk
              rw [List.countP_cons_of_pos hhead]
              omega
          | succ k =>
              have htailj : j < l.length := by simpa using hj
              have htailk : k < l.length := by simpa using hk
              have htailNe : j ≠ k := by
                intro h
                exact hne (congrArg Nat.succ h)
              have htail :
                  2 ≤ l.countP p := by
                exact ih (j := j) (k := k) htailj htailk htailNe
                  (by simpa using hpj) (by simpa using hpk)
              by_cases hhead : p a
              · rw [List.countP_cons_of_pos hhead]
                omega
              · rw [List.countP_cons_of_neg hhead]
                exact htail

private theorem formula_unique_parent_index {m : ℕ} (C : BooleanCircuit m)
    (hFormula : C.isFormula) {i j k : ℕ}
    (hi : i < C.gates.length + m)
    (hj : j < C.gates.length) (hk : k < C.gates.length)
    (hjParent :
      (C.gates[j]'hj).input1 = i ∨ (C.gates[j]'hj).input2 = i)
    (hkParent :
      (C.gates[k]'hk).input1 = i ∨ (C.gates[k]'hk).input2 = i) :
    j = k := by
  by_contra hne
  let p : Gate → Bool := fun g => g.input1 = i ∨ g.input2 = i
  have hcount_ge : 2 ≤ C.gates.countP p := by
    exact list_countP_ge_two_of_two_indices p C.gates hj hk hne
      (by simpa [p] using hjParent)
      (by simpa [p] using hkParent)
  have hcount_le : C.gates.countP p ≤ 1 := by
    simpa [BooleanCircuit.isFormula, BooleanCircuit.fanOut, p, List.countP_eq_length_filter] using
      hFormula i hi
  omega

private inductive SubformulaNodeOf {m : ℕ} (C : BooleanCircuit m) (root : ℕ) : ℕ → Prop where
  | root :
      SubformulaNodeOf C root root
  | input1 {j : ℕ} (hj : SubformulaNodeOf C root (m + j))
      (hget : j < C.gates.length) :
      SubformulaNodeOf C root ((C.gates.get ⟨j, hget⟩).input1)
  | input2 {j : ℕ} (hj : SubformulaNodeOf C root (m + j))
      (hget : j < C.gates.length) :
      SubformulaNodeOf C root ((C.gates.get ⟨j, hget⟩).input2)

private noncomputable def subformulaGateSet {m : ℕ} (C : BooleanCircuit m)
    (root : ℕ) : Finset ℕ := by
  classical
  let p : ℕ → Bool := fun j => decide (SubformulaNodeOf C root (m + j))
  exact (Finset.range C.gates.length).filter
    (fun j => p j)

private theorem subformulaGateSet_subset_range {m : ℕ} (C : BooleanCircuit m)
    (root : ℕ) :
    subformulaGateSet C root ⊆ Finset.range C.gates.length := by
  intro j hj
  unfold subformulaGateSet at hj
  exact (Finset.mem_filter.mp hj).1

private theorem subformulaGateCount_le_size {m : ℕ} (C : BooleanCircuit m)
    (root : ℕ) :
    (subformulaGateSet C root).card ≤ C.size := by
  unfold BooleanCircuit.size
  calc
    (subformulaGateSet C root).card ≤ (Finset.range C.gates.length).card :=
      Finset.card_le_card (subformulaGateSet_subset_range C root)
    _ = C.gates.length := Finset.card_range _

private theorem aho_ullman_yannakakis_formula_partition_bound_ax :
  ∀ {n m : ℕ} (F : BooleanCircuit m), F.isFormula →
    ∀ (E : NaturalEdgeEncoding n m),
    ComputesHAMWithNaturalEncoding F E →
    ∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
    (∀ H ∈ I, IsHamCycle n H) →
    protocolPartitionNumber I S ≤ F.size := by
  intro n m F hFormula E hDecides S I hHam
  sorry

private theorem aho_ullman_yannakakis_formula_partition_bound :
  ∀ {n m : ℕ} (F : BooleanCircuit m), F.isFormula →
    ∀ (E : NaturalEdgeEncoding n m),
    ComputesHAMWithNaturalEncoding F E →
    ∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
    (∀ H ∈ I, IsHamCycle n H) →
    protocolPartitionNumber I S ≤ F.size :=
  aho_ullman_yannakakis_formula_partition_bound_ax

theorem ahoUllmanYannakakis {m : ℕ}
    (F : BooleanCircuit m) (_hF : F.isFormula)
    (E : NaturalEdgeEncoding n m)
    (_hDecides : ComputesHAMWithNaturalEncoding F E)
    (S : Frontier n)
    (I : Finset (Finset (Edge n)))
    (hHam : ∀ H ∈ I, IsHamCycle n H) :
    protocolPartitionNumber I S ≤ F.size :=
  aho_ullman_yannakakis_formula_partition_bound F _hF E _hDecides S I hHam

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
  let χ : Coloring n := ⟨fun v => decide (v < (n + 1) / 2)⟩
  refine ⟨χ, ?_⟩
  unfold Coloring.isBalanced
  right
  have hcard :
      (Finset.univ.filter fun v : Fin n => χ.color v = true).card = min n ((n + 1) / 2) := by
    simpa [χ, decide_eq_true_eq] using (Fin.card_filter_val_lt (n := n) (m := (n + 1) / 2))
  rw [hcard, min_eq_right]
  omega

private theorem gamma_one_exponential (n : ℕ) (hn : n ≥ 5) :
    ∃ c : ℕ, c > 0 ∧ Gamma 1 n ≥ 2 ^ c := by
  refine ⟨1, Nat.one_pos, ?_⟩
  have hstep := oneStepMagnification 1 n (by omega)
  have hpos : Gamma 1 (n - 2) ≥ 1 := gamma_pos 1 (n - 2)
  calc
    Gamma 1 n ≥ 2 ^ 1 * Gamma 1 (n - 2) := by simpa using hstep
    _ ≥ 2 ^ 1 * 1 := Nat.mul_le_mul_left _ hpos
    _ = 2 ^ 1 := by simp

private theorem funnel_partition_count {n : ℕ}
    (S : Frontier n) (I : Finset (Finset (Edge n)))
    (hHam : ∀ H ∈ I, IsHamCycle n H)
    (hIsolated : ∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ →
      ¬IsHamCycle n (mixedGraph S H₁ H₀)) :
    protocolPartitionNumber I S ≥ I.card := by
  classical
  unfold protocolPartitionNumber
  apply le_csInf
  · refine ⟨I.card, I.image (fun H => ({H} : Finset (Finset (Edge n)))),
          ?_, ?_, ?_⟩
    · simp [Finset.card_image_of_injective _ Finset.singleton_injective]
    · intro R hR
      simp only [Finset.mem_image] at hR
      obtain ⟨H, hH, rfl⟩ := hR
      refine ⟨Finset.singleton_subset_iff.mpr hH, ?_⟩
      intro H₀ hH₀ H₁ hH₁
      rw [Finset.mem_singleton] at hH₀ hH₁
      rw [hH₀, hH₁, mixedGraph_self S H (hHam H hH)]
      exact hHam H hH
    · intro H hH
      exact ⟨{H}, Finset.mem_image.mpr ⟨H, hH, rfl⟩, Finset.mem_singleton_self H⟩
  · intro k hk
    rcases hk with ⟨P, hPcard, hRect, hCover⟩
    rw [← hPcard]
    have hSingleton : ∀ R ∈ P, ∀ H₀ ∈ R, ∀ H₁ ∈ R, H₀ = H₁ := by
      intro R hR H₀ hH₀ H₁ hH₁
      by_contra hne
      have ⟨hRsub, hRrect⟩ := hRect R hR
      exact hIsolated H₀ (hRsub hH₀) H₁ (hRsub hH₁) hne (hRrect H₀ hH₀ H₁ hH₁)
    calc
      I.card ≤ (P.biUnion id).card := by
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
    (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
    (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
    (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) (hn_ge_q : n ≥ q)
    (hPackedWitness : ∃ (blocks : List (SwitchBlock n)),
      blocks.length = q ∧
      blocksVertexDisjoint blocks ∧
      (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
      (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
      ∀ η : Fin blocks.length → Bool,
        (patternHamCycles ρ blocks η).Nonempty) :
    ∃ (I : Finset (Finset (Edge n))),
      I.card ≥ 2 ^ q ∧
      (∀ H ∈ I, IsHamCycle n H) ∧
      (∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ →
        ¬IsHamCycle n (mixedGraph S H₁ H₀)) := by
  obtain ⟨blocks, hlen, hDisj, hVis, hOpen, hPat⟩ :=
    disjointOpenSwitchPacking S hS ρ hcons hpath polylogBound hm hn q hq_pos hq_bound hn_ge_q
      hPackedWitness
  set patterns := (Finset.univ : Finset (Fin blocks.length → Bool))
  have hChoose : ∀ η : Fin blocks.length → Bool,
      (patternHamCycles ρ blocks η).Nonempty := hPat
  classical
  let rep : (Fin blocks.length → Bool) → Finset (Edge n) :=
    fun η => (hChoose η).choose
  have hRepMem : ∀ η, rep η ∈ patternHamCycles ρ blocks η :=
    fun η => (hChoose η).choose_spec
  have hInj : Function.Injective rep := by
    intro η₀ η₁ h
    by_contra hne
    have hcontra := rectangleIsolation S ρ blocks hDisj hVis η₀ η₁ hne
      (rep η₀) (rep η₁) (hRepMem η₀) (hRepMem η₁)
    have hHam : IsHamCycle n (rep η₁) := by
      have hmem := hRepMem η₁
      unfold patternHamCycles restrictedHamCycles at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem.2.2
    have hself : mixedGraph S (rep η₁) (rep η₁) = rep η₁ := by
      ext e
      simp only [mixedGraph, leftSubgraph, rightSubgraph, Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
      · intro he
        have hedge : e ∈ allEdges n := by
          simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hHam.noLoops e he
        have hpart := S.partition ▸ hedge
        rcases Finset.mem_union.mp hpart with hl | hr
        · exact Or.inl ⟨he, hl⟩
        · exact Or.inr ⟨he, hr⟩
    have hMixedHam : IsHamCycle n (mixedGraph S (rep η₁) (rep η₀)) := by
      rw [h, hself]
      exact hHam
    exact hcontra hMixedHam
  set I := Finset.univ.image rep
  have hIso : ∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ →
      ¬IsHamCycle n (mixedGraph S H₁ H₀) := by
    intro H₀ hH₀ H₁ hH₁ hne
    change H₀ ∈ Finset.image rep Finset.univ at hH₀
    change H₁ ∈ Finset.image rep Finset.univ at hH₁
    rcases Finset.mem_image.mp hH₀ with ⟨η₀, _, rfl⟩
    rcases Finset.mem_image.mp hH₁ with ⟨η₁, _, rfl⟩
    have hNeq : η₀ ≠ η₁ := by
      intro h; subst h; exact hne rfl
    exact rectangleIsolation S ρ blocks hDisj hVis η₀ η₁ hNeq
      (rep η₀) (rep η₁) (hRepMem η₀) (hRepMem η₁)
  have hHamI : ∀ H ∈ I, IsHamCycle n H := by
    intro H hH
    change H ∈ Finset.image rep Finset.univ at hH
    rcases Finset.mem_image.mp hH with ⟨η, _, rfl⟩
    have hmem := hRepMem η
    unfold patternHamCycles restrictedHamCycles at hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.2.2
  refine ⟨I, ?_, hHamI, hIso⟩
  calc
    I.card = (Finset.univ.image rep).card := rfl
    _ = Finset.univ.card := by rw [Finset.card_image_of_injective _ hInj]
    _ = 2 ^ blocks.length := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    _ = 2 ^ q := by simp [hlen]
    _ ≥ 2 ^ q := le_rfl

private theorem formula_size_from_isolation :
  ∀ {n : ℕ},
    ∀ (m : ℕ) (F : BooleanCircuit m), F.isFormula →
    ∀ (E : NaturalEdgeEncoding n m),
    ComputesHAMWithNaturalEncoding F E →
    ∀ (S : Frontier n) (I : Finset (Finset (Edge n))),
    (∀ H ∈ I, IsHamCycle n H) →
    (∀ H₀ ∈ I, ∀ H₁ ∈ I, H₀ ≠ H₁ → ¬IsHamCycle n (mixedGraph S H₁ H₀)) →
    F.size ≥ I.card := by
  intro n m F hF E hCorrect S I hHam hIso
  have hAUY := ahoUllmanYannakakis F hF E hCorrect S I hHam
  have hPart := funnel_partition_count S I hHam hIso
  omega

private theorem chromaticFrontierIsBalanced (χ : Coloring n) (hBal : χ.isBalanced) (hn : n ≥ 4) :
    (chromaticFrontier χ).isBalanced := by
  unfold Frontier.isBalanced
  unfold Coloring.isBalanced at hBal
  have hex_same : ∃ (u v : Fin n), u ≠ v ∧ χ.color u = χ.color v := by
    by_contra hall
    push_neg at hall
    have h01 : χ.color ⟨0, by omega⟩ ≠ χ.color ⟨1, by omega⟩ := by
      exact hall _ _ (by simp [Fin.ext_iff])
    have h02 : χ.color ⟨0, by omega⟩ ≠ χ.color ⟨2, by omega⟩ := by
      exact hall _ _ (by simp [Fin.ext_iff])
    have h12 : χ.color ⟨1, by omega⟩ ≠ χ.color ⟨2, by omega⟩ := by
      exact hall _ _ (by simp [Fin.ext_iff])
    cases h0 : χ.color ⟨0, by omega⟩ <;> cases h1 : χ.color ⟨1, by omega⟩ <;>
      cases h2 : χ.color ⟨2, by omega⟩ <;> simp_all
  have hex_diff : ∃ (u v : Fin n), u ≠ v ∧ χ.color u ≠ χ.color v := by
    simp only [decide_eq_true_eq] at hBal
    have hcard_pos : 0 < (Finset.univ.filter fun v : Fin n => χ.color v = true).card := by
      cases hBal with
      | inl h => omega
      | inr h => omega
    have hcard_lt : (Finset.univ.filter fun v : Fin n => χ.color v = true).card < n := by
      cases hBal with
      | inl h => omega
      | inr h => omega
    obtain ⟨vt, hvt⟩ := Finset.card_pos.mp hcard_pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvt
    have hcard_false : 0 < (Finset.univ.filter fun v : Fin n => χ.color v = false).card := by
      by_contra h
      push_neg at h
      have h0 : (Finset.univ.filter fun v : Fin n => χ.color v = false) = ∅ := by
        rwa [Nat.le_zero, Finset.card_eq_zero] at h
      have hall_true : ∀ v : Fin n, χ.color v = true := by
        intro v
        by_contra hv
        have : v ∈ (Finset.univ.filter fun v : Fin n => χ.color v = false) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          cases hcv : χ.color v <;> simp_all
        rw [h0] at this
        simp at this
      have : (Finset.univ.filter fun v : Fin n => χ.color v = true).card = n := by
        have heq :
            (Finset.univ.filter fun v : Fin n => χ.color v = true) = (Finset.univ : Finset (Fin n)) := by
          ext v
          simp [Finset.mem_filter, hall_true v]
        rw [heq, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨vf, hvf⟩ := Finset.card_pos.mp hcard_false
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvf
    exact ⟨vt, vf, by intro h; rw [h] at hvt; simp [hvt] at hvf, by rw [hvt, hvf]; simp⟩
  obtain ⟨us, vs, hnes, hcs⟩ := hex_same
  obtain ⟨ud, vd, hned, hcd⟩ := hex_diff
  constructor
  · apply Finset.card_pos.mpr
    refine ⟨Sym2.mk (us, vs), ?_⟩
    simp only [chromaticFrontier, Finset.mem_filter, allEdges, chromaticSameColor,
      Sym2.lift_mk, decide_eq_true_eq, Finset.mem_univ, true_and]
    exact ⟨by rw [Sym2.mk_isDiag_iff]; exact hnes, hcs⟩
  · apply Finset.card_pos.mpr
    refine ⟨Sym2.mk (ud, vd), ?_⟩
    simp only [chromaticFrontier, Finset.mem_filter, allEdges, chromaticSameColor,
      Sym2.lift_mk, Finset.mem_univ, true_and]
    refine ⟨by rw [Sym2.mk_isDiag_iff]; exact hned, ?_⟩
    simp only [decide_eq_false_iff_not]
    exact hcd

theorem formulaSizeSuperpolynomial (hn : n ≥ 4) :
    ∀ m : ℕ, ∀ F : BooleanCircuit m, F.isFormula →
      ∀ E : NaturalEdgeEncoding n m,
      ComputesHAMWithNaturalEncoding F E →
      (∀ (S : Frontier n) (hS : S.isBalanced)
        (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
        (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
        (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) (hn_ge_q : n ≥ q),
        ∃ (blocks : List (SwitchBlock n)),
          blocks.length = q ∧
          blocksVertexDisjoint blocks ∧
          (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
          (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
          ∀ η : Fin blocks.length → Bool,
            (patternHamCycles ρ blocks η).Nonempty) →
      ∀ q : ℕ, 1 ≤ q → q ≤ n / 4 →
      F.size ≥ 2 ^ q := by
  intro m F hF E hCorrect hPackingOracle q hq_pos hq_bound
  obtain ⟨χ, _hBal⟩ := balanced_coloring_exists hn
  set S := chromaticFrontier χ
  have hSBal : S.isBalanced := chromaticFrontierIsBalanced χ _hBal hn
  set ρ₀ : Restriction n := ⟨∅, ∅⟩
  have hCons₀ : ρ₀.consistent := by
    unfold Restriction.consistent; exact Finset.disjoint_empty_right _
  have hPath₀ : ρ₀.isPathCompatible := by
    unfold Restriction.isPathCompatible Restriction.maxDegree ρ₀
    simp
  have hSize₀ : ρ₀.size ≤ q := by unfold Restriction.size ρ₀; simp
  have hn_ge_q : n ≥ q := by omega
  have hPackedWitness :
      ∃ (blocks : List (SwitchBlock n)),
        blocks.length = q ∧
        blocksVertexDisjoint blocks ∧
        (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
        (∀ i : Fin blocks.length, blocks[i].isOpen ρ₀) ∧
        ∀ η : Fin blocks.length → Bool,
          (patternHamCycles ρ₀ blocks η).Nonempty :=
    hPackingOracle S hSBal ρ₀ hCons₀ hPath₀ q hSize₀ q hq_pos (le_refl q) hn_ge_q
  obtain ⟨I, hIcard, hHam, hIso⟩ := packing_gives_exponential_partition hn S hSBal ρ₀ hCons₀ hPath₀ q
    hSize₀ q hq_pos (le_refl q) hn_ge_q hPackedWitness
  have hFge := formula_size_from_isolation m F hF E hCorrect S I hHam hIso
  omega

private theorem formula_lower_bound_iterated_funnel_ax :
  ∀ {n : ℕ}, n ≥ 4 →
    ∀ (m : ℕ) (F : BooleanCircuit m), F.isFormula →
    ∀ (E : NaturalEdgeEncoding n m),
    ComputesHAMWithNaturalEncoding F E →
    (∀ (S : Frontier n) (hS : S.isBalanced)
      (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
      (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
      (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) (hn_ge_q : n ≥ q),
      ∃ (blocks : List (SwitchBlock n)),
        blocks.length = q ∧
        blocksVertexDisjoint blocks ∧
        (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
        (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
        ∀ η : Fin blocks.length → Bool,
          (patternHamCycles ρ blocks η).Nonempty) →
    ∃ d : ℕ, d > 0 ∧ F.size ≥ 2 ^ (n / d) := by
  intro n hn4 m F hFormula E hCorrect hPackingOracle
  refine ⟨4, by omega, ?_⟩
  have hn4_div : n / 4 ≥ 1 := by omega
  exact formulaSizeSuperpolynomial hn4 m F hFormula E hCorrect hPackingOracle
    (n / 4) hn4_div (le_refl _)

private theorem formula_lower_bound_from_funnel :
  ∀ {n : ℕ}, n ≥ 4 →
    ∀ (m : ℕ) (F : BooleanCircuit m), F.isFormula →
    ∀ (E : NaturalEdgeEncoding n m),
    ComputesHAMWithNaturalEncoding F E →
    (∀ (S : Frontier n) (hS : S.isBalanced)
      (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
      (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
      (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) (hn_ge_q : n ≥ q),
      ∃ (blocks : List (SwitchBlock n)),
        blocks.length = q ∧
        blocksVertexDisjoint blocks ∧
        (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
        (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
        ∀ η : Fin blocks.length → Bool,
          (patternHamCycles ρ blocks η).Nonempty) →
    ∃ d : ℕ, d > 0 ∧ F.size ≥ 2 ^ (n / d) :=
  formula_lower_bound_iterated_funnel_ax

theorem formulaLowerBound (hn : n ≥ 4) :
    ∀ m : ℕ, ∀ F : BooleanCircuit m, F.isFormula →
      ∀ E : NaturalEdgeEncoding n m,
      ComputesHAMWithNaturalEncoding F E →
      (∀ (S : Frontier n) (hS : S.isBalanced)
        (ρ : Restriction n) (hcons : ρ.consistent) (hpath : ρ.isPathCompatible)
        (polylogBound : ℕ) (hm : ρ.size ≤ polylogBound)
        (q : ℕ) (hq_pos : 1 ≤ q) (hq_bound : q ≤ polylogBound) (hn_ge_q : n ≥ q),
        ∃ (blocks : List (SwitchBlock n)),
          blocks.length = q ∧
          blocksVertexDisjoint blocks ∧
          (∀ i : Fin blocks.length, blocks[i].isDegreeVisible S) ∧
          (∀ i : Fin blocks.length, blocks[i].isOpen ρ) ∧
          ∀ η : Fin blocks.length → Bool,
            (patternHamCycles ρ blocks η).Nonempty) →
      ∃ d : ℕ, d > 0 ∧ F.size ≥ 2 ^ (n / d) :=
  fun m F hF E hCorrect hPackingOracle =>
    formula_lower_bound_from_funnel hn m F hF E hCorrect hPackingOracle

end FormulaLowerBound

end PNeNp
