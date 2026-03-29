import PNeNp.Basic
import PNeNp.Switch
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

open Finset

namespace PNeNp

variable {n : ℕ}

section TwoOptHamCycle

private lemma applyTwoOpt_mem_iff (H : Finset (Edge n)) (e : TwoOptMove n)
    (f : Edge n) :
    f ∈ applyTwoOpt H e ↔
      (f ∈ H ∧ f ∉ e.removedEdges) ∨ f ∈ e.addedEdges := by
  unfold applyTwoOpt
  simp [Finset.mem_union, Finset.mem_sdiff]

private lemma removedEdges_mem (e : TwoOptMove n) (f : Edge n) :
    f ∈ e.removedEdges ↔ f = Sym2.mk (e.a, e.b) ∨ f = Sym2.mk (e.c, e.d) := by
  unfold TwoOptMove.removedEdges
  simp [Finset.mem_insert, Finset.mem_singleton]

private lemma addedEdges_mem (e : TwoOptMove n) (f : Edge n) :
    f ∈ e.addedEdges ↔ f = Sym2.mk (e.a, e.c) ∨ f = Sym2.mk (e.b, e.d) := by
  unfold TwoOptMove.addedEdges
  simp [Finset.mem_insert, Finset.mem_singleton]

private lemma vertex_incident_removed (e : TwoOptMove n) (v : Fin n)
    (f : Edge n) (hf : f ∈ e.removedEdges) (hv : v ∈ f) :
    v = e.a ∨ v = e.b ∨ v = e.c ∨ v = e.d := by
  rw [removedEdges_mem] at hf
  rcases hf with rfl | rfl <;> simp [Sym2.mem_iff] at hv <;>
    rcases hv with rfl | rfl <;> simp

private lemma vertex_incident_added (e : TwoOptMove n) (v : Fin n)
    (f : Edge n) (hf : f ∈ e.addedEdges) (hv : v ∈ f) :
    v = e.a ∨ v = e.b ∨ v = e.c ∨ v = e.d := by
  rw [addedEdges_mem] at hf
  rcases hf with rfl | rfl <;> simp [Sym2.mem_iff] at hv <;>
    rcases hv with rfl | rfl <;> simp

private lemma not_in_abcd_degree_preserved (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : TwoOptMove n) (hGen : e.isGenuine H)
    (v : Fin n) (hva : v ≠ e.a) (hvb : v ≠ e.b)
    (hvc : v ≠ e.c) (hvd : v ≠ e.d) :
    vertexDegreeIn n (applyTwoOpt H e) v = 2 := by
  have hH2 := hH.twoRegular v
  unfold vertexDegreeIn at hH2 ⊢
  have heq : (applyTwoOpt H e).filter (v ∈ ·) = H.filter (v ∈ ·) := by
    ext f
    simp only [mem_filter, applyTwoOpt_mem_iff]
    constructor
    · intro ⟨hfmem, hv⟩
      rcases hfmem with ⟨hfH, _⟩ | hfadd
      · exact ⟨hfH, hv⟩
      · exfalso
        have := vertex_incident_added e v f hfadd hv
        rcases this with rfl | rfl | rfl | rfl <;> contradiction
    · intro ⟨hfH, hv⟩
      refine ⟨?_, hv⟩
      left
      refine ⟨hfH, ?_⟩
      intro hrem
      have := vertex_incident_removed e v f hrem hv
      rcases this with rfl | rfl | rfl | rfl <;> contradiction
  rw [heq]; exact hH2

private lemma genuine_ab_ne_cd (e : TwoOptMove n) :
    Sym2.mk (e.a, e.b) ≠ Sym2.mk (e.c, e.d) := by
  obtain ⟨_, hne_ac, _, _, _, _⟩ := e.all_distinct
  intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hne_ac h1
  · obtain ⟨_, _, hne_ad, _, _, _⟩ := e.all_distinct
    exact hne_ad h1

private lemma genuine_ac_ne_bd (e : TwoOptMove n) :
    Sym2.mk (e.a, e.c) ≠ Sym2.mk (e.b, e.d) := by
  obtain ⟨hne_ab, _, _, _, _, _⟩ := e.all_distinct
  intro h; rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hne_ab h1
  · obtain ⟨_, _, hne_ad, _, _, _⟩ := e.all_distinct
    exact hne_ad h1

private lemma vertex_a_degree_preserved (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : TwoOptMove n) (hGen : e.isGenuine H) :
    vertexDegreeIn n (applyTwoOpt H e) e.a = 2 := by
  obtain ⟨hab, hcd, hac, hbd⟩ := hGen
  obtain ⟨hne_ab, hne_ac, hne_ad, hne_bc, hne_bd, hne_cd⟩ := e.all_distinct
  have hH2 := hH.twoRegular e.a
  unfold vertexDegreeIn at hH2 ⊢
  have heq : (applyTwoOpt H e).filter (e.a ∈ ·) =
      ((H.filter (e.a ∈ ·)).erase (Sym2.mk (e.a, e.b))) ∪ {Sym2.mk (e.a, e.c)} := by
    ext f
    simp only [mem_filter, applyTwoOpt_mem_iff, mem_union, mem_erase, mem_singleton,
      removedEdges_mem, addedEdges_mem]
    constructor
    · intro ⟨hfmem, hv⟩
      rcases hfmem with ⟨hfH, hfnrem⟩ | hfadd
      · left
        refine ⟨?_, hfH, hv⟩
        intro hfeq; subst hfeq; exact hfnrem (by simp [removedEdges_mem])
      · right
        rcases hfadd with rfl | rfl
        · rfl
        · exfalso; simp [Sym2.mem_iff] at hv
          rcases hv with hab' | had'
          · exact hne_ab hab'
          · exact hne_ad had'
    · intro hf
      rcases hf with ⟨hfne, hfH, hv⟩ | rfl
      · refine ⟨?_, hv⟩
        left; refine ⟨hfH, ?_⟩
        push_neg; exact ⟨hfne, by
          intro hfeq; subst hfeq
          simp [Sym2.mem_iff] at hv
          rcases hv with hac' | had'
          · exact hne_ac hac'
          · exact hne_ad had'⟩
      · exact ⟨Or.inr (Or.inl rfl), Sym2.mem_mk_left _ _⟩
  rw [heq]
  have hab_mem : Sym2.mk (e.a, e.b) ∈ H.filter (e.a ∈ ·) := by
    simp [mem_filter, hab, Sym2.mem_mk_left]
  have hac_nmem : Sym2.mk (e.a, e.c) ∉ (H.filter (e.a ∈ ·)).erase (Sym2.mk (e.a, e.b)) := by
    simp [mem_erase, mem_filter, hac]
  rw [Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_singleton_right]; exact hac_nmem)]
  rw [Finset.card_erase_of_mem hab_mem, hH2, Finset.card_singleton]

private lemma vertex_b_degree_preserved (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : TwoOptMove n) (hGen : e.isGenuine H) :
    vertexDegreeIn n (applyTwoOpt H e) e.b = 2 := by
  obtain ⟨hab, hcd, hac, hbd⟩ := hGen
  obtain ⟨hne_ab, hne_ac, hne_ad, hne_bc, hne_bd, hne_cd⟩ := e.all_distinct
  have hH2 := hH.twoRegular e.b
  unfold vertexDegreeIn at hH2 ⊢
  have heq : (applyTwoOpt H e).filter (e.b ∈ ·) =
      ((H.filter (e.b ∈ ·)).erase (Sym2.mk (e.a, e.b))) ∪ {Sym2.mk (e.b, e.d)} := by
    ext f
    simp only [mem_filter, applyTwoOpt_mem_iff, mem_union, mem_erase, mem_singleton,
      removedEdges_mem, addedEdges_mem]
    constructor
    · intro ⟨hfmem, hv⟩
      rcases hfmem with ⟨hfH, hfnrem⟩ | hfadd
      · left; refine ⟨?_, hfH, hv⟩
        intro hfeq; subst hfeq; exact hfnrem (Or.inl rfl)
      · right; rcases hfadd with rfl | rfl
        · exfalso; simp [Sym2.mem_iff] at hv
          rcases hv with hab' | hbc'
          · exact hne_ab hab'.symm
          · exact hne_bc hbc'
        · rfl
    · intro hf
      rcases hf with ⟨hfne, hfH, hv⟩ | rfl
      · refine ⟨?_, hv⟩; left; refine ⟨hfH, ?_⟩
        push_neg; exact ⟨hfne, by
          intro hfeq; subst hfeq; simp [Sym2.mem_iff] at hv
          rcases hv with hbc' | hbd'
          · exact hne_bc hbc'
          · exact hne_bd hbd'⟩
      · exact ⟨Or.inr (Or.inr rfl), Sym2.mem_mk_left _ _⟩
  rw [heq]
  have hab_mem : Sym2.mk (e.a, e.b) ∈ H.filter (e.b ∈ ·) := by
    simp [mem_filter, hab, Sym2.mem_mk_right]
  have hbd_nmem : Sym2.mk (e.b, e.d) ∉ (H.filter (e.b ∈ ·)).erase (Sym2.mk (e.a, e.b)) := by
    simp [mem_erase, mem_filter, hbd]
  rw [Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_singleton_right]; exact hbd_nmem)]
  rw [Finset.card_erase_of_mem hab_mem, hH2, Finset.card_singleton]

private lemma vertex_c_degree_preserved (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : TwoOptMove n) (hGen : e.isGenuine H) :
    vertexDegreeIn n (applyTwoOpt H e) e.c = 2 := by
  obtain ⟨hab, hcd, hac, hbd⟩ := hGen
  obtain ⟨hne_ab, hne_ac, hne_ad, hne_bc, hne_bd, hne_cd⟩ := e.all_distinct
  have hH2 := hH.twoRegular e.c
  unfold vertexDegreeIn at hH2 ⊢
  have heq : (applyTwoOpt H e).filter (e.c ∈ ·) =
      ((H.filter (e.c ∈ ·)).erase (Sym2.mk (e.c, e.d))) ∪ {Sym2.mk (e.a, e.c)} := by
    ext f
    simp only [mem_filter, applyTwoOpt_mem_iff, mem_union, mem_erase, mem_singleton,
      removedEdges_mem, addedEdges_mem]
    constructor
    · intro ⟨hfmem, hv⟩
      rcases hfmem with ⟨hfH, hfnrem⟩ | hfadd
      · left; refine ⟨?_, hfH, hv⟩
        intro hfeq; subst hfeq; exact hfnrem (Or.inr rfl)
      · right; rcases hfadd with rfl | rfl
        · rfl
        · exfalso; simp [Sym2.mem_iff] at hv
          rcases hv with hbc' | hcd'
          · exact hne_bc hbc'.symm
          · exact hne_cd hcd'
    · intro hf
      rcases hf with ⟨hfne, hfH, hv⟩ | rfl
      · refine ⟨?_, hv⟩; left; refine ⟨hfH, ?_⟩
        push_neg; exact ⟨by
          intro hfeq; subst hfeq; simp [Sym2.mem_iff] at hv
          rcases hv with hac' | hbc'
          · exact hne_ac hac'.symm
          · exact hne_bc hbc'.symm, hfne⟩
      · exact ⟨Or.inr (Or.inl rfl), Sym2.mem_mk_right _ _⟩
  rw [heq]
  have hcd_mem : Sym2.mk (e.c, e.d) ∈ H.filter (e.c ∈ ·) := by
    simp [mem_filter, hcd, Sym2.mem_mk_left]
  have hac_nmem : Sym2.mk (e.a, e.c) ∉ (H.filter (e.c ∈ ·)).erase (Sym2.mk (e.c, e.d)) := by
    simp [mem_erase, mem_filter, hac]
  rw [Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_singleton_right]; exact hac_nmem)]
  rw [Finset.card_erase_of_mem hcd_mem, hH2, Finset.card_singleton]

private lemma vertex_d_degree_preserved (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : TwoOptMove n) (hGen : e.isGenuine H) :
    vertexDegreeIn n (applyTwoOpt H e) e.d = 2 := by
  obtain ⟨hab, hcd, hac, hbd⟩ := hGen
  obtain ⟨hne_ab, hne_ac, hne_ad, hne_bc, hne_bd, hne_cd⟩ := e.all_distinct
  have hH2 := hH.twoRegular e.d
  unfold vertexDegreeIn at hH2 ⊢
  have heq : (applyTwoOpt H e).filter (e.d ∈ ·) =
      ((H.filter (e.d ∈ ·)).erase (Sym2.mk (e.c, e.d))) ∪ {Sym2.mk (e.b, e.d)} := by
    ext f
    simp only [mem_filter, applyTwoOpt_mem_iff, mem_union, mem_erase, mem_singleton,
      removedEdges_mem, addedEdges_mem]
    constructor
    · intro ⟨hfmem, hv⟩
      rcases hfmem with ⟨hfH, hfnrem⟩ | hfadd
      · left; refine ⟨?_, hfH, hv⟩
        intro hfeq; subst hfeq; exact hfnrem (Or.inr rfl)
      · right; rcases hfadd with rfl | rfl
        · exfalso; simp [Sym2.mem_iff] at hv
          rcases hv with had' | hcd'
          · exact hne_ad had'.symm
          · exact hne_cd hcd'.symm
        · rfl
    · intro hf
      rcases hf with ⟨hfne, hfH, hv⟩ | rfl
      · refine ⟨?_, hv⟩; left; refine ⟨hfH, ?_⟩
        push_neg; exact ⟨by
          intro hfeq; subst hfeq; simp [Sym2.mem_iff] at hv
          rcases hv with had' | hbd'
          · exact hne_ad had'.symm
          · exact hne_bd hbd'.symm, hfne⟩
      · exact ⟨Or.inr (Or.inr rfl), Sym2.mem_mk_right _ _⟩
  rw [heq]
  have hcd_mem : Sym2.mk (e.c, e.d) ∈ H.filter (e.d ∈ ·) := by
    simp [mem_filter, hcd, Sym2.mem_mk_right]
  have hbd_nmem : Sym2.mk (e.b, e.d) ∉ (H.filter (e.d ∈ ·)).erase (Sym2.mk (e.c, e.d)) := by
    simp [mem_erase, mem_filter, hbd]
  rw [Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_singleton_right]; exact hbd_nmem)]
  rw [Finset.card_erase_of_mem hcd_mem, hH2, Finset.card_singleton]

theorem applyTwoOpt_twoRegular (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : TwoOptMove n) (hGen : e.isGenuine H) :
    ∀ v : Fin n, vertexDegreeIn n (applyTwoOpt H e) v = 2 := by
  intro v
  obtain ⟨hne_ab, hne_ac, hne_ad, hne_bc, hne_bd, hne_cd⟩ := e.all_distinct
  by_cases hva : v = e.a
  · subst hva; exact vertex_a_degree_preserved H hH e hGen
  · by_cases hvb : v = e.b
    · subst hvb; exact vertex_b_degree_preserved H hH e hGen
    · by_cases hvc : v = e.c
      · subst hvc; exact vertex_c_degree_preserved H hH e hGen
      · by_cases hvd : v = e.d
        · subst hvd; exact vertex_d_degree_preserved H hH e hGen
        · exact not_in_abcd_degree_preserved H hH e hGen v hva hvb hvc hvd

private lemma isHamCycle_isCycles (H : Finset (Edge n))
    (hH : IsHamCycle n H) :
    (edgeSetToGraph n H).IsCycles := by
  intro v ⟨w, hw⟩
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  have h2 := hH.twoRegular v
  unfold vertexDegreeIn at h2
  convert h2 using 1
  apply Finset.card_bij (fun w _ => Sym2.mk (v, w))
  · -- maps to target: Sym2.mk (v, w) ∈ H.filter (v ∈ ·) for w a neighbor
    intro w hw
    simp only [Set.Finite.mem_toFinset, SimpleGraph.mem_neighborSet, edgeSetToGraph] at hw
    simp only [mem_filter]
    exact ⟨hw.2, Sym2.mem_mk_left v w⟩
  · -- injective
    intro w₁ hw₁ w₂ hw₂ h
    simp only [Set.Finite.mem_toFinset, SimpleGraph.mem_neighborSet, edgeSetToGraph] at hw₁ hw₂
    rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exfalso; exact hw₁.1 h2.symm
  · -- surjective: every incident edge comes from a neighbor
    intro e he
    simp only [mem_filter] at he
    obtain ⟨he_mem, hv_in⟩ := he
    have hne := hH.noLoops e he_mem
    revert he_mem hv_in hne
    refine Sym2.ind (fun a b => ?_) e
    intro he_mem hv_in hne
    simp only [Sym2.mem_iff] at hv_in
    rcases hv_in with rfl | rfl
    · refine ⟨b, ?_, ?_⟩
      · simp only [Set.Finite.mem_toFinset, SimpleGraph.mem_neighborSet, edgeSetToGraph]
        exact ⟨by rwa [Sym2.mk_isDiag_iff] at hne, he_mem⟩
      · rfl
    · refine ⟨a, ?_, ?_⟩
      · simp only [Set.Finite.mem_toFinset, SimpleGraph.mem_neighborSet, edgeSetToGraph]
        exact ⟨by intro h; apply hne; rw [h]; exact Sym2.mk_isDiag_iff.mpr rfl,
          by rwa [Sym2.eq_swap]⟩
      · exact Sym2.eq_swap

private lemma isHamCycle_neighborSet_nonempty (H : Finset (Edge n))
    (hH : IsHamCycle n H) (v : Fin n) :
    ((edgeSetToGraph n H).neighborSet v).Nonempty := by
  obtain ⟨e, he, hv⟩ := hH.spanning v
  have hnd := hH.noLoops e he
  revert he hv hnd
  refine Sym2.ind (fun a b => ?_) e
  intro he hv hnd
  simp only [Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact ⟨b, by rwa [Sym2.mk_isDiag_iff] at hnd, he⟩
  · exact ⟨a, fun h => hnd (by rw [h]; exact Sym2.mk_isDiag_iff.mpr rfl),
      by rwa [Sym2.eq_swap]⟩

private noncomputable def isHamCycle_cycleWalk (H : Finset (Edge n))
    (hH : IsHamCycle n H) (v : Fin n) :
    (edgeSetToGraph n H).Walk v v :=
  (SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (isHamCycle_isCycles H hH)
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _ |>.mpr rfl)
    (isHamCycle_neighborSet_nonempty H hH v)).choose

private lemma isHamCycle_cycleWalk_isCycle (H : Finset (Edge n))
    (hH : IsHamCycle n H) (v : Fin n) :
    (isHamCycle_cycleWalk H hH v).IsCycle :=
  (SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (isHamCycle_isCycles H hH)
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _ |>.mpr rfl)
    (isHamCycle_neighborSet_nonempty H hH v)).choose_spec.1

private lemma isHamCycle_cycleWalk_mem_support (H : Finset (Edge n))
    (hH : IsHamCycle n H) (v w : Fin n) :
    w ∈ (isHamCycle_cycleWalk H hH v).support := by
  have hspec := (SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (isHamCycle_isCycles H hH)
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _ |>.mpr rfl)
    (isHamCycle_neighborSet_nonempty H hH v)).choose_spec.2
  have hw_in_comp : w ∈ ((edgeSetToGraph n H).connectedComponentMk v).supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.eq.mpr (hH.connected.preconnected w v)
  rw [← SimpleGraph.Walk.mem_verts_toSubgraph, show (isHamCycle_cycleWalk H hH v).toSubgraph.verts =
    ((edgeSetToGraph n H).connectedComponentMk v).supp from hspec]
  exact hw_in_comp

private lemma old_adj_gives_new_reachable (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : TwoOptMove n) (hGen : e.isGenuine H)
    (hNonCross :
      ((edgeSetToGraph n H).deleteEdges {s(e.a, e.b), s(e.c, e.d)}).Reachable e.b e.c)
    (u w : Fin n) (hadj : (edgeSetToGraph n H).Adj u w) :
    (edgeSetToGraph n (applyTwoOpt H e)).Reachable u w := by
  obtain ⟨hab, hcd, hac, hbd⟩ := hGen
  obtain ⟨hne_ab, hne_ac, hne_ad, hne_bc, hne_bd, hne_cd⟩ := e.all_distinct
  obtain ⟨huv_ne, huv_mem⟩ := hadj
  by_cases hrem : Sym2.mk (u, w) ∈ e.removedEdges
  · -- The old edge was removed. Need detour through new edges.
    rw [removedEdges_mem] at hrem
    -- New edges: a-c and b-d are in the new graph
    have hac_adj : (edgeSetToGraph n (applyTwoOpt H e)).Adj e.a e.c := by
      refine ⟨hne_ac, ?_⟩
      simp [applyTwoOpt, TwoOptMove.removedEdges, TwoOptMove.addedEdges,
        Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    have hbd_adj : (edgeSetToGraph n (applyTwoOpt H e)).Adj e.b e.d := by
      refine ⟨hne_bd, ?_⟩
      simp [applyTwoOpt, TwoOptMove.removedEdges, TwoOptMove.addedEdges,
        Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    -- Use IsCycles.reachable_deleteEdges from Mathlib
    -- First show edgeSetToGraph n H is IsCycles
    have hcyc := isHamCycle_isCycles H hH
    -- Key: IsCycles.reachable_deleteEdges says deleting one edge preserves reachability
    have hab_adj : (edgeSetToGraph n H).Adj e.a e.b := ⟨hne_ab, hab⟩
    have hcd_adj : (edgeSetToGraph n H).Adj e.c e.d := ⟨hne_cd, hcd⟩
    -- Deleting {a,b}: a still reaches b (other way around cycle)
    have hab_reach_del := SimpleGraph.IsCycles.reachable_deleteEdges hab_adj hcyc
    -- Deleting {c,d}: c still reaches d (other way around cycle)
    have hcd_reach_del := SimpleGraph.IsCycles.reachable_deleteEdges hcd_adj hcyc
    -- Key subgraph lemma: old edges minus both removed are in the new graph
    have hsub : (edgeSetToGraph n H).deleteEdges {s(e.a, e.b), s(e.c, e.d)} ≤
        edgeSetToGraph n (applyTwoOpt H e) := by
      intro x y ⟨⟨hne, hmem⟩, hnotdel⟩
      simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff] at hnotdel
      refine ⟨hne, ?_⟩
      simp only [applyTwoOpt, Finset.mem_union, Finset.mem_sdiff,
        TwoOptMove.removedEdges, TwoOptMove.addedEdges,
        Finset.mem_insert, Finset.mem_singleton]
      left; refine ⟨hmem, fun h => hnotdel ⟨h, hne⟩⟩
    -- Now: Reachable c d in G\{c,d}. This walk avoids {c,d}.
    -- Lift it to G\{a,b,c,d} ∪ {a,b} if needed? No.
    -- Better: Reachable c d in G\{c,d} means walk c→...→a→b→...→d.
    -- The sub-walk from c to a avoids {c,d} and {a,b} (it's the P1 segment reversed + doesn't hit {a,b}).
    -- Actually just use: a reaches d in G\{a,b,c,d} (the P2 segment), and c reaches b in G\{a,b,c,d} (the P1 segment).
    -- Then for {a,b}: a →(P2) d →(new edge) b. For {c,d}: c →(P1) b →(new edge) d.
    -- But showing reachability in G\{a,b,c,d} requires decomposing the cycle further...
    -- Simpler: use hsub.mono to lift any Reachable in G\{a,b,c,d} to new graph.
    -- Then use new edges for the bridge.
    -- Helper: edge in walk → both endpoints in support
    -- If d ∉ walk.support, then {c,d} ∉ walk.edges (contrapositive of mem_support_of_mem_edges)
    have edge_needs_vertex : ∀ {G' : SimpleGraph (Fin n)} {x y z w' : Fin n}
        (p : G'.Walk x y) (hzw : s(z, w') ∈ p.edges), z ∈ p.support ∧ w' ∈ p.support :=
      fun p hzw => ⟨p.fst_mem_support_of_mem_edges hzw, p.snd_mem_support_of_mem_edges hzw⟩
    -- Non-crossing condition: b and c are in the same component of G\{ab,cd}
    -- (This is equivalent to the 2-opt being non-crossing)
    -- We take this as a hypothesis for now; the caller ensures it by choice of partner.
    -- In a non-crossing 2-opt: a,c are on one arc, b,d on the other.
    -- So b reaches c and a reaches d in G\{ab,cd}.
    have hbc_reach := hNonCross
    rcases hrem with huv_ab | huv_cd
    · rcases Sym2.eq_iff.mp huv_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- Reachable a b: a →(new) c →(surviving arc, mono) b
        exact hac_adj.reachable.trans (hbc_reach.mono hsub).symm
      · -- Reachable b a: symmetric
        exact (hac_adj.reachable.trans (hbc_reach.mono hsub).symm).symm
    · rcases Sym2.eq_iff.mp huv_cd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- Reachable c d: c →(surviving arc reversed) b →(new) d
        exact (hbc_reach.mono hsub).symm.trans hbd_adj.reachable
      · -- Reachable d c: symmetric
        exact ((hbc_reach.mono hsub).symm.trans hbd_adj.reachable).symm
  · -- The old edge survives in the new graph
    have hnew_adj : (edgeSetToGraph n (applyTwoOpt H e)).Adj u w := by
      refine ⟨huv_ne, ?_⟩
      simp [applyTwoOpt, Finset.mem_union, Finset.mem_sdiff]
      exact Or.inl ⟨huv_mem, hrem⟩
    exact hnew_adj.reachable

private lemma lift_reachable (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : TwoOptMove n) (hGen : e.isGenuine H)
    (hNonCross :
      ((edgeSetToGraph n H).deleteEdges {s(e.a, e.b), s(e.c, e.d)}).Reachable e.b e.c)
    (u v : Fin n) (hreach : (edgeSetToGraph n H).Reachable u v) :
    (edgeSetToGraph n (applyTwoOpt H e)).Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach ⊢
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hadj ih =>
      have := old_adj_gives_new_reachable H hH e hGen hNonCross _ _ hadj
      rw [SimpleGraph.reachable_iff_reflTransGen] at this
      exact ih.trans this

theorem applyTwoOpt_connected (H : Finset (Edge n))
    (hH : IsHamCycle n H) (e : TwoOptMove n) (hGen : e.isGenuine H)
    (hNonCross :
      ((edgeSetToGraph n H).deleteEdges {s(e.a, e.b), s(e.c, e.d)}).Reachable e.b e.c) :
    IsConnectedEdgeSet n (applyTwoOpt H e) := by
  have hconn := hH.connected
  haveI : Nonempty (Fin n) := hconn.nonempty
  unfold IsConnectedEdgeSet
  constructor
  exact fun u v => lift_reachable H hH e hGen hNonCross u v (hconn.preconnected u v)

end TwoOptHamCycle

end PNeNp
