import PNeNp.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2

open Finset

namespace PNeNp

variable {n : ℕ}

theorem finset_eq_of_subset_card_eq {α : Type*} [DecidableEq α]
    {A B : Finset α} (h : A ⊆ B) (hc : A.card = B.card) : A = B :=
  Finset.eq_of_subset_of_card_le h (le_of_eq hc.symm)

section CycleComponentAbsorption

theorem incident_edges_absorbed
    (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (comp : Finset (Edge n)) (hcomp_sub : comp ⊆ H)
    (v : Fin n) (hv_deg : vertexDegreeIn n comp v = 2)
    (e : Edge n) (he : e ∈ H) (hve : v ∈ e) : e ∈ comp := by
  unfold vertexDegreeIn at hv_deg
  have hH_deg := hH.twoRegular v
  unfold vertexDegreeIn at hH_deg
  have hsub : Finset.filter (fun e' => v ∈ e') comp ⊆
      Finset.filter (fun e' => v ∈ e') H :=
    Finset.filter_subset_filter _ hcomp_sub
  have hfeq := finset_eq_of_subset_card_eq hsub (by omega)
  have : e ∈ Finset.filter (fun e' => v ∈ e') H :=
    Finset.mem_filter.mpr ⟨he, hve⟩
  rw [← hfeq] at this
  exact (Finset.mem_filter.mp this).1

theorem vertex_in_cycle_comp_deg2 (comp : Finset (Edge n))
    (hcomp_deg : ∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2)
    (v : Fin n) (hv : ∃ e ∈ comp, v ∈ e) : vertexDegreeIn n comp v = 2 := by
  obtain ⟨e, he, hve⟩ := hv
  rcases hcomp_deg v with h0 | h2
  · unfold vertexDegreeIn at h0
    have hmem : e ∈ Finset.filter (fun e' => v ∈ e') comp :=
      Finset.mem_filter.mpr ⟨he, hve⟩
    rw [Finset.card_eq_zero] at h0
    simp [h0] at hmem
  · exact h2

theorem adj_absorbed
    (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (comp : Finset (Edge n)) (hcomp_sub : comp ⊆ H)
    (hcomp_deg : ∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2)
    (u w : Fin n) (hu : ∃ e ∈ comp, u ∈ e)
    (hadj : (edgeSetToGraph n H).Adj u w) : ∃ e ∈ comp, w ∈ e := by
  obtain ⟨_, hmem⟩ := hadj
  have h_absorbed := incident_edges_absorbed H hH comp hcomp_sub u
    (vertex_in_cycle_comp_deg2 comp hcomp_deg u hu)
    (Sym2.mk (u, w)) hmem (Sym2.mem_mk_left u w)
  exact ⟨Sym2.mk (u, w), h_absorbed, Sym2.mem_mk_right u w⟩

theorem reachable_absorbed
    (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (comp : Finset (Edge n)) (hcomp_sub : comp ⊆ H)
    (hcomp_deg : ∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2)
    (u w : Fin n) (hu : ∃ e ∈ comp, u ∈ e)
    (hreach : (edgeSetToGraph n H).Reachable u w) : ∃ e ∈ comp, w ∈ e := by
  obtain ⟨walk⟩ := hreach
  induction walk with
  | nil => exact hu
  | @cons a b _ hadj _ ih =>
    have hab := adj_absorbed H hH comp hcomp_sub hcomp_deg a b hu hadj
    exact ih hab

private theorem sym2_exists_pair_of_not_isDiag :
  ∀ {α : Type*} (e : Sym2 α), ¬ e.IsDiag →
    ∃ (a b : α), a ≠ b ∧ e = Sym2.mk (a, b) := by
  intro α e hnd
  induction e using Sym2.ind with
  | h a b =>
    exact ⟨a, b, fun hab => hnd (Sym2.mk_isDiag_iff.mpr hab), rfl⟩

theorem cycle_component_equals_H
    (H : Finset (Edge n)) (hH : IsHamCycle n H)
    (comp : Finset (Edge n)) (hcomp_sub : comp ⊆ H)
    (hcomp_ne : comp.Nonempty)
    (hcomp_deg : ∀ v : Fin n, vertexDegreeIn n comp v = 0 ∨ vertexDegreeIn n comp v = 2) :
    comp = H := by
  ext e; constructor
  · exact fun he => hcomp_sub he
  · intro he
    have hnd : ¬ e.IsDiag := hH.noLoops e he
    obtain ⟨a, b, _, rfl⟩ := sym2_exists_pair_of_not_isDiag e hnd
    obtain ⟨e₀, he₀⟩ := hcomp_ne
    have hnd₀ : ¬ e₀.IsDiag := hH.noLoops e₀ (hcomp_sub he₀)
    obtain ⟨u₀, v₀, _, rfl⟩ := sym2_exists_pair_of_not_isDiag e₀ hnd₀
    have hu₀ : ∃ e ∈ comp, u₀ ∈ e := ⟨_, he₀, Sym2.mem_mk_left u₀ v₀⟩
    have hconn := hH.connected
    unfold IsConnectedEdgeSet at hconn
    have ha_in := reachable_absorbed H hH comp hcomp_sub hcomp_deg
      u₀ a hu₀ (hconn.preconnected u₀ a)
    exact incident_edges_absorbed H hH comp hcomp_sub
      a (vertex_in_cycle_comp_deg2 comp hcomp_deg a ha_in)
      (Sym2.mk (a, b)) he (Sym2.mem_mk_left a b)

end CycleComponentAbsorption

end PNeNp
