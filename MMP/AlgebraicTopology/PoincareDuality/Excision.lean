module

public import MMP.AlgebraicTopology.PoincareDuality.MayerVietoris
public import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Excision for the vanishing of `H_*(Y, Y - K)`

Let `U ⊆ Y` be open and `K ⊆ U` closed in `Y`. If `H_{m+1}(U, U - K; R) = 0` then
`H_{m+1}(Y, Y - K; R) = 0`, stated on finite singular chains with
`MMP.SingularChain.RelVanishing`. The proof uses the theorem of small chains for
the open cover `{U, Y - K}` of `Y`: for a chain `c` with boundary in `Y - K`, Hatcher's
`ρ c = c - ∂ D c - D ∂ c` splits as `a + b` with `a` in `U` and `b` in `Y - K`; `D ∂ c` lies in
`Y - K` since `D` keeps a chain inside any subset; `a` comes from a chain of `U` whose boundary
lies in `U - K`, to which the hypothesis applies.

The vanishing is transported along homeomorphisms; together with excision this passes from a
chart `e : Y ⊇ e.source ≃ e.target ⊆ H` to the space `Y`, the use in Hatcher's Lemma 3.27.

## Main results

* `MMP.SingularChain.smallHomotopy_mem_inside_of_mem`: `D` keeps chains inside `V`.
* `MMP.SingularChain.RelVanishing.of_subtype`: excision.
* `MMP.SingularChain.RelVanishing.of_homeomorph`: transport along a homeomorphism.
* `MMP.SingularChain.RelVanishing.of_openPartialHomeomorph`: from a chart.

## Implementation notes

Chains are pushed forward along continuous maps with
`MMP.SingularChain.postcomp`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21 and §3.3, Lemma 3.27.
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

section postcomp

/-- Along an injective map, a chain whose push-forward lies in `V` lies in the preimage of `V`. -/
lemma mem_inside_preimage_of_postcomp_mem_inside {f : C(Y, Z)} (hf : Function.Injective f)
    {n : ℕ} {V : Set Z} {c : Chain R Y n} (hc : postcomp R f n c ∈ inside R n V) :
    c ∈ inside R n (f ⁻¹' V) := by
  classical
  have hinj : Function.Injective fun σ : Simplex Y n ↦ f.comp σ := fun σ τ h ↦
    ContinuousMap.ext fun t ↦ hf (DFunLike.congr_fun h t)
  rw [inside, mem_supported]
  intro σ hσ
  have hmem : f.comp σ ∈ (postcomp R f n c).support := by
    rw [postcomp, lmapDomain_apply, mapDomain_support_of_injective hinj]
    exact Finset.mem_image_of_mem _ hσ
  have := (mem_supported R _).1 hc hmem
  rintro _ ⟨t, rfl⟩
  exact this ⟨t, rfl⟩

/-- A chain of `Y` inside `U` is the push-forward of a chain of the subspace `U`. -/
lemma exists_postcomp_subtypeVal_eq {n : ℕ} {U : Set Y} {c : Chain R Y n}
    (hc : c ∈ inside R n U) :
    ∃ c' : Chain R U n, postcomp R (ContinuousMap.subtypeVal U) n c' = c := by
  have : (LinearMap.id : Chain R Y n →ₗ[R] Chain R Y n) c ∈
      LinearMap.range (postcomp R (ContinuousMap.subtypeVal U) n) :=
    VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
      refine ⟨single ⟨fun t ↦ ⟨σ t, hσ ⟨t, rfl⟩⟩, σ.continuous.subtype_mk _⟩ 1, ?_⟩
      rw [postcomp_single, LinearMap.id_apply]
      rfl) hc
  exact this

end postcomp

section smallHomotopy

/-- The `{V}`-small chains are exactly the chains inside `V`. -/
lemma small_singleton (n : ℕ) (V : Set Y) : small R n {V} = inside R n V := by
  simp only [small, inside, mem_singleton_iff, exists_eq_left]

/-- The chain homotopy `homotopyUpTo R m n` keeps `𝒰`-small chains `𝒰`-small. -/
lemma homotopyUpTo_mem_small {𝒰 : Set (Set Y)} (m : ℕ) {n : ℕ} {c : Chain R Y n}
    (hc : c ∈ small R n 𝒰) : homotopyUpTo R m n c ∈ small R (n + 1) 𝒰 := by
  rw [homotopyUpTo, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ ↦ subdivHomotopy_mem_small (subdiv_pow_mem_small i hc)

/-- Hatcher's chain homotopy `D` (for any family `𝒰`) keeps `𝒱`-small chains `𝒱`-small. -/
lemma smallHomotopy_mem_small (𝒰 : Set (Set Y)) {𝒱 : Set (Set Y)} {n : ℕ} {c : Chain R Y n}
    (hc : c ∈ small R n 𝒱) : smallHomotopy R 𝒰 n c ∈ small R (n + 1) 𝒱 :=
  VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
    rw [smallHomotopy_single]
    exact homotopyUpTo_mem_small _ (single_mem_supported R _ hσ)) hc

/-- Hatcher's chain homotopy `D` keeps chains inside `V`. -/
lemma smallHomotopy_mem_inside_of_mem (𝒰 : Set (Set Y)) {V : Set Y} {n : ℕ} {c : Chain R Y n}
    (hc : c ∈ inside R n V) : smallHomotopy R 𝒰 n c ∈ inside R (n + 1) V := by
  rw [← small_singleton] at hc ⊢
  exact smallHomotopy_mem_small 𝒰 hc

end smallHomotopy

section excision

/-- Excision: for `U` open and `K ⊆ U` closed in `Y`, the vanishing of `H_{m+1}(U, U - K)`
gives the vanishing of `H_{m+1}(Y, Y - K)`. -/
theorem RelVanishing.of_subtype {m : ℕ} {U K : Set Y} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) (h : RelVanishing R U m ((↑) ⁻¹' K)) : RelVanishing R Y m K := by
  intro c hc
  set ι := ContinuousMap.subtypeVal U
  set 𝒰 : Set (Set Y) := {U, Kᶜ}
  have h𝒰 : ∀ V ∈ 𝒰, IsOpen V := by
    rintro V (rfl | rfl)
    · exact hU
    · exact hK.isOpen_compl
  have hcov : c ∈ inside R (m + 1) (⋃₀ 𝒰) := by
    have : ⋃₀ 𝒰 = univ := by
      simp only [𝒰, sUnion_insert, sUnion_singleton]
      exact eq_univ_of_forall fun y ↦ (em (y ∈ K)).imp (fun h ↦ hKU h) id
    rw [this]
    exact (mem_supported R c).2 fun _ _ ↦ subset_univ _
  obtain ⟨a, ha, b, hb, hsplit⟩ :=
    exists_add_of_mem_small_pair (smallChainMap_mem_small h𝒰 (m + 1) hcov)
  rw [smallChainMap_succ] at hsplit
  have hDbd : smallHomotopy R 𝒰 m (bd R m c) ∈ inside R (m + 1) Kᶜ :=
    smallHomotopy_mem_inside_of_mem 𝒰 hc
  -- `∂ a = ∂ c - ∂ D ∂ c - ∂ b` lies in `Y - K`
  have hbda : bd R m a ∈ inside R m Kᶜ := by
    have : bd R m a = bd R m c - bd R m (smallHomotopy R 𝒰 m (bd R m c)) - bd R m b := by
      have := congrArg (bd R m) hsplit
      rw [map_sub, map_sub, bd_bd, sub_zero, map_add] at this
      rw [this]; abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hc (bd_mem_inside hDbd)) (bd_mem_inside hb)
  obtain ⟨a', rfl⟩ := exists_postcomp_subtypeVal_eq ha
  have hbda' : bd R m a' ∈ inside R m ((↑) ⁻¹' K : Set U)ᶜ := by
    rw [← postcomp_bd] at hbda
    exact mem_inside_preimage_of_postcomp_mem_inside Subtype.val_injective hbda
  obtain ⟨w', hw'⟩ := h a' hbda'
  have hpush : postcomp R ι (m + 1) a' - bd R (m + 1) (postcomp R ι (m + 2) w') ∈
      inside R (m + 1) Kᶜ := by
    rw [← postcomp_bd, ← map_sub]
    exact postcomp_mem_inside ι (fun x hx ↦ hx) hw'
  refine ⟨smallHomotopy R 𝒰 (m + 1) c + postcomp R ι (m + 2) w', ?_⟩
  have hc' : c = postcomp R ι (m + 1) a' + b + bd R (m + 1) (smallHomotopy R 𝒰 (m + 1) c) +
      smallHomotopy R 𝒰 m (bd R m c) := by
    rw [← hsplit]; abel
  have : c - bd R (m + 1) (smallHomotopy R 𝒰 (m + 1) c + postcomp R ι (m + 2) w') =
      (postcomp R ι (m + 1) a' - bd R (m + 1) (postcomp R ι (m + 2) w')) + b +
        smallHomotopy R 𝒰 m (bd R m c) := by
    calc _ = (postcomp R ι (m + 1) a' + b + bd R (m + 1) (smallHomotopy R 𝒰 (m + 1) c) +
          smallHomotopy R 𝒰 m (bd R m c)) -
          bd R (m + 1) (smallHomotopy R 𝒰 (m + 1) c + postcomp R ι (m + 2) w') := by
          rw [← hc']
      _ = _ := by rw [map_add]; abel
  rw [this]
  exact Submodule.add_mem _ (Submodule.add_mem _ hpush hb) hDbd

end excision

section homeomorph

/-- Transport of the vanishing of `H_{m+1}(Y, Y - e⁻¹ L)` along a homeomorphism `e : Y ≃ Z`. -/
theorem RelVanishing.of_homeomorph_preimage {m : ℕ} (e : Y ≃ₜ Z) {L : Set Z}
    (h : RelVanishing R Y m (e ⁻¹' L)) : RelVanishing R Z m L := by
  intro c hc
  have hc₀ : bd R m (postcomp R (e.symm : C(Z, Y)) (m + 1) c) ∈ inside R m (e ⁻¹' L)ᶜ := by
    rw [← postcomp_bd]
    refine postcomp_mem_inside _ (fun z hz ↦ ?_) hc
    simpa using hz
  obtain ⟨w, hw⟩ := h _ hc₀
  refine ⟨postcomp R (e : C(Y, Z)) (m + 2) w, ?_⟩
  have : c = postcomp R (e : C(Y, Z)) (m + 1) (postcomp R (e.symm : C(Z, Y)) (m + 1) c) := by
    rw [postcomp_comp]
    have : (e : C(Y, Z)).comp (e.symm : C(Z, Y)) = ContinuousMap.id Z := by
      ext z; simp
    rw [this, postcomp_id]
  rw [this, ← postcomp_bd, ← map_sub]
  exact postcomp_mem_inside _ (fun y hy ↦ hy) hw

/-- Transport of the vanishing of `H_{m+1}(Y, Y - K)` along a homeomorphism `e : Y ≃ Z`. -/
theorem RelVanishing.of_homeomorph {m : ℕ} (e : Y ≃ₜ Z) {K : Set Y}
    (h : RelVanishing R Y m K) : RelVanishing R Z m (e '' K) :=
  RelVanishing.of_homeomorph_preimage e (by rwa [e.preimage_image])

/-- From a chart: for an open partial homeomorphism `e : Y → H` and `K ⊆ e.source` closed in `Y`,
the vanishing of `H_{m+1}(e.target, e.target - e(K))` gives that of `H_{m+1}(Y, Y - K)`. -/
theorem RelVanishing.of_openPartialHomeomorph {H : Type*} [TopologicalSpace H] {m : ℕ}
    (e : OpenPartialHomeomorph Y H) {K : Set Y} (hK : IsClosed K) (hKs : K ⊆ e.source)
    (h : RelVanishing R e.target m ((↑) ⁻¹' (e '' K))) : RelVanishing R Y m K := by
  refine RelVanishing.of_subtype e.open_source hK hKs
    (RelVanishing.of_homeomorph_preimage e.toHomeomorphSourceTarget.symm ?_)
  convert h using 1
  ext y
  simp only [mem_preimage, mem_image]
  have hy : ((e.toHomeomorphSourceTarget.symm y : e.source) : Y) = e.symm y := rfl
  rw [hy]
  constructor
  · exact fun hx ↦ ⟨_, hx, e.right_inv y.2⟩
  · rintro ⟨x, hx, hxy⟩
    rwa [← hxy, e.left_inv (hKs hx)]

end homeomorph

end SingularChain

end MMP
