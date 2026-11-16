module

public import MMP.AlgebraicGeometry.DeRham.Logarithmic.SncPairSpreadingOut

/-!
# Weak charts pull back along étale affine morphisms

Let `f : X ⟶ S` be a morphism with a weak chart `c` of a set `Z ⊆ X`
(`MMP.Mori.Divisor.LogSpreadingProof.WeakChart`): an affine open `W` with coordinates
`t₁, …, t_n` whose differentials are a basis of `Ω_{W/S}` and `Z ∩ W = {t₁ ⋯ t_r = 0} ∩ W`. For an
étale affine morphism `q : X' ⟶ X`, the preimage `q⁻¹ W` is affine, `Γ(W) → Γ(q⁻¹ W)` is étale so
that `Ω_{q⁻¹ W/S} = Γ(q⁻¹ W) ⊗ Ω_{W/S}`, and the pulled-back coordinates form a weak chart of
`q⁻¹ Z` for `q ≫ f`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_weakChart_comp_of_etale`: the statement above.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology MMP.Mori.Divisor.LogSpreadingProof

/-- **Weak charts pull back along étale affine morphisms.** For a weak chart `c` of `Z ⊆ X` for
`f : X ⟶ S` and an étale affine morphism `q : X' ⟶ X`, the pulled-back coordinates on the affine
open `q⁻¹ W` form a weak chart of `q⁻¹ Z` for `q ≫ f`. -/
theorem exists_weakChart_comp_of_etale {n : ℕ} {X X' S : Scheme.{0}} (f : X ⟶ S)
    (q : X' ⟶ X) [Etale q] [IsAffineHom q] {f' : X' ⟶ S} (hf' : q ≫ f = f') {Z : Set X}
    (c : WeakChart f n Z) :
    ∃ c' : WeakChart f' n (q ⁻¹' Z), (c'.W : X'.Opens) = q ⁻¹ᵁ (c.W : X.Opens) := by
  subst hf'
  set W' : X'.Opens := q ⁻¹ᵁ (c.W : X.Opens)
  have hW' : IsAffineOpen W' := c.W.2.preimage q
  have e₁ : W' ≤ q ⁻¹ᵁ (c.W : X.Opens) := le_rfl
  let t' : Fin n → Γ(X', W') := fun i => (q.appLE c.W W' e₁).hom (c.t i)
  have hbasis : letI := ((q ≫ f).appLE ⊤ W' le_top).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(X', W') Ω[Γ(X', W')⁄Γ(S, ⊤)],
        ∀ i, b i = KaehlerDifferential.D Γ(S, ⊤) Γ(X', W') (t' i) := by
    let : Algebra Γ(S, ⊤) Γ(X, c.W) := (f.appLE ⊤ c.W le_top).hom.toAlgebra
    let : Algebra Γ(X, c.W) Γ(X', W') := (q.appLE c.W W' e₁).hom.toAlgebra
    let : Algebra Γ(S, ⊤) Γ(X', W') := ((q ≫ f).appLE ⊤ W' le_top).hom.toAlgebra
    have : IsScalarTower Γ(S, ⊤) Γ(X, c.W) Γ(X', W') :=
      IsScalarTower.of_algebraMap_eq (fun x => by
        change ((q ≫ f).appLE ⊤ W' le_top).hom x =
          (f.appLE ⊤ c.W le_top ≫ q.appLE c.W W' e₁).hom x
        rw [Scheme.Hom.appLE_comp_appLE q f ⊤ c.W W' le_top e₁])
    have : Algebra.Etale Γ(X, c.W) Γ(X', W') :=
      HasRingHomProperty.appLE @Etale q ‹_› c.W ⟨W', hW'⟩ e₁
    obtain ⟨b, hb⟩ := c.basis
    refine ⟨(KaehlerDifferential.isBaseChange_of_formallyEtale Γ(S, ⊤) Γ(X, c.W)
      Γ(X', W')).basis b, fun i => ?_⟩
    rw [IsBaseChange.basis_apply, hb, KaehlerDifferential.map_D]
    rfl
  have hprod : (∏ i : Fin c.r, t' (Fin.castLE c.hr i)) =
      (q.appLE c.W W' e₁).hom (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) := by
    simp [t', map_prod]
  refine ⟨⟨⟨W', hW'⟩, t', c.r, c.hr, hbasis, ?_⟩, rfl⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Scheme.mem_zeroLocus_iff,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨hyZ, hyW⟩
    refine ⟨fun hy => ?_, hyW⟩
    have h₀ : q.base y ∈ Z ∩ (c.W : Set X) := ⟨hyZ, hyW⟩
    rw [c.zero] at h₀
    rw [hprod, Scheme.basicOpen_appLE] at hy
    exact (Scheme.mem_zeroLocus_iff _ _ _).mp h₀.1 _ rfl hy.2
  · rintro ⟨hy, hyW⟩
    refine ⟨?_, hyW⟩
    have : q.base y ∈ Z ∩ (c.W : Set X) := by
      rw [c.zero]
      refine ⟨(Scheme.mem_zeroLocus_iff _ _ _).mpr ?_, hyW⟩
      rintro _ rfl hqb
      apply hy
      rw [hprod, Scheme.basicOpen_appLE]
      exact ⟨hyW, hqb⟩
    exact this.1

end MMP.FourfoldProofs.FractionalLogComplexProof
