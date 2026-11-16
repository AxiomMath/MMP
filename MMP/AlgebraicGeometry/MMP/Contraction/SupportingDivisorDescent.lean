module

public import MMP.AlgebraicGeometry.MMP.Contraction.SupportingDivisorFree
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullbackAdd
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullbackSheaf
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafInvertible

/-!
# A supporting divisor descends to the contraction

Let `(X, Δ)` be a klt pair, `X` projective over an algebraically closed field `k` of
characteristic zero and `Δ` effective, `F` a `(K_X + Δ)`-negative extremal face of `NE̅(X)`, `D` a
supporting divisor of `F` and `g : X ⟶ Z` a contraction of `F`. Then `D ∼ g^* D_Z` for a Cartier
divisor `D_Z` on `Z`.

For every `b ≥ b₀` the sheaf `𝒪_X(bD)` is globally generated; a basis of its sections defines
`φ_b : X ⟶ ℙᴺ_k` with `φ_b^* 𝒪(1) ≅ 𝒪_X(bD)`. The first factor `ψ_b` of the Stein factorization
`φ_b = h_b ∘ ψ_b` is a contraction of `F`, so `ψ_b = σ_b ∘ g` for an isomorphism `σ_b`, and
`𝒪_X(bD) ≅ g^* 𝓜_b` with `𝓜_b = (h_b ∘ σ_b)^* 𝒪(1)`. On the integral scheme `Z` the line bundle
`𝓜_b` is `𝒪_Z(E_b)` for a Cartier divisor `E_b`, so `bD ∼ g^* E_b`. Taking two consecutive
values of `b`, `D ∼ g^*(E_{b+1} - E_b)`.

## Main results

* `MMP.Mori.exists_linearlyEquivalent_pullback_of_isSupportingDivisor`: the statement above.

## Implementation notes

The difference of `(b+1)D` and `bD` is taken at the level of Cartier divisors, using the
additivity of the pull-back, `g^*(C + E) = g^* C + g^* E` (`MMP.CartierDivisor.pullback_add`).

The pull-back of Cartier divisors is `MMP.CartierDivisor.pullback`, defined for a
morphism from an integral scheme whose image is not contained in the support of the divisor; the
conclusion therefore also provides this condition for `D_Z`. Since a contraction is surjective and
the support of a Cartier divisor on the variety `Z` is a proper closed subset, this condition holds
for every Cartier divisor on `Z`. Linear equivalence is `MMP.Intersection.LinearlyEquivalent`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.3 Step 9
* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], II.6.15
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP MMP.Mori

namespace MMP.FourfoldProofs.Km3bContractionGivenByMultiplesProof

/-- If `𝒪_X(bD)` is globally generated, `1 ≤ b`, then `bD ∼ g^* E` for a Cartier divisor `E` on
`Z`; moreover `g` is surjective. -/
private theorem descend_nsmul {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sX]
    {F : Set (NumericalCurveClasses sX)}
    {D : X.CartierDivisor} (hD : IsSupportingDivisor k sX F D)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z} (hg : IsContractionOfFace k sX sZ F g)
    {b : ℕ} (hb : 1 ≤ b)
    (hL : MMP.Intersection.IsGloballyGenerated (MMP.CartierDivisor.sheaf (b • D))) :
    Function.Surjective g
        ∧ ∃ (E : Z.CartierDivisor) (hE : ¬ Set.range g ⊆ MMP.Intersection.cartierSupport E),
      MMP.Intersection.LinearlyEquivalent (b • D) (MMP.CartierDivisor.pullback g E hE) := by
  set L := MMP.CartierDivisor.sheaf (b • D)
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    MMP.CartierDivisor.isInvertible_sheaf (b • D)
  obtain ⟨N, t, ht, -⟩ :=
    AlgebraicGeometry.exists_fin_basis_generatesStalks_of_generatesStalks_id sX L
      hL.generatesStalks_id
  obtain ⟨θ, -⟩ :=
    AlgebraicGeometry.exists_iso_projectiveSpaceTwistingSheaf_toProjectiveSpaceOver t ht sX
  let φ := Stacks.ProjectiveFromSections.toProjectiveSpaceOver t ht sX
  let sP : projectiveSpaceOver N (Spec (.of k)) ⟶ Spec (.of k) :=
    pullback.fst (terminal.from _) (terminal.from (projectiveSpaceAtUniverse.{0} N))
  have hφ : φ ≫ sP = sX := Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst t ht sX
  haveI : IsProper sP := isProper_projectiveSpaceOver N _
  haveI : IsProper (φ ≫ sP) := hφ ▸ inferInstance
  haveI : IsProper φ := IsProper.of_comp φ sP
  let O := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k))
  have hO : Scheme.Modules.IsAmple _ O :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf N (Spec (.of k)))
  obtain ⟨Z', ψ, h, ⟨hS⟩, -, hψs, hψ, -, hfin, hvar, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sX sP φ hφ
  have hc := isContractionOfFace_of_isSupportingDivisor_of_isAmple k sX inferInstance
    hg.isExtremalFace hD hb
    sP _ hO φ hφ θ ψ h hS.comp hvar hψ
  obtain ⟨σ, hσ, -⟩ := existsUnique_iso_of_isContractionOfFace hg hc
  have hgs : Function.Surjective g := by
    rw [show g = ψ ≫ σ.inv by rw [← hσ, Category.assoc, σ.hom_inv_id, Category.comp_id]]
    exact (inferInstance : Surjective (ψ ≫ σ.inv)).surj
  haveI : IsIntegral Z := hg.isProjectiveVariety_target.toIsIntegral
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} O 1 :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ 1).1
      ((Stacks.UFDExtensionGlobal.isInvertible_iff_isFiniteLocallyFreeOfRank_one _).1 inferInstance)
  let q := σ.hom ≫ h
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0}
      ((Scheme.Modules.pullback q).obj O) 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback q O 1
  obtain ⟨E, ⟨e⟩⟩ := MMP.CartierDivisor.exists_nonempty_iso_sheaf_of_isFiniteLocallyFreeOfRank
    ((Scheme.Modules.pullback q).obj O)
  have hE := MMP.CartierDivisor.not_range_subset_cartierSupport_of_surjective hgs E
  have hφq : φ = g ≫ q := by rw [← hS.comp, ← hσ, Category.assoc]
  refine ⟨hgs, E, hE, MMP.CartierDivisor.linearlyEquivalent_of_sheaf_iso ?_⟩
  exact θ.symm ≪≫ (Scheme.Modules.pullbackCongr hφq).app O ≪≫
    (Scheme.Modules.pullbackComp g q).symm.app O ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫ (MMP.CartierDivisor.pullbackSheafIso g E hE).symm

end MMP.FourfoldProofs.Km3bContractionGivenByMultiplesProof

namespace MMP.Mori

/-- **A supporting divisor descends to the contraction** (Kollár–Mori 3.3, Step 9). Let `X` be a
projective variety over an algebraically closed field `k` of characteristic zero, `(X, Δ)` a klt
pair with canonical divisor `K` and `Δ` effective, `F` a `(K + Δ)`-negative extremal face of
`NE̅(X)`, `D` a supporting divisor of `F` and `g : X ⟶ Z` a contraction of `F`. Then there is a
Cartier divisor `D_Z` on `Z` with `g^* D_Z` linearly equivalent to `D`. -/
@[mmp "lem_km3b_contraction_given_by_multiples"]
public theorem exists_linearlyEquivalent_pullback_of_isSupportingDivisor {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective)
    {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F)
    {D : X.CartierDivisor} (hD : IsSupportingDivisor k sX F D)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z} (hg : IsContractionOfFace k sX sZ F g) :
    ∃ (DZ : Z.CartierDivisor)
        (hDZ : ¬ Set.range g ⊆ MMP.Intersection.cartierSupport DZ),
      MMP.Intersection.LinearlyEquivalent (MMP.CartierDivisor.pullback g DZ hDZ) D := by
  obtain ⟨b₀, hb₀⟩ :=
    exists_isGloballyGenerated_sheaf_nsmul_of_isSupportingDivisor hklt hΔ hF hD
  obtain ⟨hgs, E₀, hE₀, h₀⟩ :=
    MMP.FourfoldProofs.Km3bContractionGivenByMultiplesProof.descend_nsmul hD hg (b := b₀ + 1)
      b₀.succ_pos (hb₀ _ b₀.le_succ)
  obtain ⟨-, E₁, hE₁, h₁⟩ :=
    MMP.FourfoldProofs.Km3bContractionGivenByMultiplesProof.descend_nsmul hD hg (b := b₀ + 2)
      (by omega) (hb₀ _ (by omega))
  haveI : IsIntegral Z := hg.isProjectiveVariety_target.toIsIntegral
  have hsupp := MMP.CartierDivisor.not_range_subset_cartierSupport_of_surjective hgs
  refine ⟨E₁ - E₀, hsupp _, ?_⟩
  have h := MMP.CartierDivisor.pullback_add g (E₁ - E₀) E₀ (hsupp _) (hsupp _) hE₀
  simp only [sub_add_cancel] at h
  rw [h] at h₁
  unfold MMP.Intersection.LinearlyEquivalent
  convert (MMP.Intersection.principalSubgroup X).neg_mem
    ((MMP.Intersection.principalSubgroup X).sub_mem h₁ h₀) using 1
  rw [show b₀ + 2 = (b₀ + 1) + 1 by omega, succ_nsmul]
  abel

end MMP.Mori
