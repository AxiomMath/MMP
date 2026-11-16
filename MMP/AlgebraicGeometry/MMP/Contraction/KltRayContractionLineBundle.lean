module

public import MMP.AlgebraicGeometry.MMP.Contraction.Existence
public import MMP.AlgebraicGeometry.MMP.Contraction.PicardNumberDrop
public import MMP.AlgebraicGeometry.MMP.Abundance.FiniteRepresentationGeneration

section

/-!
# The contraction of a negative extremal ray of a klt log variety

Let `(X, Θ)` be a klt log variety in the sense of Kollár et al., with `Θ` a `ℚ`-divisor, where `X`
is a projective variety over an algebraically closed field of characteristic zero, and let `R` be a
`(K_X + Θ)`-negative extremal ray of `NE̅(X)`. Then there is a contraction `c : X ⟶ X_R` onto a
normal projective variety, with `c_* 𝒪_X = 𝒪_{X_R}`, which contracts exactly the integral curves
whose classes lie in `R`. It drops the Picard number by one, `ρ(X_R) + 1 = ρ(X)`, and every Cartier
divisor `M` on `X` with `M · R = 0` is linearly equivalent to the pull-back `c^* M_R` of a Cartier
divisor `M_R` on `X_R`.

## Main results

* `MMP.Flips.IsKawamataLogTerminal.exists_isContractionOfRay`.

## Implementation notes

The source works over `ℂ`; the statement is made over any algebraically closed field of
characteristic zero, and in any dimension `n`. The Picard drop is written `ρ(X_R) + 1 = ρ(X)` in
`ℕ∞`, which avoids truncated subtraction; `ρ` is `MMP.Mori.picardNumber`. The pull-back of Cartier
divisors is `MMP.CartierDivisor.pullback`, defined when the image of `c` is not contained in the
support of `M_R`, and linear equivalence is `MMP.Intersection.LinearlyEquivalent`.

The proof views `R` as a negative extremal face, so the contraction theorem gives `c` and the
Picard drop. A Cartier divisor `M` with `M · R = 0` has `deg_C 𝒪_X(M) = 0` on every curve `C`
with class in `R`, so `𝒪_X(M) ≅ c^* L` for an invertible sheaf `L` on `Z`; then `L ≅ 𝒪_Z(M_R)`
for a Cartier divisor `M_R`, and isomorphic divisorial sheaves on an integral scheme give linearly
equivalent Cartier divisors.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Ch. 15
* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Thm. 3.7.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori MMP.Fourfold

/-- **The contraction of a negative extremal ray.** Let `X` be a projective variety over an
algebraically closed field of characteristic zero, `K` a canonical divisor and `Θ` a `ℚ`-divisor
such that `(X, Θ)` is klt (`MMP.Flips.IsKawamataLogTerminal`), and let `R` be a `(K + Θ)`-negative
extremal ray of `NE̅(X)`. Then there is a contraction `c : X ⟶ Z` of `R` onto a normal projective
variety `Z` (`MMP.Fourfold.IsContractionOfRay`) with `ρ(Z) + 1 = ρ(X)`, such that every Cartier
divisor `M` on `X` with `(M · u) = 0` for all `u ∈ R` is linearly equivalent to `c^* M_R` for some
Cartier divisor `M_R` on `Z`. -/
@[mmp "thm_fourfold_fa15_projective_contraction_bundle"]
public theorem IsKawamataLogTerminal.exists_isContractionOfRay
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {Θ : QDivisor X}
    (hklt : IsKawamataLogTerminal sX n K (QDivisor.toRDivisor Θ))
    (hXp : MMP.Mori.IsProjectiveVariety k sX) {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Θ) R) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of k)) (c : X ⟶ Z),
      IsContractionOfRay sX sZ R c ∧ MMP.Mori.IsProjectiveVariety k sZ ∧
        picardNumber sZ + 1 = picardNumber sX ∧
        ∀ M : X.CartierDivisor,
          (∀ u ∈ R, NumericalCurveClasses.intersectionNumber
            (KCartierDivisor.ofCartier ℝ M) u = 0) →
          ∃ (MR : Z.CartierDivisor)
            (hMR : ¬ Set.range c ⊆ MMP.Intersection.cartierSupport MR),
            MMP.Intersection.LinearlyEquivalent M
              (MMP.CartierDivisor.pullback c MR hMR) := by
  have hX : IsNormalVariety k sX := hklt.1.isNormalVariety
  have hF4 : MMP.Fourfold.IsKltPair sX Θ :=
    (isKltPair_iff_mori_isKltPair sX hklt.2.1 ⟨‹_›, ‹_›, ⟨hX, n, K, hklt.2.1, hR.1⟩,
      fun P => by simpa [QDivisor.coeff_toRDivisor] using (hklt.1.isBoundary P).1⟩).mpr
      ((isKawamataLogTerminal_iff_isKltPair sX n K Θ hX hklt.2.1 hklt.1.isBoundary hR.1).mp hklt)
  have hkm : MMP.Mori.IsKltPair sX n K Θ :=
    (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hklt.2.1 hF4.1).mp hF4
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hXp
  have hΘe : Θ.IsEffective := hF4.1.nonneg
  obtain ⟨hQ, hray, hneg⟩ := hR
  have hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Θ) hkm.1.2.2) R :=
    ⟨hray.1, hray.1.2.2.1, hneg⟩
  obtain ⟨Z, sZ, ψ, hψ, hZn⟩ :=
    MMP.Mori.exists_isContractionOfFace_of_isNegativeExtremalFace hkm hΘe hF
  haveI : AlgebraicGeometry.IsVariety k sZ := hZn.1
  have hproj : IsProjectiveMorphism ψ :=
    IsProjectiveMorphism.of_comp ψ sZ (by rw [hψ.comp_eq]; exact hXp.isProjective)
  haveI : IsProper ψ := isProper_of_isProjectiveMorphism ψ hproj
  have hsurj : Surjective ψ := ψ.surjective_of_isIso_app hψ.isIso_app
  refine ⟨Z, sZ, ψ,
    ⟨⟨hX, hZn, hψ.comp_eq, hproj, hsurj.surj, hψ.isIso_app⟩, hψ.isContractedBy_iff⟩,
    hψ.isProjectiveVariety_target,
    MMP.Mori.picardNumber_add_one_eq_of_isContractionOfFace hkm hΘe hray hneg hψ, ?_⟩
  intro M hM
  haveI : IsIntegral Z := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := sZ)
  obtain ⟨LZ, hLZ, ⟨e⟩⟩ := MMP.Mori.exists_isInvertible_iso_pullback_of_isContractionOfFace hkm
    hΘe hF hψ (MMP.CartierDivisor.sheaf M) fun C hC => by
      have h := hM _ hC
      rw [NumericalCurveClasses.intersectionNumber_numericalClass,
        OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle] at h
      exact_mod_cast h
  obtain ⟨E, ⟨e'⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf LZ
  have hE : ¬ Set.range ψ ⊆ MMP.Intersection.cartierSupport E := fun h =>
    MMP.CartierDivisor.genericPoint_notMem_cartierSupport E
      (h (hsurj.surj (genericPoint Z)))
  exact ⟨E, hE, MMP.CartierDivisor.linearlyEquivalent_of_sheaf_iso
    (e ≪≫ (Scheme.Modules.pullback ψ).mapIso e' ≪≫
      (MMP.CartierDivisor.pullbackSheafIso ψ E hE).symm)⟩

end MMP.Flips

end
