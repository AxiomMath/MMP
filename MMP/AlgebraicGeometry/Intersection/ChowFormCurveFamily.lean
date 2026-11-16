module
public import MMP.AlgebraicGeometry.ChowForm.FibreChowForm

/-!
# The Chow form of a proper flat family of curves

Let `k` be an algebraically closed field of characteristic zero, `S` a normal `k`-variety, `Y` a
projective `k`-scheme with a projective `k`-morphism `g : Y ⟶ ℙᴺ_k`, and `𝒞 ⊆ S ×ₖ Y` a closed
subscheme which is proper and flat over `S` with one-dimensional closed fibres. For a closed point
`s ∈ S` let `Z_s = g_*[𝒞_s]` be the push-forward to `ℙᴺ_k` of the fundamental 1-cycle
`[𝒞_s] = ∑ᵢ mᵢ [Cᵢ]` of the fibre, the sum over its one-dimensional irreducible components with
`mᵢ` the length of the local ring at the generic point. Suppose every `Z_s` has the same
hyperplane degree `d > 0`.

The *incidence form* (Chow form) of an integral curve `C ⊆ ℙᴺ_k` is the irreducible polynomial
`Ch_C(u, v)` in two sets of `N + 1` variables whose zero locus is the set of pairs of hyperplanes
`(H_u, H_v)` with `C ∩ H_u ∩ H_v ≠ ∅`; it is unique up to a scalar. Then there is a unique
`k`-morphism `φ` from `S` to the projective space of bihomogeneous forms of bidegree `(d, d)`
sending each closed point `s` to the class of `∏_C Ch_C^{Z_s(C)}`, the product over the
components of `Z_s`. This construction commutes with base change along every morphism of normal
`k`-varieties `S' ⟶ S`.

## Main results

* `MMP.Chow.exists_chowFormMorphism`: the morphism `φ`, with its uniqueness and its base-change
  compatibility.

## Implementation notes

* The source works over `ℂ`; the statement is made over an algebraically closed field of
  characteristic zero, which is all the proof uses.
* `ℙᴺ_k` is `Proj k[T₀, …, T_N]` (`Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading`) with
  structure morphism `projToSpecCoeff` and hyperplane sheaf `𝒪(1)`, the degree-one twisting sheaf.
  Bihomogeneous forms of bidegree `(d, d)` are polynomials in the variables `Sum.inl j` (the
  coefficients `u` of the first hyperplane) and `Sum.inr j` (those `v` of the second), and the
  space of these forms is `MMP.Intersection.ProjSpace k B` for the set `B` of monomials of that
  bidegree. A closed point of it is the class `[F]` of a nonzero form `F` exactly when its
  homogeneous prime contains every `F_{b'} X_b - F_b X_{b'}`.
* The fibre cycle is built from `MMP.Mori.ProperCurve` on the fibre `π.fiber s`, regarded as a
  `k`-scheme, and pushed forward with `MMP.Mori.cyclePushforwardOfPoint`; its degree is
  `MMP.Mori.OneCycle.degree` for `𝒪(1)`.
* "Natural" is made precise in two ways: `φ` is the unique `k`-morphism with the stated values at
  closed points, and for a morphism `h : S' ⟶ S` of normal `k`-varieties the composite `h ≫ φ`
  has the stated values for the base-changed family `𝒞 ×_S S' ⟶ S'`, so by uniqueness it is the
  morphism of that family.

## References

* [J. Kollár, *Rational curves on algebraic varieties*][Kollar1996], I.3
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Stacks.AlgebraicGeometry.ProjPolyChart MvPolynomial

universe u

namespace MMP.Chow

open DeterminantCurveForm

attribute [local instance] MvPolynomial.gradedAlgebra

section Local

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {N : ℕ}

attribute [local instance] LocalFreeData.isOpenImmersion LocalFreeData.isAffine
  LocalFreeData.isDomain LocalFreeData.isNoetherian LocalFreeData.isIntegrallyClosed
  LocalFreeData.locFT

/-- **The determinant form of the Koszul complex (the core of the construction).** Every point
of the normal variety `S` has an open neighbourhood `U` (affine, with the direct images `V_j`
free) and sections `c_b ∈ Γ(U, 𝒪)`, `b` of bidegree `(d, d)`, namely the coefficients of the
determinant `F ∈ Γ(U, 𝒪)[u, v]` of the three-term complex
`V₂ ⊗ 𝒪(-1,-1) → V₁ ⊗ (𝒪(-1,0) ⊕ 𝒪(0,-1)) → V₀` of direct images of the Koszul complex of the
universal hyperplane equations, such that
* the coefficients generate the unit ideal (an avoiding pair of hyperplanes makes the complex
  exact, so `F` is a unit there), and
* at every closed point `u` the vector `(c_b(u))_b` is a multiple of the coefficient vector of the
  product of the incidence forms with the cycle multiplicities, which has bidegree `(d, d)`.

The bidegree comes from `rank V_j - rank V_{j+1} = d`, and the poles of `F` are removed by
Hartogs extension on the normal variety `S`. -/
private theorem exists_chowSections_local {S Y 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d)
    (hdeg : haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
      ∀ s : S, IsClosed ({s} : Set S) →
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1) (cyc g sS π q s) = d) :
    ∀ s : S, ∃ (U : Scheme.{u}) (ι : U ⟶ S), IsOpenImmersion ι ∧ s ∈ Set.range ι ∧
      letI := structureAlgebra (k := k) (ι ≫ sS)
      ∃ (c : ULift.{u} (Bi N d) → Γ(U, ⊤)), Ideal.span (Set.range c) = ⊤ ∧
        ∀ u : U, IsClosed ({u} : Set U) →
          ∀ G : Mori.ProperCurve (projToSpecCoeff k N) →
              MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k,
            (∀ C ∈ (cyc g (ι ≫ sS) (pullback.snd π ι) (pullback.fst π ι ≫ q) u).support,
              IncForm C (G C)) →
            (∀ e ∈ (∏ C ∈ (cyc g (ι ≫ sS) (pullback.snd π ι) (pullback.fst π ι ≫ q) u).support,
                G C ^ ((cyc g (ι ≫ sS) (pullback.snd π ι) (pullback.fst π ι ≫ q) u) C).toNat
                ).support,
              (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d) ∧
            ∃ l : U.residueField u, ∀ b : ULift.{u} (Bi N d),
              U.Γevaluation u (c b) = l * U.Γevaluation u (algebraMap k Γ(U, ⊤)
                ((∏ C ∈ (cyc g (ι ≫ sS) (pullback.snd π ι) (pullback.fst π ι ≫ q) u).support,
                  G C ^ ((cyc g (ι ≫ sS) (pullback.snd π ι) (pullback.fst π ι ≫ q) u) C).toNat
                  ).coeff b.down.1)) := by
  intro s
  obtain ⟨D, hD, hDF⟩ := exists_localFreeData sS sY hS hY g hg hgY π q hπq hdim d hd hdeg s
  have h0 : ∀ x : D.U, IsClosed ({x} : Set D.U) →
      ∃ a b : Fin (N + 1) → k, AvoidsPair (fibreImage g π q D.ι x) a b :=
    fun x hx => exists_avoidsPair sS sY hS hY g hg hgY π q hπq hdim D.ι x hx
  obtain ⟨P, hP⟩ := complexDet_mem_polynomial D hD h0
  refine ⟨D.U, D.ι, inferInstance, D.mem, ?_⟩
  letI := structureAlgebra (k := k) (D.ι ≫ sS)
  refine ⟨fun b => P.coeff b.down.1, ?_, ?_⟩
  · have h4 := span_coeff_complexDet_eq_top D hD h0 P hP
    rw [eq_top_iff, ← h4, Ideal.span_le]
    rintro _ ⟨e, rfl⟩
    by_cases he : e ∈ P.support
    · exact Ideal.subset_span ⟨⟨⟨e, complexDet_isBihomogeneous D hD h0 P hP e he⟩⟩, rfl⟩
    · show P.coeff e ∈ _
      rw [MvPolynomial.notMem_support_iff.mp he]; exact zero_mem _
  · intro x hx G hG
    obtain ⟨l, hl0, hl⟩ := hDF x hx G hG
    have h5 := complexDet_specialize D hD h0 P hP x hx
    have heq := IsFractionRing.injective (D.PolAt x) (FractionRing (D.PolAt x)) (h5.trans hl)
    have hco : ∀ e, (D.U.Γevaluation x).hom (P.coeff e) = l * kEval (D.ι ≫ sS) x
        ((∏ C ∈ (D.cycAt x).support, G C ^ ((D.cycAt x) C).toNat).coeff e) := by
      intro e
      have := congrArg (fun p : MvPolynomial _ _ => p.coeff e) heq
      simp only [LocalFreeData.specHom, MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at this
      exact this
    refine ⟨fun e he => ?_, l, fun b => ?_⟩
    · apply complexDet_isBihomogeneous D hD h0 P hP
      rw [MvPolynomial.mem_support_iff]
      intro h
      have := hco e
      rw [h, map_zero] at this
      have hne : (∏ C ∈ (D.cycAt x).support, G C ^ ((D.cycAt x) C).toNat).coeff e ≠ 0 :=
        MvPolynomial.mem_support_iff.mp he
      exact mul_ne_zero hl0 ((map_ne_zero_iff _ (kEval (D.ι ≫ sS) x).injective).mpr hne) this.symm
    · exact hco b.down.1

/-- Local existence of the Chow-form morphism: the morphism attached to the coefficients of the
determinant form by `sectionsToProjSpace`. -/
private theorem exists_chowMor_local {S Y 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d)
    (hdeg : haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
      ∀ s : S, IsClosed ({s} : Set S) →
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1) (cyc g sS π q s) = d) :
    ∀ s : S, ∃ (U : Scheme.{u}) (ι : U ⟶ S), IsOpenImmersion ι ∧ s ∈ Set.range ι ∧
      ∃ φ : U ⟶ Intersection.ProjSpace k (ULift.{u} (Bi N d)),
        ChowMor g d (ι ≫ sS) (pullback.snd π ι) (pullback.fst π ι ≫ q) φ := by
  intro s
  obtain ⟨U, ι, hι, hs, c, hc, hval⟩ :=
    exists_chowSections_local sS sY hS hY g hg hgY π q hπq hdim d hd hdeg s
  letI := structureAlgebra (k := k) (ι ≫ sS)
  refine ⟨U, ι, hι, hs, sectionsToProjSpace (k := k) c hc, ?_, fun u hu => ?_⟩
  · exact sectionsToProjSpace_toSpec (k := k) (ι ≫ sS)
      (eq_toSpecΓ_comp_structureAlgebra (ι ≫ sS)) c hc
  · intro G hG
    obtain ⟨hb, l, hl⟩ := hval u hu G hG
    refine ⟨hb, fun b b' => ?_⟩
    exact linear_mem_asHomogeneousIdeal_sectionsToProjSpace c hc u _ l hl b b'

/-- Existence of the Chow-form morphism. -/
private theorem exists_chowMor {S Y 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d)
    (hdeg : haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
      ∀ s : S, IsClosed ({s} : Set S) →
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1) (cyc g sS π q s) = d) :
    ∃ φ : S ⟶ Intersection.ProjSpace k (ULift.{u} (Bi N d)), ChowMor g d sS π q φ := by
  haveI := hS.1
  choose U ι hι hs φ hφ using exists_chowMor_local sS sY hS hY g hg hgY π q hπq hdim d hd hdeg
  haveI := hι
  exact exists_chowMor_of_cover sS g d π q
    (Scheme.Cover.mkOfCovers S U ι (fun x => ⟨x, hs x⟩) hι) fun x => ⟨φ x, hφ x⟩

end Local

/-- **The Chow form of a proper flat family of curves.** Let `S` be a normal variety over an
algebraically closed field `k` of characteristic zero, `Y` a projective `k`-scheme with a
projective `k`-morphism `g : Y ⟶ ℙᴺ_k`, and `π : 𝒞 ⟶ S`, `q : 𝒞 ⟶ Y` a closed subscheme of
`S ×ₖ Y`, proper and flat over `S`, with one-dimensional closed fibres. For a closed point `s` let
`Z_s = ∑ᵢ mᵢ (g ∘ q)_*[Cᵢ]` be the push-forward to `ℙᴺ_k` of the fundamental 1-cycle of `𝒞_s`, and
suppose `deg_{𝒪(1)} Z_s = d > 0` for all `s`. Then there is a unique `k`-morphism `φ` from `S` to
the projective space of bihomogeneous forms of bidegree `(d, d)` such that, for every closed point
`s` and every choice of incidence forms `G_C` of the components `C` of `Z_s` (irreducible
polynomials in `(u, v)` vanishing exactly when `C ∩ H_u ∩ H_v ≠ ∅`), the form
`F = ∏_C G_C^{Z_s(C)}` has bidegree `(d, d)` and `φ(s) = [F]`. For every morphism `h : S' ⟶ S` of
normal `k`-varieties, `h ≫ φ` has the same property for the family `𝒞 ×_S S' ⟶ S'`. -/
@[mmp "lem_mmp_chow_determinant_curve_form"]
public theorem exists_chowFormMorphism {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {S Y 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    {N : ℕ} (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) (hd : 0 < d) :
    haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
    -- the push-forward to `ℙᴺ_k` of the fundamental 1-cycle of the fibre of `ρ` over `s`
    let cyc : ∀ {T 𝒟 : Scheme.{u}} (sT : T ⟶ Spec (.of k)) (ρ : 𝒟 ⟶ T) (r : 𝒟 ⟶ Y) (s : T),
        Mori.OneCycle ℤ (projToSpecCoeff k N) := fun sT ρ r s =>
      ∑ᶠ C : {C : Mori.ProperCurve (ρ.fiberι s ≫ ρ ≫ sT) //
              closure {C.point} ∈ irreducibleComponents (ρ.fiber s)},
        ((Module.length ((ρ.fiber s).presheaf.stalk C.1.point)
            ((ρ.fiber s).presheaf.stalk C.1.point)).toNat : ℤ) •
          Mori.cyclePushforwardOfPoint ℤ (projToSpecCoeff k N) (ρ.fiberι s ≫ r ≫ g) C.1.point
    -- the monomials of bidegree `(d, d)` in `(u, v)`
    let B := {e : (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ //
      (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d}
    -- `φ` is a `k`-morphism sending each closed point to the class of the product of the
    -- incidence forms of the components of the pushed-forward fibre cycle
    let P : ∀ {T 𝒟 : Scheme.{u}}, (T ⟶ Spec (.of k)) → (𝒟 ⟶ T) → (𝒟 ⟶ Y) →
        (T ⟶ Intersection.ProjSpace k (ULift.{u} B)) → Prop := fun sT ρ r φ =>
      φ ≫ Intersection.ProjSpace.toSpec k _ = sT ∧
      ∀ s, IsClosed ({s} : Set _) →
        ∀ G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k,
          (∀ C ∈ (cyc sT ρ r s).support, Irreducible (G C) ∧
            ∀ u v : Fin (N + 1) → k, eval (Sum.elim u v) (G C) = 0 ↔
              ∃ p ∈ closure ({C.point} : Set (AlgebraicGeometry.Proj (polyGrading k N))),
                (∑ j, MvPolynomial.C (u j) * X j) ∈ ProjectiveSpectrum.asHomogeneousIdeal p ∧
                (∑ j, MvPolynomial.C (v j) * X j) ∈ ProjectiveSpectrum.asHomogeneousIdeal p) →
          let F := ∏ C ∈ (cyc sT ρ r s).support, G C ^ (cyc sT ρ r s C).toNat
          (∀ e ∈ F.support, (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d) ∧
          ∀ b b' : ULift.{u} B, F.coeff b'.down.1 • X b - F.coeff b.down.1 • X b' ∈
            ProjectiveSpectrum.asHomogeneousIdeal (φ s)
    (∀ s : S, IsClosed ({s} : Set S) →
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1) (cyc sS π q s) = d) →
    ∃ φ, (∀ ψ, P sS π q ψ ↔ ψ = φ) ∧
      ∀ (S' : Scheme.{u}) (sS' : S' ⟶ Spec (.of k)), Mori.IsNormalVariety k sS' →
        ∀ h : S' ⟶ S, h ≫ sS = sS' →
          P sS' (pullback.snd π h) (pullback.fst π h ≫ q) (h ≫ φ) := by
  intro _ _ _ hdeg
  obtain ⟨φ, hφ⟩ := exists_chowMor sS sY hS hY g hg hgY π q hπq hdim d hd hdeg
  haveI := hS.1
  exact ⟨φ, fun ψ => ⟨fun hψ => chowMor_unique sS g d π q hψ hφ, fun h => h ▸ hφ⟩,
    fun S' sS' hS' h hh => by
      haveI := hS'.1
      exact chowMor_baseChange sS sS' g d π q hφ h hh⟩

end MMP.Chow
