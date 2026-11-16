module

public import MMP.AlgebraicGeometry.DeRham.Logarithmic.DeligneIllusieReduction
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Construction
public import MMP.AlgebraicGeometry.Cohomology.StupidTruncationEdgeSurjective
public import MMP.Analysis.Complex.Coherent.MatrixMapsSubmanifolds
public import MMP.AlgebraicGeometry.Singularities.Snc.SncOfRelativeSnc
public import MMP.AlgebraicGeometry.Analytic.SmoothCentreSlices
public import MMP.AlgebraicGeometry.DeRham.BettiComparison

/-!
# The restriction complex of a simple normal crossing divisor

Let `Z` be a smooth projective complex variety and `E` a reduced simple normal crossing divisor
on `Z`. The compact logarithmic de Rham complex `Ω^•_Z(log E)(-E)` is a subcomplex of `Ω^•_Z`,
and the *restriction complex* of `E` is the quotient

`𝒟_E^• = Ω^•_Z / Ω^•_Z(log E)(-E)`.

Its Hodge-to-de Rham spectral sequence (the spectral sequence of the stupid filtration,
`E_1^{p,q} = H^q(Z, 𝒟_E^p) ⇒ ℍ^{p+q}(Z, 𝒟_E^•)`) degenerates at `E₁`, and its degree-zero term is
`𝒟_E^0 = 𝒪_Z / 𝒪_Z(-E) = 𝒪_E`. After analytification `𝒟_E^•` resolves the constant sheaf
`ℂ_E`, and the degree-zero edge map of the degenerate spectral sequence is the map
`H^i(E, ℂ) → H^i(E, 𝒪_E^an)` induced by the inclusion of the constants `ℂ_E → 𝒪_E^an`; it is
therefore surjective for every `i`.

## Main results

* `MMP.Mori.Divisor.IsRelativeSNC.restrictionComplex_degenerates_and_surjective`: the three
  assertions above.

## Implementation notes

* The variety is a scheme `Z` with a morphism `sZ : Z ⟶ Spec ℂ` smooth of relative dimension `n`
  and projective; a reduced snc divisor is a relative snc divisor over `Spec ℂ`
  (`MMP.Mori.Divisor.IsRelativeSNC`, which includes reducedness).
* `Ω^•_Z(log E)(-E)` is `MMP.Mori.Divisor.relativeLogDeRhamComplex n sZ E hE E.suppIdeal`, a
  subcomplex of `j_*Ω^•_{U}` for `U = Z ∖ E`. Its inclusion `i` into
  `Ω^•_Z = AlgebraicGeometry.Scheme.Hom.deRhamComplex sZ` is pinned by the requirement that `i`
  followed by restriction to `U` (`Stacks.DeRhamPullback.deRhamPushforwardChain`) is the
  inclusion into `j_*Ω^•_U`; since restriction to the dense open `U` is injective, this
  determines `i`. The quotient `𝒟_E^•` is any cokernel `q : Ω^•_Z ⟶ D` of `i` in the abelian
  category of complexes; every assertion is invariant under isomorphism of cokernels.
* Degeneration at `E₁` is stated, as in
  `MMP.Mori.Divisor.finrank_hypercohomology_relativeLogDeRhamComplex_eq_sum`, as the equality
  `dim_ℂ ℍ^k(Z, 𝒟_E^•) = ∑_{p ≤ k} dim_ℂ H^{k-p}(Z, 𝒟_E^p)`: all these spaces are finite
  dimensional since `Z` is projective, and `E_∞` is a subquotient of `E_1` of the same total
  dimension exactly when every differential `d_r`, `r ≥ 1`, vanishes.
* `𝒟_E^0 = 𝒪_E` is stated canonically: under `Ω^0_Z ≅ 𝒪_Z`
  (`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsZeroIso`), a function on an affine open
  is killed by `q` exactly when it lies in the ideal of `E`.
* `E` is the closed subscheme `E.suppIdeal.subscheme`, `E^an` its analytification
  (`MMP.Analytic.analytification`), and sheaf cohomology is `MMP.Analytic.sheafCohomology` of
  sheaves of abelian groups on `E^an`. The map `ℂ_E → 𝒪_E^an` is the adjoint of the constants
  `ℂ → Γ(E, 𝒪_E) → Γ(E^an, 𝒪_E^an)`.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de
  Rham*][DeligneIllusie1987]
* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992]
-/

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open MMP.Mori MMP.Mori.Divisor
open MMP.Mori.Divisor.LogSpreadingProof MMP.FourfoldProofs.LogDegenerationProof
open MMP.FourfoldProofs.FractionalLogComplexProof (TB δ proj_incl_of_ne isSMulRegular_of_basis_D)
open MMP.Mori.Divisor.MmpRelativeLogFormsBasisProof (appLE_id flat_map injective_map_of_eq_basicOpen)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Proof_thm_mmp_conductor_snc_restriction_degeneration

/-! ### Functions are determined off a relative snc divisor -/

section Density

variable {n : ℕ} {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension n f]
  {D : Divisor X}

/-- On an affine open `W'` where the support of `D` is cut out by `h`, the complement of the
support is the basic open of `h`. -/
private theorem basicOpen_eq_compl_inf {W' : X.affineOpens} {h : Γ(X, W')}
    (hI : D.suppIdeal.ideal W' = Ideal.span {h}) :
    X.basicOpen h = (D.supp.compl : X.Opens) ⊓ W' := by
  have key : ∀ x ∈ (W' : X.Opens), x ∈ (D.supp : Set X) ↔ x ∉ X.basicOpen h := by
    intro x hx
    rw [← MMP.Mori.DivisorWithCoeffs.coe_support_suppIdeal, SetLike.mem_coe,
      D.suppIdeal.mem_support_iff_of_mem hx, hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
    rfl
  ext x
  refine ⟨fun hx => ⟨fun hxD => (key x (X.basicOpen_le h hx)).mp hxD hx, X.basicOpen_le h hx⟩,
    fun ⟨hxU, hxW⟩ => ?_⟩
  by_contra hx
  exact hxU ((key x hxW).mpr hx)

include f in
/-- **Functions are determined off the divisor.** For a relative simple normal crossing divisor
`D` on `X` and any open `W`, restriction `Γ(X, W) → Γ(X ∖ D, W ∖ D)` is injective. -/
private theorem app_compl_injective (hD : D.IsRelativeSNC n f) (W : X.Opens) :
    Function.Injective (X.presheaf.map
      (homOfLE (inf_le_right : (D.supp.compl : X.Opens) ⊓ W ≤ W)).op).hom := by
  intro a b hab
  have hloc : ∀ x : W, ∃ (W'' : X.affineOpens) (h : (W'' : X.Opens) ≤ W), x.1 ∈ (W'' : X.Opens) ∧
      X.presheaf.map (homOfLE h).op a = X.presheaf.map (homOfLE h).op b := by
    intro x
    obtain ⟨Wc, V, e, t, hx, hb, r, hr, j, -, -, hDW⟩ := hD.2 x.1
    obtain ⟨_, ⟨W'', hW''a, rfl⟩, hxW'', hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_inter x.2 hx) (W ⊓ (Wc : X.Opens)).isOpen
    let W''a : X.affineOpens := ⟨W'', hW''a⟩
    have hle1 : (W''a : X.Opens) ≤ W := fun y hy => (hle hy).1
    have hle2 : (W''a : X.Opens) ≤ Wc := fun y hy => (hle hy).2
    refine ⟨W''a, hle1, hxW'', ?_⟩
    -- the product of the boundary coordinates on `W''`
    let hh : Γ(X, W''a) := X.presheaf.map (homOfLE hle2).op (∏ i, t (Fin.castLE hr i))
    have hI : D.suppIdeal.ideal W''a = Ideal.span {hh} := by
      rw [← D.suppIdeal.map_ideal hle2, hDW, Ideal.map_span, Set.image_singleton]
      rfl
    have hreg : IsSMulRegular Γ(X, W''a) hh := by
      let _ := (f.appLE V Wc e).hom.toAlgebra
      have : Algebra.Smooth Γ(S, V) Γ(X, Wc) :=
        HasRingHomProperty.appLE @Smooth f (SmoothOfRelativeDimension.smooth n f) V Wc e
      obtain ⟨b, hb⟩ := hb
      have hreg : IsSMulRegular Γ(X, Wc) (∏ i, t (Fin.castLE hr i)) :=
        Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) (IsSMulRegular.one Γ(X, Wc))
          fun i _ => isSMulRegular_of_basis_D t b hb _
      let _ := (X.presheaf.map (homOfLE hle2).op).hom.toAlgebra
      have := flat_map hle2
      exact hreg.of_flat
    have hres := injective_map_of_eq_basicOpen W''a.2 hreg (basicOpen_eq_compl_inf hI).symm
      inf_le_right
    refine hres ?_
    have hk : (D.supp.compl : X.Opens) ⊓ (W''a : X.Opens) ≤ (D.supp.compl : X.Opens) ⊓ W :=
      inf_le_inf_left _ hle1
    rw [MMP.DeRham.ring_presheaf_map_map _ _ (homOfLE (hk.trans inf_le_right)),
      MMP.DeRham.ring_presheaf_map_map _ _ (homOfLE (hk.trans inf_le_right)),
      ← MMP.DeRham.ring_presheaf_map_map (homOfLE inf_le_right) (homOfLE hk),
      ← MMP.DeRham.ring_presheaf_map_map (homOfLE inf_le_right) (homOfLE hk), hab]
  choose W'' hW'' hxW'' heq using hloc
  exact TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun x => (W'' x : X.Opens)) W
    (fun x => homOfLE (hW'' x)) (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW'' _⟩) a b heq

end Density

/-! ### Degree-zero forms -/

section DegreeZero

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The degree-zero identification `Ω^0 ≅ 𝒪` takes `r · 1` to `r`. -/
private theorem zeroIso_hom_smul_one (W : X.Opens) (r : X.sheaf.obj.obj (op W)) :
    (Scheme.Hom.relativeDifferentialFormsZeroIso f).hom.val.app (op W)
      (r • (Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op W)) = r := by
  erw [PresheafOfModules.app_smul,
    (Scheme.Hom.deRhamAlgebras f).exteriorPieceZeroIsoUnit_one (op W)]
  exact mul_one r

/-- The inverse of the degree-zero identification `Ω^0 ≅ 𝒪` takes `r` to `r · 1`. -/
private theorem zeroIso_inv_eq_smul_one (W : X.Opens) (r : Γ(X, W)) :
    (Scheme.Hom.relativeDifferentialFormsZeroIso f).inv.val.app (op W) r =
      (show X.sheaf.obj.obj (op W) from r) •
        (Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op W) := by
  have h3 : ∀ x, (Scheme.Hom.relativeDifferentialFormsZeroIso f).inv.val.app (op W)
      ((Scheme.Hom.relativeDifferentialFormsZeroIso f).hom.val.app (op W) x) = x := fun x =>
    congrArg (fun φ => φ.val.app (op W) x)
      (Scheme.Hom.relativeDifferentialFormsZeroIso f).hom_inv_id
  conv_lhs => rw [← zeroIso_hom_smul_one f W r]
  exact h3 _

/-- Degree-zero forms are free on `1`. -/
private theorem smul_one_injective (W : X.Opens) :
    Function.Injective fun r : X.sheaf.obj.obj (op W) =>
      r • (Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op W) := by
  intro r s h
  have := congrArg ((Scheme.Hom.relativeDifferentialFormsZeroIso f).hom.val.app (op W)) h
  rwa [zeroIso_hom_smul_one, zeroIso_hom_smul_one] at this

/-- **Restriction of degree-zero forms.** The canonical map `Ω^0_X ⟶ j_*Ω^0_U` of an open
`j : U ⟶ X` carries `r · 1` to `r|_U · 1`. -/
private theorem pushforwardChain_zero_smul_one (U W : X.Opens) (r : X.sheaf.obj.obj (op W)) :
    ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι U) f).f 0).val.app (op W)
        (r • (Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op W)) =
      (show U.toScheme.sheaf.obj.obj (op (U.ι ⁻¹ᵁ W)) from (U.ι.app W).hom r) •
        (Scheme.Hom.deRhamAlgebras (U.ι ≫ f)).exterior.one.eval (op (U.ι ⁻¹ᵁ W)) := by
  change ((Stacks.DeRhamPullback.pushforwardSquareIso (Scheme.Opens.ι U) f).inv.app
      (Scheme.Hom.relativeDifferentialForms (U.ι ≫ f) ((0 : ℕ) : ℤ))).val.app (op W)
      (((Stacks.DeRhamPullback.formsPushforwardComponent (Scheme.Opens.ι U) f 0).val.app (op W))
        (r • (Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op W))) = _
  refine (Stacks.DeRhamPullback.pushforwardSquareIso_inv_val_app (Scheme.Opens.ι U) f
    (Scheme.Hom.relativeDifferentialForms (U.ι ≫ f) ((0 : ℕ) : ℤ)) (op W)
    (((Stacks.DeRhamPullback.formsPushforwardComponent (Scheme.Opens.ι U) f 0).val.app (op W))
        (r • (Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op W)))).trans ?_
  refine (Scheme.Hom.deRhamFormsPushforwardHom_smul _ _ _ _ _ 0 (op W) r _).trans ?_
  have h1 : ((Scheme.Hom.deRhamFormsPushforwardHom (Scheme.Opens.ι U) f (U.ι ≫ f) (𝟙 S)
      (Category.comp_id (U.ι ≫ f)).symm).app 0).val.app (op W)
        ((Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op W)) =
      (Scheme.Hom.deRhamAlgebras (U.ι ≫ f)).exterior.one.eval (op (U.ι ⁻¹ᵁ W)) :=
    (Scheme.Hom.deRhamFormsPushforwardHom _ _ _ _ _).map_one (op W)
  rw [h1]
  rfl

variable {n : ℕ} [SmoothOfRelativeDimension n f] {D : Divisor X}

include f in
/-- Restriction of functions to the complement of a relative snc divisor is injective. -/
private theorem ι_app_compl_injective (hD : D.IsRelativeSNC n f) (W : X.Opens) :
    Function.Injective ((Scheme.Opens.ι (D.supp.compl : X.Opens)).app W).hom := by
  obtain ⟨h0, e⟩ : ∃ h0 : Scheme.Opens.ι (D.supp.compl : X.Opens) ''ᵁ
      Scheme.Opens.ι (D.supp.compl : X.Opens) ⁻¹ᵁ W ≤ W,
      (Scheme.Opens.ι (D.supp.compl : X.Opens)).app W = X.presheaf.map (homOfLE h0).op :=
    ⟨_, Scheme.Opens.ι_app _ _⟩
  have hO : (D.supp.compl : X.Opens) ⊓ W ≤ Scheme.Opens.ι (D.supp.compl : X.Opens) ''ᵁ
      Scheme.Opens.ι (D.supp.compl : X.Opens) ⁻¹ᵁ W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  intro a b hab
  rw [e] at hab
  apply app_compl_injective f hD W
  change X.presheaf.map (homOfLE h0).op a = X.presheaf.map (homOfLE h0).op b at hab
  rw [← MMP.DeRham.ring_presheaf_map_map (homOfLE h0) (homOfLE hO) (homOfLE (hO.trans h0)),
    ← MMP.DeRham.ring_presheaf_map_map (homOfLE h0) (homOfLE hO) (homOfLE (hO.trans h0)), hab]

/-- **Degree-zero forms are determined off the divisor.** -/
private theorem pushforwardChain_zero_injective (hD : D.IsRelativeSNC n f) (W : X.Opens) :
    Function.Injective
      (((Stacks.DeRhamPullback.deRhamPushforwardChain
        (Scheme.Opens.ι (D.supp.compl : X.Opens)) f).f 0).val.app (op W)) := by
  intro x y h
  obtain ⟨r, hr⟩ := (Scheme.Hom.deRhamAlgebras f).exists_exterior_eq_smul_one (op W) x
  obtain ⟨s, hs⟩ := (Scheme.Hom.deRhamAlgebras f).exists_exterior_eq_smul_one (op W) y
  subst hr hs
  have h' := (pushforwardChain_zero_smul_one f D.supp.compl W r).symm.trans
    (h.trans (pushforwardChain_zero_smul_one f D.supp.compl W s))
  have h3 : ((Scheme.Opens.ι (D.supp.compl : X.Opens)).app W).hom r =
      ((Scheme.Opens.ι (D.supp.compl : X.Opens)).app W).hom s :=
    smul_one_injective (Scheme.Opens.ι (D.supp.compl : X.Opens) ≫ f)
      (Scheme.Opens.ι (D.supp.compl : X.Opens) ⁻¹ᵁ W) h'
  rw [ι_app_compl_injective f hD W h3]

end DegreeZero

/-! ### The degree-zero part of the ring of forms generated by functions and log forms -/

section TotalRing

variable {Y S : Scheme.{u}} (g : Y ⟶ S)

variable {g}

/-- A product of degree-one elements is homogeneous of degree the length of the list. -/
private theorem exists_prod_eq_incl {O : Y.Opens} (l : List Γ(Y, O)) :
    ∃ k : ℤ, k = l.length ∧
      ∃ y : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece k).val.obj (op O),
        (l.map (δ g O)).prod = (TB g).incl k y := by
  induction l with
  | nil => exact ⟨0, rfl, (TB g).one.eval (op O), (TB g).one_eq_incl (op O)⟩
  | cons a l ih =>
    obtain ⟨k, hk, y, hy⟩ := ih
    refine ⟨1 + k, by simp [hk]; ring, ((TB g).mul 1 k).app (op O)
      ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials g)).val.app (op O)
        ((Scheme.Hom.universalRelativeDerivation g).d (X := op O) a)) y, ?_⟩
    rw [List.map_cons, List.prod_cons, hy]
    exact (TB g).incl_mul_incl 1 k _ y

private theorem structureMap_mul_eq_smul {O : Y.Opens}
    (c : (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O))
    (z : (TB g).Total (op O)) :
    (TB g).structureMap (op O) c * z = c • z := by
  change c • (1 : (TB g).Total (op O)) * z = _
  rw [(TB g).smul_mul_eq, one_mul]

/-- **The degree-zero part of the ring generated by functions and one-forms.** If every
generator is the image of a function in a subring `R`, or a function times an exact one-form,
then the degree-zero component of every element of the generated ring is `c · 1` for some
`c ∈ R`. -/
private theorem exists_proj_zero_eq_of_mem_closure {O : Y.Opens}
    (R : Subring ((Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O)))
    (G : Set ((TB g).Total (op O)))
    (hG : ∀ z ∈ G, (∃ c ∈ R, z = (TB g).structureMap (op O) c) ∨
      ∃ b a, z = (TB g).structureMap (op O) b * δ g O a)
    {ζ : (TB g).Total (op O)} (hζ : ζ ∈ Subring.closure G) :
    ∃ c ∈ R, (TB g).proj (op O) 0 ζ = c • (TB g).one.eval (op O) := by
  let sm := (TB g).structureMap (op O)
  let M : Submonoid ((TB g).Total (op O)) :=
    { carrier := {z | ∃ b l, z = sm b * (l.map (δ g O)).prod ∧ (l = [] → b ∈ R)}
      one_mem' := ⟨1, [], by simp [sm], fun _ => R.one_mem⟩
      mul_mem' := by
        rintro _ _ ⟨b, l, rfl, hb⟩ ⟨b', l', rfl, hb'⟩
        refine ⟨b * b', l ++ l', ?_, fun h => ?_⟩
        · simp only [List.map_append, List.prod_append, map_mul, sm]
          rw [mul_assoc, ← mul_assoc _ ((TB g).structureMap (op O) b'),
            ← (TB g).structureMap_commutes, mul_assoc, mul_assoc]
        · obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.mp h
          exact R.mul_mem (hb h1) (hb' h2) }
  have hGM : Submonoid.closure G ≤ M := by
    refine Submonoid.closure_le.mpr fun z hz => ?_
    rcases hG z hz with ⟨c, hc, rfl⟩ | ⟨b, a, rfl⟩
    · exact ⟨c, [], by simp [sm], fun _ => hc⟩
    · exact ⟨b, [a], by simp [sm], fun h => absurd h (List.cons_ne_nil _ _)⟩
  have hζ' : ζ ∈ AddSubgroup.closure (M : Set ((TB g).Total (op O))) :=
    AddSubgroup.closure_mono hGM (Subring.mem_closure_iff.mp hζ)
  clear hζ
  induction hζ' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, l, rfl, hb⟩ := hz
    obtain ⟨k, hk, y, hy⟩ := exists_prod_eq_incl (g := g) l
    rw [hy, structureMap_mul_eq_smul, map_smul]
    by_cases hl : l = []
    · subst hl
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      refine ⟨b, hb rfl, ?_⟩
      rw [(TB g).proj_incl]
      have h1 := congrArg ((TB g).proj (op O) 0) hy
      rw [List.map_nil, List.prod_nil, (TB g).one_eq_incl, (TB g).proj_incl,
        (TB g).proj_incl] at h1
      rw [h1]
    · have hk0 : k ≠ 0 := by
        rw [hk]; exact_mod_cast (List.length_pos_iff.mpr hl).ne'
      refine ⟨0, R.zero_mem, ?_⟩
      rw [proj_incl_of_ne hk0, smul_zero, zero_smul]
  | zero => exact ⟨0, R.zero_mem, by rw [map_zero, zero_smul]⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨c, hc, e⟩ := hz
    obtain ⟨c', hc', e'⟩ := hz'
    exact ⟨c + c', R.add_mem hc hc', by rw [map_add, e, e', add_smul]⟩
  | neg z _ hz =>
    obtain ⟨c, hc, e⟩ := hz
    exact ⟨-c, R.neg_mem hc, by rw [map_neg, e, neg_smul]⟩

/-- **The degree-zero part of an ideal multiple.** In the ring of forms, the degree-zero
component of a sum of products `c · ζ`, with `c` in the image of an ideal `J` and `ζ` in the
ring generated by functions in the image of `ρ` and multiples of exact one-forms, is `c · 1`
for some `c` in the image of `J`. -/
private theorem exists_proj_zero_eq_of_mem_closure_mul {O : Y.Opens} {A : Type*} [CommRing A]
    (ρ : A →+* (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O))
    (J : Ideal A) (G : Set ((TB g).Total (op O))) (T : Set ((TB g).Total (op O)))
    (hT : ∀ η ∈ T, ∃ c ∈ J, ∃ ζ ∈ Subring.closure G, η = (TB g).structureMap (op O) (ρ c) * ζ)
    (hG : ∀ z ∈ G, (∃ c ∈ ρ.range, z = (TB g).structureMap (op O) c) ∨
      ∃ b a, z = (TB g).structureMap (op O) b * δ g O a)
    {η : (TB g).Total (op O)} (hη : η ∈ AddSubgroup.closure T) :
    ∃ c ∈ J, (TB g).proj (op O) 0 η = ρ c • (TB g).one.eval (op O) := by
  induction hη using AddSubgroup.closure_induction with
  | mem η hη =>
    obtain ⟨c, hc, ζ, hζ, rfl⟩ := hT η hη
    obtain ⟨_, ⟨a, rfl⟩, e⟩ := exists_proj_zero_eq_of_mem_closure ρ.range G hG hζ
    refine ⟨c * a, J.mul_mem_right a hc, ?_⟩
    rw [structureMap_mul_eq_smul, map_smul, e, smul_smul, map_mul]
  | zero => exact ⟨0, J.zero_mem, by rw [map_zero, map_zero, zero_smul]⟩
  | add η η' _ _ hη hη' =>
    obtain ⟨c, hc, e⟩ := hη
    obtain ⟨c', hc', e'⟩ := hη'
    exact ⟨c + c', J.add_mem hc hc', by rw [map_add, e, e', map_add, add_smul]⟩
  | neg η _ hη =>
    obtain ⟨c, hc, e⟩ := hη
    exact ⟨-c, J.neg_mem hc, by rw [map_neg, e, map_neg, neg_smul]⟩

end TotalRing

/-! ### Degree-zero logarithmic forms -/

section LogFormsZero

variable {n : ℕ} {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension n f]

/-- **Degree-zero logarithmic forms are functions in the ideal.** A degree-zero section of
`I · Ω^•(log D)` over `W` is, near every point, the restriction of a function in `I`. -/
private theorem exists_smul_one_of_mem_relativeLogForms {D : Divisor X} (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) {W : X.Opens}
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      (Scheme.Opens.ι (D.supp.compl : X.Opens) ≫ f)).piece 0).val.obj
        (op (Scheme.Opens.ι (D.supp.compl : X.Opens) ⁻¹ᵁ W))}
    (hω : ω ∈ relativeLogForms n f D hD I 0 W) {x : X} (hx : x ∈ W) :
    ∃ (W' : X.affineOpens) (h : (W' : X.Opens) ≤ W), x ∈ (W' : X.Opens) ∧
      ∃ g ∈ I.ideal W',
        ((Scheme.Hom.relativeDifferentialFormsAlgebra
          (Scheme.Opens.ι (D.supp.compl : X.Opens) ≫ f)).piece 0).val.map
            ((Opens.map (Scheme.Opens.ι (D.supp.compl : X.Opens)).base).map (homOfLE h)).op ω =
          (show (Stacks.RingedSpace.structureRingSheaf
              (Scheme.Opens.toScheme (D.supp.compl : X.Opens)).toRingedSpace).obj.obj
              (op (Scheme.Opens.ι (D.supp.compl : X.Opens) ⁻¹ᵁ (W' : X.Opens))) from
            ((Scheme.Opens.ι (D.supp.compl : X.Opens)).app W').hom g) •
            (TB (Scheme.Opens.ι (D.supp.compl : X.Opens) ≫ f)).one.eval
              (op (Scheme.Opens.ι (D.supp.compl : X.Opens) ⁻¹ᵁ (W' : X.Opens))) := by
  obtain ⟨W', h, hxW', hmem⟩ := hω x hx
  refine ⟨W', h, hxW', ?_⟩
  obtain ⟨g, hg, e⟩ := exists_proj_zero_eq_of_mem_closure_mul
    (show Γ(X, W') →+* (Stacks.RingedSpace.structureRingSheaf
        (Scheme.Opens.toScheme (D.supp.compl : X.Opens)).toRingedSpace).obj.obj
        (op (Scheme.Opens.ι (D.supp.compl : X.Opens) ⁻¹ᵁ (W' : X.Opens))) from
      ((Scheme.Opens.ι (D.supp.compl : X.Opens)).app W').hom) (I.ideal W') _ _
      (fun η hη => by
        obtain ⟨g, hg, ζ, hζ, e⟩ := hη
        exact ⟨g, hg, ζ, hζ, e⟩)
      (fun z hz => by
        rcases hz with (⟨b, rfl⟩ | ⟨b, rfl⟩) | ⟨E, -, t, -, s, -, rfl⟩
        · exact Or.inl ⟨_, ⟨b, rfl⟩, rfl⟩
        · exact Or.inr ⟨1, _, by rw [map_one, one_mul]; rfl⟩
        · exact Or.inr ⟨s, _, rfl⟩) hmem
  exact ⟨g, hg,
    ((TB (Scheme.Opens.ι (D.supp.compl : X.Opens) ≫ f)).proj_incl _ _ _).symm.trans e⟩

/-- **Functions in the ideal are degree-zero logarithmic forms.** -/
private theorem smul_one_mem_relativeLogForms {D : Divisor X} (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) (W : X.affineOpens) {g : Γ(X, W)} (hg : g ∈ I.ideal W) :
    (show (Stacks.RingedSpace.structureRingSheaf
        (Scheme.Opens.toScheme (D.supp.compl : X.Opens)).toRingedSpace).obj.obj
        (op (Scheme.Opens.ι (D.supp.compl : X.Opens) ⁻¹ᵁ (W : X.Opens))) from
      ((Scheme.Opens.ι (D.supp.compl : X.Opens)).app W).hom g) •
      (TB (Scheme.Opens.ι (D.supp.compl : X.Opens) ≫ f)).one.eval
        (op (Scheme.Opens.ι (D.supp.compl : X.Opens) ⁻¹ᵁ (W : X.Opens))) ∈
      relativeLogForms n f D hD I 0 W := by
  intro x hx
  refine ⟨W, le_rfl, hx, ?_⟩
  refine AddSubgroup.subset_closure ⟨g, hg, 1, Subring.one_mem _, ?_⟩
  have hid : ((Opens.map (Scheme.Opens.ι (D.supp.compl : X.Opens)).base).map
      (homOfLE (le_refl (W : X.Opens)))).op = 𝟙 _ := Subsingleton.elim _ _
  rw [mul_one, hid, PresheafOfModules.map_id]
  exact (TB (Scheme.Opens.ι (D.supp.compl : X.Opens) ≫ f)).incl_smul _ _ _

/-- The direct image `j_*Ω^p_{U/S}` of the forms on the complement `U` of `D`, as a sheaf of
`f⁻¹𝒪_S`-modules on `X`: the ambient sheaf of `MMP.Mori.Divisor.relativeLogDeRhamComplex`. -/
private noncomputable abbrev jForms (D : Divisor X) (p : ℕ) :
    SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) :=
  (SheafOfModules.pushforward.{u} (F := Opens.map (Scheme.Opens.ι (D.supp.compl : X.Opens)).base)
    ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv S.sheaf
        ((TopCat.Sheaf.pushforward CommRingCat.{u}
          (Scheme.Opens.ι (D.supp.compl : X.Opens)).base).obj
          ((TopCat.Sheaf.pullback CommRingCat.{u}
            (Scheme.Opens.ι (D.supp.compl : X.Opens) ≫ f).base).obj S.sheaf))).symm
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          (Scheme.Opens.ι (D.supp.compl : X.Opens) ≫ f).base).unit.app S.sheaf)))).obj
    ((Scheme.Hom.deRhamComplex (Scheme.Opens.ι (D.supp.compl : X.Opens) ≫ f)).X p)

/-- The restriction `Ω^0_X ⟶ j_*Ω^0_U`, read into `jForms`. -/
private noncomputable def ρ0 (D : Divisor X) (W : X.Opens) :
    ((Scheme.Hom.deRhamComplex f).X 0).val.obj (op W) →+ (jForms f D 0).val.obj (op W) :=
  (((Stacks.DeRhamPullback.deRhamPushforwardChain
    (Scheme.Opens.ι (D.supp.compl : X.Opens)) f).f 0).val.app (op W)).hom.toAddMonoidHom

private theorem ρ0_smul (D : Divisor X) (W : X.Opens)
    (r : (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj.obj (op W))
    (x : ((Scheme.Hom.deRhamComplex f).X 0).val.obj (op W)) :
    ρ0 f D W (r • x) = r • ρ0 f D W x :=
  (((Stacks.DeRhamPullback.deRhamPushforwardChain
    (Scheme.Opens.ι (D.supp.compl : X.Opens)) f).f 0).val.app (op W)).hom.map_smul r x

private theorem ρ0_restrict (D : Divisor X) {W W' : X.Opens} (h : W' ≤ W)
    (x : ((Scheme.Hom.deRhamComplex f).X 0).val.obj (op W)) :
    ρ0 f D W' (((Scheme.Hom.deRhamComplex f).X 0).val.map (homOfLE h).op x) =
      (jForms f D 0).val.map (homOfLE h).op (ρ0 f D W x) :=
  PresheafOfModules.naturality_apply ((Stacks.DeRhamPullback.deRhamPushforwardChain
    (Scheme.Opens.ι (D.supp.compl : X.Opens)) f).f 0).val (homOfLE h).op x

/-- The degree-zero form attached to a function. -/
private noncomputable abbrev z0 {W : X.Opens} (g : Γ(X, W)) :
    ((Scheme.Hom.deRhamComplex f).X 0).val.obj (op W) :=
  (Scheme.Hom.relativeDifferentialFormsZeroIso f).inv.val.app (op W) g

private theorem z0_restrict {W W' : X.Opens} (h : W' ≤ W) (g : Γ(X, W)) :
    z0 f (X.presheaf.map (homOfLE h).op g) =
      ((Scheme.Hom.deRhamComplex f).X 0).val.map (homOfLE h).op (z0 f g) :=
  PresheafOfModules.naturality_apply (Scheme.Hom.relativeDifferentialFormsZeroIso f).inv.val
    (homOfLE h).op g

private theorem z0_add {W : X.Opens} (g g' : Γ(X, W)) : z0 f (g + g') = z0 f g + z0 f g' :=
  map_add _ g g'

private theorem z0_zero {W : X.Opens} : z0 f (0 : Γ(X, W)) = 0 :=
  map_zero _

/-- A degree-zero section of `j_*Ω^0_U` which near every point is the restriction of a function in
`I`. -/
private def IsLocallyIdeal (D : Divisor X) (I : X.IdealSheafData) {W : X.Opens}
    (ω : (jForms f D 0).val.obj (op W)) : Prop :=
  ∀ y ∈ W, ∃ (W' : X.affineOpens) (h : (W' : X.Opens) ≤ W), y ∈ (W' : X.Opens) ∧
    ∃ g ∈ I.ideal W', (jForms f D 0).val.map (homOfLE h).op ω = ρ0 f D W' (z0 f g)

private theorem ρ0_injective {D : Divisor X} (hD : D.IsRelativeSNC n f) (W : X.Opens) :
    Function.Injective (ρ0 f D W) :=
  pushforwardChain_zero_injective f hD W

/-- A witness of `IsLocallyIdeal` restricts to smaller affine opens. -/
private theorem restrict_witness (D : Divisor X) (I : X.IdealSheafData) {W : X.Opens}
    (ω : (jForms f D 0).val.obj (op W)) {W' W'' : X.affineOpens} (h : (W' : X.Opens) ≤ W)
    (h' : (W'' : X.Opens) ≤ W') {g : Γ(X, W')} (hg : g ∈ I.ideal W')
    (e : (jForms f D 0).val.map (homOfLE h).op ω = ρ0 f D W' (z0 f g)) :
    X.presheaf.map (homOfLE h').op g ∈ I.ideal W'' ∧
      (jForms f D 0).val.map (homOfLE (h'.trans h)).op ω =
        ρ0 f D W'' (z0 f (X.presheaf.map (homOfLE h').op g)) := by
  refine ⟨?_, ?_⟩
  · rw [← I.map_ideal h']
    exact Ideal.mem_map_of_mem _ hg
  · rw [z0_restrict, ρ0_restrict, ← e, ← PresheafOfModules.map_comp_apply]
    rfl

/-- Scalars of `f⁻¹𝒪_S` act on degree-zero forms through functions. -/
private theorem exists_smul_z0 {W : X.Opens}
    (r : (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj.obj (op W))
    (g : Γ(X, W)) : ∃ c : Γ(X, W), r • z0 f g = z0 f (c * g) :=
  ⟨_, ((Scheme.Hom.relativeDifferentialFormsZeroIso f).inv.val.app (op W)).hom.map_smul _ g |>.symm⟩

/-- Being locally a function in the ideal is a local condition. -/
private theorem isLocallyIdeal_of_cover (D : Divisor X) (I : X.IdealSheafData) {W : X.Opens}
    (ω : (jForms f D 0).val.obj (op W))
    (hω : ∀ y ∈ W, ∃ (V : X.Opens) (i : V ⟶ W), y ∈ V ∧
      IsLocallyIdeal f D I (W := V) ((jForms f D 0).val.map i.op ω)) :
    IsLocallyIdeal f D I ω := by
  intro y hy
  obtain ⟨V, i, hyV, hi⟩ := hω y hy
  obtain ⟨W₁, h₁, hy₁, g, hg, e⟩ := hi y hyV
  refine ⟨W₁, h₁.trans (leOfHom i), hy₁, g, hg, ?_⟩
  rw [← e]
  exact PresheafOfModules.map_comp_apply _ _ _ _

/-- The degree-zero sections of `j_*Ω^0_U` which are locally functions in `I`: a subsheaf of
`f⁻¹𝒪_S`-modules. -/
private noncomputable def idealZeroSubmodule (D : Divisor X) (I : X.IdealSheafData) :
    (jForms f D 0).Submodule where
  obj W :=
    { carrier := {ω | IsLocallyIdeal f D I (W := W.unop) ω}
      add_mem' := by
        intro ω ω' hω hω' y hy
        obtain ⟨W₁, h₁, hy₁, g₁, hg₁, e₁⟩ := hω y hy
        obtain ⟨W₂, h₂, hy₂, g₂, hg₂, e₂⟩ := hω' y hy
        obtain ⟨W'', hy'', hle⟩ := LogSpreadingProof.G1.exists_affineOpens_le (X := X)
          (show y ∈ (W₁ : X.Opens) ⊓ (W₂ : X.Opens) from ⟨hy₁, hy₂⟩)
        obtain ⟨hg₁', e₁'⟩ := restrict_witness f D I ω h₁ (hle.trans inf_le_left) hg₁ e₁
        obtain ⟨hg₂', e₂'⟩ := restrict_witness f D I ω' h₂ (hle.trans inf_le_right) hg₂ e₂
        refine ⟨W'', (hle.trans inf_le_left).trans h₁, hy'', _, (I.ideal W'').add_mem hg₁' hg₂',
          ?_⟩
        rw [map_add, e₁', e₂', z0_add, map_add]
        rfl
      zero_mem' := by
        intro y hy
        obtain ⟨W'', hy'', hle⟩ := LogSpreadingProof.G1.exists_affineOpens_le (X := X) hy
        refine ⟨W'', hle, hy'', 0, (I.ideal W'').zero_mem, ?_⟩
        rw [z0_zero, map_zero, map_zero]
        rfl
      smul_mem' := by
        intro r ω hω y hy
        obtain ⟨W', h, hy', g, hg, e⟩ := hω y hy
        obtain ⟨c, hc⟩ := exists_smul_z0 f ((SheafOfModules.underlyingRingSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)).obj.map (homOfLE h).op r) g
        refine ⟨W', h, hy', c * g, (I.ideal W').mul_mem_left c hg, ?_⟩
        rw [← hc, ρ0_smul, ← e]
        exact PresheafOfModules.map_smul _ _ _ _ }
  map := by
    intro W W' i ω hω y hy
    obtain ⟨W₁, h₁, hy₁, g, hg, e⟩ := hω y (leOfHom i.unop hy)
    obtain ⟨W'', hy'', hle⟩ := LogSpreadingProof.G1.exists_affineOpens_le (X := X)
      (show y ∈ (W₁ : X.Opens) ⊓ W'.unop from ⟨hy₁, hy⟩)
    obtain ⟨hg', e'⟩ := restrict_witness f D I ω h₁ (hle.trans inf_le_left) hg e
    refine ⟨W'', hle.trans inf_le_right, hy'', _, hg', ?_⟩
    rw [← e']
    exact (PresheafOfModules.map_comp_apply _ _ _ _).symm
  isSheaf := by
    intro W ω hω
    show IsLocallyIdeal f D I (W := W.unop) ω
    refine isLocallyIdeal_of_cover f D I ω fun y hy => ?_
    have hω' := (Opens.mem_grothendieckTopology _).mp hω y hy
    exact hω'.elim fun V hV => hV.elim fun i hi => ⟨V, i, hi.2, hi.1⟩

/-- Membership in an infimum of families of subsheaves of modules. -/
private theorem mem_sInf_obj_iff {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M : ℕ → SheafOfModules.{u} R} (S : Set (∀ p, (M p).Submodule))
    (p : ℕ) (W : Cᵒᵖ) (ω : (M p).val.obj W) :
    ω ∈ ((sInf S) p).obj W ↔ ∀ N ∈ S, ω ∈ (N p).obj W := by
  simp only [sInf_apply, iInf, SheafOfModules.Submodule.toSubmodule_sInf,
    PresheafOfModules.Submodule.sInf_obj]
  simp only [Submodule.mem_sInf, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · intro h N hN
    exact h _ ⟨N p, ⟨⟨N, hN⟩, rfl⟩, rfl⟩
  · rintro h _ ⟨_, ⟨⟨N, hN⟩, rfl⟩, rfl⟩
    exact h N hN

/-- The whole sheaf, as a submodule of itself, with every section a member by definition. -/
private def wholeSubmodule {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) : M.Submodule where
  obj _ := ⊤
  map _ _ _ := Submodule.mem_top
  isSheaf _ _ _ := Submodule.mem_top

/-- `idealZeroSubmodule` in degree zero and everything in positive degrees. -/
private noncomputable def zeroFamily (D : Divisor X) (I : X.IdealSheafData) :
    ∀ p : ℕ, (jForms f D p).Submodule
  | 0 => idealZeroSubmodule f D I
  | p + 1 => wholeSubmodule (jForms f D (p + 1))

/-- The restriction of a function, read in `j_*Ω^0_U`, is `ρ0` of its degree-zero form. -/
private theorem ρ0_z0 (D : Divisor X) (W : X.Opens) (g : Γ(X, W)) :
    ρ0 f D W (z0 f g) =
      (show (Stacks.RingedSpace.structureRingSheaf
          (Scheme.Opens.toScheme (D.supp.compl : X.Opens)).toRingedSpace).obj.obj
          (op (Scheme.Opens.ι (D.supp.compl : X.Opens) ⁻¹ᵁ W)) from
        ((Scheme.Opens.ι (D.supp.compl : X.Opens)).app W).hom g) •
        (TB (Scheme.Opens.ι (D.supp.compl : X.Opens) ≫ f)).one.eval
          (op (Scheme.Opens.ι (D.supp.compl : X.Opens) ⁻¹ᵁ W)) := by
  change ((Stacks.DeRhamPullback.deRhamPushforwardChain
    (Scheme.Opens.ι (D.supp.compl : X.Opens)) f).f 0).val.app (op W) (z0 f g) = _
  rw [z0, zeroIso_inv_eq_smul_one]
  exact pushforwardChain_zero_smul_one f _ W g

/-- **Degree-zero sections of `I · Ω^•(log D)` are locally functions in `I`.** -/
private theorem relativeLogDeRhamComplex_X_zero_isLocallyIdeal {D : Divisor X} (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) (W : X.Opens)
    (x : ((relativeLogDeRhamComplex n f D hD I).X 0).val.obj (op W)) :
    IsLocallyIdeal f D I (W := W) x.1 := by
  unfold relativeLogDeRhamComplex at x
  obtain ⟨ω, hω⟩ := x
  suffices h : ∀ S : Set (∀ p, (jForms f D p).Submodule), zeroFamily f D I ∈ S →
      ω ∈ ((sInf S) 0).obj (op W) → IsLocallyIdeal f D I (W := W) ω from h _ ?_ hω
  · refine ⟨fun p W' ω' hω' => ?_, fun p W' ω' _ => ?_⟩
    · cases p with
      | zero =>
        show IsLocallyIdeal f D I ω'
        intro y hy
        obtain ⟨W₁, h₁, hy₁, g, hg, e⟩ := exists_smul_one_of_mem_relativeLogForms f hD I hω' hy
        exact ⟨W₁, h₁, hy₁, g, hg, e.trans (ρ0_z0 f D W₁ g).symm⟩
      | succ p => exact trivial
    · exact trivial
  · intro S hS h
    exact ((sInf_le hS : sInf S ≤ zeroFamily f D I) 0) (op W) h

/-- **Functions in the ideal are degree-zero sections of `I · Ω^•(log D)`.** -/
private theorem exists_relativeLogDeRhamComplex_X_zero {D : Divisor X} (hD : D.IsRelativeSNC n f)
    (I : X.IdealSheafData) (W : X.affineOpens) {g : Γ(X, W)} (hg : g ∈ I.ideal W) :
    ∃ x : ((relativeLogDeRhamComplex n f D hD I).X 0).val.obj (op (W : X.Opens)),
      x.1 = ρ0 f D W (z0 f g) := by
  unfold relativeLogDeRhamComplex
  refine ⟨⟨ρ0 f D W (z0 f g), ?_⟩, rfl⟩
  refine (mem_sInf_obj_iff _ 0 _ _).2 fun N hN => hN.1 0 W _ ?_
  rw [ρ0_z0]
  exact smul_one_mem_relativeLogForms f hD I W hg

end LogFormsZero

/-- A section of a sheaf of modules which vanishes locally vanishes. -/
private theorem sheafOfModules_eq_zero_of_locally {T : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} (M : SheafOfModules.{u} R)
    {W : Opens T} (s : M.val.obj (op W))
    (h : ∀ y ∈ W, ∃ (W' : Opens T) (h : W' ≤ W), y ∈ W' ∧ M.val.map (homOfLE h).op s = 0) :
    s = 0 := by
  choose W' hW' hy hs using h
  exact TopCat.Sheaf.eq_of_locally_eq' (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} T)
    (fun y : W => W' y.1 y.2) W (fun y => homOfLE (hW' y.1 y.2))
    (fun y hyW => Opens.mem_iSup.2 ⟨⟨y, hyW⟩, hy y hyW⟩) s 0
    (fun y => (hs y.1 y.2).trans (map_zero _).symm)

/-! ### The degree-zero term of the restriction complex -/

section RestrictionZero

variable {n : ℕ} {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension n f]

/-- The functions on the closed subscheme cut out by `E`, as a sheaf of `f⁻¹𝒪_S`-modules on
`X`. -/
private noncomputable abbrev subschemeFunctions (E : X.IdealSheafData) :
    SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) :=
  (SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap f))).obj
    ((Scheme.Modules.pushforward E.subschemeι).obj (SheafOfModules.unit _))

/-- Degree-zero forms on `X`, read as functions on the closed subscheme cut out by `E`. -/
private noncomputable def toSubschemeFunctions (E : X.IdealSheafData) :
    (Scheme.Hom.deRhamComplex f).X 0 ⟶ subschemeFunctions f E :=
  (SheafOfModules.restrictScalars _).map ((Scheme.Hom.relativeDifferentialFormsZeroIso f).hom ≫
    SheafOfModules.unitToPushforwardObjUnit E.subschemeι.toRingCatSheafHom)

private theorem toSubschemeFunctions_z0 (E : X.IdealSheafData) (W : X.Opens) (g : Γ(X, W)) :
    (toSubschemeFunctions f E).val.app (op W) (z0 f g) = (E.subschemeι.app W).hom g := by
  have h3 : (Scheme.Hom.relativeDifferentialFormsZeroIso f).hom.val.app (op W)
      ((Scheme.Hom.relativeDifferentialFormsZeroIso f).inv.val.app (op W) g) = g :=
    congrArg (fun φ => φ.val.app (op W) g)
      (Scheme.Hom.relativeDifferentialFormsZeroIso f).inv_hom_id
  change (SheafOfModules.unitToPushforwardObjUnit E.subschemeι.toRingCatSheafHom).val.app (op W)
    ((Scheme.Hom.relativeDifferentialFormsZeroIso f).hom.val.app (op W)
      ((Scheme.Hom.relativeDifferentialFormsZeroIso f).inv.val.app (op W) g)) = _
  rw [h3]
  exact SheafOfModules.unitToPushforwardObjUnit_val_app_apply _ _

variable {D : Divisor X}

/-- **The inclusion `𝒪(-D) ⊆ 𝒪` composed with restriction to `D` vanishes.** -/
private theorem comp_toSubschemeFunctions_eq_zero (hD : D.IsRelativeSNC n f)
    (i₀ : (relativeLogDeRhamComplex n f D hD D.suppIdeal).X 0 ⟶ (Scheme.Hom.deRhamComplex f).X 0)
    (hi : ∀ (W : X.Opens) (ω : ((relativeLogDeRhamComplex n f D hD D.suppIdeal).X 0).val.obj
      (op W)), ρ0 f D W (i₀.val.app (op W) ω) = ω.1) :
    ∀ (W : X.Opens) (x : ((relativeLogDeRhamComplex n f D hD D.suppIdeal).X 0).val.obj (op W)),
      (toSubschemeFunctions f D.suppIdeal).val.app (op W) (i₀.val.app (op W) x) = 0 := by
  intro W x
  refine sheafOfModules_eq_zero_of_locally _ _ fun y hy => ?_
  obtain ⟨W', h, hy', g, hg, e⟩ :=
    relativeLogDeRhamComplex_X_zero_isLocallyIdeal f hD D.suppIdeal W x y hy
  refine ⟨W', h, hy', ?_⟩
  have e1 : ((Scheme.Hom.deRhamComplex f).X 0).val.map (homOfLE h).op (i₀.val.app (op W) x) =
      z0 f g := by
    apply ρ0_injective f hD W'
    rwa [ρ0_restrict, hi]
  rw [← PresheafOfModules.naturality_apply (toSubschemeFunctions f D.suppIdeal).val, e1,
    toSubschemeFunctions_z0]
  change g ∈ RingHom.ker (D.suppIdeal.subschemeι.app W').hom
  rwa [D.suppIdeal.ker_subschemeι_app W']

end RestrictionZero

/-! ### Splitting the third term of a short exact sequence -/

section TriangleSplitting

open Pretriangulated

universe w₀ v₀ u₀

variable {C : Type u₀} [Category.{v₀} C] [Abelian C] [HasDerivedCategory.{w₀} C]

/-- **Compatible splittings of two terms split the third.** Let `0 → A → B → C → 0` be a short
exact sequence of complexes and `0 → a_j → b_j → c_j → 0` short exact sequences of objects. If
`⨁ a_j[-deg j] ≅ A` and `⨁ b_j[-deg j] ≅ B` in the derived category, compatibly with `A → B` and
the `a_j → b_j`, then `⨁ c_j[-deg j] ≅ C`. -/
private theorem nonempty_iso_of_shortExact {J : Type} [Finite J] (deg : J → ℤ)
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (s : J → ShortComplex C) (hs : ∀ j, (s j).ShortExact)
    (α : (⨁ fun j => (DerivedCategory.singleFunctor C (deg j)).obj (s j).X₁) ⟶
      DerivedCategory.Q.obj S.X₁)
    (β : (⨁ fun j => (DerivedCategory.singleFunctor C (deg j)).obj (s j).X₂) ⟶
      DerivedCategory.Q.obj S.X₂) [IsIso α] [IsIso β]
    (hcomm : α ≫ DerivedCategory.Q.map S.f =
      biproduct.map (fun j => (DerivedCategory.singleFunctor C (deg j)).map (s j).f) ≫ β) :
    Nonempty ((⨁ fun j => (DerivedCategory.singleFunctor C (deg j)).obj (s j).X₃) ≅
      DerivedCategory.Q.obj S.X₃) := by
  have := Fintype.ofFinite J
  have hs' : ∀ j, ((s j).map (HomologicalComplex.single C (ComplexShape.up ℤ) (deg j))).ShortExact :=
    fun j => (hs j).map_of_exact _
  let T : J → Triangle (DerivedCategory C) := fun j => DerivedCategory.triangleOfSES (hs' j)
  have hT := productTriangle_distinguished T fun j => DerivedCategory.triangleOfSES_distinguished _
  have hT' := DerivedCategory.triangleOfSES_distinguished hS
  let i₁ : ∀ j, (T j).obj₁ ≅ (DerivedCategory.singleFunctor C (deg j)).obj (s j).X₁ := fun j =>
    ((DerivedCategory.singleFunctorIsoCompQ C (deg j)).app (s j).X₁).symm
  let i₂ : ∀ j, (T j).obj₂ ≅ (DerivedCategory.singleFunctor C (deg j)).obj (s j).X₂ := fun j =>
    ((DerivedCategory.singleFunctorIsoCompQ C (deg j)).app (s j).X₂).symm
  let i₃ : ∀ j, (T j).obj₃ ≅ (DerivedCategory.singleFunctor C (deg j)).obj (s j).X₃ := fun j =>
    ((DerivedCategory.singleFunctorIsoCompQ C (deg j)).app (s j).X₃).symm
  let e₁ : (∏ᶜ fun j => (T j).obj₁) ≅ ⨁ fun j => (DerivedCategory.singleFunctor C (deg j)).obj (s j).X₁ :=
    Pi.mapIso i₁ ≪≫ (biproduct.isoProduct _).symm
  let e₂ : (∏ᶜ fun j => (T j).obj₂) ≅ ⨁ fun j => (DerivedCategory.singleFunctor C (deg j)).obj (s j).X₂ :=
    Pi.mapIso i₂ ≪≫ (biproduct.isoProduct _).symm
  let e₃ : (∏ᶜ fun j => (T j).obj₃) ≅ ⨁ fun j => (DerivedCategory.singleFunctor C (deg j)).obj (s j).X₃ :=
    Pi.mapIso i₃ ≪≫ (biproduct.isoProduct _).symm
  have hi : ∀ j, (T j).mor₁ ≫ (i₂ j).hom =
      (i₁ j).hom ≫ (DerivedCategory.singleFunctor C (deg j)).map (s j).f := fun j =>
    ((DerivedCategory.singleFunctorIsoCompQ C (deg j)).inv.naturality (s j).f)
  have he : (Limits.Pi.map fun j => (T j).mor₁) ≫ e₂.hom =
      e₁.hom ≫ biproduct.map (fun j => (DerivedCategory.singleFunctor C (deg j)).map (s j).f) := by
    refine biproduct.hom_ext _ _ fun j => ?_
    simp [e₁, e₂, hi]
  have hab : (productTriangle T).mor₁ ≫ (e₂.hom ≫ β) =
      (e₁.hom ≫ α) ≫ (DerivedCategory.triangleOfSES hS).mor₁ := by
    show (Limits.Pi.map fun j => (T j).mor₁) ≫ (e₂.hom ≫ β) = (e₁.hom ≫ α) ≫ DerivedCategory.Q.map S.f
    rw [Category.assoc, hcomm, ← Category.assoc e₁.hom, ← he, Category.assoc]
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism _ _ hT hT' _ _ hab
  let φ : productTriangle T ⟶ DerivedCategory.triangleOfSES hS :=
    { hom₁ := e₁.hom ≫ α, hom₂ := e₂.hom ≫ β, hom₃ := c, comm₁ := hab, comm₂ := hc₁, comm₃ := hc₂ }
  have h1 : IsIso φ.hom₁ := inferInstanceAs (IsIso (e₁.hom ≫ α))
  have h2 : IsIso φ.hom₂ := inferInstanceAs (IsIso (e₂.hom ≫ β))
  have h3 := isIso₃_of_isIso₁₂ φ hT hT' h1 h2
  exact ⟨e₃.symm ≪≫ @asIso _ _ _ _ φ.hom₃ h3⟩

end TriangleSplitting

/-! ### Naturality of the Čech gluing -/

section CechNaturality

open MMP.DeRham Stacks.CechSiteChange Stacks.CechTotalComplex.CoveringResolution ComplexShape

variable {V : Scheme.{u}} {ι : Type u} {U : ι → V.Opens} [HasDerivedCategory.{u} V.Modules]

/-- The map of Čech double complexes induced by a morphism of complexes. -/
private noncomputable abbrev cechBicomplexMap {K K' : CochainComplex V.Modules ℤ} (φ : K ⟶ K') :
    cechBicomplex U K ⟶ cechBicomplex U K' :=
  ((coveringComplexOpens V U ⋙ embeddingUpNat.extendFunctor V.Modules).mapHomologicalComplex
    (up ℤ)).map φ

private theorem cechAugBi_naturality_map {K K' : CochainComplex V.Modules ℤ} (φ : K ⟶ K') (p : ℤ) :
    cechAugBi (U := U) K p ≫ ((cechBicomplexMap (U := U) φ).f p).f 0 =
      φ.f p ≫ cechAugBi K' p :=
  cechAugExt_naturality (φ.f p)

private theorem toCechTotal_naturality {K K' : CochainComplex V.Modules ℤ} (φ : K ⟶ K') :
    toCechTotal U K ≫ HomologicalComplex₂.total.map (cechBicomplexMap (U := U) φ) (up ℤ) =
      φ ≫ toCechTotal U K' := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, toCechTotal_f, Category.assoc,
    HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc, cechAugBi_naturality_map, Category.assoc]

variable {K K' : CochainComplex V.Modules ℤ} {M M' : V.Modules} {n : ℤ}

private theorem cocycle_comp_totalMap (φ : K ⟶ K') (D : CechCocycleData U K M n)
    (D' : CechCocycleData U K' M n)
    (hg : ∀ p m h, D'.g p m h = D.g p m h ≫ ((cechBicomplexMap (U := U) φ).f p).f m) (a : ℤ) :
    D.cocycle a ≫ (HomologicalComplex₂.total.map (cechBicomplexMap (U := U) φ) (up ℤ)).f n =
      D'.cocycle a := by
  simp only [CechCocycleData.cocycle, Preadditive.sum_comp, Category.assoc, HomologicalComplex₂.ιTotal_map, hg]

private theorem cechMap_comp_totalMap (φ : K ⟶ K') (D : CechCocycleData U K M n)
    (D' : CechCocycleData U K' M n)
    (hg : ∀ p m h, D'.g p m h = D.g p m h ≫ ((cechBicomplexMap (U := U) φ).f p).f m) (a : ℤ)
    [K.IsStrictlyGE a] [K'.IsStrictlyGE a] :
    D.cechMap a ≫ HomologicalComplex₂.total.map (cechBicomplexMap (U := U) φ) (up ℤ) =
      D'.cechMap a := by
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, CechCocycleData.cechMap_f, CechCocycleData.cechMap_f, Category.assoc,
    cocycle_comp_totalMap φ D D' hg]

/-- **Naturality of the glued morphism in the complex.** -/
private theorem derivedMap_comp_Q_map (φ : K ⟶ K') (D : CechCocycleData U K M n)
    (D' : CechCocycleData U K' M n)
    (hg : ∀ p m h, D'.g p m h = D.g p m h ≫ ((cechBicomplexMap (U := U) φ).f p).f m)
    (hU : ⨆ i, U i = ⊤) (a : ℤ) [K.IsStrictlyGE a] [K'.IsStrictlyGE a] :
    D.derivedMap hU a ≫ DerivedCategory.Q.map φ = D'.derivedMap hU a := by
  haveI := (DerivedCategory.isIso_Q_map_iff_quasiIso _ (toCechTotal U K)).2
    (quasiIso_toCechTotal hU K a)
  haveI := (DerivedCategory.isIso_Q_map_iff_quasiIso _ (toCechTotal U K')).2
    (quasiIso_toCechTotal hU K' a)
  have h := congrArg DerivedCategory.Q.map (toCechTotal_naturality (U := U) φ)
  rw [Functor.map_comp, Functor.map_comp] at h
  have h' : inv (DerivedCategory.Q.map (toCechTotal U K)) ≫ DerivedCategory.Q.map φ =
      DerivedCategory.Q.map (HomologicalComplex₂.total.map (cechBicomplexMap (U := U) φ) (up ℤ)) ≫
        inv (DerivedCategory.Q.map (toCechTotal U K')) := by
    rw [IsIso.inv_comp_eq, reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]
  simp only [CechCocycleData.derivedMap, Category.assoc, h']
  rw [← Functor.map_comp_assoc, cechMap_comp_totalMap φ D D' hg]

private theorem cocycle_precomp (ψ : M' ⟶ M) (D : CechCocycleData U K M n)
    (D' : CechCocycleData U K M' n) (hg : ∀ p m h, D'.g p m h = ψ ≫ D.g p m h) (a : ℤ) :
    D'.cocycle a = ψ ≫ D.cocycle a := by
  simp only [CechCocycleData.cocycle, Preadditive.comp_sum, hg, Category.assoc]

private theorem cechMap_precomp (ψ : M' ⟶ M) (D : CechCocycleData U K M n)
    (D' : CechCocycleData U K M' n) (hg : ∀ p m h, D'.g p m h = ψ ≫ D.g p m h) (a : ℤ)
    [K.IsStrictlyGE a] :
    D'.cechMap a = (HomologicalComplex.single V.Modules (up ℤ) n).map ψ ≫ D.cechMap a := by
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, CechCocycleData.cechMap_f, CechCocycleData.cechMap_f, cocycle_precomp ψ D D' hg,
    HomologicalComplex.single_map_f_self]
  simp

/-- **Naturality of the glued morphism in the module.** -/
private theorem derivedMap_precomp (ψ : M' ⟶ M) (D : CechCocycleData U K M n)
    (D' : CechCocycleData U K M' n) (hg : ∀ p m h, D'.g p m h = ψ ≫ D.g p m h)
    (hU : ⨆ i, U i = ⊤) (a : ℤ) [K.IsStrictlyGE a] :
    D'.derivedMap hU a = (DerivedCategory.singleFunctor V.Modules n).map ψ ≫ D.derivedMap hU a := by
  simp only [CechCocycleData.derivedMap, cechMap_precomp ψ D D' hg, Functor.map_comp]
  have h := (DerivedCategory.singleFunctorIsoCompQ V.Modules n).hom.naturality ψ
  simp only [Functor.comp_map] at h
  rw [reassoc_of% h, Category.assoc]

private theorem cechBicomplexMap_cechBiπ {K K' : CochainComplex V.Modules ℤ} (ψ : K ⟶ K') (p : ℤ)
    (m : ℕ) (x : Fin (m + 1) → ι) :
    ((cechBicomplexMap (U := U) ψ).f p).f m ≫ cechBiπ K' p m x =
      cechBiπ K p m x ≫ ((cechDiagramOpens V).map (ψ.f p)).app (op (Stacks.CategoryTheory.CechComplex.inter U x)) := by
  have h1 : ((cechBicomplexMap (U := U) ψ).f p).f m = (cechBiXIso K p m).hom ≫
      ((cechComplexFunctor U).map ((cechDiagramOpens V).map (ψ.f p))).f m ≫
        (cechBiXIso K' p m).inv :=
    HomologicalComplex.extendMap_f _ embeddingUpNat rfl
  rw [h1, cechBiπ, cechBiπ, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Stacks.AlgebraicGeometry.CoveringResolution.cech_map_f_comp_π U
    ((cechDiagramOpens V).map (ψ.f p)) m x, Category.assoc]

private theorem secCochain_comp_cechBicomplexMap {K K' : CochainComplex V.Modules ℤ} (ψ : K ⟶ K')
    {M : V.Modules} {p : ℤ} {m : ℕ} (φ : M ⟶ ((cechBicomplex U K).X p).X m) (W : V.Opens)
    (s : Γ(M, W)) (x : Fin (m + 1) → ι) :
    secCochain ((φ ≫ ((cechBicomplexMap (U := U) ψ).f p).f m).app W s) x =
      (ψ.f p).app (W ⊓ Stacks.CategoryTheory.CechComplex.inter U x) (secCochain (φ.app W s) x) := by
  have h := congrArg (fun χ => ((χ.app W) (φ.app W s)).down) (cechBicomplexMap_cechBiπ (U := U) ψ p m x)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  exact h

private theorem cechF_comp_cechBicomplexMap {K K' : CochainComplex V.Modules ℤ} (ψ : K ⟶ K')
    {M M' : V.Modules} (ι' : M ⟶ M') {n : ℤ} (G : CechGluingData U K M n)
    (G' : CechGluingData U K' M' n)
    (hf : ∀ α, ι' ≫ G'.f α = G.f α ≫ ((cechDiagramOpens V).map (ψ.f (n + 1))).app (op (U α))) :
    ι' ≫ G'.cechF = G.cechF ≫ ((cechBicomplexMap (U := U) ψ).f (n + 1)).f ((0 : ℕ) : ℤ) := by
  refine cechBi_hom_ext K' (n + 1) 0 fun x => ?_
  rw [Category.assoc, Category.assoc, cechBicomplexMap_cechBiπ, CechGluingData.cechF,
    CechGluingData.cechF, toCechBi_cechBiπ, toCechBi_cechBiπ_assoc, ← Category.assoc, hf (x 0),
    Category.assoc, Category.assoc]
  congr 1
  exact (((cechDiagramOpens V).map (ψ.f (n + 1))).naturality _).symm

private theorem cechH_comp_cechBicomplexMap {K K' : CochainComplex V.Modules ℤ} (ψ : K ⟶ K')
    {M M' : V.Modules} (ι' : M ⟶ M') {n : ℤ} (G : CechGluingData U K M n)
    (G' : CechGluingData U K' M' n)
    (hh : ∀ α β, ι' ≫ G'.h α β = G.h α β ≫
      ((cechDiagramOpens V).map (ψ.f n)).app (op (U α ⊓ U β))) :
    ι' ≫ G'.cechH = G.cechH ≫ ((cechBicomplexMap (U := U) ψ).f n).f ((1 : ℕ) : ℤ) := by
  refine cechBi_hom_ext K' n 1 fun x => ?_
  rw [Category.assoc, Category.assoc, cechBicomplexMap_cechBiπ, CechGluingData.cechH,
    CechGluingData.cechH, toCechBi_cechBiπ, toCechBi_cechBiπ_assoc, ← Category.assoc,
    hh (x 0) (x 1), Category.assoc, Category.assoc]
  congr 1
  exact (((cechDiagramOpens V).map (ψ.f n)).naturality _).symm

/-- **Čech gluing data compatible with a morphism of complexes give compatible cocycles.** -/
private theorem toCechCocycleData_g_comp {K K' : CochainComplex V.Modules ℤ} (ψ : K ⟶ K')
    {M M' : V.Modules} (ι' : M ⟶ M') {n : ℤ} (G : CechGluingData U K M n)
    (G' : CechGluingData U K' M' n)
    (hf : ∀ α, ι' ≫ G'.f α = G.f α ≫ ((cechDiagramOpens V).map (ψ.f (n + 1))).app (op (U α)))
    (hh : ∀ α β, ι' ≫ G'.h α β = G.h α β ≫
      ((cechDiagramOpens V).map (ψ.f n)).app (op (U α ⊓ U β)))
    (p : ℤ) (m : ℕ) (hpm : p + m = n + 1) :
    ι' ≫ G'.toCechCocycleData.g p m hpm =
      G.toCechCocycleData.g p m hpm ≫ ((cechBicomplexMap (U := U) ψ).f p).f m := by
  rcases m with _ | _ | m
  · obtain rfl : p = n + 1 := by push_cast at hpm; omega
    rw [CechGluingData.toCechCocycleData_g, CechGluingData.toCechCocycleData_g,
      CechGluingData.cocycleComponent_zero, CechGluingData.cocycleComponent_zero]
    exact cechF_comp_cechBicomplexMap ψ ι' G G' hf
  · obtain rfl : p = n := by push_cast at hpm; omega
    rw [CechGluingData.toCechCocycleData_g, CechGluingData.toCechCocycleData_g,
      CechGluingData.cocycleComponent_one, CechGluingData.cocycleComponent_one, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
      cechH_comp_cechBicomplexMap ψ ι' G G' hh]
  · rw [CechGluingData.toCechCocycleData_g, CechGluingData.toCechCocycleData_g,
      CechGluingData.cocycleComponent_add_two, CechGluingData.cocycleComponent_add_two,
      comp_zero, zero_comp]

/-- A Čech cocycle on `M` composed with a morphism `M' ⟶ M`. -/
private noncomputable def cocyclePrecomp {K : CochainComplex V.Modules ℤ} {M M' : V.Modules}
    {n : ℤ} (ψ : M' ⟶ M) (D : CechCocycleData U K M n) : CechCocycleData U K M' n where
  g p m h := ψ ≫ D.g p m h
  isCocycle W s := by
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using
      D.isCocycle W (ψ.app W s)

/-- **Čech cocycles inducing isomorphisms on cohomology sheaves give a splitting.** Let `K` be a
complex concentrated in degrees `≥ 0` whose cohomology sheaves vanish outside `0, …, N`, and let
`Ψ q` be Čech cocycles of total degree `q` on `M q` whose cohomology maps `M q ⟶ ℋ^q(K)` are
isomorphisms. Then the sum of the glued morphisms `⨁_{q ≤ N} M q[-q] ⟶ K` is an isomorphism. -/
private theorem isIso_biproduct_desc_derivedMap (hU : ⨆ i, U i = ⊤) {K : CochainComplex V.Modules ℤ}
    [K.IsStrictlyGE 0] {N : ℕ} (M : Fin (N + 1) → V.Modules)
    (Ψ : ∀ q : Fin (N + 1), CechCocycleData U K (M q) ((q : ℕ) : ℤ))
    (hΨ : ∀ q, IsIso ((Ψ q).homologyMap hU 0))
    (hK : ∀ m : ℤ, (∀ q : Fin (N + 1), ((q : ℕ) : ℤ) ≠ m) → IsZero (K.homology m)) :
    IsIso (biproduct.desc fun q : Fin (N + 1) ↦ (Ψ q).derivedMap hU 0) := by
  classical
  set X : Fin (N + 1) → DerivedCategory V.Modules :=
    fun q ↦ (DerivedCategory.singleFunctor V.Modules ((q : ℕ) : ℤ)).obj (M q)
  set ψ : (⨁ X) ⟶ DerivedCategory.Q.obj K := biproduct.desc fun q ↦ (Ψ q).derivedMap hU 0
  rw [DerivedCategory.isIso_iff]
  intro m
  set H := DerivedCategory.homologyFunctor V.Modules m
  have hsum : ∀ q : Fin (N + 1), (∀ q' : Fin (N + 1), q' ≠ q → ((q' : ℕ) : ℤ) ≠ m) →
      H.map (biproduct.π X q ≫ biproduct.ι X q) = 𝟙 _ := by
    intro q hq
    have htot := congrArg H.map (biproduct.total (f := X))
    rw [H.map_id, H.map_sum, Finset.sum_eq_single q] at htot
    · exact htot
    · intro q' _ hq'
      rw [H.map_comp, (FrobeniusSplittingData.isZero_homologyFunctor_singleFunctor_obj (M q')
        (hq q' hq')).eq_of_tgt (H.map (biproduct.π X q')) 0, Limits.zero_comp]
    · intro h
      exact absurd (Finset.mem_univ q) h
  by_cases hm : ∃ q : Fin (N + 1), ((q : ℕ) : ℤ) = m
  · obtain ⟨q, rfl⟩ := hm
    have hq : ∀ q' : Fin (N + 1), q' ≠ q → ((q' : ℕ) : ℤ) ≠ ((q : ℕ) : ℤ) := by
      intro q' hq' h
      exact hq' (Fin.ext (by exact_mod_cast h))
    have hι : IsIso (H.map (biproduct.ι X q)) :=
      ⟨H.map (biproduct.π X q), by rw [← H.map_comp, biproduct.ι_π_self, H.map_id],
        by rw [← H.map_comp]; exact hsum q hq⟩
    have hc : IsIso (H.map (biproduct.ι X q) ≫ H.map ψ) := by
      rw [← H.map_comp, biproduct.ι_desc, CechCocycleData.homologyFunctor_map_derivedMap]
      exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' (hΨ q) (Iso.isIso_inv _))
    exact IsIso.of_isIso_comp_left (H.map (biproduct.ι X q)) (H.map ψ)
  · push Not at hm
    have h1 : IsZero (H.obj (⨁ X)) := by
      rw [IsZero.iff_id_eq_zero, ← H.map_id, ← biproduct.total, H.map_sum]
      refine Finset.sum_eq_zero fun q _ ↦ ?_
      rw [H.map_comp, (FrobeniusSplittingData.isZero_homologyFunctor_singleFunctor_obj (M q)
        (hm q)).eq_of_tgt (H.map (biproduct.π X q)) 0, Limits.zero_comp]
    have h2 : IsZero (H.obj (DerivedCategory.Q.obj K)) :=
      IsZero.of_iso (hK m hm) ((DerivedCategory.homologyFunctorFactors V.Modules m).app _)
    exact isIso_of_source_target_iso_zero _ h1.isoZero h2.isoZero

/-- **Compatible Čech splittings of a short exact sequence.** Let `0 → K₁ → K₂ → K₃ → 0` be a short
exact sequence of complexes in degrees `≥ 0` and `0 → M₁ q → M₂ q → M₃ q → 0` short exact
sequences of modules. If Čech cocycles `Ψ₁ q` on `M₁ q` into `K₁` and `Ψ₂ q` on `M₂ q` into `K₂`
induce isomorphisms on cohomology sheaves, the cohomology of `K₁`, `K₂` vanishes outside
`0, …, N`, and the cocycles are compatible with `K₁ → K₂` and `M₁ q → M₂ q`, then
`⨁_{q ≤ N} M₃ q[-q] ≅ K₃` in the derived category. -/
private theorem nonempty_iso_of_compatible_cocycles (hU : ⨆ i, U i = ⊤)
    {S : ShortComplex (CochainComplex V.Modules ℤ)} (hS : S.ShortExact)
    [S.X₁.IsStrictlyGE 0] [S.X₂.IsStrictlyGE 0] {N : ℕ}
    (s : Fin (N + 1) → ShortComplex V.Modules) (hs : ∀ q, (s q).ShortExact)
    (Ψ₁ : ∀ q : Fin (N + 1), CechCocycleData U S.X₁ (s q).X₁ ((q : ℕ) : ℤ))
    (Ψ₂ : ∀ q : Fin (N + 1), CechCocycleData U S.X₂ (s q).X₂ ((q : ℕ) : ℤ))
    (hΨ₁ : ∀ q, IsIso ((Ψ₁ q).homologyMap hU 0)) (hΨ₂ : ∀ q, IsIso ((Ψ₂ q).homologyMap hU 0))
    (hK₁ : ∀ m : ℤ, (∀ q : Fin (N + 1), ((q : ℕ) : ℤ) ≠ m) → IsZero (S.X₁.homology m))
    (hK₂ : ∀ m : ℤ, (∀ q : Fin (N + 1), ((q : ℕ) : ℤ) ≠ m) → IsZero (S.X₂.homology m))
    (hcompat : ∀ q p m h, (s q).f ≫ (Ψ₂ q).g p m h =
      (Ψ₁ q).g p m h ≫ ((cechBicomplexMap (U := U) S.f).f p).f m) :
    Nonempty ((⨁ fun q : Fin (N + 1) =>
        (DerivedCategory.singleFunctor V.Modules ((q : ℕ) : ℤ)).obj (s q).X₃) ≅
      DerivedCategory.Q.obj S.X₃) := by
  have hα := isIso_biproduct_desc_derivedMap hU (fun q => (s q).X₁) Ψ₁ hΨ₁ hK₁
  have hβ := isIso_biproduct_desc_derivedMap hU (fun q => (s q).X₂) Ψ₂ hΨ₂ hK₂
  refine @nonempty_iso_of_shortExact _ _ _ _ _ _ (fun q : Fin (N + 1) => ((q : ℕ) : ℤ)) _ hS s hs
    (biproduct.desc fun q => (Ψ₁ q).derivedMap hU 0)
    (biproduct.desc fun q => (Ψ₂ q).derivedMap hU 0) hα hβ ?_
  refine biproduct.hom_ext' _ _ fun q => ?_
  rw [biproduct.ι_desc_assoc, biproduct.ι_map_assoc, biproduct.ι_desc,
    derivedMap_comp_Q_map S.f (Ψ₁ q) (cocyclePrecomp (s q).f (Ψ₂ q))
      (fun p m h => hcompat q p m h) hU 0]
  exact derivedMap_precomp (s q).f (Ψ₂ q) (cocyclePrecomp (s q).f (Ψ₂ q)) (fun _ _ _ => rfl) hU 0

end CechNaturality

/-! ### Čech cochains mapped along a morphism of complexes -/

section MapCochain

open MMP.DeRham ComplexShape
open Stacks.CategoryTheory.CechComplex (inter)

variable {V : Scheme.{u}} {ι : Type u} {U : ι → V.Opens} {K K' : CochainComplex V.Modules ℤ}
  {W : V.Opens}

/-- A Čech cochain of `K` mapped along `ψ : K ⟶ K'`. -/
private noncomputable def mapCochain (ψ : K ⟶ K') {p : ℤ} {m : ℕ} (c : CechCochain U K W p m) :
    CechCochain U K' W p m :=
  fun x => (ψ.f p).app (W ⊓ inter U x) (c x)

private theorem mapCochain_pull (ψ : K ⟶ K') {p : ℤ} {m : ℕ} (c : CechCochain U K W p m) {m' : ℕ}
    (z : Fin m' → ι) (g : Fin (m + 1) → Fin m') :
    (mapCochain ψ c).pull z g = (ψ.f p).app _ (c.pull z g) :=
  (app_presheaf_map (ψ.f p) _ (c (z ∘ g))).symm

variable (μ : SectionProduct K) (μ' : SectionProduct K') (ψ : K ⟶ K')

/-- `ψ` is multiplicative for the products `μ`, `μ'`. -/
private def IsMulMap : Prop :=
  ∀ (a b c : ℤ) (h : a + b = c) (A : V.Opens) (x : Γ(K.X a, A)) (y : Γ(K.X b, A)),
    (ψ.f c).app A (μ.mul a b c h A x y) = μ'.mul a b c h A ((ψ.f a).app A x) ((ψ.f b).app A y)

variable {μ μ' ψ}

private theorem mapCochain_aw (hψ : IsMulMap μ μ' ψ) {a b c : ℤ} (h : a + b = c) {m₁ m₂ m : ℕ}
    (hm : m₁ + m₂ = m) (x : CechCochain U K W a m₁) (y : CechCochain U K W b m₂) :
    CechCochain.aw μ' h hm (mapCochain ψ x) (mapCochain ψ y) =
      mapCochain ψ (CechCochain.aw μ h hm x y) := by
  funext z
  simp only [CechCochain.aw, mapCochain_pull]
  exact (hψ _ _ _ _ _ _ _).symm

/-- A total Čech cochain of `K` mapped along `ψ`. -/
private noncomputable def mapTotal (ψ : K ⟶ K') {n : ℤ} (c : CechTotalCochain U K W n) : CechTotalCochain U K' W n :=
  fun p m h => mapCochain ψ (c p m h)

private theorem mapCochain_add {p : ℤ} {m : ℕ} (c c' : CechCochain U K W p m) :
    mapCochain ψ (c + c') = mapCochain ψ c + mapCochain ψ c' := by
  funext x
  exact map_add _ _ _

private theorem mapCochain_zsmul {p : ℤ} {m : ℕ} (k : ℤ) (c : CechCochain U K W p m) :
    mapCochain ψ (k • c) = k • mapCochain ψ c := by
  funext x
  exact map_zsmul _ _ _

private theorem mapCochain_zero {p : ℤ} {m : ℕ} :
    mapCochain ψ (0 : CechCochain U K W p m) = 0 := by
  funext x
  exact map_zero _

private theorem mapCochain_sum {α : Type*} (s : Finset α) {p : ℤ} {m : ℕ}
    (c : α → CechCochain U K W p m) :
    mapCochain ψ (∑ a ∈ s, c a) = ∑ a ∈ s, mapCochain ψ (c a) := by
  funext x
  simp only [mapCochain, Finset.sum_apply, map_sum]

private theorem mapTotal_cup (hψ : IsMulMap μ μ' ψ) {n n' : ℤ} (c : CechTotalCochain U K W n)
    (c' : CechTotalCochain U K W n') (N : ℤ) (hN : n + n' = N) :
    CechTotalCochain.cup μ' (mapTotal ψ c) (mapTotal ψ c') N hN =
      mapTotal ψ (CechTotalCochain.cup μ c c' N hN) := by
  funext p m h
  simp only [CechTotalCochain.cup, mapTotal, mapCochain_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  simp only [CechTotalCochain.cupTerm]
  split_ifs with hij
  · rw [mapCochain_zsmul]
    exact congrArg _ (mapCochain_aw hψ _ hij _ _)
  · exact mapCochain_zero.symm

private theorem mapTotal_cupFin (hψ : IsMulMap μ μ' ψ) : (q : ℕ) →
    (c : Fin (q + 1) → CechTotalCochain U K W 1) →
    CechTotalCochain.cupFin μ' q (fun i => mapTotal ψ (c i)) =
      mapTotal ψ (CechTotalCochain.cupFin μ q c)
  | 0, _ => rfl
  | q + 1, c => by
    change CechTotalCochain.cup μ' (CechTotalCochain.cupFin μ' q fun i => mapTotal ψ (c i.castSucc))
        (mapTotal ψ (c (Fin.last _))) _ _ = _
    rw [mapTotal_cupFin hψ q, mapTotal_cup hψ]
    rfl

private theorem mapCochain_delta {p : ℤ} {m : ℕ} (c : CechCochain U K W p m) :
    mapCochain ψ c.delta = (mapCochain ψ c).delta := by
  funext z
  simp only [CechCochain.delta, mapCochain, map_sum, map_zsmul, mapCochain_pull]

private theorem mapCochain_horiz (p p' : ℤ) {m : ℕ} (c : CechCochain U K W p m) :
    mapCochain ψ (CechCochain.horiz p p' c) = CechCochain.horiz p p' (mapCochain ψ c) := by
  funext x
  have e := congrArg (fun φ => φ.app (W ⊓ inter U x) (c x)) (ψ.comm p p')
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at e
  exact e.symm

private theorem mapCochain_vert {n : ℤ} (c : CechTotalCochain U K W n) (p : ℤ) (m : ℕ)
    (h : p + m = n + 1) :
    mapCochain ψ (c.vert p m h) = (mapTotal ψ c).vert p m h := by
  rcases m with _ | m
  · exact mapCochain_zero
  · exact mapCochain_delta (c p m _)

private theorem mapTotal_d {n : ℤ} (c : CechTotalCochain U K W n) (n' : ℤ) (hn : n + 1 = n') :
    mapTotal ψ (c.d n' hn) = (mapTotal ψ c).d n' hn := by
  funext p m h
  simp only [mapTotal, CechTotalCochain.d_apply, mapCochain_add, mapCochain_zsmul,
    mapCochain_horiz, mapCochain_vert]

/-- The image of a cocycle along a map of complexes is a cocycle. -/
private theorem isCocycle_mapTotal {n : ℤ} {c : CechTotalCochain U K W n} (h : c.IsCocycle) :
    (mapTotal ψ c).IsCocycle := by
  intro p m hpm
  have e := congrFun (congrFun (congrFun (mapTotal_d (ψ := ψ) c (n + 1) rfl) p) m) hpm
  rw [← e]
  change mapCochain ψ (c.d (n + 1) rfl p m hpm) = 0
  rw [h p m hpm]
  exact mapCochain_zero

/-- A total cochain whose image along a termwise injective map is a cocycle is a cocycle. -/
private theorem isCocycle_of_mapTotal (hψ : ∀ (p : ℤ) (A : V.Opens), Function.Injective ((ψ.f p).app A))
    {n : ℤ} {c : CechTotalCochain U K W n} (h : (mapTotal ψ c).IsCocycle) : c.IsCocycle := by
  intro p m hpm
  funext x
  refine hψ p _ ?_
  have e := congrFun (h p m hpm) x
  rw [← mapTotal_d] at e
  exact e.trans (map_zero _).symm

end MapCochain

/-! ### Lifting morphisms and Čech cocycles along injective morphisms -/

section CocycleLift

open MMP.DeRham ComplexShape

variable {V : Scheme.{u}}

/-- The lift of a morphism `φ : M ⟶ B` through a sectionwise injective `i : A ⟶ B` whose
sections contain those of `φ`. -/
private noncomputable def liftOfRange {M A B : V.Modules} (i : A ⟶ B)
    (hi : ∀ W : V.Opens, Function.Injective (i.app W)) (φ : M ⟶ B)
    (h : ∀ (W : V.Opens) (s : Γ(M, W)), ∃ a, i.app W a = φ.app W s) : M ⟶ A :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun s => (h W.unop s).choose
          map_zero' := hi W.unop ((h W.unop 0).choose_spec.trans
            ((map_zero _).trans (map_zero _).symm))
          map_add' := fun a b => hi W.unop ((h W.unop (a + b)).choose_spec.trans
            ((map_add _ a b).trans ((congrArg₂ (· + ·) (h W.unop a).choose_spec.symm
              (h W.unop b).choose_spec.symm).trans (map_add _ _ _).symm))) }
      naturality := fun W W' g => by
        ext s
        refine hi W'.unop ?_
        change i.app W'.unop (h W'.unop (M.presheaf.map (homOfLE (leOfHom g.unop)).op s)).choose =
          i.app W'.unop (A.presheaf.map (homOfLE (leOfHom g.unop)).op (h W.unop s).choose)
        have e1 := (h W'.unop (M.presheaf.map (homOfLE (leOfHom g.unop)).op s)).choose_spec
        have e2 := app_presheaf_map φ (homOfLE (leOfHom g.unop)) (show Γ(M, W.unop) from s)
        have e3 := app_presheaf_map i (homOfLE (leOfHom g.unop)) (h W.unop s).choose
        have e4 := (h W.unop s).choose_spec
        exact e1.trans (e2.trans ((congrArg _ e4.symm).trans e3.symm)) }
    fun W r s => hi W.unop (by
      have e := Scheme.Modules.Hom.app_smul (U := W.unop) i r (h W.unop s).choose
      have e' := Scheme.Modules.Hom.app_smul (U := W.unop) φ r s
      refine ((h W.unop (r • s)).choose_spec).trans (e'.trans (Eq.trans ?_ e.symm))
      rw [(h W.unop s).choose_spec])⟩

private theorem liftOfRange_app {M A B : V.Modules} (i : A ⟶ B)
    (hi : ∀ W : V.Opens, Function.Injective (i.app W)) (φ : M ⟶ B)
    (h : ∀ (W : V.Opens) (s : Γ(M, W)), ∃ a, i.app W a = φ.app W s) (W : V.Opens)
    (s : Γ(M, W)) : i.app W ((liftOfRange i hi φ h).app W s) = φ.app W s :=
  (h W s).choose_spec

private theorem liftOfRange_comp {M A B : V.Modules} (i : A ⟶ B)
    (hi : ∀ W : V.Opens, Function.Injective (i.app W)) (φ : M ⟶ B)
    (h : ∀ (W : V.Opens) (s : Γ(M, W)), ∃ a, i.app W a = φ.app W s) :
    liftOfRange i hi φ h ≫ i = φ :=
  Scheme.Modules.hom_ext _ _ fun W => by
    ext s
    exact liftOfRange_app i hi φ h W s

variable {ι : Type u} {U : ι → V.Opens} {K K' : CochainComplex V.Modules ℤ}
  [HasDerivedCategory.{u} V.Modules]

private theorem secCochain_cechBicomplexMap_app (ψ : K ⟶ K') {p : ℤ} {m : ℕ} (W : V.Opens)
    (a : Γ(((cechBicomplex U K).X p).X m, W)) (x : Fin (m + 1) → ι) :
    secCochain ((((cechBicomplexMap (U := U) ψ).f p).f m).app W a) x =
      (ψ.f p).app _ (secCochain a x) := by
  have h := congrArg (fun χ => ((χ.app W) a).down) (cechBicomplexMap_cechBiπ (U := U) ψ p m x)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  exact h

private theorem injective_cechBicomplexMap (ψ : K ⟶ K')
    (hψ : ∀ (p : ℤ) (A : V.Opens), Function.Injective ((ψ.f p).app A)) (p : ℤ) (m : ℕ)
    (W : V.Opens) : Function.Injective ((((cechBicomplexMap (U := U) ψ).f p).f m).app W) := by
  intro a b hab
  refine secCochain_injective (funext fun x => hψ p _ ?_)
  rw [← secCochain_cechBicomplexMap_app, ← secCochain_cechBicomplexMap_app, hab]

private theorem exists_cechBicomplexMap_app_eq (ψ : K ⟶ K') {p : ℤ} {m : ℕ} {W : V.Opens}
    (b : Γ(((cechBicomplex U K').X p).X m, W))
    (hb : ∀ x, ∃ y, (ψ.f p).app _ y = secCochain b x) :
    ∃ a, (((cechBicomplexMap (U := U) ψ).f p).f m).app W a = b := by
  choose c hc using hb
  obtain ⟨a, ha⟩ := secCochain_surjective (U := U) (K := K) (W := W) (p := p) (m := m) c
  refine ⟨a, secCochain_injective (funext fun x => ?_)⟩
  rw [secCochain_cechBicomplexMap_app, ha]
  exact hc x

/-- **A Čech cocycle lifted along a termwise injective map of complexes**, when the components
of its sections lie in the image. -/
private noncomputable def cocycleLift (ψ : K ⟶ K')
    (hψ : ∀ (p : ℤ) (A : V.Opens), Function.Injective ((ψ.f p).app A)) {M : V.Modules} {n : ℤ}
    (Ψ : CechCocycleData U K' M n)
    (h : ∀ (p : ℤ) (m : ℕ) (hpm : p + m = n) (W : V.Opens) (s : Γ(M, W)) (x : Fin (m + 1) → ι),
      ∃ y, (ψ.f p).app _ y = secCochain ((Ψ.g p m hpm).app W s) x) :
    CechCocycleData U K M n where
  g p m hpm := liftOfRange (((cechBicomplexMap (U := U) ψ).f p).f m)
    (injective_cechBicomplexMap (U := U) ψ hψ p m) (Ψ.g p m hpm)
    (fun W s => exists_cechBicomplexMap_app_eq (U := U) ψ _ (h p m hpm W s))
  isCocycle W s := by
    refine isCocycle_of_mapTotal hψ ?_
    convert Ψ.isCocycle W s using 1
    funext p m hpm x
    refine Eq.trans ?_ (congrArg (fun b => secCochain b x) (liftOfRange_app _
      (injective_cechBicomplexMap (U := U) ψ hψ p m) (Ψ.g p m hpm)
      (fun W s => exists_cechBicomplexMap_app_eq (U := U) ψ _ (h p m hpm W s)) W s))
    exact (secCochain_cechBicomplexMap_app ψ W _ x).symm

private theorem cocycleLift_g_comp (ψ : K ⟶ K')
    (hψ : ∀ (p : ℤ) (A : V.Opens), Function.Injective ((ψ.f p).app A)) {M : V.Modules} {n : ℤ}
    (Ψ : CechCocycleData U K' M n)
    (h : ∀ (p : ℤ) (m : ℕ) (hpm : p + m = n) (W : V.Opens) (s : Γ(M, W)) (x : Fin (m + 1) → ι),
      ∃ y, (ψ.f p).app _ y = secCochain ((Ψ.g p m hpm).app W s) x) (p : ℤ) (m : ℕ)
    (hpm : p + m = n) :
    (cocycleLift ψ hψ Ψ h).g p m hpm ≫ ((cechBicomplexMap (U := U) ψ).f p).f m = Ψ.g p m hpm :=
  liftOfRange_comp _ (injective_cechBicomplexMap (U := U) ψ hψ p m) _
    (fun W s => exists_cechBicomplexMap_app_eq (U := U) ψ _ (h p m hpm W s))

/-- A Čech cocycle pushed along a map of complexes. -/
private noncomputable def cocyclePostcomp (ψ : K ⟶ K') {M : V.Modules} {n : ℤ}
    (Ψ : CechCocycleData U K M n) : CechCocycleData U K' M n where
  g p m hpm := Ψ.g p m hpm ≫ ((cechBicomplexMap (U := U) ψ).f p).f m
  isCocycle W s := by
    have := isCocycle_mapTotal (ψ := ψ) (Ψ.isCocycle W s)
    convert this using 1
    funext p m hpm x
    exact secCochain_comp_cechBicomplexMap ψ (Ψ.g p m hpm) W s x

/-- A cocycle pushed along a quasi-isomorphism induces an isomorphism on cohomology when the
original one does. -/
private theorem isIso_homologyMap_cocyclePostcomp (hU : ⨆ i, U i = ⊤) (ψ : K ⟶ K') [QuasiIso ψ]
    {a : ℤ} [K.IsStrictlyGE a] [K'.IsStrictlyGE a] {M : V.Modules} {n : ℤ}
    (Ψ : CechCocycleData U K M n) (hΨ : IsIso (Ψ.homologyMap hU a)) :
    IsIso ((cocyclePostcomp ψ Ψ).homologyMap hU a) := by
  haveI := hΨ
  have e := derivedMap_comp_Q_map ψ Ψ (cocyclePostcomp ψ Ψ) (fun _ _ _ => rfl) hU a
  have hQ : IsIso (DerivedCategory.Q.map ψ) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ).2 inferInstance
  set H := DerivedCategory.homologyFunctor V.Modules n
  have h1 : IsIso (H.map (Ψ.derivedMap hU a)) := by
    rw [CechCocycleData.homologyFunctor_map_derivedMap]
    exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' hΨ (Iso.isIso_inv _))
  have h2 : IsIso (H.map ((cocyclePostcomp ψ Ψ).derivedMap hU a)) := by
    rw [← e, H.map_comp]
    infer_instance
  rw [CechCocycleData.homologyFunctor_map_derivedMap] at h2
  have h3 := IsIso.of_isIso_comp_left (homologySingleIso n M).hom
    ((cocyclePostcomp ψ Ψ).homologyMap hU a ≫
      ((DerivedCategory.homologyFunctorFactors V.Modules n).app K').inv)
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
    ((DerivedCategory.homologyFunctorFactors V.Modules n).app K').inv (Iso.isIso_inv _) h3

end CocycleLift

/-! ### The Leibniz rule and the twisted logarithmic forms -/

section TwistedLogDifferential

open KaehlerDifferential KaehlerDifferential.Cartier exteriorPower

variable {A L : Type} [CommRing A] [CommRing L] [Algebra A L]

/-- The wedges `d b₁ ∧ ⋯ ∧ d bₚ` span `⋀^p Ω[L⁄A]` over `L`. -/
private theorem span_range_ιMulti_D_eq_top' (i : ℕ) :
    Submodule.span L (Set.range fun c : Fin i → L ↦
      exteriorPower.ιMulti L i fun m ↦ D A L (c m)) = ⊤ := by
  have himg : exteriorPower.ιMulti L i ''
        {a : Fin i → Ω[L⁄A] | Set.range a ⊆ Set.range (D A L)} =
      Set.range fun c : Fin i → L ↦ exteriorPower.ιMulti L i fun m ↦ D A L (c m) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      choose c hc using fun m ↦ ha (Set.mem_range_self m)
      exact ⟨c, congrArg _ (funext hc)⟩
    · rintro _ ⟨c, rfl⟩
      exact ⟨_, Set.range_subset_iff.2 fun m ↦ ⟨c m, rfl⟩, rfl⟩
  rw [← himg, exteriorPower.ιMulti_span_of_span L i (Ω[L⁄A])
    (KaehlerDifferential.span_range_derivation A L)]

/-- **The Leibniz rule** `d(c y) = dc ∧ y + c dy`. -/
private theorem coe_deRhamDifferential_smul (i : ℕ) (y : ⋀[L]^i (Ω[L⁄A])) (c : L) :
    ((deRhamDifferential (A := A) i (c • y) : ⋀[L]^(i + 1) (Ω[L⁄A])) :
        ExteriorAlgebra L (Ω[L⁄A])) =
      ExteriorAlgebra.ι L (D A L c) * (y : ExteriorAlgebra L (Ω[L⁄A])) +
        c • ((deRhamDifferential (A := A) i y : ⋀[L]^(i + 1) (Ω[L⁄A])) :
          ExteriorAlgebra L (Ω[L⁄A])) := by
  have hmem : y ∈ Submodule.span L (Set.range fun g : Fin i → L ↦
      exteriorPower.ιMulti L i fun m ↦ D A L (g m)) := by
    rw [span_range_ιMulti_D_eq_top' (A := A)]; exact Submodule.mem_top
  induction hmem using Submodule.span_induction generalizing c with
  | mem v hv =>
    obtain ⟨g, rfl⟩ := hv
    have h1 := MMP.DeRham.coe_deRhamDifferential_smul_ιMulti_D (A := A) (L := L) i c g
    have h0 := MMP.DeRham.coe_deRhamDifferential_smul_ιMulti_D (A := A) (L := L) i 1 g
    rw [one_smul, Derivation.map_one_eq_zero, map_zero, zero_mul] at h0
    dsimp only
    rw [h1, h0, smul_zero, add_zero, exteriorPower.ιMulti_apply_coe]
  | zero => simp
  | add v w _ _ hv hw =>
    rw [smul_add, map_add, Submodule.coe_add, hv, hw, Submodule.coe_add, mul_add, map_add,
      Submodule.coe_add, smul_add]
    abel
  | smul a v _ hv =>
    rw [smul_smul, hv, hv, Derivation.leibniz, map_add, add_mul, map_smul, map_smul]
    simp only [Submodule.coe_smul, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    abel

/-- The differential of a product of units. -/
private theorem D_prod_eq_smul_sum {κ : Type*} (s : Finset κ) (u : κ → L)
    (hu : ∀ k ∈ s, IsUnit (u k)) :
    D A L (∏ k ∈ s, u k) = (∏ k ∈ s, u k) • ∑ k ∈ s, Ring.inverse (u k) • D A L (u k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert m s hm ih =>
    rw [Finset.prod_insert hm, Finset.sum_insert hm, Derivation.leibniz,
      ih fun k hk => hu k (Finset.mem_insert_of_mem hk), smul_add, smul_smul, smul_smul,
      mul_right_comm (u m) _ (Ring.inverse (u m)),
      Ring.mul_inverse_cancel _ (hu m (Finset.mem_insert_self m s)), one_mul]
    abel

variable {B : Type} [CommRing B] [Algebra B L] {ι : Type*} {u : ι → B}

/-- **The differential preserves the logarithmic forms twisted by the product of the poles.** -/
private theorem deRhamDifferential_mem_twisted_logForms [Fintype ι]
    (hu : ∀ k, IsUnit (algebraMap B L (u k))) {i : ℕ} (y₀ : ⋀[L]^i (Ω[L⁄A]))
    (hy₀ : (y₀ : ExteriorAlgebra L (Ω[L⁄A])) ∈ MMP.DeRham.logForms A L u i) :
    ∃ y₁ : ⋀[L]^(i + 1) (Ω[L⁄A]),
      (y₁ : ExteriorAlgebra L (Ω[L⁄A])) ∈ MMP.DeRham.logForms A L u (i + 1) ∧
      deRhamDifferential (A := A) i (algebraMap B L (∏ k, u k) • y₀) =
        algebraMap B L (∏ k, u k) • y₁ := by
  set h := algebraMap B L (∏ k, u k)
  set w : Ω[L⁄A] := ∑ k, Ring.inverse (algebraMap B L (u k)) • D A L (algebraMap B L (u k))
  have hDh : D A L h = h • w := by
    simp only [h, w, map_prod]
    exact D_prod_eq_smul_sum _ _ fun k _ => hu k
  have hw : w ∈ Submodule.span B (MMP.DeRham.logGenerators A L u) :=
    Submodule.sum_mem _ fun k _ => Submodule.subset_span (Or.inr ⟨k, rfl⟩)
  have h1 := MMP.DeRham.ι_mul_mem_logForms hw hy₀
  have h2 := MMP.DeRham.coe_deRhamDifferential_mem_logForms u i y₀ hy₀
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ⋀[L]^(i + 1) (Ω[L⁄A]), (y₁ : ExteriorAlgebra L (Ω[L⁄A])) =
      ExteriorAlgebra.ι L w * (y₀ : ExteriorAlgebra L (Ω[L⁄A])) +
        ((deRhamDifferential (A := A) i y₀ : ⋀[L]^(i + 1) (Ω[L⁄A])) :
          ExteriorAlgebra L (Ω[L⁄A])) := by
    refine ⟨⟨_, add_mem ?_ (deRhamDifferential (A := A) i y₀).2⟩, rfl⟩
    have := Submodule.mul_mem_mul (LinearMap.mem_range_self (ExteriorAlgebra.ι L) w) y₀.2
    rwa [← pow_succ'] at this
  refine ⟨y₁, hy₁ ▸ add_mem h1 h2, Subtype.ext ?_⟩
  rw [coe_deRhamDifferential_smul, Submodule.coe_smul, hy₁, hDh, map_smul, smul_mul_assoc,
    smul_add]

end TwistedLogDifferential

/-! ### Regular forms are determined off the divisor -/

section DensityForms

open TensorProduct

/-- In a reduced ring, an element outside every minimal prime is a nonzerodivisor. -/
private theorem isSMulRegular_of_forall_notMem_minimalPrimes {B : Type*} [CommRing B] [IsReduced B]
    {t : B} (h : ∀ 𝔭 ∈ minimalPrimes B, t ∉ 𝔭) : IsSMulRegular B t := by
  intro x y hxy
  simp only [smul_eq_mul] at hxy
  have hz : t * (x - y) = 0 := by rw [mul_sub, hxy, sub_self]
  by_contra hne
  have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hnil : ¬ IsNilpotent (x - y) := fun hn => hne' (IsReduced.eq_zero _ hn)
  rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf] at hnil
  push Not at hnil
  obtain ⟨𝔮, h𝔮, hx𝔮⟩ := hnil
  have : Ideal.IsPrime 𝔮 := h𝔮
  obtain ⟨𝔭, h𝔭, h𝔭𝔮⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal B) ≤ 𝔮)
  have h𝔭p : 𝔭.IsPrime := h𝔭.1.1
  have hmem : t * (x - y) ∈ 𝔭 := by rw [hz]; exact 𝔭.zero_mem
  rcases h𝔭p.mem_or_mem hmem with ht | hxy'
  · exact h 𝔭 h𝔭 ht
  · exact hx𝔮 (h𝔭𝔮 hxy')

/-- The exterior powers of a projective module are projective. -/
private theorem projective_exteriorPower {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Projective R M] (n : ℕ) : Module.Projective R (⋀[R]^n M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective R M)
  refine Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination R id)) ?_
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]

/-- In a reduced ring, an element of a minimal prime is killed by an element outside it. -/
private theorem exists_mul_eq_zero_of_mem_minimalPrimes {B : Type*} [CommRing B] [IsReduced B]
    {𝔭 : Ideal B} (h𝔭 : 𝔭 ∈ minimalPrimes B) {t : B} (ht : t ∈ 𝔭) :
    ∃ s ∉ 𝔭, s * t = 0 := by
  have : 𝔭.IsPrime := h𝔭.1.1
  have hdim := Ring.KrullDimLE.of_isLocalization 𝔭 h𝔭 (Localization.AtPrime 𝔭)
  have hfield : IsField (Localization.AtPrime 𝔭) := Ring.KrullDimLE.isField_of_isReduced
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) = ⊥ :=
    (IsLocalRing.isField_iff_maximalIdeal_eq).1 hfield
  have hm : algebraMap B (Localization.AtPrime 𝔭) t ∈ IsLocalRing.maximalIdeal _ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ ht
  rw [hmax, Ideal.mem_bot] at hm
  obtain ⟨⟨s, hs⟩, hst⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl _ t).1 hm
  exact ⟨s, hs, hst⟩

/-- **The differential of an element of a minimal prime vanishes in the fibre.** -/
private theorem tmul_D_eq_zero_of_mem_minimalPrimes {k B : Type*} [CommRing k] [CommRing B]
    [Algebra k B] [IsReduced B] {𝔭 : Ideal B} (h𝔭 : 𝔭 ∈ minimalPrimes B) {t : B} (ht : t ∈ 𝔭) :
    haveI : 𝔭.IsPrime := h𝔭.1.1
    ((1 : 𝔭.ResidueField) ⊗ₜ[B] KaehlerDifferential.D k B t : 𝔭.ResidueField ⊗[B] Ω[B⁄k]) = 0 := by
  have : 𝔭.IsPrime := h𝔭.1.1
  obtain ⟨s, hs, hst⟩ := exists_mul_eq_zero_of_mem_minimalPrimes h𝔭 ht
  have hD : s • KaehlerDifferential.D k B t + t • KaehlerDifferential.D k B s = 0 := by
    rw [← Derivation.leibniz, hst, map_zero]
  have h1 := congrArg (fun ω => (1 : 𝔭.ResidueField) ⊗ₜ[B] ω) hD
  simp only [TensorProduct.tmul_add, TensorProduct.tmul_zero, ← TensorProduct.smul_tmul,
    Algebra.smul_def, mul_one] at h1
  rw [(Ideal.algebraMap_residueField_eq_zero).2 ht, TensorProduct.zero_tmul, add_zero] at h1
  have hs' : algebraMap B 𝔭.ResidueField s ≠ 0 :=
    fun h => hs ((Ideal.algebraMap_residueField_eq_zero).1 h)
  rw [← inv_mul_cancel₀ hs', ← smul_eq_mul, ← TensorProduct.smul_tmul', h1, smul_zero]

/-- **Forms of a smooth algebra inject into the forms of a localization at a nonzerodivisor.** -/
private theorem injective_mapExteriorPower_of_isSMulRegular {k L L' : Type} [Field k] [CommRing L]
    [CommRing L'] [Algebra k L] [Algebra k L'] [Algebra L L'] [IsScalarTower k L L']
    [Algebra.Smooth k L] (f : L) [IsLocalization.Away f L'] (hf : IsSMulRegular L f) (i : ℕ) :
    Function.Injective (KaehlerDifferential.mapExteriorPower k L L' i) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨N, hN⟩ := MMP.DeRham.exists_pow_smul_eq_zero_of_mapExteriorPower_eq_zero
    (A := k) (L' := L') f hy
  have := projective_exteriorPower (R := L) (M := Ω[L⁄k]) i
  have hreg : IsSMulRegular (⋀[L]^i (Ω[L⁄k])) (f ^ N) :=
    Module.Flat.isSMulRegular_of_isRegular (IsRegular.pow N ⟨hf, by
      intro a b h; simp only [mul_comm _ f] at h; exact hf h⟩)
  exact hreg (hN.trans (smul_zero _).symm)

/-- **The product of snc local equations is a nonzerodivisor** on a reduced algebra, when the
differentials of the equations through each point are linearly independent in the fibre. -/
private theorem isSMulRegular_prod_of_linearIndependent {k B : Type*} [CommRing k] [CommRing B]
    [Algebra k B] [IsReduced B] {ι : Type*} [Fintype ι] (t : ι → B)
    (h : ∀ 𝔭 : PrimeSpectrum B, LinearIndependent 𝔭.asIdeal.ResidueField
      (fun j : {j : ι // t j ∈ 𝔭.asIdeal} =>
        ((1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[B] KaehlerDifferential.D k B (t j) :
          𝔭.asIdeal.ResidueField ⊗[B] Ω[B⁄k]))) :
    IsSMulRegular B (∏ j, t j) := by
  refine Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) (IsSMulRegular.one B)
    fun j _ => isSMulRegular_of_forall_notMem_minimalPrimes fun 𝔭 h𝔭 htj => ?_
  have : 𝔭.IsPrime := h𝔭.1.1
  exact (h ⟨𝔭, this⟩).ne_zero ⟨j, htj⟩ (tmul_D_eq_zero_of_mem_minimalPrimes h𝔭 htj)

end DensityForms

/-! ### Ideal multiples of a sheaf of modules -/

section IdealSmul

open MMP.DeRham

variable {V : Scheme.{0}} (M : V.Modules) (𝔍 : ∀ W : V.affineOpens, Ideal Γ(V, W))
  (h𝔍 : ∀ (W W' : V.affineOpens) (h : (W' : V.Opens) ≤ W),
    Ideal.map (V.presheaf.map (homOfLE h).op).hom (𝔍 W) ≤ 𝔍 W')

/-- A section lies locally in `𝔍 • M`. -/
private def IsLocallyIn {W : V.Opens} (s : Γ(M, W)) : Prop :=
  ∀ x ∈ W, ∃ (W' : V.affineOpens) (h : (W' : V.Opens) ≤ W), x ∈ (W' : V.Opens) ∧
    M.presheaf.map (homOfLE h).op s ∈ 𝔍 W' • (⊤ : Submodule Γ(V, W') Γ(M, W'))

include h𝔍 in
private theorem map_mem_ideal_smul_top {W W' : V.affineOpens} (h : (W' : V.Opens) ≤ W) {y : Γ(M, W)}
    (hy : y ∈ 𝔍 W • (⊤ : Submodule Γ(V, W) Γ(M, W))) :
    M.presheaf.map (homOfLE h).op y ∈ 𝔍 W' • (⊤ : Submodule Γ(V, W') Γ(M, W')) := by
  refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun z z' hz hz' => ?_)
  · rw [Scheme.Modules.map_smul]
    exact Submodule.smul_mem_smul (h𝔍 W W' h (Ideal.mem_map_of_mem _ ha)) trivial
  · rw [map_add]; exact add_mem hz hz'

include h𝔍 in
private theorem IsLocallyIn.restrict {W : V.Opens} {s : Γ(M, W)} (hs : IsLocallyIn M 𝔍 s) {x : V}
    (hx : x ∈ W) {O : V.Opens} (hxO : x ∈ O) :
    ∃ (W' : V.affineOpens) (h : (W' : V.Opens) ≤ W), x ∈ (W' : V.Opens) ∧ (W' : V.Opens) ≤ O ∧
      M.presheaf.map (homOfLE h).op s ∈ 𝔍 W' • (⊤ : Submodule Γ(V, W') Γ(M, W')) := by
  obtain ⟨W₁, h₁, hx₁, hm⟩ := hs x hx
  obtain ⟨W'', hx'', hle⟩ := LogSpreadingProof.G1.exists_affineOpens_le
    (show x ∈ (W₁ : V.Opens) ⊓ O from ⟨hx₁, hxO⟩)
  refine ⟨W'', (hle.trans inf_le_left).trans h₁, hx'', hle.trans inf_le_right, ?_⟩
  have := map_mem_ideal_smul_top M 𝔍 h𝔍 (hle.trans inf_le_left) hm
  rwa [MMP.DeRham.presheaf_map_map] at this

private theorem IsLocallyIn.zero {W : V.Opens} : IsLocallyIn M 𝔍 (0 : Γ(M, W)) := by
  intro x hx
  obtain ⟨W'', hx'', hle⟩ := LogSpreadingProof.G1.exists_affineOpens_le hx
  exact ⟨W'', hle, hx'', by rw [map_zero]; exact zero_mem _⟩

include h𝔍 in
private theorem IsLocallyIn.add {W : V.Opens} {s s' : Γ(M, W)} (hs : IsLocallyIn M 𝔍 s)
    (hs' : IsLocallyIn M 𝔍 s') : IsLocallyIn M 𝔍 (s + s') := by
  intro x hx
  obtain ⟨W₁, h₁, hx₁, -, hm₁⟩ := hs x hx |> fun _ => hs.restrict M 𝔍 h𝔍 hx hx
  obtain ⟨W₂, h₂, hx₂, hle₂, hm₂⟩ := hs'.restrict M 𝔍 h𝔍 hx hx₁
  have hm₁' := map_mem_ideal_smul_top M 𝔍 h𝔍 hle₂ hm₁
  rw [MMP.DeRham.presheaf_map_map] at hm₁'
  refine ⟨W₂, h₂, hx₂, ?_⟩
  rw [map_add]
  exact add_mem hm₁' hm₂

private theorem IsLocallyIn.smul {W : V.Opens} (r : Γ(V, W)) {s : Γ(M, W)} (hs : IsLocallyIn M 𝔍 s) :
    IsLocallyIn M 𝔍 (r • s) := by
  intro x hx
  obtain ⟨W', h, hx', hm⟩ := hs x hx
  refine ⟨W', h, hx', ?_⟩
  rw [Scheme.Modules.map_smul]
  exact Submodule.smul_of_tower_mem _ _ hm

include h𝔍 in
private theorem IsLocallyIn.map {W W' : V.Opens} (i : W' ≤ W) {s : Γ(M, W)} (hs : IsLocallyIn M 𝔍 s) :
    IsLocallyIn M 𝔍 (M.presheaf.map (homOfLE i).op s) := by
  intro x hx
  obtain ⟨W₁, h₁, hx₁, hle, hm⟩ := hs.restrict M 𝔍 h𝔍 (i hx) hx
  refine ⟨W₁, hle, hx₁, ?_⟩
  rwa [MMP.DeRham.presheaf_map_map]

private theorem IsLocallyIn.of_cover {W : V.Opens} {s : Γ(M, W)}
    (h : ∀ x ∈ W, ∃ (O : V.Opens) (i : O ≤ W), x ∈ O ∧
      IsLocallyIn M 𝔍 (M.presheaf.map (homOfLE i).op s)) : IsLocallyIn M 𝔍 s := by
  intro x hx
  obtain ⟨O, i, hxO, hO⟩ := h x hx
  obtain ⟨W₁, h₁, hx₁, hm⟩ := hO x hxO
  refine ⟨W₁, h₁.trans i, hx₁, ?_⟩
  rwa [MMP.DeRham.presheaf_map_map] at hm

/-- **The subsheaf `𝔍 · M`** of sections lying locally in `𝔍 • M`. -/
private noncomputable def idealSmulSubmodule : M.Submodule where
  obj W :=
    { carrier := {s | IsLocallyIn M 𝔍 (W := W.unop) s}
      add_mem' := fun hs hs' => IsLocallyIn.add M 𝔍 h𝔍 hs hs'
      zero_mem' := IsLocallyIn.zero M 𝔍
      smul_mem' := fun r _ hs => IsLocallyIn.smul M 𝔍 r hs }
  map := fun i _ hs => IsLocallyIn.map M 𝔍 h𝔍 (leOfHom i.unop) hs
  isSheaf := by
    intro W s hs
    refine IsLocallyIn.of_cover M 𝔍 fun x hx => ?_
    have hs' := (Opens.mem_grothendieckTopology _).mp hs x hx
    exact hs'.elim fun O hO => hO.elim fun i hi => ⟨O, leOfHom i, hi.2, hi.1⟩

end IdealSmul

/-! ### Weak charts: coordinates adapted to the divisor -/

section SNCWeakChart

open KaehlerDifferential

/-- **A weak chart adapted to a simple normal crossing family.** Let `V` be smooth of relative
dimension `n` over a field `k` and `J j` ideal sheaves whose intersections are smooth of the
expected dimension. Every point `y` of an open `O` lies in a weak chart `c ⊆ O` of the support
of the family, on which every `J j` is generated by a section `t j`, the boundary coordinates of
`c` are the `t (eB i)` for an injective `eB`, every other `t j` is a unit, and the product of the
boundary coordinates is a non-zero-divisor. -/
private theorem exists_weakChart_of_snc_injective {k : Type} [Field k] {V : Scheme.{0}}
    (f : V ⟶ Spec (CommRingCat.of k)) {n : ℕ} [SmoothOfRelativeDimension n f]
    {ι : Type} [Fintype ι] (J : ι → V.IdealSheafData)
    (hJ : ∀ T : Finset ι,
      SmoothOfRelativeDimension (n - T.card) ((⨆ j ∈ T, J j).subschemeι ≫ f) ∧
      (n < T.card → IsEmpty (⨆ j ∈ T, J j).subscheme))
    {O : V.Opens} {y : V} (hy : y ∈ O) :
    ∃ (c : WeakChart f n (((⨅ j, J j).support : Set V))) (t : ι → Γ(V, c.W)),
      (c.W : V.Opens) ≤ O ∧ y ∈ (c.W : V.Opens) ∧
      (∀ j, (J j).ideal c.W = Ideal.span {t j}) ∧
      ∃ eB : Fin c.r → ι, Function.Injective eB ∧
        (∀ i, t (eB i) = c.t (Fin.castLE c.hr i)) ∧ (∀ j, j ∉ Set.range eB → IsUnit (t j)) ∧
      IsSMulRegular Γ(V, c.W) (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) := by
  classical
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨W, t, hWO, hyW, hideal, -, hWU, hS⟩ :=
    MMP.DeRham.exists_affineOpen_snc_chart_le f J hJ _ rfl hy
  let := MMP.Mori.sectionAlgebra f W
  have : Algebra.Smooth k Γ(V, W) := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra f W.2
  set 𝔭 := W.2.primeIdealOf ⟨y, hyW⟩
  have hmem : ∀ a : Γ(V, W), y ∈ V.basicOpen a ↔ a ∉ 𝔭.asIdeal := fun a ↦ by
    rw [← PrimeSpectrum.mem_basicOpen a 𝔭, ← W.2.fromSpec_preimage_basicOpen a]
    change _ ↔ W.2.fromSpec.base 𝔭 ∈ V.basicOpen a
    rw [show W.2.fromSpec.base 𝔭 = y from W.2.fromSpec_primeIdealOf ⟨y, hyW⟩]
  obtain ⟨g, hg, m, s, ε, hsε, het⟩ := MMP.DeRham.exists_etale_mvPolynomial_fin t hS 𝔭
  set g' : Γ(V, W) := g * ∏ j ∈ Finset.univ.filter (fun j => t j ∉ 𝔭.asIdeal), t j
  have hg' : g' ∉ 𝔭.asIdeal := 𝔭.asIdeal.primeCompl.mul_mem hg
    (Submonoid.prod_mem _ fun j hj => (Finset.mem_filter.1 hj).2)
  set W' : V.affineOpens := ⟨V.basicOpen g', W.2.basicOpen g'⟩
  have hW'W : (W' : V.Opens) ≤ W := V.basicOpen_le g'
  have hyW' : y ∈ (W' : V.Opens) := (hmem g').2 hg'
  set ρ : Γ(V, W) →+* Γ(V, W') := (V.presheaf.map (homOfLE hW'W).op).hom with hρ_def
  have hρg' : IsUnit (ρ g') :=
    MMP.DeRham.isUnit_map_of_le_basicOpen hW'W g' le_rfl
  have hρg'' := hρg'
  rw [map_mul, map_prod] at hρg''
  have hρg : IsUnit (ρ g) := isUnit_of_mul_isUnit_left hρg''
  have hρt : ∀ j, t j ∉ 𝔭.asIdeal → IsUnit (ρ (t j)) := fun j hj =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => ρ (t j))
      (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩)) (isUnit_of_mul_isUnit_right hρg'')
  let : Algebra Γ(V, W) Γ(V, W') := ρ.toAlgebra
  have : IsLocalization.Away g' Γ(V, W') := W.2.isLocalization_basicOpen g'
  let := MMP.Mori.sectionAlgebra f W'
  have : IsScalarTower k Γ(V, W) Γ(V, W') :=
    MMP.Flips.ResolutionInputs.isScalarTower_section_res f hW'W
  have hét := MMP.DeRham.formallyEtale_aeval_of_isLocalization (k := k) s g g' hρg het
  obtain ⟨b₀, hb₀⟩ := exists_basis_D_of_formallyEtale_aeval _ hét
  have hreg : ∀ i, IsSMulRegular Γ(V, W') (ρ (s i)) := by
    intro i
    let φ := (MvPolynomial.aeval (R := k) fun i => algebraMap Γ(V, W) Γ(V, W') (s i)).toRingHom
    letI : Algebra (MvPolynomial (Fin m) k) Γ(V, W') := φ.toAlgebra
    haveI : IsScalarTower k (MvPolynomial (Fin m) k) Γ(V, W') :=
      IsScalarTower.of_algebraMap_eq fun r => by simp [RingHom.algebraMap_toAlgebra, φ]
    haveI : Algebra.FormallyEtale (MvPolynomial (Fin m) k) Γ(V, W') := hét
    haveI : Algebra.Smooth k Γ(V, W') := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra f W'.2
    haveI : Algebra.FinitePresentation (MvPolynomial (Fin m) k) Γ(V, W') :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation k _ _
    haveI : Algebra.Etale (MvPolynomial (Fin m) k) Γ(V, W') := ⟨inferInstance, inferInstance⟩
    have h := (MMP.DeRham.isSMulRegular_mvPolynomial_X (k := k) i).of_flat (S := Γ(V, W'))
    have e : algebraMap (MvPolynomial (Fin m) k) Γ(V, W') (MvPolynomial.X i) = ρ (s i) := by
      simp [RingHom.algebraMap_toAlgebra, φ]
    rwa [e] at h
  -- the number of coordinates is the relative dimension
  have hmn : m = n := by
    set 𝔮 := W'.2.primeIdealOf ⟨y, hyW'⟩
    have h := (MMP.DeRham.finite_finrank_tensor_kaehlerDifferential_of_locally
      (MMP.DeRham.locally_isStandardSmoothOfRelativeDimension_sectionAlgebra (m := n) f W'.2)
      𝔮.asIdeal.ResidueField).2
    rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis 𝔮.asIdeal.ResidueField b₀),
      Fintype.card_fin] at h
    exact h
  subst hmn
  -- order the coordinates so that the boundary ones come first
  let r := Fintype.card {j : ι // t j ∈ 𝔭.asIdeal}
  let eT : Fin r ≃ {j : ι // t j ∈ 𝔭.asIdeal} := (Fintype.equivFin _).symm
  have hr : r ≤ m := by
    simpa [r] using Fintype.card_le_of_injective ε ε.injective
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hr) (fun i => ε (eT i))
    (Fin.castLE_injective hr) (ε.injective.comp eT.injective)
  set tc : Fin m → Γ(V, W') := fun i => ρ (s (σ i))
  have htc : ∀ i : Fin r, tc (Fin.castLE hr i) = ρ (t (eT i)) := fun i => by
    show ρ (s (σ (Fin.castLE hr i))) = _
    rw [hσ]
    exact congrArg ρ (hsε (eT i))
  let b₁ : Module.Basis (Fin m) Γ(V, W') Ω[Γ(V, W')⁄k] := b₀.reindex σ.symm
  have hb₁ : ∀ i, b₁ i = D k Γ(V, W') (tc i) := fun i => by
    simp only [b₁, Module.Basis.reindex_apply, Equiv.symm_symm, hb₀, tc]
    rfl
  have hbasis : letI := (f.appLE ⊤ (W' : V.Opens) (by simp)).hom.toAlgebra
      ∃ b : Module.Basis (Fin m) Γ(V, W') Ω[Γ(V, W')⁄Γ(Spec (CommRingCat.of k), ⊤)],
        ∀ i, b i = KaehlerDifferential.D Γ(Spec (CommRingCat.of k), ⊤) Γ(V, W') (tc i) := by
    refine ⟨b₁.map (MMP.DeRham.kaehlerSpecEquiv f W').symm, fun i => ?_⟩
    change (MMP.DeRham.kaehlerSpecEquiv f W').symm (b₁ i) = _
    rw [hb₁]
    exact (LinearEquiv.symm_apply_eq _).2 (MMP.DeRham.kaehlerBaseEquiv_d _ _ _ (tc i)).symm
  have hprod : ∏ i : Fin r, tc (Fin.castLE hr i) = ρ (∏ j ∈ Finset.univ.filter
      (fun j => t j ∈ 𝔭.asIdeal), t j) := by
    rw [Finset.prod_congr rfl (fun i _ => htc i), ← map_prod]
    congr 1
    rw [Equiv.prod_comp eT (fun j : {j : ι // t j ∈ 𝔭.asIdeal} => t j)]
    exact (Finset.prod_subtype _ (fun j => by simp) _).symm
  have key : ∀ y' ∈ (W' : Set V), (y' ∈ ((⨅ j, J j).support : Set V) ↔
      y' ∉ V.basicOpen (∏ i : Fin r, tc (Fin.castLE hr i))) := by
    intro y' hy'
    have hy'W : y' ∈ (W : V.Opens) := hW'W hy'
    have h1 : y' ∈ ((⨅ j, J j).support : Set V) ↔
        y' ∉ (W : V.Opens) ⊓ (⨅ j, J j).support.compl := by
      simp only [TopologicalSpace.Opens.mem_inf]
      exact ⟨fun h h' => h'.2 h, fun h => by by_contra h'; exact h ⟨hy'W, h'⟩⟩
    have h2 : y' ∈ V.basicOpen (∏ j ∈ Finset.univ.filter (fun j => ¬ t j ∈ 𝔭.asIdeal), t j) := by
      have hle : (W' : V.Opens) ≤
          V.basicOpen (∏ j ∈ Finset.univ.filter (fun j => ¬ t j ∈ 𝔭.asIdeal), t j) := by
        change V.basicOpen g' ≤ _
        rw [Scheme.basicOpen_mul]
        exact inf_le_right
      exact hle hy'
    rw [h1, hWU, hprod, Scheme.basicOpen_res,
      ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => t j ∈ 𝔭.asIdeal),
      Scheme.basicOpen_mul]
    rw [TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_inf]
    exact not_congr ⟨fun h => ⟨hy', h.1⟩, fun h => ⟨h.2, h2⟩⟩
  refine ⟨⟨W', tc, r, hr, hbasis, ?_⟩, fun j => ρ (t j), hW'W.trans hWO, hyW', fun j => ?_,
    fun i => (eT i).1, fun i i' h => eT.injective (Subtype.ext h), fun i => (htc i).symm,
    fun j hj => ?_, ?_⟩
  · ext y'
    constructor
    · rintro ⟨hZ, hy'⟩
      exact ⟨(Scheme.mem_zeroLocus_iff _ _ _).2 (by rintro _ rfl; exact (key y' hy').1 hZ), hy'⟩
    · rintro ⟨hz, hy'⟩
      exact ⟨(key y' hy').2 ((Scheme.mem_zeroLocus_iff _ _ _).1 hz _ rfl), hy'⟩
  · rw [← (J j).map_ideal hW'W, hideal j, Ideal.map_span, Set.image_singleton]
    rfl
  · refine hρt j fun hjp => hj ⟨eT.symm ⟨j, hjp⟩, ?_⟩
    change (eT (eT.symm ⟨j, hjp⟩)).1 = j
    rw [Equiv.apply_symm_apply]
  · exact Finset.prod_induction _ (IsSMulRegular Γ(V, W')) (fun a b ha hb => ha.mul hb)
      (isUnit_one.isSMulRegular _) fun i _ => hreg _

end SNCWeakChart

/-! ### The homogeneous parts of the logarithmic ring -/

section Graded

variable {Y S : Scheme.{u}} {g : Y ⟶ S}

private theorem incl_proj_mem_closure {O : Y.Opens} (G : Set ((TB g).Total (op O)))
    (hG : ∀ z ∈ G, ∃ (k : ℤ) (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece k).val.obj
      (op O)), z = (TB g).incl k y)
    {ζ : (TB g).Total (op O)} (hζ : ζ ∈ Subring.closure G) (p : ℤ) :
    (TB g).incl p ((TB g).proj (op O) p ζ) ∈ Subring.closure G := by
  have hM : ∀ z ∈ Submonoid.closure G, ∃ (k : ℤ)
      (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece k).val.obj (op O)),
      z = (TB g).incl k y := by
    intro z hz
    induction hz using Submonoid.closure_induction with
    | mem z hz => exact hG z hz
    | one => exact ⟨0, (TB g).one.eval (op O), (TB g).one_eq_incl (op O)⟩
    | mul a b _ _ ha hb =>
      obtain ⟨k, x, rfl⟩ := ha
      obtain ⟨l, y, rfl⟩ := hb
      exact ⟨k + l, _, (TB g).incl_mul_incl k l x y⟩
  have hζ' : ζ ∈ AddSubgroup.closure (Submonoid.closure G : Set ((TB g).Total (op O))) :=
    Subring.mem_closure_iff.mp hζ
  clear hζ
  induction hζ' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨k, y, rfl⟩ := hM z hz
    by_cases hk : k = p
    · subst hk
      rw [(TB g).proj_incl]
      exact Subring.mem_closure_iff.mpr (AddSubgroup.subset_closure hz)
    · rw [proj_incl_of_ne hk]
      convert zero_mem (Subring.closure G) using 1
      exact map_zero _
  | zero =>
    rw [map_zero]
    convert zero_mem (Subring.closure G) using 1
    exact map_zero _
  | add z z' _ _ hz hz' =>
    rw [map_add]
    convert add_mem hz hz' using 1
    exact map_add _ _ _
  | neg z _ hz =>
    rw [map_neg]
    convert neg_mem hz using 1
    exact map_neg _ _

end Graded

section LogIdeal

open MMP.Mori.Divisor.LogSpreadingProof.G1

variable {X S : Scheme.{u}} (f : X ⟶ S) (D : MMP.Mori.Divisor X)

/-- Multiplying a logarithmic form by a function of `I` gives a form of `I · Ω(log D)`. -/
private theorem structureMap_mul_mem_BrSet_of_mem (I : X.IdealSheafData) (W' : X.affineOpens)
    {c : Γ(X, W')} (hc : c ∈ I.ideal W') {z} (hz : z ∈ BrSet f D ⊤ W') :
    (G1.TB ((G1.LU D).ι ≫ f)).structureMap _ (((G1.LU D).ι.app W').hom c) * z ∈
      BrSet f D I W' := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨g, -, ζ, hζ, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨c * g, I.ideal W' |>.mul_mem_right g hc, ζ, hζ, ?_⟩
    rw [map_mul ((G1.LU D).ι.app W').hom c g, ← mul_assoc]
    congr 1
    exact (map_mul ((G1.TB ((G1.LU D).ι ≫ f)).structureMap _) _ _).symm
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

private theorem Br_smul_of_mem (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens)
    {c : Γ(X, W')} (hc : c ∈ I.ideal W') {ω} (h : Br f D ⊤ p W' ω) :
    Br f D I p W' ((show (Stacks.RingedSpace.structureRingSheaf
      (G1.LU D).toScheme.toRingedSpace).obj.obj (op _) from ((G1.LU D).ι.app W').hom c) • ω) := by
  rw [Br_iff, incl_smul_eq]
  exact structureMap_mul_mem_BrSet_of_mem f D I W' hc h

private theorem Br_mono {I I' : X.IdealSheafData} (hII' : I ≤ I') (p : ℤ) (W' : X.affineOpens)
    {ω} (h : Br f D I p W' ω) : Br f D I' p W' ω := by
  refine AddSubgroup.closure_mono ?_ h
  rintro _ ⟨g, hg, ζ, hζ, rfl⟩
  exact ⟨g, hII' W' hg, ζ, hζ, rfl⟩

variable {f D} in
private theorem structureMap_mul_eq_smul' {O : (G1.LU D).toScheme.Opens}
    (c : (Stacks.RingedSpace.structureRingSheaf (G1.LU D).toScheme.toRingedSpace).obj.obj (op O))
    (z : (G1.TB ((G1.LU D).ι ≫ f)).Total (op O)) :
    (G1.TB ((G1.LU D).ι ≫ f)).structureMap (op O) c * z = c • z := by
  change c • (1 : (G1.TB ((G1.LU D).ι ≫ f)).Total (op O)) * z = _
  rw [(G1.TB ((G1.LU D).ι ≫ f)).smul_mul_eq, one_mul]

/-- The local generators of the logarithmic forms are homogeneous. -/
private theorem gens_homogeneous (W' : X.affineOpens) :
    ∀ z ∈ gens f D W', ∃ (k : ℤ) (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((G1.LU D).ι ≫ f)).piece k).val.obj (op ((G1.LU D).ι ⁻¹ᵁ (W' : X.Opens)))),
      z = (G1.TB ((G1.LU D).ι ≫ f)).incl k y := by
  rintro _ ((⟨g, rfl⟩ | ⟨g, rfl⟩) | ⟨E, -, t, -, s, -, rfl⟩)
  · refine ⟨0, (show (Stacks.RingedSpace.structureRingSheaf
      (G1.LU D).toScheme.toRingedSpace).obj.obj (op _) from ((G1.LU D).ι.app W').hom g) •
        (G1.TB ((G1.LU D).ι ≫ f)).one.eval _, ?_⟩
    rw [incl_smul_eq, ← (G1.TB ((G1.LU D).ι ≫ f)).one_eq_incl, mul_one]
  · exact ⟨1, _, rfl⟩
  · exact ⟨1, (show (Stacks.RingedSpace.structureRingSheaf
      (G1.LU D).toScheme.toRingedSpace).obj.obj (op _) from s) • dOne f D _ (((G1.LU D).ι.app W').hom t),
      (incl_smul_eq f D 1 s _).symm⟩

/-- The degree-`p` part of an element of the ring generated by the local generators is a
logarithmic form. -/
private theorem Br_top_proj (p : ℤ) (W' : X.affineOpens) {ζ}
    (hζ : ζ ∈ Subring.closure (gens f D W')) :
    Br f D ⊤ p W' ((G1.TB ((G1.LU D).ι ≫ f)).proj _ p ζ) := by
  have h := incl_proj_mem_closure _ (gens_homogeneous f D W') hζ p
  refine AddSubgroup.subset_closure ⟨1, Submodule.mem_top, _, h, ?_⟩
  rw [map_one]
  exact (one_mul _).symm.trans (congrArg (· * _) (map_one _).symm)

/-- **A form of `I · Ω(log D)` on an affine open is a sum of `c • ω'`** with `c ∈ I` and `ω'`
logarithmic. -/
private theorem mem_closure_smul_of_Br (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens) {ω}
    (h : Br f D I p W' ω) :
    ω ∈ AddSubgroup.closure {η | ∃ c ∈ I.ideal W', ∃ ω', Br f D ⊤ p W' ω' ∧
      η = (show (Stacks.RingedSpace.structureRingSheaf
        (G1.LU D).toScheme.toRingedSpace).obj.obj (op _) from ((G1.LU D).ι.app W').hom c) • ω'} := by
  have key : ∀ z ∈ BrSet f D I W', (G1.TB ((G1.LU D).ι ≫ f)).proj _ p z ∈
      AddSubgroup.closure {η | ∃ c ∈ I.ideal W', ∃ ω', Br f D ⊤ p W' ω' ∧
        η = (show (Stacks.RingedSpace.structureRingSheaf
          (G1.LU D).toScheme.toRingedSpace).obj.obj (op _) from ((G1.LU D).ι.app W').hom c) •
            ω'} := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨g, hg, ζ, hζ, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨g, hg, _, Br_top_proj f D p W' hζ, ?_⟩
      refine (congrArg ((G1.TB ((G1.LU D).ι ≫ f)).proj _ p)
        (structureMap_mul_eq_smul' (f := f) (D := D) _ ζ)).trans ?_
      exact map_smul _ _ _
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  have := key _ h
  rwa [(G1.TB ((G1.LU D).ι ≫ f)).proj_incl] at this

end LogIdeal

section LogModuleIdeal

open MMP.Mori.Divisor.LogSpreadingProof.G1

variable {X S : Scheme.{0}} (n : ℕ) (f : X ⟶ S) [SmoothOfRelativeDimension n f]
  (D : MMP.Mori.Divisor X) (hD : D.IsRelativeSNC n f)

private theorem rs_refl (p : ℤ) {W : X.Opens} (ω) : rs f D p (le_refl W) ω = ω := by
  have hid : ((Opens.map (G1.LU D).ι.base).map (homOfLE (le_refl W))).op = 𝟙 _ :=
    Subsingleton.elim _ _
  change ((Scheme.Hom.relativeDifferentialFormsAlgebra ((G1.LU D).ι ≫ f)).piece p).val.map
    ((Opens.map (G1.LU D).ι.base).map (homOfLE (le_refl W))).op ω = ω
  rw [hid, PresheafOfModules.map_id]
  rfl

private theorem mem_relativeLogForms_of_Br (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens)
    {ω} (h : Br f D I p W' ω) : ω ∈ relativeLogForms n f D hD I p W' := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ⟨W', le_rfl, hx, ?_⟩
  rwa [rs_refl]

/-- **A function of `I` times a logarithmic form is a form of `I · Ω(log D)`.** -/
private theorem smul_mem_relativeLogForms_of_mem (I : X.IdealSheafData) (p : ℤ)
    (W : X.affineOpens) {c : Γ(X, W)} (hc : c ∈ I.ideal W) {ω}
    (hω : ω ∈ relativeLogForms n f D hD ⊤ p W) :
    (show (Stacks.RingedSpace.structureRingSheaf
      (G1.LU D).toScheme.toRingedSpace).obj.obj (op _) from ((G1.LU D).ι.app W).hom c) • ω ∈
      relativeLogForms n f D hD I p W := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ?_
  obtain ⟨W', hW', hxW', hb⟩ := (mem_relativeLogForms_iff' n f D hD ⊤ p _ _).1 hω x hx
  refine ⟨W', hW', hxW', ?_⟩
  have e : rs f D p hW' ((show (Stacks.RingedSpace.structureRingSheaf
      (G1.LU D).toScheme.toRingedSpace).obj.obj (op _) from ((G1.LU D).ι.app W).hom c) • ω) =
      (show (Stacks.RingedSpace.structureRingSheaf
      (G1.LU D).toScheme.toRingedSpace).obj.obj (op _) from ((G1.LU D).ι.app W').hom
        (X.presheaf.map (homOfLE hW').op c)) • rs f D p hW' ω := by
    refine (PresheafOfModules.map_smul _ _ _ _).trans ?_
    exact congrArg (· • rs f D p hW' ω) (app_restrict hW' c)
  rw [e]
  exact Br_smul_of_mem f D I p W' (I.ideal_le_comap_ideal hW' hc) hb

/-- **`I · Ω^q(log D)` is the subsheaf of logarithmic forms lying locally in `I · Ω^q(log D)`.** -/
private theorem mem_relativeLogForms_iff_isLocallyIn (I : X.IdealSheafData) (q : ℕ)
    {W : X.Opens} (s : Γ(G1.logModule n f D hD ⊤ q, W)) :
    s.1 ∈ relativeLogForms n f D hD I q W ↔
      IsLocallyIn (G1.logModule n f D hD ⊤ q) (fun W' => I.ideal W') s := by
  constructor
  · intro hs x hx
    obtain ⟨W', h, hxW', hb⟩ := (mem_relativeLogForms_iff' n f D hD I q _ _).1 hs x hx
    refine ⟨W', h, hxW', ?_⟩
    have key : ∀ η ∈ AddSubgroup.closure {η | ∃ c ∈ I.ideal W', ∃ ω', Br f D ⊤ q W' ω' ∧
        η = (show (Stacks.RingedSpace.structureRingSheaf
          (G1.LU D).toScheme.toRingedSpace).obj.obj (op _) from ((G1.LU D).ι.app W').hom c) • ω'},
        ∃ t : Γ(G1.logModule n f D hD ⊤ q, W'),
          t ∈ I.ideal W' • (⊤ : Submodule Γ(X, W') Γ(G1.logModule n f D hD ⊤ q, W')) ∧
            t.1 = η := by
      intro η hη
      induction hη using AddSubgroup.closure_induction with
      | mem η hη =>
        obtain ⟨c, hc, ω', hω', rfl⟩ := hη
        exact ⟨c • ⟨ω', mem_relativeLogForms_of_Br n f D hD ⊤ q W' hω'⟩,
          Submodule.smul_mem_smul hc trivial, rfl⟩
      | zero => exact ⟨0, zero_mem _, rfl⟩
      | add η η' _ _ h h' =>
        obtain ⟨t, ht, rfl⟩ := h
        obtain ⟨t', ht', rfl⟩ := h'
        exact ⟨t + t', add_mem ht ht', rfl⟩
      | neg η _ h =>
        obtain ⟨t, ht, rfl⟩ := h
        exact ⟨-t, neg_mem ht, rfl⟩
    obtain ⟨t, ht, he⟩ := key _ (mem_closure_smul_of_Br f D I q W' hb)
    convert ht using 1
    exact Subtype.ext he.symm
  · intro hs
    refine relativeLogForms_of_local n f D hD I q fun x hx => ?_
    obtain ⟨W', h, hxW', hm⟩ := hs x hx
    refine ⟨W', h, hxW', ?_⟩
    change ((G1.logModule n f D hD ⊤ q).presheaf.map (homOfLE h).op s).1 ∈ _
    refine Submodule.smul_induction_on hm (fun c hc m _ => ?_) (fun a b ha hb => ?_)
    · exact smul_mem_relativeLogForms_of_mem n f D hD I q W' hc m.2
    · exact add_mem_relativeLogForms n f D hD I q ha hb

private theorem relativeLogForms_le_top (I : X.IdealSheafData) (p : ℤ) {W : X.Opens} {ω}
    (hω : ω ∈ relativeLogForms n f D hD I p W) : ω ∈ relativeLogForms n f D hD ⊤ p W := by
  refine (mem_relativeLogForms_iff' n f D hD ⊤ p _ _).2 fun x hx => ?_
  obtain ⟨W', h, hxW', hb⟩ := (mem_relativeLogForms_iff' n f D hD I p _ _).1 hω x hx
  exact ⟨W', h, hxW', Br_mono f D le_top p W' hb⟩

/-- The local `I`-multiples of logarithmic forms, as a subsheaf of `Ω^q(log D)`. -/
private noncomputable abbrev idealLogSubmodule (I : X.IdealSheafData) (q : ℕ) :
    (G1.logModule n f D hD ⊤ q).Submodule :=
  idealSmulSubmodule (G1.logModule n f D hD ⊤ q) (fun W => I.ideal W)
    (fun _ _ h => (I.map_ideal h).le)

/-- **`I · Ω^q(log D)` is the subsheaf of local `I`-multiples of `Ω^q(log D)`.** -/
private noncomputable def logModuleIdealHom (I : X.IdealSheafData) (q : ℕ) :
    G1.logModule n f D hD I q ⟶ (idealLogSubmodule n f D hD I q).toSheafOfModules :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun x => ⟨⟨x.1, relativeLogForms_le_top n f D hD I q x.2⟩,
            (mem_relativeLogForms_iff_isLocallyIn n f D hD I q _).1 x.2⟩
          map_zero' := Subtype.ext (Subtype.ext rfl)
          map_add' := fun _ _ => Subtype.ext (Subtype.ext rfl) }
      naturality := fun _ _ _ => by
        ext x
        exact Subtype.ext (Subtype.ext rfl) }
    fun _ _ _ => Subtype.ext (Subtype.ext rfl)⟩

private noncomputable def logModuleIdealInv (I : X.IdealSheafData) (q : ℕ) :
    (idealLogSubmodule n f D hD I q).toSheafOfModules ⟶ G1.logModule n f D hD I q :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun x => ⟨x.1.1, (mem_relativeLogForms_iff_isLocallyIn n f D hD I q x.1).2 x.2⟩
          map_zero' := Subtype.ext rfl
          map_add' := fun _ _ => Subtype.ext rfl }
      naturality := fun _ _ _ => by
        ext x
        exact Subtype.ext rfl }
    fun _ _ _ => Subtype.ext rfl⟩

private theorem logModuleIdealHom_app_val (I : X.IdealSheafData) (q : ℕ) (W : X.Opens)
    (x : (G1.logModule n f D hD I q).val.obj (op W)) :
    ((logModuleIdealHom n f D hD I q).val.app (op W) x).1.1 = x.1 := rfl

private theorem logModuleIdealInv_app_val (I : X.IdealSheafData) (q : ℕ) (W : X.Opens)
    (x : (idealLogSubmodule n f D hD I q).toSheafOfModules.val.obj (op W)) :
    ((logModuleIdealInv n f D hD I q).val.app (op W) x).1 = x.1.1 := rfl

/-- **`I · Ω^q(log D)` is the subsheaf of local `I`-multiples of `Ω^q(log D)`.** -/
private noncomputable def logModuleIdealIso (I : X.IdealSheafData) (q : ℕ) :
    G1.logModule n f D hD I q ≅ (idealLogSubmodule n f D hD I q).toSheafOfModules where
  hom := logModuleIdealHom n f D hD I q
  inv := logModuleIdealInv n f D hD I q
  hom_inv_id := by
    ext W x
    exact Subtype.ext ((logModuleIdealInv_app_val n f D hD I q W _).trans
      (logModuleIdealHom_app_val n f D hD I q W x))
  inv_hom_id := by
    ext W x
    exact Subtype.ext (Subtype.ext ((logModuleIdealHom_app_val n f D hD I q W _).trans
      (logModuleIdealInv_app_val n f D hD I q W x)))

end LogModuleIdeal

/-- **Locally equal families of ideals have the same local multiples.** -/
private theorem isLocallyIn_of_locally_eq {V : Scheme.{0}} (M : V.Modules)
    {𝔍 𝔍' : ∀ W : V.affineOpens, Ideal Γ(V, W)}
    (h𝔍 : ∀ (W W' : V.affineOpens) (h : (W' : V.Opens) ≤ W),
      Ideal.map (V.presheaf.map (homOfLE h).op).hom (𝔍 W) ≤ 𝔍 W')
    (heq : ∀ {x : V} {O : V.Opens}, x ∈ O → ∃ W'' : V.affineOpens, x ∈ (W'' : V.Opens) ∧
      (W'' : V.Opens) ≤ O ∧ 𝔍 W'' = 𝔍' W'')
    {W : V.Opens} {s : Γ(M, W)} (hs : IsLocallyIn M 𝔍 s) : IsLocallyIn M 𝔍' s := by
  intro x hx
  obtain ⟨W₁, h₁, hx₁, hm⟩ := hs x hx
  obtain ⟨W'', hx'', hle, he⟩ := heq hx₁
  refine ⟨W'', hle.trans h₁, hx'', ?_⟩
  have := map_mem_ideal_smul_top M 𝔍 h𝔍 hle hm
  rwa [MMP.DeRham.presheaf_map_map, he] at this

/-- Subsheaves with the same sections give isomorphic sheaves of modules, by the identity on
sections. -/
private noncomputable def submoduleIsoOfIff {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{u} R}
    (N N' : M.Submodule) (h : ∀ (W : Cᵒᵖ) (s : M.val.obj W), s ∈ N.obj W ↔ s ∈ N'.obj W) :
    N.toSheafOfModules ≅ N'.toSheafOfModules where
  hom := ⟨PresheafOfModules.Submodule.homOfLE (N₁ := N.toSubmodule) (N₂ := N'.toSubmodule)
    fun W s hs => (h W s).1 hs⟩
  inv := ⟨PresheafOfModules.Submodule.homOfLE (N₁ := N'.toSubmodule) (N₂ := N.toSubmodule)
    fun W s hs => (h W s).2 hs⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-! ### The ordinary de Rham data of a lifted pair -/

section OrdinaryData

open MMP.DeRham Stacks.Frobenius

section FrobeniusDeRham

variable {k : Type} [Field k] {V : Scheme.{0}} (f : V ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime]
  (hV : IsInCharacteristic V p)

/-- The de Rham differential on sections of `Ω^q`. -/
private noncomputable def deRhamSec (q : ℕ) (W : V.Opens) :
    Γ(f.relativeDifferentialForms (q : ℤ), W) →+ Γ(f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ), W) where
  toFun x := ((f.deRhamComplex).d q (q + 1)).val.app (op W) x
  map_zero' := map_zero _
  map_add' := map_add _

/-- **The de Rham differential of `F_*Ω^•`**, a morphism of `𝒪_V`-modules in characteristic `p`. -/
private noncomputable def frobeniusDeRhamD (q : ℕ) :
    (Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
        (f.relativeDifferentialForms (q : ℤ)) ⟶
      (Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj
        (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)) :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (deRhamSec f q W.unop)
      naturality := fun W W' g => by
        ext x
        exact PresheafOfModules.naturality_apply ((f.deRhamComplex).d q (q + 1)).val g x }
    fun W r x => by
      have hr : (show Γ(V, W.unop) from (absoluteFrobenius V p hV).app W.unop
          (show Γ(V, W.unop) from r)) = (show Γ(V, W.unop) from r) ^ p :=
        absoluteFrobenius_app_apply V p hV W.unop _
      change deRhamSec f q W.unop
          ((show Γ(V, W.unop) from (absoluteFrobenius V p hV).app W.unop
            (show Γ(V, W.unop) from r)) •
            (show Γ(f.relativeDifferentialForms (q : ℤ), W.unop) from x)) =
        (show Γ(V, W.unop) from (absoluteFrobenius V p hV).app W.unop
            (show Γ(V, W.unop) from r)) • deRhamSec f q W.unop x
      rw [hr]
      exact deRhamComplex_d_pow_smul f p hV q W.unop r x⟩

private theorem frobeniusDeRhamD_comp (q : ℕ) :
    frobeniusDeRhamD f p hV q ≫ frobeniusDeRhamD f p hV (q + 1) = 0 := by
  ext W x
  exact congrArg (fun φ => φ.val.app (op W) x) ((f.deRhamComplex).d_comp_d q (q + 1) (q + 2))

end FrobeniusDeRham

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectField k] {n : ℕ}
  {V : Scheme.{0}} {f : V ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f]
  {ι : Type} [Fintype ι] [HasDerivedCategory.{0} V.Modules]
  (D : MMP.DeRham.FrobeniusSplittingData p k n f ι)

private theorem iSup_mem_empty {X : Scheme.{0}} {κ : Type} (J : κ → X.IdealSheafData) (T : Finset κ)
    (hT : T = ∅) : (⨆ j ∈ T, J j) = ⊥ := by
  subst hT
  simp

/-- The forms on `W ⊓ ⊤` are the forms on `W`. -/
private noncomputable def restrictTop (q : ℕ) (W : V.Opens) :
    Γ(f.relativeDifferentialForms (q : ℤ), W) →+ Γ(f.relativeDifferentialForms (q : ℤ), W ⊓ ⊤) :=
  ((f.relativeDifferentialForms (q : ℤ)).presheaf.map
    (homOfLE (inf_le_left : W ⊓ ⊤ ≤ W)).op).hom

private theorem restrictTop_bijective (q : ℕ) (W : V.Opens) :
    Function.Bijective (restrictTop (f := f) q W) := by
  have h : W ⊓ ⊤ = W := inf_top_eq W
  have hi : IsIso (homOfLE (inf_le_left : W ⊓ ⊤ ≤ W)) := by
    rw [show homOfLE (inf_le_left : W ⊓ ⊤ ≤ W) = eqToHom h from Subsingleton.elim _ _]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE (inf_le_left : W ⊓ ⊤ ≤ W)).op)

/-- **The ordinary de Rham data of a lifted pair**: the data of `D` with the empty divisor, the
sheaves `Ω^q_{V/k}` and the de Rham differential of `F_*Ω^•`. -/
private noncomputable def ordinaryData : MMP.DeRham.FrobeniusSplittingData p k n f PEmpty where
  hpn := D.hpn
  hV := D.hV
  J := PEmpty.elim
  hJ T := by
    have hT : T = ∅ := Subsingleton.elim _ _
    subst hT
    have h := D.hJ ∅
    rw [iSup_mem_empty _ _ rfl] at h ⊢
    exact ⟨h.1, fun h' => absurd h' (Nat.not_lt_zero _)⟩
  𝒱 := D.𝒱
  g := D.g
  I := PEmpty.elim
  π := D.π
  hπ := D.hπ
  i := D.i
  hi := D.hi
  hIJ j := j.elim
  hI T := by
    have hT : T = ∅ := Subsingleton.elim _ _
    subst hT
    have h := D.hI ∅
    rw [iSup_mem_empty _ _ rfl] at h ⊢
    exact ⟨h.1, fun h' => absurd h' (Nat.not_lt_zero _)⟩
  U := ⊤
  hU := by
    rw [iInf_of_empty, Scheme.IdealSheafData.support_top]
    ext x
    simp
  K q := f.relativeDifferentialForms (q : ℤ)
  e q W := restrictTop q W
  he_inj q W := (restrictTop_bijective q W).1
  he_smul q W a s := Scheme.Modules.map_smul _ _ _ _
  he_res q W₁ W₂ h s := by
    change (f.relativeDifferentialForms (q : ℤ)).presheaf.map _
        ((f.relativeDifferentialForms (q : ℤ)).presheaf.map _ s) =
      (f.relativeDifferentialForms (q : ℤ)).presheaf.map _
        ((f.relativeDifferentialForms (q : ℤ)).presheaf.map _ s)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    rfl
  he_range q W ω := by
    refine ⟨fun _ W' hW' c _ => ⟨⟨(f.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (hW'.trans (le_inf le_rfl le_top) : (W' : V.Opens) ≤ W ⊓ ⊤)).op ω, ?_⟩,
      ⟨(f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
        (homOfLE (hW'.trans (le_inf le_rfl le_top) : (W' : V.Opens) ≤ W ⊓ ⊤)).op
          (((f.deRhamComplex).d q (q + 1)).val.app (op (W ⊓ ⊤)) ω), ?_⟩⟩,
      fun _ => (restrictTop_bijective q W).2 ω⟩
    · rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, one_smul]
      exact MMP.DeRham.presheaf_map_map _ _ _ _
    · rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, one_smul]
      exact MMP.DeRham.presheaf_map_map _ _ _ _
  d := frobeniusDeRhamD f p D.hV
  hd := frobeniusDeRhamD_comp f p D.hV
  he_d q W s :=
    (PresheafOfModules.naturality_apply ((f.deRhamComplex).d q (q + 1)).val
      (homOfLE (inf_le_left : W ⊓ ⊤ ≤ W)).op s).symm

/-- A regular form, restricted to the complement of the divisor, has logarithmic poles. -/
private theorem res_mem_range_e (q : ℕ) (W : V.Opens) (s : Γ(f.relativeDifferentialForms (q : ℤ), W)) :
    (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE (inf_le_left : W ⊓ D.U ≤ W)).op s ∈
      Set.range (D.e q W) := by
  refine (D.he_range q W _).2 fun W' hW' c _ => ⟨⟨(∏ j, c j) •
      (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hW').op s, ?_⟩,
    ⟨(∏ j, c j) • (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hW').op
      (((f.deRhamComplex).d q (q + 1)).val.app (op W) s), ?_⟩⟩
  · rw [Scheme.Modules.map_smul]
    congr 1
    exact (MMP.DeRham.presheaf_map_map _ _ (homOfLE (inf_le_left.trans hW'))  _).trans
      (MMP.DeRham.presheaf_map_map _ _ _ _).symm
  · rw [Scheme.Modules.map_smul]
    congr 1
    have h1 := PresheafOfModules.naturality_apply ((f.deRhamComplex).d q (q + 1)).val
      (homOfLE (inf_le_left : W ⊓ D.U ≤ W)).op s
    refine (MMP.DeRham.presheaf_map_map _ _ (homOfLE (inf_le_left.trans hW')) _).trans ?_
    refine Eq.trans ?_ (congrArg ((f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
      (homOfLE (inf_le_inf_right D.U hW')).op) h1).symm
    exact (MMP.DeRham.presheaf_map_map _ _ _ _).symm

/-- The logarithmic form of a regular form. -/
private noncomputable def regularSec (q : ℕ) (W : V.Opens) (s : Γ(f.relativeDifferentialForms (q : ℤ), W)) :
    Γ(D.K q, W) :=
  (res_mem_range_e D q W s).choose

private theorem e_regularSec (q : ℕ) (W : V.Opens) (s : Γ(f.relativeDifferentialForms (q : ℤ), W)) :
    D.e q W (regularSec D q W s) =
      (f.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (inf_le_left : W ⊓ D.U ≤ W)).op s :=
  (res_mem_range_e D q W s).choose_spec

private theorem regularSec_res (q : ℕ) {W W' : V.Opens} (h : W' ≤ W)
    (s : Γ(f.relativeDifferentialForms (q : ℤ), W)) :
    regularSec D q W' ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h).op s) =
      (D.K q).presheaf.map (homOfLE h).op (regularSec D q W s) := by
  refine D.he_inj q W' ?_
  rw [e_regularSec D, D.he_res, e_regularSec D]
  exact (MMP.DeRham.presheaf_map_map _ _ (homOfLE (inf_le_left.trans h)) _).trans
    (MMP.DeRham.presheaf_map_map _ _ _ _).symm

private theorem regularSec_smul (q : ℕ) (W : V.Opens) (a : Γ(V, W))
    (s : Γ(f.relativeDifferentialForms (q : ℤ), W)) :
    regularSec D q W (a • s) = a • regularSec D q W s := by
  refine D.he_inj q W ?_
  rw [e_regularSec D, D.he_smul, e_regularSec D, Scheme.Modules.map_smul]

/-- The additive map of regular forms into logarithmic forms over an open. -/
private noncomputable def regularSecHom (q : ℕ) (W : V.Opens) :
    Γ(f.relativeDifferentialForms (q : ℤ), W) →+ Γ(D.K q, W) :=
  AddMonoidHom.mk' (regularSec D q W) fun a b => D.he_inj q W (by
    rw [map_add, e_regularSec D, e_regularSec D, e_regularSec D, map_add])

/-- **Regular forms are logarithmic**: the inclusion `Ω^q ⟶ Ω^q(log S)`. -/
private noncomputable def regularIncl (q : ℕ) : f.relativeDifferentialForms (q : ℤ) ⟶ D.K q :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (regularSecHom D q W.unop)
      naturality := fun W W' g => by
        ext s
        exact regularSec_res D q (leOfHom g.unop) s }
    fun W a s => regularSec_smul D q W.unop a s⟩

private theorem e_regularIncl_app (q : ℕ) (W : V.Opens) (s : Γ(f.relativeDifferentialForms (q : ℤ), W)) :
    D.e q W ((regularIncl D q).app W s) =
      (f.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (inf_le_left : W ⊓ D.U ≤ W)).op s :=
  e_regularSec D q W s

/-- **The inclusion of regular forms commutes with the de Rham differential** of `F_*Ω^•`. -/
private theorem regularIncl_comp_d (q : ℕ) :
    (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (regularIncl D q) ≫ D.d q =
      frobeniusDeRhamD f p D.hV q ≫
        (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (regularIncl D (q + 1)) := by
  ext W s
  refine D.he_inj (q + 1) (absoluteFrobenius V p D.hV ⁻¹ᵁ W) ?_
  have h1 := D.he_d q W ((regularIncl D q).app W s)
  have h2 := e_regularIncl_app D q W s
  have h3 := e_regularIncl_app D (q + 1) W (deRhamSec f q W s)
  refine h1.trans (Eq.trans ?_ h3.symm)
  refine (congrArg (fun y => ((f.deRhamComplex).d q (q + 1)).val.app (op (W ⊓ D.U)) y) h2).trans ?_
  exact (PresheafOfModules.naturality_apply ((f.deRhamComplex).d q (q + 1)).val
    (homOfLE (inf_le_left : W ⊓ D.U ≤ W)).op s)

/-- **The inclusion `F_*Ω^• ⟶ F_*Ω^•(log S)`** of complexes of `𝒪_V`-modules. -/
private noncomputable def regularComplexMap : (ordinaryData D).complex ⟶ D.complex :=
  CochainComplex.ofHom
    (fun q => (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (regularIncl D q))
    (fun q => by
      have h1 := CochainComplex.of_d
        (fun q ↦ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K q)) D.d q
      have h2 := CochainComplex.of_d (fun q ↦ (Scheme.Modules.pushforward
        (absoluteFrobenius V p (ordinaryData D).hV)).obj ((ordinaryData D).K q))
        (ordinaryData D).d q
      exact (congrArg (_ ≫ ·) h1).trans ((regularIncl_comp_d D q).trans
        (congrArg (· ≫ _) h2.symm)))

/-- The inclusion `F_*Ω^• ⟶ F_*Ω^•(log S)` of the complexes extended to `ℤ`. -/
private noncomputable def regularComplexMapZ : (ordinaryData D).complexZ ⟶ D.complexZ :=
  HomologicalComplex.extendMap (regularComplexMap D) ComplexShape.embeddingUpNat

/-- **The inclusion of regular forms is multiplicative.** -/
private theorem regularIncl_wedge (i j m : ℕ) (h : i + j = m) (A : V.Opens)
    (s : Γ(f.relativeDifferentialForms (i : ℤ), A)) (t : Γ(f.relativeDifferentialForms (j : ℤ), A)) :
    (regularIncl D m).app A ((ordinaryData D).wedge i j m h A s t) =
      D.wedge i j m h A ((regularIncl D i).app A s) ((regularIncl D j).app A t) := by
  refine D.he_inj m A ?_
  have hle : A ⊓ D.U ≤ A ⊓ ⊤ := inf_le_inf_left _ le_top
  have e1 := e_regularIncl_app D m A ((ordinaryData D).wedge i j m h A s t)
  have e2 := (ordinaryData D).e_wedge i j m h A s t
  have e3 := D.e_wedge i j m h A ((regularIncl D i).app A s) ((regularIncl D j).app A t)
  have e4 := e_regularIncl_app D i A s
  have e5 := e_regularIncl_app D j A t
  have e6 : (f.relativeDifferentialForms (m : ℤ)).presheaf.map
      (homOfLE (inf_le_left : A ⊓ D.U ≤ A)).op ((ordinaryData D).wedge i j m h A s t) =
      (f.relativeDifferentialForms (m : ℤ)).presheaf.map (homOfLE hle).op
        ((ordinaryData D).e m A ((ordinaryData D).wedge i j m h A s t)) :=
    (MMP.DeRham.presheaf_map_map _ _ _ _).symm
  refine e1.trans (e6.trans (Eq.trans ?_ e3.symm))
  have e7 := congrArg ((f.relativeDifferentialForms (m : ℤ)).presheaf.map (homOfLE hle).op) e2
  have e8 := formsWedge_map f i j m h hle ((ordinaryData D).e i A s) ((ordinaryData D).e j A t)
  have e9 : (f.relativeDifferentialForms (i : ℤ)).presheaf.map (homOfLE hle).op
      ((ordinaryData D).e i A s) = D.e i A ((regularIncl D i).app A s) :=
    (MMP.DeRham.presheaf_map_map _ _ _ _).trans e4.symm
  have e10 : (f.relativeDifferentialForms (j : ℤ)).presheaf.map (homOfLE hle).op
      ((ordinaryData D).e j A t) = D.e j A ((regularIncl D j).app A t) :=
    (MMP.DeRham.presheaf_map_map _ _ _ _).trans e5.symm
  exact e7.trans (e8.trans (congrArg₂ (fun a b => formsWedge f i j m h (A ⊓ D.U) a b) e9 e10))

/-- **The inclusion of regular forms carries wedges of `1`-forms to wedges.** -/
private theorem regularIncl_wedgeFin {A : V.Opens} : (q : ℕ) →
    (θ : Fin (q + 1) → Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), A)) →
    (regularIncl D (q + 1)).app A ((ordinaryData D).wedgeFin q θ) =
      D.wedgeFin q (fun i => (regularIncl D 1).app A (θ i))
  | 0, _ => rfl
  | q + 1, θ => by
    change (regularIncl D (q + 1 + 1)).app A ((ordinaryData D).wedge (q + 1) 1 (q + 1 + 1) rfl A
        ((ordinaryData D).wedgeFin q fun i => θ i.castSucc) (θ (Fin.last _))) =
      D.wedge (q + 1) 1 (q + 1 + 1) rfl A
        (D.wedgeFin q fun i => (regularIncl D 1).app A (θ i.castSucc))
        ((regularIncl D 1).app A (θ (Fin.last _)))
    exact (regularIncl_wedge D (q + 1) 1 (q + 1 + 1) rfl A _ _).trans
      (congrArg (fun x => D.wedge (q + 1) 1 (q + 1 + 1) rfl A x
        ((regularIncl D 1).app A (θ (Fin.last _)))) (regularIncl_wedgeFin q _))

private theorem regularComplexMapZ_f (q : ℕ) :
    (regularComplexMapZ D).f (q : ℤ) = ((ordinaryData D).complexZXIso q).hom ≫
      (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (regularIncl D q) ≫
        (D.complexZXIso q).inv :=
  HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat rfl

/-- The inclusion of complexes on sections of degree `q`. -/
private theorem regularComplexMapZ_toComplexZ (q : ℕ) (W : V.Opens)
    (s : Γ(f.relativeDifferentialForms (q : ℤ), W)) :
    ((regularComplexMapZ D).f (q : ℤ)).app W ((ordinaryData D).toComplexZ q W s) =
      D.toComplexZ q W ((regularIncl D q).app W s) := by
  rw [regularComplexMapZ_f]
  change (D.complexZXIso q).inv.app W ((regularIncl D q).app W
    (((ordinaryData D).complexZXIso q).hom.app W (((ordinaryData D).complexZXIso q).inv.app W s))) = _
  have h : ((ordinaryData D).complexZXIso q).hom.app W
      (((ordinaryData D).complexZXIso q).inv.app W s) = s :=
    congrArg (fun φ => φ.app W s) ((ordinaryData D).complexZXIso q).inv_hom_id
  rw [h]
  rfl

/-- **The inclusion of complexes is multiplicative** for the wedge products on sections. -/
private theorem regularComplexMapZ_mul (a b c : ℤ) (h : a + b = c) (A : V.Opens)
    (x : Γ((ordinaryData D).complexZ.X a, A)) (y : Γ((ordinaryData D).complexZ.X b, A)) :
    ((regularComplexMapZ D).f c).app A ((ordinaryData D).sectionProduct.mul a b c h A x y) =
      D.sectionProduct.mul a b c h A (((regularComplexMapZ D).f a).app A x)
        (((regularComplexMapZ D).f b).app A y) := by
  by_cases hab : 0 ≤ a ∧ 0 ≤ b
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hab.1
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hab.2
    obtain rfl : c = ((i + j : ℕ) : ℤ) := by push_cast; omega
    obtain ⟨x', rfl⟩ := ((ordinaryData D).toComplexZ_bijective i A).2 x
    obtain ⟨y', rfl⟩ := ((ordinaryData D).toComplexZ_bijective j A).2 y
    have e1 := (ordinaryData D).sectionProduct_mul_toComplexZ i j A x' y'
    have e2 := regularComplexMapZ_toComplexZ D (i + j) A ((ordinaryData D).wedge i j (i + j) rfl A x' y')
    have e3 := regularComplexMapZ_toComplexZ D i A x'
    have e4 := regularComplexMapZ_toComplexZ D j A y'
    have e5 := D.sectionProduct_mul_toComplexZ i j A ((regularIncl D i).app A x')
      ((regularIncl D j).app A y')
    have e6 := regularIncl_wedge D i j (i + j) rfl A x' y'
    refine (congrArg _ e1).trans (e2.trans ?_)
    refine Eq.trans ?_ (congrArg₂ (fun u v => D.sectionProduct.mul (i : ℤ) (j : ℤ)
      ((i + j : ℕ) : ℤ) h A u v) e3 e4).symm
    refine Eq.trans ?_ e5.symm
    exact congrArg (D.toComplexZ (i + j) A) e6
  · rcases not_and_or.1 hab with ha | hb
    · obtain rfl := (ordinaryData D).extend_X_eq_zero (by omega) x
      simp only [map_zero, AddMonoidHom.zero_apply]
    · obtain rfl := (ordinaryData D).extend_X_eq_zero (by omega) y
      simp only [map_zero, AddMonoidHom.zero_apply]

/-- Every affine open is a chart of the empty divisor. -/
private theorem isSNCChart_ordinary (W : V.affineOpens) : (ordinaryData D).IsSNCChart W :=
  ⟨PEmpty.elim, fun j => j.elim⟩

private theorem affineInf_le_ordinary {W : V.affineOpens} (h : D.IsSNCChart W) :
    (h.affineInf : V.Opens) ≤ (isSNCChart_ordinary D W).affineInf :=
  inf_le_inf_left _ le_top

set_option maxRecDepth 4000 in
/-- **The Frobenius `p`-th powers of the two data agree on functions.** -/
private theorem powForm_toOrdinary {W : V.affineOpens} (h : D.IsSNCChart W)
    (ω : Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), (isSNCChart_ordinary D W).affineInf)) :
    FrobeniusSplittingData.powForm h ((f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map
        (homOfLE (affineInf_le_ordinary D h)).op ω) =
      (f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map
        (homOfLE (affineInf_le_ordinary D h)).op
          (FrobeniusSplittingData.powForm (isSNCChart_ordinary D W) ω) := by
  have hA := affineInf_le_ordinary D h
  by_cases hL' : Nontrivial Γ(V, h.affineInf)
  swap
  · have : Subsingleton Γ(V, h.affineInf) := not_nontrivial_iff_subsingleton.1 hL'
    have := Module.subsingleton Γ(V, h.affineInf)
      Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), h.affineInf)
    exact Subsingleton.elim _ _
  have : Nontrivial Γ(V, (isSNCChart_ordinary D W).affineInf) :=
    FrobeniusSplittingData.nontrivial_of_le D hA
  have := FrobeniusSplittingData.charP_of_nontrivial D h.affineInf
  have := FrobeniusSplittingData.charP_of_nontrivial (ordinaryData D)
    (isSNCChart_ordinary D W).affineInf
  let := MMP.Mori.sectionAlgebra f h.affineInf
  let := MMP.Mori.sectionAlgebra f (isSNCChart_ordinary D W).affineInf
  let : Algebra Γ(V, (isSNCChart_ordinary D W).affineInf) Γ(V, h.affineInf) :=
    (V.presheaf.map (homOfLE hA).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f hA
  refine (formsAlgEquiv f 0 h.affineInf).injective ?_
  have r2 := formsAlgEquiv_restrict f 0 (W := (isSNCChart_ordinary D W).affineInf)
    (W' := h.affineInf) hA (FrobeniusSplittingData.powForm (isSNCChart_ordinary D W) ω)
  have p2 := FrobeniusSplittingData.formsAlgEquiv_powForm (isSNCChart_ordinary D W) ω
  have m := mapExteriorPower_powZeroForm (p := p) (k := k) (L' := Γ(V, h.affineInf))
    (formsAlgEquiv f 0 (isSNCChart_ordinary D W).affineInf ω)
  rw [FrobeniusSplittingData.formsAlgEquiv_powForm, formsAlgEquiv_restrict f 0 hA]
  refine Eq.trans ?_ r2.symm
  rw [p2]
  exact m.symm

/-- **The Frobenius powers of the two data agree on regular functions**, on a chart. -/
private theorem regularIncl_powPiece {W : V.affineOpens} (h : D.IsSNCChart W)
    (t : Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), W)) :
    (regularIncl D 0).app _ (FrobeniusSplittingData.powPiece (isSNCChart_ordinary D W) t) =
      FrobeniusSplittingData.powPiece h ((regularIncl D 0).app _ t) := by
  refine D.he_inj 0 _ ?_
  have e1 := e_regularIncl_app D 0 _ (FrobeniusSplittingData.powPiece (isSNCChart_ordinary D W) t)
  have e2 := FrobeniusSplittingData.e_powPiece (isSNCChart_ordinary D W) t
  have e3 := FrobeniusSplittingData.e_powPiece h ((regularIncl D 0).app _ t)
  have e4 := e_regularIncl_app D 0 _ t
  have e5 := powForm_toOrdinary D h ((ordinaryData D).e 0 _ t)
  have e6 : (f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map
      (homOfLE (inf_le_left : (W : V.Opens) ⊓ D.U ≤ W)).op t =
      (f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map
        (homOfLE (affineInf_le_ordinary D h)).op ((ordinaryData D).e 0 _ t) :=
    (MMP.DeRham.presheaf_map_map _ _ _ _).symm
  refine e1.trans (Eq.trans ?_ e3.symm)
  refine Eq.trans ?_ (congrArg (FrobeniusSplittingData.powForm h) e4).symm
  refine Eq.trans ?_ (congrArg (FrobeniusSplittingData.powForm h) e6).symm
  refine Eq.trans ?_ e5.symm
  refine Eq.trans ?_ (congrArg _ e2)
  exact (MMP.DeRham.presheaf_map_map _ _ _ _).symm

/-- **The Frobenius powers of the two data agree on regular functions.** -/
private theorem regularIncl_powSection (W : V.Opens)
    (s : Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), W)) :
    (regularIncl D 0).app W ((ordinaryData D).powSection W s) =
      D.powSection W ((regularIncl D 0).app W s) := by
  refine MMP.DeRham.eq_of_locally_eq_sections _ _ fun x hx => ?_
  obtain ⟨⟨W', hW'⟩, hxW', hle⟩ := D.exists_isSNCChart hx
  refine ⟨_, hle, hxW', ?_⟩
  have e1 := (regularSec_res D 0 hle ((ordinaryData D).powSection W s)).symm
  have e2 := (ordinaryData D).powSection_spec W s (isSNCChart_ordinary D W') hle
  have e3 := regularIncl_powPiece D hW'
    ((f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map (homOfLE hle).op s)
  have e4 := regularSec_res D 0 hle s
  have e5 := D.powSection_spec W ((regularIncl D 0).app W s) hW' hle
  refine e1.trans (Eq.trans ?_ e5.symm)
  refine (congrArg (regularSec D 0 _) e2).trans ?_
  refine e3.trans ?_
  exact congrArg (FrobeniusSplittingData.powPiece hW') e4

/-- **Regular forms are determined by their restriction to the complement of the divisor.** -/
private theorem forms_res_injective (q : ℕ) (W : V.Opens) :
    Function.Injective ((f.relativeDifferentialForms (q : ℤ)).presheaf.map
      (homOfLE (inf_le_left : W ⊓ D.U ≤ W)).op) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine MMP.DeRham.eq_of_locally_eq_sections _ _ fun x hx => ?_
  obtain ⟨W', t, hW'W, hxW', -, -, hWU, hli⟩ :=
    exists_affineOpen_snc_chart_le f D.J D.hJ D.U D.hU hx
  refine ⟨W', hW'W, hxW', ?_⟩
  rw [map_zero]
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  haveI : IsReduced V := isReduced_of_smooth f
  letI := MMP.Mori.sectionAlgebra f W'
  haveI := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra f W'.2
  have hreg := isSMulRegular_prod_of_linearIndependent (k := k) t hli
  let G : V.affineOpens := ⟨V.basicOpen (∏ j, t j), W'.2.basicOpen _⟩
  have hGle : (G : V.Opens) ≤ W' := V.basicOpen_le _
  letI := MMP.Mori.sectionAlgebra f G
  letI : Algebra Γ(V, W') Γ(V, G) := (V.presheaf.map (homOfLE hGle).op).hom.toAlgebra
  haveI := MMP.Flips.ResolutionInputs.isScalarTower_section_res f hGle
  haveI : IsLocalization.Away (∏ j, t j) Γ(V, G) := W'.2.isLocalization_basicOpen _
  have hinj := injective_mapExteriorPower_of_isSMulRegular (k := k) (L := Γ(V, W'))
    (L' := Γ(V, G)) (∏ j, t j) hreg q
  have hGW : (G : V.Opens) ≤ W ⊓ D.U := by
    change V.basicOpen (∏ j, t j) ≤ W ⊓ D.U
    rw [← hWU]
    exact inf_le_inf_right _ hW'W
  have h0 : (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hGle).op
      ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hW'W).op s) = 0 :=
    (MMP.DeRham.presheaf_map_map (homOfLE hW'W) (homOfLE hGle)
      (homOfLE (hGW.trans inf_le_left)) s).trans
      ((MMP.DeRham.presheaf_map_map (homOfLE (inf_le_left : W ⊓ D.U ≤ W)) (homOfLE hGW)
        (homOfLE (hGW.trans inf_le_left)) s).symm.trans ((congrArg _ hs).trans (map_zero _)))
  apply (formsAlgEquiv f q W').injective
  rw [map_zero]
  apply hinj
  rw [map_zero, ← formsAlgEquiv_restrict f q hGle, h0, map_zero]

/-- **The inclusion of regular forms into logarithmic forms is injective.** -/
private theorem regularIncl_app_injective (q : ℕ) (W : V.Opens) :
    Function.Injective ((regularIncl D q).app W) := fun a b h =>
  forms_res_injective D q W ((e_regularIncl_app D q W a).symm.trans
    ((congrArg (D.e q W) h).trans (e_regularIncl_app D q W b)))

/-- The `m`-th power of the ideal of the divisor on an affine open. -/
private def divisorIdealPow (m : ℕ) (W : V.affineOpens) : Ideal Γ(V, W) :=
  (∏ j, (D.J j).ideal W) ^ m

private theorem map_divisorIdealPow_le (m : ℕ) (W W' : V.affineOpens) (h : (W' : V.Opens) ≤ W) :
    Ideal.map (V.presheaf.map (homOfLE h).op).hom (divisorIdealPow D m W) ≤
      divisorIdealPow D m W' := by
  rw [divisorIdealPow, divisorIdealPow, Ideal.map_pow]
  have e : Ideal.map (V.presheaf.map (homOfLE h).op).hom (∏ j, (D.J j).ideal W) =
      ∏ j, Ideal.map (V.presheaf.map (homOfLE h).op).hom ((D.J j).ideal W) :=
    map_prod (Ideal.mapHom _) _ _
  rw [e]
  refine le_of_eq (congrArg (· ^ m) (Finset.prod_congr rfl fun j _ => ?_))
  exact (D.J j).map_ideal h

/-- **The twisted logarithmic forms** `(I_S)^m Ω^q(log S)`, as a subsheaf of `Ω^q(log S)`. -/
private noncomputable def twistedLogSubmodule (m q : ℕ) : (D.K q).Submodule :=
  idealSmulSubmodule (D.K q) (divisorIdealPow D m) (map_divisorIdealPow_le D m)

/-- The sheaf of twisted logarithmic forms. -/
private noncomputable abbrev twistedLog (m q : ℕ) : V.Modules :=
  (twistedLogSubmodule D m q).toSheafOfModules

/-- On a chart of the divisor, `(∏ⱼ Jⱼ)^m` is generated by `(∏ⱼ tⱼ)^m`. -/
private theorem divisorIdealPow_eq_span {W : V.affineOpens} {t : ι → Γ(V, W)}
    (ht : ∀ j, (D.J j).ideal W = Ideal.span {t j}) (m : ℕ) :
    divisorIdealPow D m W = Ideal.span {(∏ j, t j) ^ m} := by
  rw [divisorIdealPow, ← Ideal.span_singleton_pow, ← Ideal.prod_span_singleton]
  exact congrArg (· ^ m) (Finset.prod_congr rfl fun j _ => ht j)

/-- On a chart of the divisor, an `(∏ⱼ Jⱼ)^m`-multiple is `(∏ⱼ tⱼ)^m` times a section. -/
private theorem exists_eq_pow_smul_of_mem {q : ℕ} {W : V.affineOpens} {t : ι → Γ(V, W)}
    (ht : ∀ j, (D.J j).ideal W = Ideal.span {t j}) (m : ℕ) {s : Γ(D.K q, W)}
    (hs : s ∈ divisorIdealPow D m W • (⊤ : Submodule Γ(V, W) Γ(D.K q, W))) :
    ∃ y : Γ(D.K q, W), s = (∏ j, t j) ^ m • y := by
  rw [divisorIdealPow_eq_span D ht, Submodule.ideal_span_singleton_smul] at hs
  obtain ⟨y, -, rfl⟩ := hs
  exact ⟨y, rfl⟩

/-- **The differential of `F_*Ω^•(log S)` preserves `I_S^p Ω^•(log S)`**: locally
`d(hᵖ y) = hᵖ dy` for the local equation `h` of the divisor. -/
private theorem isLocallyIn_d_pow (q : ℕ) {W : V.Opens} {s : Γ(D.K q, W)}
    (hs : IsLocallyIn (D.K q) (divisorIdealPow D p) s) :
    IsLocallyIn (D.K (q + 1)) (divisorIdealPow D p) ((D.d q).app W s) := by
  intro x hx
  obtain ⟨W₀, t, -, hxW₀, ht, -, -, -⟩ :=
    exists_affineOpen_snc_chart_le f D.J D.hJ D.U D.hU hx
  obtain ⟨W₁, h₁, hx₁, hle, hm⟩ :=
    hs.restrict (D.K q) _ (map_divisorIdealPow_le D p) hx hxW₀
  let t₁ : ι → Γ(V, W₁) := fun j => V.presheaf.map (homOfLE hle).op (t j)
  have ht₁ : ∀ j, (D.J j).ideal W₁ = Ideal.span {t₁ j} := by
    intro j
    rw [← (D.J j).map_ideal hle, ht j, Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨y, hy⟩ := exists_eq_pow_smul_of_mem D ht₁ p hm
  refine ⟨W₁, h₁, hx₁, ?_⟩
  have hnat := (app_presheaf_map (D.d q) (homOfLE h₁) s).symm
  have p1 := D.pushforward_smul (D.K q) W₁ (∏ j, t₁ j) y
  have p2 := Scheme.Modules.Hom.app_smul (U := (W₁ : V.Opens)) (D.d q) (∏ j, t₁ j)
    (show Γ((Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K q), W₁) from y)
  have p3 := D.pushforward_smul (D.K (q + 1)) W₁ (∏ j, t₁ j) ((D.d q).app W₁ y)
  have key : ((D.K (q + 1)).presheaf.map (homOfLE h₁).op ((D.d q).app W s) :
      Γ(D.K (q + 1), W₁)) = (∏ j, t₁ j) ^ p •
        (show Γ(D.K (q + 1), W₁) from (D.d q).app W₁ y) :=
    hnat.trans ((congrArg ((D.d q).app (W₁ : V.Opens)) (hy.trans p1.symm)).trans (p2.trans p3))
  rw [key, divisorIdealPow_eq_span D ht₁]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial

/-- The differential of `F_*Ω^•(log S)` restricted to `F_*(I_S^p Ω^•(log S))`. -/
private noncomputable def twistedD (q : ℕ) :
    (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (twistedLog D p q) ⟶
      (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (twistedLog D p (q + 1)) :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun s => ⟨(D.d q).app W.unop s.1, isLocallyIn_d_pow D q s.2⟩
          map_zero' := Subtype.ext (map_zero _)
          map_add' := fun a b => Subtype.ext (map_add _ a.1 b.1) }
      naturality := fun W W' g => by
        ext s
        exact Subtype.ext (app_presheaf_map (D.d q) (homOfLE (leOfHom g.unop)) s.1) }
    fun W r s => Subtype.ext (Scheme.Modules.Hom.app_smul (U := W.unop) (D.d q) r s.1)⟩

private theorem twistedD_comp (q : ℕ) : twistedD D q ≫ twistedD D (q + 1) = 0 := by
  ext W s
  exact Subtype.ext (congrArg (fun φ => φ.app W s.1) (D.hd q))

/-- The complex `F_*(I_S^p Ω^•(log S))`, indexed by `ℕ`. -/
private noncomputable abbrev twistedComplex : CochainComplex V.Modules ℕ :=
  CochainComplex.of (fun q => (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj
    (twistedLog D p q)) (twistedD D) (twistedD_comp D)

/-- **The complex `F_*(I_S^p Ω^•(log S))`**, extended to `ℤ`. -/
private noncomputable abbrev twistedComplexZ : CochainComplex V.Modules ℤ :=
  (twistedComplex D).extend ComplexShape.embeddingUpNat

/-- The relation "the regular form `ω` restricts to the form of the twisted logarithmic form `s`
off the divisor". -/
private def IsRegularRep (m q : ℕ) (O : V.Opens) (_ : O ≤ ⊤) (s : Γ(twistedLog D m q, O))
    (ω : Γ(f.relativeDifferentialForms (q : ℤ), O)) : Prop :=
  (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE (inf_le_left : O ⊓ D.U ≤ O)).op ω =
    D.e q O s.1

/-- **A twisted logarithmic form is regular near every point** (for `m ≥ 1`). -/
private theorem exists_isRegularRep (m q : ℕ) (hm : 1 ≤ m) (O : V.Opens) (s : Γ(twistedLog D m q, O))
    {x : V} (hx : x ∈ O) : ∃ (O' : V.Opens) (h : O' ≤ O), x ∈ O' ∧
      ∃ ω, IsRegularRep D m q O' le_top ((twistedLog D m q).presheaf.map (homOfLE h).op s) ω := by
  obtain ⟨W₀, t, -, hxW₀, ht, -, -, -⟩ :=
    exists_affineOpen_snc_chart_le f D.J D.hJ D.U D.hU hx
  obtain ⟨W₁, h₁, hx₁, hle, hmem⟩ :=
    IsLocallyIn.restrict (D.K q) _ (map_divisorIdealPow_le D m) s.2 hx hxW₀
  let t₁ : ι → Γ(V, W₁) := fun j => V.presheaf.map (homOfLE hle).op (t j)
  have ht₁ : ∀ j, (D.J j).ideal W₁ = Ideal.span {t₁ j} := by
    intro j
    rw [← (D.J j).map_ideal hle, ht j, Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨y, hy⟩ := exists_eq_pow_smul_of_mem D ht₁ m hmem
  obtain ⟨⟨η, hη⟩, -⟩ := (D.he_range q W₁ (D.e q W₁ y)).1 ⟨y, rfl⟩ W₁ le_rfl t₁
    (fun j => by rw [ht₁ j]; exact Ideal.mem_span_singleton_self _)
  refine ⟨W₁, h₁, hx₁, (∏ j, t₁ j) ^ (m - 1) • η, ?_⟩
  change (f.relativeDifferentialForms (q : ℤ)).presheaf.map _ ((∏ j, t₁ j) ^ (m - 1) • η) =
    D.e q W₁ ((D.K q).presheaf.map (homOfLE h₁).op s.1)
  rw [hy, D.he_smul, Scheme.Modules.map_smul, hη, MMP.DeRham.presheaf_map_id, smul_smul,
    ← map_mul, ← pow_succ, Nat.sub_add_cancel hm]

private theorem isRegularRep_res (m q : ℕ) {O O' : V.Opens} (h : O' ≤ O)
    {s : Γ(twistedLog D m q, O)} {ω : Γ(f.relativeDifferentialForms (q : ℤ), O)}
    (hs : IsRegularRep D m q O le_top s ω) :
    IsRegularRep D m q O' le_top ((twistedLog D m q).presheaf.map (homOfLE h).op s)
      ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h).op ω) := by
  have a := D.he_res q O' O h s.1
  have b := MMP.DeRham.presheaf_map_map (F := f.relativeDifferentialForms (q : ℤ)) (homOfLE h)
    (homOfLE (inf_le_left : O' ⊓ D.U ≤ O')) (homOfLE (inf_le_left.trans h)) ω
  have c := MMP.DeRham.presheaf_map_map (F := f.relativeDifferentialForms (q : ℤ))
    (homOfLE (inf_le_left : O ⊓ D.U ≤ O)) (homOfLE (inf_le_inf_right D.U h))
    (homOfLE (inf_le_left.trans h)) ω
  exact b.trans (c.symm.trans ((congrArg _ hs).trans a.symm))

/-- The regular representatives of twisted logarithmic forms define a morphism. -/
private theorem isLocalSectionRel_isRegularRep (m q : ℕ) (hm : 1 ≤ m) :
    IsLocalSectionRel (A := ⊤) (IsRegularRep D m q) where
  exists_local O _ s _ hx := by
    obtain ⟨O', h, hx', ω, hω⟩ := exists_isRegularRep D m q hm O s hx
    exact ⟨O', h, hx', ω, hω⟩
  compat {O₁ O₂ O₃} _ _ h₃₁ h₃₂ s₁ y₁ s₂ y₂ h₁ h₂ hs := by
    refine forms_res_injective D q O₃ ?_
    have e₁ := isRegularRep_res D m q h₃₁ h₁
    have e₂ := isRegularRep_res D m q h₃₂ h₂
    exact e₁.trans ((congrArg (fun z => D.e q O₃ (Subtype.val z)) hs).trans e₂.symm)
  res _ h _ _ hs := isRegularRep_res D m q h hs
  add {O} _ s y s' y' hs hs' :=
    (map_add _ y y').trans ((congrArg₂ (· + ·) hs hs').trans (map_add (D.e q O) s.1 s'.1).symm)
  smul {O} _ r s y hs :=
    (Scheme.Modules.map_smul _ _ _ _).trans ((congrArg _ hs).trans (D.he_smul q O r s.1).symm)

/-- **Twisted logarithmic forms are regular**: the morphism `I_S^m Ω^q(log S) ⟶ Ω^q`, `m ≥ 1`. -/
private noncomputable def twistedToRegular (m q : ℕ) (hm : 1 ≤ m) :
    twistedLog D m q ⟶ f.relativeDifferentialForms (q : ℤ) :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        ((isLocalSectionRel_isRegularRep D m q hm).glue W.unop le_top)
      naturality := fun W W' g => by
        ext s
        change (isLocalSectionRel_isRegularRep D m q hm).glueSec le_top
            ((twistedLog D m q).presheaf.map (homOfLE (leOfHom g.unop)).op s) =
          (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE (leOfHom g.unop)).op
            ((isLocalSectionRel_isRegularRep D m q hm).glueSec le_top s)
        exact (isLocalSectionRel_isRegularRep D m q hm).glueSec_res le_top
          (leOfHom g.unop) s }
    fun W r s => (isLocalSectionRel_isRegularRep D m q hm).glueSec_smul le_top r s⟩

private theorem isRegularRep_twistedToRegular (m q : ℕ) (hm : 1 ≤ m) (W : V.Opens)
    (s : Γ(twistedLog D m q, W)) :
    IsRegularRep D m q W le_top s ((twistedToRegular D m q hm).app W s) := by
  set hR := isLocalSectionRel_isRegularRep D m q hm
  set Ω := f.relativeDifferentialForms (q : ℤ)
  let W' : V.Opens := W ⊓ D.U
  have hW' : W' ≤ W' ⊓ D.U := le_inf le_rfl inf_le_right
  let s' := (twistedLog D m q).presheaf.map (homOfLE (inf_le_left : W' ≤ W)).op s
  have hrep : IsRegularRep D m q W' le_top s' (Ω.presheaf.map (homOfLE hW').op (D.e q W' s'.1)) :=
    (MMP.DeRham.presheaf_map_map (F := Ω) _ _ (𝟙 _) _).trans (MMP.DeRham.presheaf_map_id (F := Ω) _ _)
  have h1 : hR.glueSec le_top s' = Ω.presheaf.map (homOfLE hW').op (D.e q W' s'.1) :=
    hR.glueSec_eq le_top hrep
  have h2 : hR.glueSec le_top s' = Ω.presheaf.map (homOfLE (inf_le_left : W' ≤ W)).op
      (hR.glueSec le_top s) := hR.glueSec_res le_top inf_le_left s
  have a := D.he_res q W' W inf_le_left s.1
  change Ω.presheaf.map (homOfLE (inf_le_left : W' ≤ W)).op (hR.glueSec le_top s) = D.e q W s.1
  rw [← h2, h1]
  change Ω.presheaf.map (homOfLE hW').op (D.e q W' ((D.K q).presheaf.map
    (homOfLE (inf_le_left : W' ≤ W)).op s.1)) = _
  rw [a]
  exact (MMP.DeRham.presheaf_map_map (F := Ω) _ _ (𝟙 _) _).trans
    (MMP.DeRham.presheaf_map_id (F := Ω) _ _)

/-- The inclusion of twisted logarithmic forms factors through the regular forms. -/
private theorem twistedToRegular_comp_regularIncl (m q : ℕ) (hm : 1 ≤ m) :
    twistedToRegular D m q hm ≫ regularIncl D q = (twistedLogSubmodule D m q).ι := by
  ext W s
  refine D.he_inj q W ?_
  exact (e_regularIncl_app D q W _).trans (isRegularRep_twistedToRegular D m q hm W s)

/-! ### The inclusion of the twisted complex and twisted Čech cocycles -/

/-- The sections of a zero sheaf of modules form a subsingleton. -/
private theorem subsingleton_sections_of_isZero {M : V.Modules} (hM : IsZero M) (W : V.Opens) :
    Subsingleton Γ(M, W) := by
  refine ⟨fun a b => ?_⟩
  have e := hM.eq_of_src (𝟙 M) 0
  have ha : a = 0 := congrArg (fun φ : M ⟶ M => φ.app W a) e
  have hb : b = 0 := congrArg (fun φ : M ⟶ M => φ.app W b) e
  rw [ha, hb]

private theorem twistedD_comp_ι (q : ℕ) :
    twistedD D q ≫ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map
      (twistedLogSubmodule D p (q + 1)).ι =
    (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (twistedLogSubmodule D p q).ι ≫
      D.d q := by
  ext W s
  rfl

/-- The inclusion `F_*(I_S^p Ω^•(log S)) ⟶ F_*Ω^•(log S)`. -/
private noncomputable def twistedIncl : twistedComplex D ⟶ D.complex :=
  CochainComplex.ofHom
    (fun q => (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map
      (twistedLogSubmodule D p q).ι)
    (fun q => by
      have h1 := CochainComplex.of_d
        (fun q ↦ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K q)) D.d q
      have h2 := CochainComplex.of_d (fun q => (Scheme.Modules.pushforward
        (absoluteFrobenius V p D.hV)).obj (twistedLog D p q)) (twistedD D) q
      exact (congrArg (_ ≫ ·) h1).trans ((twistedD_comp_ι D q).symm.trans
        (congrArg (· ≫ _) h2.symm)))

/-- The inclusion of the twisted complexes extended to `ℤ`. -/
private noncomputable def twistedInclZ : twistedComplexZ D ⟶ D.complexZ :=
  HomologicalComplex.extendMap (twistedIncl D) ComplexShape.embeddingUpNat

private theorem twistedInclZ_f (q : ℕ) : (twistedInclZ D).f (q : ℤ) =
    ((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫ (twistedIncl D).f q ≫
      (D.complex.extendXIso ComplexShape.embeddingUpNat rfl).inv :=
  HomologicalComplex.extendMap_f (twistedIncl D) ComplexShape.embeddingUpNat (i := q)
    (i' := (q : ℤ)) rfl

private theorem twistedIncl_f_app_injective (q : ℕ) (W : V.Opens) :
    Function.Injective (((twistedIncl D).f q).app W) := fun y y' h => Subtype.ext h

/-- The inclusion of the twisted complex is injective on sections. -/
private theorem twistedInclZ_injective (a : ℤ) (W : V.Opens) :
    Function.Injective (((twistedInclZ D).f a).app W) := by
  by_cases ha : 0 ≤ a
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    have key : Function.Injective
        ((((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
          (twistedIncl D).f q ≫ (D.complex.extendXIso ComplexShape.embeddingUpNat rfl).inv).app W) := by
      intro y y' hy
      simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hy
      exact app_injective_of_mono _ W (twistedIncl_f_app_injective D q W
        (app_injective_of_mono (D.complex.extendXIso ComplexShape.embeddingUpNat rfl).inv W hy))
    exact (twistedInclZ_f D q) ▸ key
  · haveI := subsingleton_sections_of_isZero (HomologicalComplex.isZero_extend_X
      (twistedComplex D) ComplexShape.embeddingUpNat a (fun i hi => ha (hi ▸ by
        change (0 : ℤ) ≤ (i : ℤ); omega))) W
    exact fun _ _ _ => Subsingleton.elim _ _

section TwistedCocycle

open Stacks.CategoryTheory.CechComplex (inter)

variable {κ : Type} {U : κ → V.Opens}

/-- The component at `x` of a morphism into the Čech bicomplex of `F_*K^•`, read in `F_*K^b`. -/
private noncomputable def cechComp {M : V.Modules} (b : ℕ) {m : ℕ}
    (g : M ⟶ ((cechBicomplex U D.complexZ).X (b : ℤ)).X m) (x : Fin (m + 1) → κ) (W : V.Opens)
    (t : Γ(M, W)) : Γ(D.K b, W ⊓ inter U x) :=
  (D.complexZXIso b).hom.app _ (secCochain (g.app W t) x)

private theorem cechComp_add {M : V.Modules} (b : ℕ) {m : ℕ}
    (g : M ⟶ ((cechBicomplex U D.complexZ).X (b : ℤ)).X m) (x : Fin (m + 1) → κ) (W : V.Opens)
    (t t' : Γ(M, W)) :
    cechComp D b g x W (t + t') = cechComp D b g x W t + cechComp D b g x W t' := by
  unfold cechComp
  rw [map_add, secCochain_add, Pi.add_apply, map_add]
  rfl

private theorem cechComp_smul {M : V.Modules} (b : ℕ) {m : ℕ}
    (g : M ⟶ ((cechBicomplex U D.complexZ).X (b : ℤ)).X m) (x : Fin (m + 1) → κ) (W : V.Opens)
    (r : Γ(V, W)) (t : Γ(M, W)) :
    cechComp D b g x W (r • t) =
      (V.presheaf.map (homOfLE (inf_le_left : W ⊓ inter U x ≤ W)).op r) ^ p •
        cechComp D b g x W t := by
  unfold cechComp
  rw [Scheme.Modules.Hom.app_smul, secCochain_smul, CechCochain.smul_apply,
    Scheme.Modules.Hom.app_smul]
  exact D.pushforward_smul (D.K b) _ _ _

private theorem cechComp_res {M : V.Modules} (b : ℕ) {m : ℕ}
    (g : M ⟶ ((cechBicomplex U D.complexZ).X (b : ℤ)).X m) (x : Fin (m + 1) → κ) {W W' O : V.Opens}
    (h : W' ≤ W) (hO : O ≤ W' ⊓ inter U x) (t : Γ(M, W)) :
    (D.K b).presheaf.map (homOfLE hO).op
        (cechComp D b g x W' (M.presheaf.map (homOfLE h).op t)) =
      (D.K b).presheaf.map (homOfLE (hO.trans (inf_le_inf_right _ h))).op
        (cechComp D b g x W t) := by
  unfold cechComp
  have e1 := app_presheaf_map g (homOfLE h) t
  have e2 := secCochain_map (U := U) (K := D.complexZ) h (g.app W t)
  have e3 := congrFun e2 x
  rw [CechCochain.res_apply] at e3
  rw [e1, e3]
  have e4 := app_presheaf_map (D.complexZXIso b).hom (homOfLE (inf_le_inf_right (inter U x) h))
    (secCochain (g.app W t) x)
  erw [e4]
  exact MMP.DeRham.presheaf_map_map _ _ _ _

private theorem pow_mem_divisorIdealPow {W : V.affineOpens} {r : Γ(V, W)}
    (hr : r ∈ divisorIdealPow D 1 W) : r ^ p ∈ divisorIdealPow D p W := by
  have hr' : r ∈ ∏ j, (D.J j).ideal W := by simpa [divisorIdealPow] using hr
  exact Ideal.pow_mem_pow hr' p

/-- **The components of a Čech cochain of `I_S Ω^q(log S)` lie in `I_S^p`**: the Čech
components are Frobenius-semilinear. -/
private theorem isLocallyIn_cechComp (q b : ℕ) {m : ℕ}
    (g : D.K q ⟶ ((cechBicomplex U D.complexZ).X (b : ℤ)).X m) (x : Fin (m + 1) → κ)
    (W : V.Opens) (s : Γ(twistedLog D 1 q, W)) :
    IsLocallyIn (D.K b) (divisorIdealPow D p) (cechComp D b g x W s.1) := by
  intro z hz
  have hs : IsLocallyIn (D.K q) (divisorIdealPow D 1) s.1 := s.2
  obtain ⟨W₁, h₁, hz₁, hm⟩ := hs z hz.1
  obtain ⟨W₂, hz₂, hle⟩ := LogSpreadingProof.G1.exists_affineOpens_le
    (show z ∈ (W₁ : V.Opens) ⊓ inter U x from ⟨hz₁, hz.2⟩)
  refine ⟨W₂, hle.trans (inf_le_inf_right _ h₁), hz₂, ?_⟩
  have hres := cechComp_res D b g x h₁ hle s.1
  rw [← hres]
  refine Submodule.smul_induction_on hm (fun r hr u _ => ?_) (fun u u' hu hu' => ?_)
  · rw [cechComp_smul, Scheme.Modules.map_smul, map_pow,
      MMP.DeRham.ring_presheaf_map_map _ _ (homOfLE (hle.trans inf_le_left))]
    exact Submodule.smul_mem_smul (pow_mem_divisorIdealPow D
      (map_divisorIdealPow_le D 1 W₁ W₂ (hle.trans inf_le_left) (Ideal.mem_map_of_mem _ hr)))
      trivial
  · rw [cechComp_add, map_add]
    exact add_mem hu hu'

/-- **The components of a Čech cocycle on `I_S Ω^q(log S)` come from `F_*(I_S^p Ω^•(log S))`.** -/
private theorem exists_twistedInclZ_app_eq (q : ℕ) {n' : ℤ}
    (Ψ : CechCocycleData U D.complexZ (D.K q) n') (a : ℤ) (m : ℕ) (hpm : a + m = n')
    (W : V.Opens) (s : Γ(twistedLog D 1 q, W)) (x : Fin (m + 1) → κ) :
    ∃ y, ((twistedInclZ D).f a).app _ y =
      secCochain (((cocyclePrecomp (twistedLogSubmodule D 1 q).ι Ψ).g a m hpm).app W s) x := by
  by_cases ha : 0 ≤ a
  · obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    let τ : Γ(twistedLog D p b, W ⊓ inter U x) :=
      ⟨cechComp D b (Ψ.g b m hpm) x W s.1, isLocallyIn_cechComp D q b (Ψ.g b m hpm) x W s⟩
    refine ⟨((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).inv.app _ τ, ?_⟩
    rw [twistedInclZ_f]
    change (D.complex.extendXIso ComplexShape.embeddingUpNat rfl).inv.app _
        (((twistedIncl D).f b).app _
          (((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).hom.app _
            (((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).inv.app _ τ))) = _
    have e1 : ((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).hom.app
        (W ⊓ inter U x)
        (((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).inv.app _ τ) = τ := by
      have := congrArg (fun φ => φ.app (W ⊓ inter U x) τ)
        ((twistedComplex D).extendXIso ComplexShape.embeddingUpNat (rfl : _ = (b : ℤ))).inv_hom_id
      exact this
    have e2 := congrArg (fun φ => φ.app (W ⊓ inter U x) (secCochain ((Ψ.g b m hpm).app W s.1) x))
      (D.complexZXIso b).hom_inv_id
    refine (congrArg (fun t => (D.complex.extendXIso ComplexShape.embeddingUpNat rfl).inv.app
      (W ⊓ inter U x) (((twistedIncl D).f b).app _ t)) e1).trans ?_
    exact e2
  · haveI := subsingleton_sections_of_isZero (HomologicalComplex.isZero_extend_X
      D.complex ComplexShape.embeddingUpNat a (fun i hi => ha (hi ▸ by
        change (0 : ℤ) ≤ (i : ℤ); omega))) (W ⊓ inter U x)
    exact ⟨0, Subsingleton.elim _ _⟩

/-- **The twisted Čech cocycle**: a Čech cocycle of `F_*Ω^•(log S)` on `Ω^q(log S)`, restricted
to `I_S Ω^q(log S)`, with values in `F_*(I_S^p Ω^•(log S))`. -/
private noncomputable def twistedCocycle (q : ℕ) {n' : ℤ}
    (Ψ : CechCocycleData U D.complexZ (D.K q) n') :
    CechCocycleData U (twistedComplexZ D) (twistedLog D 1 q) n' :=
  cocycleLift (twistedInclZ D) (twistedInclZ_injective D)
    (cocyclePrecomp (twistedLogSubmodule D 1 q).ι Ψ) (exists_twistedInclZ_app_eq D q Ψ)

private theorem twistedCocycle_g_comp (q : ℕ) {n' : ℤ}
    (Ψ : CechCocycleData U D.complexZ (D.K q) n') (a : ℤ) (m : ℕ) (hpm : a + m = n') :
    (twistedCocycle D q Ψ).g a m hpm ≫ ((cechBicomplexMap (U := U) (twistedInclZ D)).f a).f m =
      (twistedLogSubmodule D 1 q).ι ≫ Ψ.g a m hpm :=
  cocycleLift_g_comp _ _ _ _ a m hpm

/-! ### The inverse Cartier relation on twisted forms -/

/-- The algebraic form of a multiple of a logarithmic form. -/
private theorem formsAlgEquiv_e_smul (q : ℕ) {W : V.Opens} (A : V.affineOpens)
    (hA : (A : V.Opens) ≤ W ⊓ D.U) (r : Γ(V, W)) (t : Γ(D.K q, W)) :
    letI := MMP.Mori.sectionAlgebra f A
    formsAlgEquiv f q A ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hA).op
        (D.e q W (r • t))) =
      V.presheaf.map (homOfLE (hA.trans inf_le_left)).op r •
        formsAlgEquiv f q A ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hA).op
          (D.e q W t)) := by
  letI := MMP.Mori.sectionAlgebra f A
  rw [D.he_smul, Scheme.Modules.map_smul, MMP.DeRham.ring_presheaf_map_map, map_smul]

/-- **The inverse Cartier relation is Frobenius-semilinear**: `C⁻¹(r s) = r^p C⁻¹(s)`. -/
private theorem cartierRep_smul_pow (q : ℕ) {W : V.Opens} (r : Γ(V, W)) {s z : Γ(D.K q, W)}
    (h : D.cartierRep q W s z) : D.cartierRep q W (r • s) (r ^ p • z) := by
  intro A hA _
  letI := MMP.Mori.sectionAlgebra f A
  rw [formsAlgEquiv_e_smul D q A hA, formsAlgEquiv_e_smul D q A hA, map_pow]
  exact (h A hA).smul _

/-- **Representatives of `C⁻¹ 0` can be divided by a function invertible off the divisor.** -/
private theorem cartierRep_zero_of_pow_smul (q : ℕ) {W : V.Opens} (r : Γ(V, W))
    (hr : ∀ (A : V.affineOpens) (hA : (A : V.Opens) ≤ W ⊓ D.U),
      IsUnit (V.presheaf.map (homOfLE (hA.trans inf_le_left)).op r))
    {w : Γ(D.K q, W)} (h : D.cartierRep q W 0 (r ^ p • w)) : D.cartierRep q W 0 w := by
  intro A hA _
  letI := MMP.Mori.sectionAlgebra f A
  set X := formsAlgEquiv f q A ((f.relativeDifferentialForms (q : ℤ)).presheaf.map
    (homOfLE hA).op (D.e q W w)) with hX
  set c := V.presheaf.map (homOfLE (hA.trans inf_le_left)).op r with hc
  have h0 : formsAlgEquiv f q A ((f.relativeDifferentialForms (q : ℤ)).presheaf.map
      (homOfLE hA).op (D.e q W 0)) = 0 := by
    simp only [map_zero]
  have h1 : IsInvCartierRep p q 0 (c ^ p • X) := by
    have h' := h A hA
    rw [h0, formsAlgEquiv_e_smul D q A hA, map_pow] at h'
    exact h'
  obtain ⟨u, hu⟩ := hr A hA
  have hu' : (u : Γ(V, A)) = c := hu
  have h2 := h1.smul (↑u⁻¹ : Γ(V, A))
  rw [← hu', smul_zero, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at h2
  rw [h0]
  exact h2

/-- A morphism between Frobenius pushforwards is linear for `p`-th powers. -/
private theorem pushforward_hom_app_pow_smul {M N : V.Modules}
    (φ : (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj M ⟶
      (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj N) (W : V.Opens)
    (r : Γ(V, W)) (y : Γ(M, W)) :
    (φ.app W (show Γ(M, W) from r ^ p • y) : Γ(N, W)) =
      r ^ p • (show Γ(N, W) from φ.app W y) := by
  have p1 := D.pushforward_smul M W r y
  have p2 := Scheme.Modules.Hom.app_smul (U := W) φ r
    (show Γ((Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj M, W) from y)
  have p3 := D.pushforward_smul N W r (φ.app W y)
  exact (congrArg (φ.app W) p1.symm).trans (p2.trans p3)

/-- On a chart, the `p`-th power of the product of the coordinates lies in `I_S^p`. -/
private theorem prod_pow_mem_divisorIdealPow (m : ℕ) {W₁ : V.affineOpens} {t : ι → Γ(V, W₁)}
    (ht : ∀ j, (D.J j).ideal W₁ = Ideal.span {t j}) {W'' : V.affineOpens}
    (h : (W'' : V.Opens) ≤ W₁) :
    (V.presheaf.map (homOfLE h).op (∏ j, t j)) ^ m ∈ divisorIdealPow D m W'' := by
  refine Ideal.pow_mem_pow ?_ m
  rw [map_prod]
  refine Ideal.prod_mem_prod fun j _ => ?_
  rw [← (D.J j).map_ideal h]
  exact Ideal.mem_map_of_mem _ (by rw [ht j]; exact Ideal.mem_span_singleton_self _)

/-- A `p`-th power multiple of the product of chart coordinates is a twisted form. -/
private theorem isLocallyIn_prod_pow_smul (m q : ℕ) {W₁ : V.affineOpens} {t : ι → Γ(V, W₁)}
    (ht : ∀ j, (D.J j).ideal W₁ = Ideal.span {t j}) {W₂ : V.Opens} (h : W₂ ≤ W₁)
    (y : Γ(D.K q, W₂)) :
    IsLocallyIn (D.K q) (divisorIdealPow D m)
      ((V.presheaf.map (homOfLE h).op (∏ j, t j)) ^ m • y) := by
  intro x hx
  obtain ⟨W'', hx'', hle⟩ := LogSpreadingProof.G1.exists_affineOpens_le hx
  refine ⟨W'', hle, hx'', ?_⟩
  rw [Scheme.Modules.map_smul, map_pow, MMP.DeRham.ring_presheaf_map_map _ _ (homOfLE (hle.trans h))]
  exact Submodule.smul_mem_smul (prod_pow_mem_divisorIdealPow D m ht (hle.trans h)) trivial

/-- **Twisted forms on a chart**: near every point, a section of `I_S^m Ω^q(log S)` is
`(∏ⱼ tⱼ)^m w` on an affine chart with coordinates `tⱼ` of the divisor, whose product is
invertible off the divisor. -/
private theorem exists_chart_pow_smul (m q : ℕ) {W : V.Opens} (v : Γ(twistedLog D m q, W)) {x : V}
    (hx : x ∈ W) :
    ∃ (W₁ : V.affineOpens) (h₁ : (W₁ : V.Opens) ≤ W) (t₁ : ι → Γ(V, W₁)), x ∈ (W₁ : V.Opens) ∧
      (∀ j, (D.J j).ideal W₁ = Ideal.span {t₁ j}) ∧
      (∀ (A : V.affineOpens) (hA : (A : V.Opens) ≤ (W₁ : V.Opens) ⊓ D.U),
        IsUnit (V.presheaf.map (homOfLE (hA.trans inf_le_left)).op (∏ j, t₁ j))) ∧
      ∃ w : Γ(D.K q, W₁), (D.K q).presheaf.map (homOfLE h₁).op v.1 = (∏ j, t₁ j) ^ m • w := by
  obtain ⟨W₀, t, -, hxW₀, ht, -, hWU, -⟩ :=
    exists_affineOpen_snc_chart_le f D.J D.hJ D.U D.hU hx
  have hv : IsLocallyIn (D.K q) (divisorIdealPow D m) v.1 := v.2
  obtain ⟨W₁, h₁, hx₁, hle, hmem⟩ :=
    hv.restrict (D.K q) _ (map_divisorIdealPow_le D m) hx hxW₀
  let t₁ : ι → Γ(V, W₁) := fun j => V.presheaf.map (homOfLE hle).op (t j)
  have ht₁ : ∀ j, (D.J j).ideal W₁ = Ideal.span {t₁ j} := by
    intro j
    rw [← (D.J j).map_ideal hle, ht j, Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨w, hw⟩ := exists_eq_pow_smul_of_mem D ht₁ m hmem
  refine ⟨W₁, h₁, t₁, hx₁, ht₁, fun A hA => ?_, w, hw⟩
  have hprod : ∏ j, t₁ j = V.presheaf.map (homOfLE hle).op (∏ j, t j) := (map_prod _ _ _).symm
  have hA' : (A : V.Opens) ≤ V.basicOpen (∏ j, t j) :=
    hWU ▸ (hA.trans (inf_le_inf_right _ hle))
  have hu := MMP.DeRham.isUnit_map_of_le_basicOpen (hA'.trans (V.basicOpen_le _)) (∏ j, t j) hA'
  rw [hprod, MMP.DeRham.ring_presheaf_map_map]
  exact hu

/-- **A twisted representative of `C⁻¹ 0` is locally a twisted boundary.** -/
private theorem exists_d_eq_of_cartierRep_zero_twisted (q : ℕ) {W : V.Opens}
    (v : Γ(twistedLog D p (q + 1), W)) (hv : D.cartierRep (q + 1) W 0 v.1) {x : V}
    (hx : x ∈ W) :
    ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧ ∃ y : Γ(twistedLog D p q, W'),
      (D.d q).app W' y.1 = (D.K (q + 1)).presheaf.map (homOfLE h).op v.1 := by
  obtain ⟨W₁, h₁, t₁, hx₁, ht₁, hunit, w, hw⟩ := exists_chart_pow_smul D p (q + 1) v hx
  have hr : D.cartierRep (q + 1) W₁ 0 ((∏ j, t₁ j) ^ p • w) := by
    have := D.cartierRep_restrict (q + 1) h₁ hv
    rwa [map_zero, hw] at this
  have hw0 := cartierRep_zero_of_pow_smul D (q + 1) _ hunit hr
  obtain ⟨W₂, h₂, hx₂, y, hy⟩ := D.exists_d_eq_of_cartierRep_zero q hw0 hx₁
  refine ⟨W₂, h₂.trans h₁, hx₂, ⟨(V.presheaf.map (homOfLE h₂).op (∏ j, t₁ j)) ^ p • y,
    isLocallyIn_prod_pow_smul D p q ht₁ h₂ y⟩, ?_⟩
  change (D.d q).app W₂ ((V.presheaf.map (homOfLE h₂).op (∏ j, t₁ j)) ^ p • y) = _
  rw [pushforward_hom_app_pow_smul D (D.d q) W₂, hy]
  have e1 := MMP.DeRham.presheaf_map_map (F := D.K (q + 1)) (homOfLE h₁) (homOfLE h₂)
    (homOfLE (h₂.trans h₁)) v.1
  have e2 : (D.K (q + 1)).presheaf.map (homOfLE h₂).op ((∏ j, t₁ j) ^ p • w) =
      (V.presheaf.map (homOfLE h₂).op (∏ j, t₁ j)) ^ p •
        (D.K (q + 1)).presheaf.map (homOfLE h₂).op w := by
    rw [Scheme.Modules.map_smul, map_pow]
  exact (e2.symm.trans (congrArg _ hw.symm)).trans e1

/-- Logarithmic forms have no torsion for a function invertible off the divisor. -/
private theorem eq_zero_of_pow_smul_eq_zero (a : ℕ) {W : V.Opens} (r : Γ(V, W))
    (hr : ∀ (A : V.affineOpens) (hA : (A : V.Opens) ≤ W ⊓ D.U),
      IsUnit (V.presheaf.map (homOfLE (hA.trans inf_le_left)).op r))
    {u : Γ(D.K a, W)} (h : r ^ p • u = 0) : u = 0 := by
  refine D.he_inj a W (Eq.trans ?_ (map_zero _).symm)
  refine D.eq_zero_of_forall_affineOpens a _ fun A hA _ => ?_
  obtain ⟨c, hc⟩ := hr A hA
  set X := (f.relativeDifferentialForms (a : ℤ)).presheaf.map (homOfLE hA).op (D.e a W u)
  have e1 : (f.relativeDifferentialForms (a : ℤ)).presheaf.map (homOfLE hA).op
      (D.e a W (r ^ p • u)) = 0 := by rw [h, map_zero, map_zero]
  rw [D.he_smul, Scheme.Modules.map_smul, MMP.DeRham.ring_presheaf_map_map, map_pow] at e1
  have hc' : (c : Γ(V, A)) = V.presheaf.map (homOfLE (hA.trans inf_le_left)).op r := hc
  have e2 := congrArg (fun y => ((↑c⁻¹ : Γ(V, A)) ^ p) • y) e1
  simp only [smul_zero] at e2
  rw [← hc', smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at e2
  exact e2

/-- The relation "`z` represents `C⁻¹ s`" between twisted forms. -/
private def TwistedRep (q : ℕ) (W : V.Opens) (s : Γ(twistedLog D 1 q, W))
    (z : ToType (((twistedComplex D).X q).val.obj (op W))) : Prop :=
  D.cartierRep q W s.1 (show Γ(twistedLog D p q, W) from z).1

private theorem twistedComplex_d_val (i j : ℕ) {W : V.Opens}
    (y : ToType (((twistedComplex D).X i).val.obj (op W))) :
    (show Γ(twistedLog D p j, W) from ((twistedComplex D).d i j).val.app (op W) y).1 =
      (D.complex.d i j).val.app (op W) (show Γ(twistedLog D p i, W) from y).1 := by
  have h := congrArg (fun φ => φ.app W y) ((twistedIncl D).comm i j)
  exact h.symm

/-- **Twisted cycles are locally represented**: a cycle of `F_*(I_S^p Ω^•(log S))` is, near
every point, a representative of `C⁻¹ s` for a section `s` of `I_S Ω^q(log S)`, up to a
twisted boundary. -/
private theorem exists_twistedRep_of_cycle (q : ℕ) (W : V.Opens)
    (z : ToType (((twistedComplex D).X q).val.obj (op W)))
    (hz : ((twistedComplex D).d q (q + 1)).val.app (op W) z = 0) {x : V} (hx : x ∈ W) :
    ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧ ∃ (s : Γ(twistedLog D 1 q, W'))
      (y : ToType (((twistedComplex D).X ((ComplexShape.up ℕ).prev q)).val.obj (op W')))
      (z' : ToType (((twistedComplex D).X q).val.obj (op W'))), TwistedRep D q W' s z' ∧
      ((twistedComplex D).X q).val.map (homOfLE h).op z =
        z' + ((twistedComplex D).d _ q).val.app (op W') y := by
  set z₀ : Γ(twistedLog D p q, W) := z
  obtain ⟨W₁, h₁, t₁, hx₁, ht₁, hunit, w, hw⟩ := exists_chart_pow_smul D p q z₀ hx
  have hdz : (D.d q).app W z₀.1 = 0 := by
    have h := twistedComplex_d_val D q (q + 1) z
    rw [hz] at h
    have hd : D.complex.d q (q + 1) = D.d q := CochainComplex.of_d
      (fun q ↦ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K q)) D.d q
    rw [hd] at h
    exact h.symm
  have hdw : (D.d q).app W₁ w = 0 := by
    refine eq_zero_of_pow_smul_eq_zero D (q + 1) _ hunit ?_
    have e1 := pushforward_hom_app_pow_smul D (D.d q) W₁ (∏ j, t₁ j) w
    have e2 := app_presheaf_map (D.d q) (homOfLE h₁) z₀.1
    rw [hdz, map_zero] at e2
    rw [← e1, ← hw]
    exact e2
  have hdw' : (D.complex.d q (q + 1)).val.app (op (W₁ : V.Opens)) w = 0 := by
    have hd : D.complex.d q (q + 1) = D.d q := CochainComplex.of_d
      (fun q ↦ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K q)) D.d q
    rw [hd]
    exact hdw
  obtain ⟨W₂, h₂, hx₂, s', y, z', hr, hwz⟩ := D.exists_cartierRep_of_cycle q W₁ w hdw' hx₁
  set c : Γ(V, W₂) := V.presheaf.map (homOfLE h₂).op (∏ j, t₁ j)
  have hs : IsLocallyIn (D.K q) (divisorIdealPow D 1) (c • s') := by
    have := isLocallyIn_prod_pow_smul D 1 q ht₁ h₂ s'
    rwa [pow_one] at this
  let y₀ : Γ(D.K ((ComplexShape.up ℕ).prev q), W₂) := y
  let y'' : Γ(twistedLog D p ((ComplexShape.up ℕ).prev q), W₂) :=
    ⟨c ^ p • y₀, isLocallyIn_prod_pow_smul D p _ ht₁ h₂ _⟩
  let z₁ : Γ(D.K q, W₂) := z'
  let z'' : Γ(twistedLog D p q, W₂) := ⟨c ^ p • z₁, isLocallyIn_prod_pow_smul D p q ht₁ h₂ _⟩
  refine ⟨W₂, h₂.trans h₁, hx₂, ⟨c • s', hs⟩, y'', z'', cartierRep_smul_pow D q c hr, ?_⟩
  apply Subtype.ext
  have hd := twistedComplex_d_val D ((ComplexShape.up ℕ).prev q) q (W := W₂) y''
  have he3 := pushforward_hom_app_pow_smul D (D.complex.d ((ComplexShape.up ℕ).prev q) q) W₂ c y₀
  have e1 := MMP.DeRham.presheaf_map_map (F := D.K q) (homOfLE h₁) (homOfLE h₂)
    (homOfLE (h₂.trans h₁)) z₀.1
  have e2 : (D.K q).presheaf.map (homOfLE h₂).op ((∏ j, t₁ j) ^ p • w) =
      c ^ p • (D.K q).presheaf.map (homOfLE h₂).op w := by
    rw [Scheme.Modules.map_smul, map_pow]
  have hmain : (D.K q).presheaf.map (homOfLE (h₂.trans h₁)).op z₀.1 =
      c ^ p • (z₁ + (show Γ(D.K q, W₂) from
        (D.complex.d ((ComplexShape.up ℕ).prev q) q).val.app (op W₂) y₀)) := by
    rw [← e1, hw, e2]
    exact congrArg (c ^ p • ·) hwz
  refine hmain.trans ((smul_add _ _ _).trans ?_)
  refine congrArg (c ^ p • z₁ + ·) ?_
  exact (hd.trans he3).symm

/-- **Twisted forms have twisted representatives** of their inverse Cartier images, locally. -/
private theorem exists_twistedRep (q : ℕ) (W : V.Opens) (s : Γ(twistedLog D 1 q, W)) {x : V}
    (hx : x ∈ W) :
    ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧
      ∃ z, TwistedRep D q W' ((twistedLog D 1 q).val.map (homOfLE h).op s) z := by
  obtain ⟨W₁, h₁, t₁, hx₁, ht₁, -, w, hw⟩ := exists_chart_pow_smul D 1 q s hx
  obtain ⟨W₂, h₂, hx₂, z', hz'⟩ := D.exists_cartierRep q W₁ w hx₁
  set c : Γ(V, W₂) := V.presheaf.map (homOfLE h₂).op (∏ j, t₁ j)
  refine ⟨W₂, h₂.trans h₁, hx₂,
    (show Γ(twistedLog D p q, W₂) from ⟨c ^ p • z', isLocallyIn_prod_pow_smul D p q ht₁ h₂ _⟩), ?_⟩
  have e1 := MMP.DeRham.presheaf_map_map (F := D.K q) (homOfLE h₁) (homOfLE h₂)
    (homOfLE (h₂.trans h₁)) s.1
  have e2 : (D.K q).presheaf.map (homOfLE h₂).op ((∏ j, t₁ j) ^ 1 • w) =
      c • (D.K q).presheaf.map (homOfLE h₂).op w := by
    rw [Scheme.Modules.map_smul, pow_one]
  have hs : ((twistedLog D 1 q).val.map (homOfLE (h₂.trans h₁)).op s).1 =
      c • (D.K q).presheaf.map (homOfLE h₂).op w := by
    refine e1.symm.trans ?_
    rw [hw, e2]
  unfold TwistedRep
  rw [hs]
  exact cartierRep_smul_pow D q c hz'

private theorem twistedRep_restrict (q : ℕ) {W W' : V.Opens} (h : W' ≤ W)
    {s : Γ(twistedLog D 1 q, W)} {z : ToType (((twistedComplex D).X q).val.obj (op W))}
    (hr : TwistedRep D q W s z) :
    TwistedRep D q W' ((twistedLog D 1 q).val.map (homOfLE h).op s)
      (((twistedComplex D).X q).val.map (homOfLE h).op z) :=
  D.cartierRep_restrict q h hr

private theorem twistedRep_d_eq_zero (q : ℕ) {W : V.Opens}
    {s : Γ(twistedLog D 1 q, W)} {z : ToType (((twistedComplex D).X q).val.obj (op W))}
    (hr : TwistedRep D q W s z) : ((twistedComplex D).d q (q + 1)).val.app (op W) z = 0 :=
  Subtype.ext <| (twistedComplex_d_val D q (q + 1) z).trans (D.cartierRep_complex_d_eq_zero hr)

private theorem twistedRep_eq_zero (q : ℕ) {W : V.Opens}
    {s : Γ(twistedLog D 1 q, W)} {z : ToType (((twistedComplex D).X q).val.obj (op W))}
    (y : ToType (((twistedComplex D).X ((ComplexShape.up ℕ).prev q)).val.obj (op W)))
    (hr : TwistedRep D q W s z) (hy : ((twistedComplex D).d _ q).val.app (op W) y = z) :
    s = 0 := by
  apply Subtype.ext
  have hz : (show Γ(twistedLog D p q, W) from z).1 =
      (D.complex.d ((ComplexShape.up ℕ).prev q) q).val.app (op W)
        (show Γ(twistedLog D p _, W) from y).1 := by
    rw [← hy]
    exact twistedComplex_d_val D _ q y
  have hr' : D.cartierRep q W s.1 ((D.complex.d ((ComplexShape.up ℕ).prev q) q).val.app (op W)
      (show Γ(twistedLog D p _, W) from y).1) := by
    have := hr
    unfold TwistedRep at this
    rwa [hz] at this
  exact D.cartierRep_eq_zero_of_complex_d _ _ hr'

/-- **Compatibility with all twisted representatives from compatibility with some local ones.** -/
private theorem twisted_homologyπ_eq_of_local (q : ℕ)
    (c : twistedLog D 1 q ⟶ (twistedComplex D).homology q)
    (hc : ∀ (W : V.Opens) (s : Γ(twistedLog D 1 q, W)) {x : V}, x ∈ W → ∃ (W' : V.Opens)
      (h : W' ≤ W), x ∈ W' ∧ ∃ z' : ToType (((twistedComplex D).cycles q).val.obj (op W')),
        TwistedRep D q W' ((twistedLog D 1 q).val.map (homOfLE h).op s)
          (((twistedComplex D).iCycles q).val.app (op W') z') ∧
        c.val.app (op W') ((twistedLog D 1 q).val.map (homOfLE h).op s) =
          ((twistedComplex D).homologyπ q).val.app (op W') z')
    {W : V.Opens} {s : Γ(twistedLog D 1 q, W)}
    {z : ToType (((twistedComplex D).cycles q).val.obj (op W))}
    (hr : TwistedRep D q W s (((twistedComplex D).iCycles q).val.app (op W) z)) :
    c.val.app (op W) s = ((twistedComplex D).homologyπ q).val.app (op W) z := by
  refine eq_of_locally_eq_sections (M := (twistedComplex D).homology q) _ _ fun x hx ↦ ?_
  obtain ⟨W', h, hxW', z', hz', hcz'⟩ := hc W s hx
  set z₁ : ToType (((twistedComplex D).cycles q).val.obj (op W')) := ((twistedComplex D).cycles q).val.map (homOfLE h).op z
  have hi₁ : ((twistedComplex D).iCycles q).val.app (op W') z₁ =
      ((twistedComplex D).X q).val.map (homOfLE h).op (((twistedComplex D).iCycles q).val.app (op W) z) :=
    PresheafOfModules.naturality_apply ((twistedComplex D).iCycles q).val (homOfLE h).op z
  have hr₁ : TwistedRep D q W' ((twistedLog D 1 q).val.map (homOfLE h).op s)
      (((twistedComplex D).iCycles q).val.app (op W') z₁) := by
    rw [hi₁]
    exact twistedRep_restrict D q h hr
  have h0 : D.cartierRep q W' 0
      (show Γ(twistedLog D p q, W') from ((twistedComplex D).iCycles q).val.app (op W') (z₁ - z')).1 := by
    have := D.cartierRep_sub q hr₁ hz'
    have e1 : (0 : Γ(D.K q, W')) = ((twistedLog D 1 q).val.map (homOfLE h).op s).1 -
        ((twistedLog D 1 q).val.map (homOfLE h).op s).1 := (sub_self _).symm
    have e2 : (show Γ(twistedLog D p q, W') from
        ((twistedComplex D).iCycles q).val.app (op W') (z₁ - z')).1 =
        (show Γ(twistedLog D p q, W') from ((twistedComplex D).iCycles q).val.app (op W') z₁).1 -
        (show Γ(twistedLog D p q, W') from ((twistedComplex D).iCycles q).val.app (op W') z').1 := by
      rw [map_sub]
      rfl
    exact (congrArg₂ (D.cartierRep q W') e1 e2).mpr this
  have hcs : ((twistedComplex D).homology q).presheaf.map (homOfLE h).op (c.val.app (op W) s) =
      c.val.app (op W') ((twistedLog D 1 q).val.map (homOfLE h).op s) :=
    (PresheafOfModules.naturality_apply c.val (homOfLE h).op s).symm
  have hπ : ((twistedComplex D).homology q).presheaf.map (homOfLE h).op
      (((twistedComplex D).homologyπ q).val.app (op W) z) = ((twistedComplex D).homologyπ q).val.app (op W') z₁ :=
    (PresheafOfModules.naturality_apply ((twistedComplex D).homologyπ q).val (homOfLE h).op z).symm
  rcases q with _ | q
  · refine ⟨W', h, hxW', ?_⟩
    rw [hcs, hπ, hcz']
    have h00 := D.eq_zero_of_cartierRep_zero_zero h0
    have h01 : ((twistedComplex D).iCycles 0).val.app (op W') (z₁ - z') = 0 := Subtype.ext h00
    rw [map_sub, sub_eq_zero] at h01
    rw [app_injective_of_mono ((twistedComplex D).iCycles 0) W' h01]
  · obtain ⟨W'', h', hxW'', y, hy⟩ := exists_d_eq_of_cartierRep_zero_twisted D q
      (show Γ(twistedLog D p (q + 1), W') from ((twistedComplex D).iCycles (q + 1)).val.app (op W') (z₁ - z'))
      h0 hxW'
    refine ⟨W'', h'.trans h, hxW'', ?_⟩
    refine (MMP.DeRham.presheaf_map_map (homOfLE h) (homOfLE h') _ _).symm.trans
      (Eq.trans ?_ (MMP.DeRham.presheaf_map_map (homOfLE h) (homOfLE h') _ _))
    rw [hcs, hπ, hcz']
    set w : ToType (((twistedComplex D).cycles (q + 1)).val.obj (op W'')) :=
      ((twistedComplex D).cycles (q + 1)).val.map (homOfLE h').op (z₁ - z')
    have hw : w = ((twistedComplex D).toCycles q (q + 1)).val.app (op W'') y := by
      apply app_injective_of_mono ((twistedComplex D).iCycles (q + 1)) W''
      have h1 : ((twistedComplex D).iCycles (q + 1)).val.app (op W'') w =
          ((twistedComplex D).X (q + 1)).val.map (homOfLE h').op
            (((twistedComplex D).iCycles (q + 1)).val.app (op W') (z₁ - z')) :=
        PresheafOfModules.naturality_apply ((twistedComplex D).iCycles (q + 1)).val (homOfLE h').op _
      have hd : (twistedComplex D).d q (q + 1) = twistedD D q := CochainComplex.of_d
        (fun q => (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj
          (twistedLog D p q)) (twistedD D) q
      have h2 : ((twistedComplex D).iCycles (q + 1)).app W'' (((twistedComplex D).toCycles q (q + 1)).app W'' y) =
          (twistedD D q).app W'' y := by
        have := congrArg (fun φ ↦ φ.app W'' y) ((twistedComplex D).toCycles_i q (q + 1))
        rw [hd] at this
        exact this
      change ((twistedComplex D).iCycles (q + 1)).val.app (op W'') w =
        ((twistedComplex D).iCycles (q + 1)).app W'' (((twistedComplex D).toCycles q (q + 1)).app W'' y)
      rw [h2, h1]
      exact Subtype.ext hy.symm
    have h3 := congrArg (fun φ ↦ φ.app W'' y) ((twistedComplex D).toCycles_comp_homologyπ q (q + 1))
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app] at h3
    have h4 : ((twistedComplex D).homologyπ (q + 1)).val.app (op W'') w = 0 := by
      rw [hw]
      exact h3
    have h5 : ((twistedComplex D).homologyπ (q + 1)).val.app (op W'') w =
        ((twistedComplex D).homology (q + 1)).presheaf.map (homOfLE h').op
          (((twistedComplex D).homologyπ (q + 1)).val.app (op W') z₁ -
            ((twistedComplex D).homologyπ (q + 1)).val.app (op W') z') := by
      rw [← map_sub]
      exact PresheafOfModules.naturality_apply ((twistedComplex D).homologyπ (q + 1)).val
        (homOfLE h').op _
    have h6 := h5.symm.trans h4
    exact (sub_eq_zero.1 ((map_sub _ _ _).symm.trans h6)).symm

private theorem twistedInclZ_app_extendXIso_inv (q : ℕ) (O : V.Opens) (y : Γ(twistedLog D p q, O)) :
    ((twistedInclZ D).f q).app O
        (((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).inv.app O y) =
      (D.complexZXIso q).inv.app O y.1 := by
  rw [twistedInclZ_f]
  have e1 : ((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).hom.app O
      (((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).inv.app O y) = y := by
    have := congrArg (fun φ => φ.app O y)
      ((twistedComplex D).extendXIso ComplexShape.embeddingUpNat (rfl : _ = (q : ℤ))).inv_hom_id
    exact this
  exact congrArg (fun t => (D.complex.extendXIso ComplexShape.embeddingUpNat rfl).inv.app O
    (((twistedIncl D).f q).app O t)) e1

/-- The cohomology map of a Čech cocycle of the twisted complex, on an open inside a member of
the cover. -/
private theorem twisted_homologyMap_app_eq (hU : ⨆ i, U i = ⊤) {q : ℕ}
    (Ψ' : CechCocycleData U (twistedComplexZ D) (twistedLog D 1 q) (q : ℤ)) (α : κ) {W : V.Opens}
    (hW : W ≤ U α) (s : Γ(twistedLog D 1 q, W))
    (z : ToType (((twistedComplex D).cycles q).val.obj (op W)))
    (hz : ((cechBiπ (twistedComplexZ D) (q : ℤ) 0 (fun _ ↦ α)).app W
        ((Ψ'.g (q : ℤ) 0 (by simp)).app W s)).down =
      ((twistedComplexZ D).X (q : ℤ)).presheaf.map
        (homOfLE (inf_le_left : W ⊓ inter U (fun _ : Fin 1 ↦ α) ≤ W)).op
        (((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).inv.app W
          (((twistedComplex D).iCycles q).val.app (op W) z))) :
    (Ψ'.homologyMap hU 0 ≫ ((twistedComplex D).extendHomologyIso ComplexShape.embeddingUpNat
        (j := q) (j' := (q : ℤ)) rfl).hom).val.app (op W) s =
      ((twistedComplex D).homologyπ q).val.app (op W) z := by
  set e := ComplexShape.embeddingUpNat
  let z' := ((twistedComplex D).extendCyclesIso e (j := q) (j' := (q : ℤ)) rfl).inv.app W z
  have hz' : ((twistedComplexZ D).iCycles (q : ℤ)).app W z' =
      ((twistedComplex D).extendXIso e rfl).inv.app W
        (((twistedComplex D).iCycles q).val.app (op W) z) := by
    have h := congrArg (fun φ => φ.app W z)
      ((twistedComplex D).extendCyclesIso_inv_iCycles e (j := q) (j' := (q : ℤ)) rfl)
    exact h
  have h1 := Ψ'.homologyMap_app_eq hU 0 α hW s z' (hz.trans (by rw [hz']))
  have h2 := congrArg (fun φ => φ.app W z')
    ((twistedComplex D).homologyπ_extendHomologyIso_hom e (j := q) (j' := (q : ℤ)) rfl)
  have h3 := congrArg (fun φ => φ.app W z)
    ((twistedComplex D).extendCyclesIso e (j := q) (j' := (q : ℤ)) rfl).inv_hom_id
  change ((twistedComplex D).extendHomologyIso e rfl).hom.app W ((Ψ'.homologyMap hU 0).app W s) = _
  rw [h1]
  exact h2.trans (congrArg (((twistedComplex D).homologyπ q).app W) h3)

/-- **The twisted inverse Cartier isomorphism**: the restriction to `I_S Ω^q(log S)` of a Čech
cocycle representing the inverse Cartier map induces
`I_S Ω^q(log S) ≅ ℋ^q(F_*(I_S^p Ω^•(log S)))`. -/
private theorem isIso_homologyMap_twistedCocycle (hU : ⨆ i, U i = ⊤) (q : ℕ)
    (Ψ : CechCocycleData U D.complexZ (D.K q) (q : ℤ)) (hΨ : D.IsCartierCocycle q Ψ) :
    IsIso ((twistedCocycle D q Ψ).homologyMap hU 0) := by
  let eH := (twistedComplex D).extendHomologyIso ComplexShape.embeddingUpNat (j := q)
    (j' := (q : ℤ)) rfl
  let c := (twistedCocycle D q Ψ).homologyMap hU 0 ≫ eH.hom
  have hloc : ∀ (W : V.Opens) (s : Γ(twistedLog D 1 q, W)) {x : V}, x ∈ W → ∃ (W' : V.Opens)
      (h : W' ≤ W), x ∈ W' ∧ ∃ z' : ToType (((twistedComplex D).cycles q).val.obj (op W')),
        TwistedRep D q W' ((twistedLog D 1 q).val.map (homOfLE h).op s)
          (((twistedComplex D).iCycles q).val.app (op W') z') ∧
        c.val.app (op W') ((twistedLog D 1 q).val.map (homOfLE h).op s) =
          ((twistedComplex D).homologyπ q).val.app (op W') z' := by
    intro W s x hx
    obtain ⟨α, W', h, hα, hxW', y, hy, hgy⟩ := hΨ W s.1 x hx
    set s' := (twistedLog D 1 q).val.map (homOfLE h).op s
    let O := W' ⊓ inter U (fun _ : Fin 1 ↦ α)
    set comp := ((cechBiπ (twistedComplexZ D) (q : ℤ) 0 (fun _ ↦ α)).app W'
      (((twistedCocycle D q Ψ).g (q : ℤ) 0 (by simp)).app W' s')).down
    have hcomp : ((twistedInclZ D).f q).app O comp =
        (D.complexZ.X (q : ℤ)).presheaf.map (homOfLE (inf_le_left : O ≤ W')).op
          (D.toComplexZ q W' y) := by
      have e1 := secCochain_comp_cechBicomplexMap (U := U) (twistedInclZ D)
        ((twistedCocycle D q Ψ).g (q : ℤ) 0 (by simp)) W' s' (fun _ => α)
      rw [twistedCocycle_g_comp] at e1
      exact e1.symm.trans hgy
    let yt : Γ(twistedLog D p q, O) :=
      ((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).hom.app O comp
    have hyt : yt.1 = (D.K q).presheaf.map (homOfLE (inf_le_left : O ≤ W')).op y := by
      apply app_injective_of_mono (D.complexZXIso q).symm.hom O
      have e2 : ((twistedInclZ D).f q).app O comp = (D.complexZXIso q).inv.app O yt.1 := by
        have := twistedInclZ_app_extendXIso_inv D q O yt
        refine Eq.trans ?_ this
        refine congrArg _ ?_
        have := congrArg (fun φ => φ.app O comp)
          ((twistedComplex D).extendXIso ComplexShape.embeddingUpNat (rfl : _ = (q : ℤ))).hom_inv_id
        exact this.symm
      have e3 := app_presheaf_map (D.complexZXIso q).inv (homOfLE (inf_le_left : O ≤ W')) y
      exact (e2.symm.trans hcomp).trans e3.symm
    have hle : W' ≤ O := le_inf le_rfl (le_inter fun _ => hα)
    have e4 : (D.K q).presheaf.map (homOfLE hle).op
        ((D.K q).presheaf.map (homOfLE (inf_le_left : O ≤ W')).op y) = y :=
      (MMP.DeRham.presheaf_map_map _ _ (𝟙 W') y).trans (MMP.DeRham.presheaf_map_id _ y)
    have hytm : IsLocallyIn (D.K q) (divisorIdealPow D p)
        ((D.K q).presheaf.map (homOfLE (inf_le_left : O ≤ W')).op y) := hyt ▸ yt.2
    have hm := IsLocallyIn.map (D.K q) _ (map_divisorIdealPow_le D p) hle hytm
    rw [e4] at hm
    let yh : Γ(twistedLog D p q, W') := ⟨y, hm⟩
    have hd : ((twistedComplex D).d q (q + 1)).val.app (op W')
        (show ToType (((twistedComplex D).X q).val.obj (op W')) from yh) = 0 :=
      Subtype.ext ((twistedComplex_d_val D q (q + 1) _).trans (D.cartierRep_complex_d_eq_zero hy))
    obtain ⟨z', hz'⟩ := exists_iCycles_app_eq (twistedComplex D) q W' _ hd
    have e6 := twistedInclZ_app_extendXIso_inv D q W' yh
    have e7 : ((twistedInclZ D).f q).app W'
        (((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).inv.app W'
          (((twistedComplex D).iCycles q).val.app (op W') z')) = D.toComplexZ q W' y :=
      (congrArg (fun t => ((twistedInclZ D).f q).app W'
        (((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).inv.app W' t)) hz').trans e6
    refine ⟨W', h, hxW', z', ?_, ?_⟩
    · have := congrArg (fun t => D.cartierRep q W' s'.1
        (show Γ(twistedLog D p q, W') from t).1) hz'
      exact this.mpr hy
    · refine twisted_homologyMap_app_eq D hU (twistedCocycle D q Ψ) α hα s' z' ?_
      apply twistedInclZ_injective D q O
      refine hcomp.trans ?_
      have e5 := app_presheaf_map ((twistedInclZ D).f q) (homOfLE (inf_le_left : O ≤ W'))
        (((twistedComplex D).extendXIso ComplexShape.embeddingUpNat rfl).inv.app W'
          (((twistedComplex D).iCycles q).val.app (op W') z'))
      refine Eq.trans ?_ e5.symm
      exact congrArg _ e7.symm
  have hR : IsLocalCohomologyRep (twistedComplex D) q c (TwistedRep D q) :=
    { restrict := fun h _ _ hr => twistedRep_restrict D q h hr
      d_eq_zero := fun hr => twistedRep_d_eq_zero D q hr
      class_eq := fun hr => twisted_homologyπ_eq_of_local D q c hloc hr
      exists_rep := fun W s _ hx => exists_twistedRep D q W s hx
      eq_zero := fun y hr hy => twistedRep_eq_zero D q y hr hy
      exists_rep_of_cycle := fun W z hz _ hx => exists_twistedRep_of_cycle D q W z hz hx }
  have : IsIso c := hR.isIso
  have hc : (twistedCocycle D q Ψ).homologyMap hU 0 = c ≫ eH.inv := by
    simp only [c, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hc]
  infer_instance

end TwistedCocycle

/-! ### Weak charts of the lifted pair -/

section EulerCharts

open KaehlerDifferential TensorProduct

/-- On a weak chart of the divisor, the complement of the divisor is the basic open of the
product of the boundary coordinates. -/
private theorem weakChart_inf_U (c : WeakChart f n (((⨅ j, D.J j).support : Set V))) :
    (c.W : V.Opens) ⊓ D.U = V.basicOpen (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) := by
  ext y
  change y ∈ (c.W : Set V) ∧ y ∈ (D.U : Set V) ↔ y ∈ V.basicOpen _
  rw [D.hU]
  change y ∈ (c.W : Set V) ∧ y ∉ (((⨅ j, D.J j).support : Set V)) ↔ _
  have hz := Set.ext_iff.1 c.zero y
  simp only [Set.mem_inter_iff] at hz
  constructor
  · rintro ⟨hyW, hyD⟩
    by_contra hb
    exact hyD (hz.2 ⟨(Scheme.mem_zeroLocus_iff _ _ _).2 (by rintro _ rfl; exact hb), hyW⟩).1
  · intro hb
    have hyW : y ∈ (c.W : Set V) := V.basicOpen_le _ hb
    refine ⟨hyW, fun hyD => ?_⟩
    exact (Scheme.mem_zeroLocus_iff _ _ _).1 (hz.1 ⟨hyD, hyW⟩).1 _ rfl hb

/-- The basis of the differentials of a weak chart, over `k`. -/
private theorem WeakChart.exists_basis_k (c : WeakChart f n (((⨅ j, D.J j).support : Set V))) :
    letI := MMP.Mori.sectionAlgebra f c.W
    ∃ bB : Module.Basis (Fin n) Γ(V, c.W) Ω[Γ(V, c.W)⁄k],
      ∀ i, bB i = KaehlerDifferential.D k Γ(V, c.W) (c.t i) := by
  let := MMP.Mori.sectionAlgebra f c.W
  obtain ⟨b₀, hb₀⟩ := c.basis
  refine ⟨b₀.map (MMP.DeRham.kaehlerSpecEquiv f c.W), fun i => ?_⟩
  change MMP.DeRham.kaehlerSpecEquiv f c.W (b₀ i) = _
  rw [hb₀]
  exact MMP.DeRham.kaehlerBaseEquiv_d _ _ _ _

/-- **Coordinates off the divisor on a weak chart**: the differentials of the coordinates are a
basis of `Ω[Γ(W ∖ S)⁄k]`, in which the differentials of functions on `W` have coefficients
coming from `W`. -/
private theorem WeakChart.exists_basis_inf_U
    (c : WeakChart f n (((⨅ j, D.J j).support : Set V))) :
    letI := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ D.U)
    letI : Algebra Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ D.U) :=
      (V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ D.U ≤ c.W)).op).hom.toAlgebra
    ∃ bL : Module.Basis (Fin n) Γ(V, (c.W : V.Opens) ⊓ D.U) Ω[Γ(V, (c.W : V.Opens) ⊓ D.U)⁄k],
      (∀ i, bL i = KaehlerDifferential.D k Γ(V, (c.W : V.Opens) ⊓ D.U)
        (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ D.U) (c.t i))) ∧
      (∀ (b : Γ(V, c.W)) j, bL.repr (KaehlerDifferential.D k Γ(V, (c.W : V.Opens) ⊓ D.U)
        (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ D.U) b)) j ∈
          Set.range (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ D.U))) := by
  have hWU := weakChart_inf_U D c
  let := MMP.Mori.sectionAlgebra f c.W
  let := MMP.Mori.sectionAlgebra f ((c.W : V.Opens) ⊓ D.U)
  let : Algebra Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ D.U) :=
    (V.presheaf.map (homOfLE (inf_le_left : (c.W : V.Opens) ⊓ D.U ≤ c.W)).op).hom.toAlgebra
  have : IsScalarTower k Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ D.U) :=
    MMP.Flips.ResolutionInputs.isScalarTower_section_res f inf_le_left
  have : IsLocalization.Away (∏ i : Fin c.r, c.t (Fin.castLE c.hr i))
      Γ(V, (c.W : V.Opens) ⊓ D.U) :=
    MMP.DeRham.isLocalization_away_of_eq_basicOpen _ hWU inf_le_left
  have : Algebra.FormallyEtale Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ D.U) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)))
  obtain ⟨bB, hbB⟩ := WeakChart.exists_basis_k D c
  let bL : Module.Basis (Fin n) Γ(V, (c.W : V.Opens) ⊓ D.U)
      Ω[Γ(V, (c.W : V.Opens) ⊓ D.U)⁄k] :=
    (Algebra.TensorProduct.basis Γ(V, (c.W : V.Opens) ⊓ D.U) bB).map
      (tensorKaehlerEquivOfFormallyEtale k Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ D.U))
  have hD' : ∀ b, KaehlerDifferential.D k Γ(V, (c.W : V.Opens) ⊓ D.U)
      (algebraMap Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ D.U) b) =
      tensorKaehlerEquivOfFormallyEtale k Γ(V, c.W) Γ(V, (c.W : V.Opens) ⊓ D.U)
        ((1 : Γ(V, (c.W : V.Opens) ⊓ D.U)) ⊗ₜ KaehlerDifferential.D k Γ(V, c.W) b) := by
    intro b
    rw [tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul,
      KaehlerDifferential.map_D]
  refine ⟨bL, fun i => ?_, fun b j => ?_⟩
  · rw [hD', ← hbB]
    simp only [bL, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
  · refine ⟨bB.repr (KaehlerDifferential.D k Γ(V, c.W) b) j, ?_⟩
    rw [hD']
    simp only [bL, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

/-- **A chart adapted to the divisor**: a weak chart with generators `tⱼ` of the components,
each either a unit or one of the boundary coordinates, the boundary coordinates being the `tⱼ`
indexed by an injection `eB`. -/
private structure EulerChart where
  /-- the weak chart -/
  c : WeakChart f n (((⨅ j, D.J j).support : Set V))
  /-- generators of the components -/
  t : ι → Γ(V, c.W)
  ht : ∀ j, (D.J j).ideal c.W = Ideal.span {t j}
  /-- the components through the boundary coordinates -/
  eB : Fin c.r → ι
  heB : Function.Injective eB
  hteB : ∀ i, t (eB i) = c.t (Fin.castLE c.hr i)
  hunit : ∀ j, j ∉ Set.range eB → IsUnit (t j)

private theorem exists_eulerChart {O : V.Opens} {x : V} (hx : x ∈ O) :
    ∃ C : EulerChart D, (C.c.W : V.Opens) ≤ O ∧ x ∈ (C.c.W : V.Opens) := by
  obtain ⟨c, t, hcO, hxc, ht, eB, heB, hteB, hunit, -⟩ :=
    exists_weakChart_of_snc_injective f D.J D.hJ hx
  exact ⟨⟨c, t, ht, eB, heB, hteB, hunit⟩, hcO, hxc⟩

variable {D}

/-- The product of the boundary coordinates of a chart. -/
private noncomputable abbrev EulerChart.h (C : EulerChart D) : Γ(V, C.c.W) :=
  ∏ i : Fin C.c.r, C.c.t (Fin.castLE C.c.hr i)

/-- The product of the generators is the product of the boundary coordinates up to a unit. -/
private theorem EulerChart.exists_prod_t (C : EulerChart D) :
    ∃ v : Γ(V, C.c.W), IsUnit v ∧ ∏ j, C.t j = v * C.h := by
  classical
  set S := Finset.univ.image C.eB
  refine ⟨∏ j ∈ Sᶜ, C.t j, Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb)
    isUnit_one fun j hj => C.hunit j ?_, ?_⟩
  · rintro ⟨i, rfl⟩
    exact (Finset.mem_compl.1 hj) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  · rw [← Finset.prod_compl_mul_prod S, Finset.prod_image fun i _ i' _ h => C.heB h]
    exact congrArg _ (Finset.prod_congr rfl fun i _ => C.hteB i)

private theorem EulerChart.inf_U (C : EulerChart D) :
    (C.c.W : V.Opens) ⊓ D.U = V.basicOpen (∏ j, C.t j) := by
  obtain ⟨v, hv, hprod⟩ := C.exists_prod_t
  rw [weakChart_inf_U D C.c, hprod, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hv]
  exact (inf_eq_right.2 (V.basicOpen_le _)).symm

private theorem EulerChart.isAffineOpen_inf_U (C : EulerChart D) :
    IsAffineOpen ((C.c.W : V.Opens) ⊓ D.U) :=
  MMP.DeRham.isAffineOpen_of_eq_basicOpen _ C.inf_U

/-- The components through a point of a chart are independent there. -/
private theorem EulerChart.linearIndependent (C : EulerChart D) :
    letI := MMP.Mori.sectionAlgebra f C.c.W
    ∀ 𝔭 : PrimeSpectrum Γ(V, C.c.W),
      LinearIndependent 𝔭.asIdeal.ResidueField
        (fun j : {j : ι // C.t j ∈ 𝔭.asIdeal} ↦
          ((1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[Γ(V, C.c.W)] KaehlerDifferential.D k Γ(V, C.c.W) (C.t j) :
            𝔭.asIdeal.ResidueField ⊗[Γ(V, C.c.W)] Ω[Γ(V, C.c.W)⁄k])) := by
  letI := MMP.Mori.sectionAlgebra f C.c.W
  intro 𝔭
  obtain ⟨bB, hbB⟩ := WeakChart.exists_basis_k D C.c
  let bK := Algebra.TensorProduct.basis 𝔭.asIdeal.ResidueField bB
  have hmem : ∀ j : {j : ι // C.t j ∈ 𝔭.asIdeal}, j.1 ∈ Set.range C.eB := fun j => by
    by_contra h
    exact 𝔭.2.ne_top ((Ideal.eq_top_of_isUnit_mem _ j.2 (C.hunit j.1 h)))
  choose g hg using hmem
  have hinj : Function.Injective fun j => Fin.castLE C.c.hr (g j) := fun a b h => by
    have h' := Fin.castLE_injective C.c.hr h
    exact Subtype.ext ((hg a).symm.trans ((congrArg C.eB h').trans (hg b)))
  convert bK.linearIndependent.comp _ hinj using 1
  funext j
  simp only [Function.comp_apply, bK, Algebra.TensorProduct.basis_apply, hbB]
  rw [← C.hteB, hg j]

set_option maxRecDepth 20000 in
/-- The algebraic forms of the sections of `K q` over a chart, as forms of the ring of functions
on the complement of the divisor in the chart. -/
private noncomputable def EulerChart.twistedFacts_α (C : EulerChart D) :
    letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
    ∀ q : ℕ, Γ(D.K q, C.c.W) →
      ⋀[Γ(V, (C.c.W : V.Opens) ⊓ D.U)]^q (Ω[Γ(V, (C.c.W : V.Opens) ⊓ D.U)⁄k]) :=
  letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
  fun q s => formsAlgEquiv f q ⟨_, C.isAffineOpen_inf_U⟩ (D.e q C.c.W s)

set_option maxRecDepth 20000 in
/-- The algebraic form of a section of `K q` over a chart determines it. -/
private theorem EulerChart.twistedFacts_inj (C : EulerChart D) :
    letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
    ∀ q, Function.Injective (C.twistedFacts_α q) := by
  letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
  intro q a b hab
  exact D.he_inj q _ ((formsAlgEquiv f q _).injective hab)

set_option maxRecDepth 20000 in
/-- The algebraic form of a multiple of a section of `K q` over a chart. -/
private theorem EulerChart.twistedFacts_smulα (C : EulerChart D) :
    letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
    letI : Algebra Γ(V, C.c.W) Γ(V, (C.c.W : V.Opens) ⊓ D.U) :=
      (V.presheaf.map (homOfLE (inf_le_left : (C.c.W : V.Opens) ⊓ D.U ≤ C.c.W)).op).hom.toAlgebra
    ∀ (q : ℕ) (b : Γ(V, C.c.W)) (s : Γ(D.K q, C.c.W)),
      C.twistedFacts_α q (b • s) =
        algebraMap Γ(V, C.c.W) Γ(V, (C.c.W : V.Opens) ⊓ D.U) b • C.twistedFacts_α q s := by
  letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
  letI : Algebra Γ(V, C.c.W) Γ(V, (C.c.W : V.Opens) ⊓ D.U) :=
    (V.presheaf.map (homOfLE (inf_le_left : (C.c.W : V.Opens) ⊓ D.U ≤ C.c.W)).op).hom.toAlgebra
  intro q b s
  have e := formsAlgEquiv_e_smul D q ⟨_, C.isAffineOpen_inf_U⟩ (le_refl _) b s
  simp only [MMP.DeRham.presheaf_map_id] at e
  exact e

set_option maxRecDepth 20000 in
/-- The algebraic form of the differential of a section of `K q` over a chart. -/
private theorem EulerChart.twistedFacts_dα (C : EulerChart D) :
    letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
    ∀ (q : ℕ) (s : Γ(D.K q, C.c.W)),
      C.twistedFacts_α (q + 1) ((D.d q).app C.c.W s) =
        KaehlerDifferential.deRhamDifferential (A := k) q (C.twistedFacts_α q s) := by
  letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
  intro q s
  exact D.formsAlgEquiv_e_d q C.isAffineOpen_inf_U s

set_option maxRecDepth 20000 in
/-- The algebraic form of the zero section. -/
private theorem EulerChart.twistedFacts_zeroα (C : EulerChart D) :
    letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
    ∀ q, C.twistedFacts_α q 0 = 0 := by
  letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
  intro q
  exact (congrArg (formsAlgEquiv f q ⟨_, C.isAffineOpen_inf_U⟩) (D.e q C.c.W).map_zero).trans
    (LinearEquiv.map_zero _)

set_option maxRecDepth 20000 in
/-- The algebraic form of a difference of sections. -/
private theorem EulerChart.twistedFacts_subα (C : EulerChart D) :
    letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
    ∀ q (a b : Γ(D.K q, C.c.W)),
      C.twistedFacts_α q (a - b) = C.twistedFacts_α q a - C.twistedFacts_α q b := by
  letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
  intro q a b
  exact (congrArg (formsAlgEquiv f q ⟨_, C.isAffineOpen_inf_U⟩) ((D.e q C.c.W).map_sub a b)).trans
    (map_sub _ _ _)

set_option maxRecDepth 20000 in
/-- The algebraic form of a section of `K q` over a chart has logarithmic poles along the
boundary coordinates. -/
private theorem EulerChart.twistedFacts_log (C : EulerChart D) :
    letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
    letI : Algebra Γ(V, C.c.W) Γ(V, (C.c.W : V.Opens) ⊓ D.U) :=
      (V.presheaf.map (homOfLE (inf_le_left : (C.c.W : V.Opens) ⊓ D.U ≤ C.c.W)).op).hom.toAlgebra
    ∀ (q : ℕ) (s : Γ(D.K q, C.c.W)),
      ((C.twistedFacts_α q s :
          ⋀[Γ(V, (C.c.W : V.Opens) ⊓ D.U)]^q (Ω[Γ(V, (C.c.W : V.Opens) ⊓ D.U)⁄k])) :
        ExteriorAlgebra Γ(V, (C.c.W : V.Opens) ⊓ D.U) (Ω[Γ(V, (C.c.W : V.Opens) ⊓ D.U)⁄k])) ∈
        MMP.DeRham.logForms k Γ(V, (C.c.W : V.Opens) ⊓ D.U)
          (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) q := by
  letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
  letI : Algebra Γ(V, C.c.W) Γ(V, (C.c.W : V.Opens) ⊓ D.U) :=
    (V.presheaf.map (homOfLE (inf_le_left : (C.c.W : V.Opens) ⊓ D.U ≤ C.c.W)).op).hom.toAlgebra
  intro q s
  have h1 := (D.mem_range_e_iff_mem_logForms q C.c.W C.t C.ht C.inf_U C.linearIndependent
    (D.e q C.c.W s)).1 ⟨s, rfl⟩
  refine @MMP.DeRham.logForms_le_logForms k Γ(V, C.c.W) Γ(V, C.c.W)
    Γ(V, (C.c.W : V.Opens) ⊓ D.U) _ _ _ _ _ _ (Algebra.id _) _ _ _ _ C.t
    (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) (fun j => ?_) q _ h1
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  by_cases hj : j ∈ Set.range C.eB
  · obtain ⟨k', rfl⟩ := hj
    exact Or.inr ⟨k', (C.hteB k').symm⟩
  · exact Or.inl (C.hunit j hj)

set_option maxRecDepth 20000 in
/-- A form with logarithmic poles along the boundary coordinates is the algebraic form of a
section of `K q` over a chart. -/
private theorem EulerChart.twistedFacts_range (C : EulerChart D) :
    letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
    letI : Algebra Γ(V, C.c.W) Γ(V, (C.c.W : V.Opens) ⊓ D.U) :=
      (V.presheaf.map (homOfLE (inf_le_left : (C.c.W : V.Opens) ⊓ D.U ≤ C.c.W)).op).hom.toAlgebra
    ∀ (q : ℕ) (y : ⋀[Γ(V, (C.c.W : V.Opens) ⊓ D.U)]^q (Ω[Γ(V, (C.c.W : V.Opens) ⊓ D.U)⁄k])),
      (y : ExteriorAlgebra Γ(V, (C.c.W : V.Opens) ⊓ D.U) (Ω[Γ(V, (C.c.W : V.Opens) ⊓ D.U)⁄k])) ∈
        MMP.DeRham.logForms k Γ(V, (C.c.W : V.Opens) ⊓ D.U)
          (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) q →
      ∃ s, C.twistedFacts_α q s = y := by
  letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
  letI : Algebra Γ(V, C.c.W) Γ(V, (C.c.W : V.Opens) ⊓ D.U) :=
    (V.presheaf.map (homOfLE (inf_le_left : (C.c.W : V.Opens) ⊓ D.U ≤ C.c.W)).op).hom.toAlgebra
  intro q y hy
  have hy' := MMP.DeRham.logForms_mono (u := (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)))
    (u' := C.t) (fun k' => ⟨C.eB k', C.hteB k'⟩) q hy
  obtain ⟨s, hs⟩ := (D.mem_range_e_iff_mem_logForms q C.c.W C.t C.ht C.inf_U C.linearIndependent
    ((formsAlgEquiv f q ⟨_, C.isAffineOpen_inf_U⟩).symm y)).2
      (by rw [LinearEquiv.apply_symm_apply]; exact hy')
  exact ⟨s, (congrArg (formsAlgEquiv f q ⟨_, C.isAffineOpen_inf_U⟩) hs).trans
    (LinearEquiv.apply_symm_apply _ _)⟩

set_option maxRecDepth 20000 in
/-- The boundary coordinates of a chart are units off the divisor. -/
private theorem EulerChart.twistedFacts_unit (C : EulerChart D) :
    letI : Algebra Γ(V, C.c.W) Γ(V, (C.c.W : V.Opens) ⊓ D.U) :=
      (V.presheaf.map (homOfLE (inf_le_left : (C.c.W : V.Opens) ⊓ D.U ≤ C.c.W)).op).hom.toAlgebra
    ∀ m, IsUnit (algebraMap Γ(V, C.c.W) Γ(V, (C.c.W : V.Opens) ⊓ D.U)
      (C.c.t (Fin.castLE C.c.hr m))) := by
  letI := MMP.Mori.sectionAlgebra f C.c.W
  letI := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U)
  letI : Algebra Γ(V, C.c.W) Γ(V, (C.c.W : V.Opens) ⊓ D.U) :=
    (V.presheaf.map (homOfLE (inf_le_left : (C.c.W : V.Opens) ⊓ D.U ≤ C.c.W)).op).hom.toAlgebra
  haveI : IsLocalization.Away C.h Γ(V, (C.c.W : V.Opens) ⊓ D.U) :=
    MMP.DeRham.isLocalization_away_of_eq_basicOpen _ (weakChart_inf_U D C.c) inf_le_left
  intro m
  exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem
    (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i))
    (Finset.mem_univ m))) (IsLocalization.Away.algebraMap_isUnit C.h)

set_option maxRecDepth 20000 in
/-- `d(h Ω^q(log S)) ⊆ h Ω^{q+1}(log S)` on a chart, for any injective algebraic model `α` of the
sections of `K` with logarithmic image. -/
private theorem EulerChart.twistedFacts_d (C : EulerChart D) {L : Type} [CommRing L]
    [iA : Algebra k L] [iB : Algebra Γ(V, C.c.W) L] (α : ∀ q : ℕ, Γ(D.K q, C.c.W) → ⋀[L]^q (Ω[L⁄k]))
    (hα_inj : ∀ q, Function.Injective (α q))
    (hα_smul : ∀ (q : ℕ) (b : Γ(V, C.c.W)) (s : Γ(D.K q, C.c.W)),
      α q (b • s) = algebraMap Γ(V, C.c.W) L b • α q s)
    (hα_d : ∀ (q : ℕ) (s : Γ(D.K q, C.c.W)),
      α (q + 1) ((D.d q).app C.c.W s) = KaehlerDifferential.deRhamDifferential (A := k) q (α q s))
    (hlog : ∀ (q : ℕ) (s : Γ(D.K q, C.c.W)),
      ((α q s : ⋀[L]^q (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
        MMP.DeRham.logForms k L (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) q)
    (hrange : ∀ (q : ℕ) (y : ⋀[L]^q (Ω[L⁄k])),
      (y : ExteriorAlgebra L (Ω[L⁄k])) ∈
        MMP.DeRham.logForms k L (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) q →
      ∃ s, α q s = y)
    (hu : ∀ m, IsUnit (algebraMap Γ(V, C.c.W) L (C.c.t (Fin.castLE C.c.hr m)))) :
    ∀ (q : ℕ) (s₀ : Γ(D.K q, C.c.W)), ∃ s₁ : Γ(D.K (q + 1), C.c.W),
      (show Γ(D.K (q + 1), C.c.W) from (D.d q).app C.c.W (C.h • s₀ : Γ(D.K q, C.c.W))) =
        C.h • s₁ := by
  intro q s₀
  obtain ⟨y₁, hy₁, hd⟩ := deRhamDifferential_mem_twisted_logForms (A := k)
    (u := fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) hu (α q s₀) (hlog q s₀)
  obtain ⟨s₁, hs₁⟩ := hrange (q + 1) y₁ hy₁
  refine ⟨s₁, hα_inj (q + 1) ?_⟩
  exact (hα_d q (C.h • s₀)).trans
    ((congrArg (KaehlerDifferential.deRhamDifferential (A := k) q) (hα_smul q C.h s₀)).trans
      (hd.trans ((congrArg (fun y => algebraMap Γ(V, C.c.W) L C.h • y) hs₁).symm.trans
        (hα_smul (q + 1) C.h s₁).symm)))

set_option maxRecDepth 20000 in
/-- A closed function of `h 𝒪(log S)` on a chart lies in `h^p 𝒪(log S)`. -/
private theorem EulerChart.twistedFacts_zero (C : EulerChart D) {L : Type} [CommRing L]
    [iA : Algebra k L] [iB : Algebra Γ(V, C.c.W) L] (α : ∀ q : ℕ, Γ(D.K q, C.c.W) → ⋀[L]^q (Ω[L⁄k]))
    (hα_inj : ∀ q, Function.Injective (α q))
    (hα_smul : ∀ (q : ℕ) (b : Γ(V, C.c.W)) (s : Γ(D.K q, C.c.W)),
      α q (b • s) = algebraMap Γ(V, C.c.W) L b • α q s)
    (hα_d : ∀ (q : ℕ) (s : Γ(D.K q, C.c.W)),
      α (q + 1) ((D.d q).app C.c.W s) = KaehlerDifferential.deRhamDifferential (A := k) q (α q s))
    (hlog : ∀ (q : ℕ) (s : Γ(D.K q, C.c.W)),
      ((α q s : ⋀[L]^q (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
        MMP.DeRham.logForms k L (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) q)
    (hrange : ∀ (q : ℕ) (y : ⋀[L]^q (Ω[L⁄k])),
      (y : ExteriorAlgebra L (Ω[L⁄k])) ∈
        MMP.DeRham.logForms k L (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) q →
      ∃ s, α q s = y)
    (hu : ∀ m, IsUnit (algebraMap Γ(V, C.c.W) L (C.c.t (Fin.castLE C.c.hr m))))
    (bL : Module.Basis (Fin n) L (Ω[L⁄k]))
    (hb : ∀ i, bL i = KaehlerDifferential.D k L (algebraMap Γ(V, C.c.W) L (C.c.t i)))
    (hcoord : ∀ (b : Γ(V, C.c.W)) j, bL.repr (KaehlerDifferential.D k L
      (algebraMap Γ(V, C.c.W) L b)) j ∈ Set.range (algebraMap Γ(V, C.c.W) L))
    (hpL : ((p : ℕ) : L) = 0)
    (hα0 : ∀ q, α q 0 = 0) :
    ∀ z₀ : Γ(D.K 0, C.c.W),
      (show Γ(D.K 1, C.c.W) from (D.d 0).app C.c.W (C.h • z₀ : Γ(D.K 0, C.c.W))) = 0 →
      ∃ w : Γ(D.K 0, C.c.W), (C.h • z₀ : Γ(D.K 0, C.c.W)) = C.h ^ p • w := by
  classical
  have hPh : ∏ j ∈ Finset.univ.map (Fin.castLEEmb C.c.hr), C.c.t j = C.h := Finset.prod_map _ _ _
  have hP : ∀ j ∈ Finset.univ.map (Fin.castLEEmb C.c.hr),
      IsUnit (algebraMap Γ(V, C.c.W) L (C.c.t j)) := by
    intro j hj
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.1 hj
    exact hu m
  have hu₁ : ∀ m, ∃ j ∈ Finset.univ.map (Fin.castLEEmb C.c.hr),
      C.c.t j = (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) m := fun m =>
    ⟨Fin.castLE C.c.hr m, Finset.mem_map_of_mem _ (Finset.mem_univ m), rfl⟩
  have hu₂ : ∀ j ∈ Finset.univ.map (Fin.castLEEmb C.c.hr),
      ∃ m, (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) m = C.c.t j := by
    intro j hj
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.1 hj
    exact ⟨m, rfl⟩
  have hTw : ∀ (a q : ℕ) (s₀ : Γ(D.K q, C.c.W)),
      IsTwistedLogForm k L C.c.t (Finset.univ.map (Fin.castLEEmb C.c.hr))
        (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) a q (α q (C.h ^ a • s₀)) :=
    fun a q s₀ => ⟨α q s₀, hlog q s₀, (hα_smul q (C.h ^ a) s₀).trans (by rw [map_pow, hPh])⟩
  have hTw' : ∀ (a q : ℕ) (y : ⋀[L]^q (Ω[L⁄k])),
      IsTwistedLogForm k L C.c.t (Finset.univ.map (Fin.castLEEmb C.c.hr))
        (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) a q y →
      ∃ s₀, α q (C.h ^ a • s₀) = y := by
    rintro a q y ⟨y₀, hy₀, rfl⟩
    obtain ⟨s₀, hs₀⟩ := hrange q y₀ hy₀
    exact ⟨s₀, (hα_smul q _ s₀).trans (by rw [map_pow, hPh, hs₀])⟩
  have hpow1 : ∀ q (s : Γ(D.K q, C.c.W)), C.h • s = C.h ^ 1 • s := fun q s => by rw [pow_one]
  intro z₀ hz
  have hz' : KaehlerDifferential.deRhamDifferential (A := k) 0 (α 0 (C.h ^ 1 • z₀)) = 0 :=
    (congrArg (fun t => KaehlerDifferential.deRhamDifferential (A := k) 0 (α 0 t))
      (hpow1 0 z₀)).symm.trans ((hα_d 0 (C.h • z₀)).symm.trans
        ((congrArg (α 1) hz).trans (hα0 1)))
  obtain ⟨w, hw⟩ := hTw' p 0 _ (IsTwistedLogForm.pow_of_closed_zero hb hP hcoord hu₁ hu₂ p hpL
    (hTw 1 0 z₀) hz')
  exact ⟨w, hα_inj 0 ((congrArg (α 0) (hpow1 0 z₀)).trans hw.symm)⟩

set_option maxRecDepth 20000 in
/-- A closed form of `h Ω^{i+1}(log S)` on a chart is, up to the differential of a form of
`h Ω^i(log S)`, a form of `h^p Ω^{i+1}(log S)`. -/
private theorem EulerChart.twistedFacts_succ (C : EulerChart D) {L : Type} [CommRing L]
    [iA : Algebra k L] [iB : Algebra Γ(V, C.c.W) L] (α : ∀ q : ℕ, Γ(D.K q, C.c.W) → ⋀[L]^q (Ω[L⁄k]))
    (hα_inj : ∀ q, Function.Injective (α q))
    (hα_smul : ∀ (q : ℕ) (b : Γ(V, C.c.W)) (s : Γ(D.K q, C.c.W)),
      α q (b • s) = algebraMap Γ(V, C.c.W) L b • α q s)
    (hα_d : ∀ (q : ℕ) (s : Γ(D.K q, C.c.W)),
      α (q + 1) ((D.d q).app C.c.W s) = KaehlerDifferential.deRhamDifferential (A := k) q (α q s))
    (hlog : ∀ (q : ℕ) (s : Γ(D.K q, C.c.W)),
      ((α q s : ⋀[L]^q (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
        MMP.DeRham.logForms k L (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) q)
    (hrange : ∀ (q : ℕ) (y : ⋀[L]^q (Ω[L⁄k])),
      (y : ExteriorAlgebra L (Ω[L⁄k])) ∈
        MMP.DeRham.logForms k L (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) q →
      ∃ s, α q s = y)
    (hu : ∀ m, IsUnit (algebraMap Γ(V, C.c.W) L (C.c.t (Fin.castLE C.c.hr m))))
    (bL : Module.Basis (Fin n) L (Ω[L⁄k]))
    (hb : ∀ i, bL i = KaehlerDifferential.D k L (algebraMap Γ(V, C.c.W) L (C.c.t i)))
    (hcoord : ∀ (b : Γ(V, C.c.W)) j, bL.repr (KaehlerDifferential.D k L
      (algebraMap Γ(V, C.c.W) L b)) j ∈ Set.range (algebraMap Γ(V, C.c.W) L))
    (hpL : ((p : ℕ) : L) = 0)
    (hα0 : ∀ q, α q 0 = 0) (hα_sub : ∀ q (a b : Γ(D.K q, C.c.W)), α q (a - b) = α q a - α q b) :
    ∀ (i : ℕ) (z₀ : Γ(D.K (i + 1), C.c.W)),
      (show Γ(D.K (i + 2), C.c.W) from
        (D.d (i + 1)).app C.c.W (C.h • z₀ : Γ(D.K (i + 1), C.c.W))) = 0 →
      ∃ (y₀ : Γ(D.K i, C.c.W)) (w : Γ(D.K (i + 1), C.c.W)),
        (C.h • z₀ : Γ(D.K (i + 1), C.c.W)) -
          (show Γ(D.K (i + 1), C.c.W) from (D.d i).app C.c.W (C.h • y₀ : Γ(D.K i, C.c.W))) =
            C.h ^ p • w := by
  classical
  have hPh : ∏ j ∈ Finset.univ.map (Fin.castLEEmb C.c.hr), C.c.t j = C.h := Finset.prod_map _ _ _
  have hP : ∀ j ∈ Finset.univ.map (Fin.castLEEmb C.c.hr),
      IsUnit (algebraMap Γ(V, C.c.W) L (C.c.t j)) := by
    intro j hj
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.1 hj
    exact hu m
  have hu₁ : ∀ m, ∃ j ∈ Finset.univ.map (Fin.castLEEmb C.c.hr),
      C.c.t j = (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) m := fun m =>
    ⟨Fin.castLE C.c.hr m, Finset.mem_map_of_mem _ (Finset.mem_univ m), rfl⟩
  have hu₂ : ∀ j ∈ Finset.univ.map (Fin.castLEEmb C.c.hr),
      ∃ m, (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) m = C.c.t j := by
    intro j hj
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.1 hj
    exact ⟨m, rfl⟩
  have hTw : ∀ (a q : ℕ) (s₀ : Γ(D.K q, C.c.W)),
      IsTwistedLogForm k L C.c.t (Finset.univ.map (Fin.castLEEmb C.c.hr))
        (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) a q (α q (C.h ^ a • s₀)) :=
    fun a q s₀ => ⟨α q s₀, hlog q s₀, (hα_smul q (C.h ^ a) s₀).trans (by rw [map_pow, hPh])⟩
  have hTw' : ∀ (a q : ℕ) (y : ⋀[L]^q (Ω[L⁄k])),
      IsTwistedLogForm k L C.c.t (Finset.univ.map (Fin.castLEEmb C.c.hr))
        (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) a q y →
      ∃ s₀, α q (C.h ^ a • s₀) = y := by
    rintro a q y ⟨y₀, hy₀, rfl⟩
    obtain ⟨s₀, hs₀⟩ := hrange q y₀ hy₀
    exact ⟨s₀, (hα_smul q _ s₀).trans (by rw [map_pow, hPh, hs₀])⟩
  have hpow1 : ∀ q (s : Γ(D.K q, C.c.W)), C.h • s = C.h ^ 1 • s := fun q s => by rw [pow_one]
  intro i z₀ hz
  have hz' : KaehlerDifferential.deRhamDifferential (A := k) (i + 1)
      (α (i + 1) (C.h ^ 1 • z₀)) = 0 :=
    (congrArg (fun t => KaehlerDifferential.deRhamDifferential (A := k) (i + 1) (α (i + 1) t))
      (hpow1 (i + 1) z₀)).symm.trans ((hα_d (i + 1) (C.h • z₀)).symm.trans
        ((congrArg (α (i + 2)) hz).trans (hα0 (i + 2))))
  obtain ⟨y, hy1, hyp⟩ := IsTwistedLogForm.exists_sub_deRhamDifferential hb hP hcoord hu₁ hu₂ p
    hpL (hTw 1 (i + 1) z₀) hz'
  obtain ⟨y₀, rfl⟩ := hTw' 1 i y hy1
  obtain ⟨w, hw⟩ := hTw' p (i + 1) _ hyp
  refine ⟨y₀, w, hα_inj (i + 1) ?_⟩
  exact (hα_sub (i + 1) _ _).trans ((congrArg₂ (· - ·) (congrArg (α (i + 1)) (hpow1 (i + 1) z₀))
    ((hα_d i (C.h • y₀)).trans
      (congrArg (fun t => KaehlerDifferential.deRhamDifferential (A := k) i (α i t))
        (hpow1 i y₀)))).trans hw.symm)

set_option maxRecDepth 20000 in
/-- A form of `h^p Ω^{i+1}(log S)` on a chart which is the differential of a form of
`h Ω^i(log S)` is the differential of a form of `h^p Ω^i(log S)`. -/
private theorem EulerChart.twistedFacts_exact (C : EulerChart D) {L : Type} [CommRing L]
    [iA : Algebra k L] [iB : Algebra Γ(V, C.c.W) L] (α : ∀ q : ℕ, Γ(D.K q, C.c.W) → ⋀[L]^q (Ω[L⁄k]))
    (hα_inj : ∀ q, Function.Injective (α q))
    (hα_smul : ∀ (q : ℕ) (b : Γ(V, C.c.W)) (s : Γ(D.K q, C.c.W)),
      α q (b • s) = algebraMap Γ(V, C.c.W) L b • α q s)
    (hα_d : ∀ (q : ℕ) (s : Γ(D.K q, C.c.W)),
      α (q + 1) ((D.d q).app C.c.W s) = KaehlerDifferential.deRhamDifferential (A := k) q (α q s))
    (hlog : ∀ (q : ℕ) (s : Γ(D.K q, C.c.W)),
      ((α q s : ⋀[L]^q (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
        MMP.DeRham.logForms k L (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) q)
    (hrange : ∀ (q : ℕ) (y : ⋀[L]^q (Ω[L⁄k])),
      (y : ExteriorAlgebra L (Ω[L⁄k])) ∈
        MMP.DeRham.logForms k L (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) q →
      ∃ s, α q s = y)
    (hu : ∀ m, IsUnit (algebraMap Γ(V, C.c.W) L (C.c.t (Fin.castLE C.c.hr m))))
    (bL : Module.Basis (Fin n) L (Ω[L⁄k]))
    (hb : ∀ i, bL i = KaehlerDifferential.D k L (algebraMap Γ(V, C.c.W) L (C.c.t i)))
    (hcoord : ∀ (b : Γ(V, C.c.W)) j, bL.repr (KaehlerDifferential.D k L
      (algebraMap Γ(V, C.c.W) L b)) j ∈ Set.range (algebraMap Γ(V, C.c.W) L))
    (hpL : ((p : ℕ) : L) = 0) :
    ∀ (i : ℕ) (y₀ : Γ(D.K i, C.c.W)) (w : Γ(D.K (i + 1), C.c.W)),
      (show Γ(D.K (i + 1), C.c.W) from (D.d i).app C.c.W (C.h • y₀ : Γ(D.K i, C.c.W))) =
        C.h ^ p • w →
      ∃ y' : Γ(D.K i, C.c.W),
        (show Γ(D.K (i + 1), C.c.W) from (D.d i).app C.c.W (C.h ^ p • y' : Γ(D.K i, C.c.W))) =
          (show Γ(D.K (i + 1), C.c.W) from (D.d i).app C.c.W (C.h • y₀ : Γ(D.K i, C.c.W))) := by
  classical
  have hPh : ∏ j ∈ Finset.univ.map (Fin.castLEEmb C.c.hr), C.c.t j = C.h := Finset.prod_map _ _ _
  have hP : ∀ j ∈ Finset.univ.map (Fin.castLEEmb C.c.hr),
      IsUnit (algebraMap Γ(V, C.c.W) L (C.c.t j)) := by
    intro j hj
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.1 hj
    exact hu m
  have hu₁ : ∀ m, ∃ j ∈ Finset.univ.map (Fin.castLEEmb C.c.hr),
      C.c.t j = (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) m := fun m =>
    ⟨Fin.castLE C.c.hr m, Finset.mem_map_of_mem _ (Finset.mem_univ m), rfl⟩
  have hu₂ : ∀ j ∈ Finset.univ.map (Fin.castLEEmb C.c.hr),
      ∃ m, (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) m = C.c.t j := by
    intro j hj
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.1 hj
    exact ⟨m, rfl⟩
  have hTw : ∀ (a q : ℕ) (s₀ : Γ(D.K q, C.c.W)),
      IsTwistedLogForm k L C.c.t (Finset.univ.map (Fin.castLEEmb C.c.hr))
        (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) a q (α q (C.h ^ a • s₀)) :=
    fun a q s₀ => ⟨α q s₀, hlog q s₀, (hα_smul q (C.h ^ a) s₀).trans (by rw [map_pow, hPh])⟩
  have hTw' : ∀ (a q : ℕ) (y : ⋀[L]^q (Ω[L⁄k])),
      IsTwistedLogForm k L C.c.t (Finset.univ.map (Fin.castLEEmb C.c.hr))
        (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) a q y →
      ∃ s₀, α q (C.h ^ a • s₀) = y := by
    rintro a q y ⟨y₀, hy₀, rfl⟩
    obtain ⟨s₀, hs₀⟩ := hrange q y₀ hy₀
    exact ⟨s₀, (hα_smul q _ s₀).trans (by rw [map_pow, hPh, hs₀])⟩
  have hpow1 : ∀ q (s : Γ(D.K q, C.c.W)), C.h • s = C.h ^ 1 • s := fun q s => by rw [pow_one]
  intro i y₀ w hyw
  have he : KaehlerDifferential.deRhamDifferential (A := k) i (α i (C.h ^ 1 • y₀)) =
      α (i + 1) (C.h ^ p • w) :=
    (congrArg (fun t => KaehlerDifferential.deRhamDifferential (A := k) i (α i t))
      (hpow1 i y₀)).symm.trans ((hα_d i (C.h • y₀)).symm.trans (congrArg (α (i + 1)) hyw))
  have hdy := (congrArg (IsTwistedLogForm k L C.c.t (Finset.univ.map (Fin.castLEEmb C.c.hr))
    (fun i : Fin C.c.r => C.c.t (Fin.castLE C.c.hr i)) p (i + 1)) he).mpr (hTw p (i + 1) w)
  obtain ⟨y', hy', hdy'⟩ := IsTwistedLogForm.exists_deRhamDifferential_eq hb hP hcoord hu₁ hu₂ p
    hpL (hTw 1 i y₀) hdy
  obtain ⟨y'₀, rfl⟩ := hTw' p i y' hy'
  refine ⟨y'₀, hα_inj (i + 1) ?_⟩
  exact (hα_d i (C.h ^ p • y'₀)).trans (hdy'.trans
    ((congrArg (fun t => KaehlerDifferential.deRhamDifferential (A := k) i (α i t))
      (hpow1 i y₀).symm).trans (hα_d i (C.h • y₀)).symm))

set_option maxRecDepth 20000 in
/-- **The twisted logarithmic forms on a chart**, `h = ∏ᵢ tᵢ` the product of the boundary
coordinates: `d(h Ω^q(log S)) ⊆ h Ω^{q+1}(log S)`; a closed form of `h Ω^q(log S)` is, up to the
differential of a form of `h Ω^{q-1}(log S)`, a form of `h^p Ω^q(log S)` (Euler homotopy); and a
form of `h^p Ω^{q+1}(log S)` which is the differential of a form of `h Ω^q(log S)` is the
differential of a form of `h^p Ω^q(log S)`. -/
private theorem EulerChart.twisted_facts (C : EulerChart D) :
    (∀ (q : ℕ) (s₀ : Γ(D.K q, C.c.W)), ∃ s₁ : Γ(D.K (q + 1), C.c.W),
      (show Γ(D.K (q + 1), C.c.W) from (D.d q).app C.c.W (C.h • s₀ : Γ(D.K q, C.c.W))) =
        C.h • s₁) ∧
    (∀ z₀ : Γ(D.K 0, C.c.W),
      (show Γ(D.K 1, C.c.W) from (D.d 0).app C.c.W (C.h • z₀ : Γ(D.K 0, C.c.W))) = 0 →
      ∃ w : Γ(D.K 0, C.c.W), (C.h • z₀ : Γ(D.K 0, C.c.W)) = C.h ^ p • w) ∧
    (∀ (i : ℕ) (z₀ : Γ(D.K (i + 1), C.c.W)),
      (show Γ(D.K (i + 2), C.c.W) from
        (D.d (i + 1)).app C.c.W (C.h • z₀ : Γ(D.K (i + 1), C.c.W))) = 0 →
      ∃ (y₀ : Γ(D.K i, C.c.W)) (w : Γ(D.K (i + 1), C.c.W)),
        (C.h • z₀ : Γ(D.K (i + 1), C.c.W)) -
          (show Γ(D.K (i + 1), C.c.W) from (D.d i).app C.c.W (C.h • y₀ : Γ(D.K i, C.c.W))) =
            C.h ^ p • w) ∧
    (∀ (i : ℕ) (y₀ : Γ(D.K i, C.c.W)) (w : Γ(D.K (i + 1), C.c.W)),
      (show Γ(D.K (i + 1), C.c.W) from (D.d i).app C.c.W (C.h • y₀ : Γ(D.K i, C.c.W))) =
        C.h ^ p • w →
      ∃ y' : Γ(D.K i, C.c.W),
        (show Γ(D.K (i + 1), C.c.W) from (D.d i).app C.c.W (C.h ^ p • y' : Γ(D.K i, C.c.W))) =
          (show Γ(D.K (i + 1), C.c.W) from (D.d i).app C.c.W (C.h • y₀ : Γ(D.K i, C.c.W)))) := by
  obtain ⟨bL, hb, hcoord⟩ := WeakChart.exists_basis_inf_U D C.c
  have hpL : ((p : ℕ) : Γ(V, (C.c.W : V.Opens) ⊓ D.U)) = 0 :=
    cast_eq_zero_of_isInCharacteristic D.hV _
  exact ⟨C.twistedFacts_d (iA := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U))
      (iB := (V.presheaf.map
        (homOfLE (inf_le_left : (C.c.W : V.Opens) ⊓ D.U ≤ C.c.W)).op).hom.toAlgebra)
      C.twistedFacts_α C.twistedFacts_inj C.twistedFacts_smulα C.twistedFacts_dα C.twistedFacts_log
      C.twistedFacts_range C.twistedFacts_unit,
    C.twistedFacts_zero (iA := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U))
      (iB := (V.presheaf.map
        (homOfLE (inf_le_left : (C.c.W : V.Opens) ⊓ D.U ≤ C.c.W)).op).hom.toAlgebra)
      C.twistedFacts_α C.twistedFacts_inj C.twistedFacts_smulα C.twistedFacts_dα C.twistedFacts_log
      C.twistedFacts_range C.twistedFacts_unit bL hb hcoord hpL C.twistedFacts_zeroα,
    C.twistedFacts_succ (iA := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U))
      (iB := (V.presheaf.map
        (homOfLE (inf_le_left : (C.c.W : V.Opens) ⊓ D.U ≤ C.c.W)).op).hom.toAlgebra)
      C.twistedFacts_α C.twistedFacts_inj C.twistedFacts_smulα C.twistedFacts_dα C.twistedFacts_log
      C.twistedFacts_range C.twistedFacts_unit bL hb hcoord hpL C.twistedFacts_zeroα
      C.twistedFacts_subα,
    C.twistedFacts_exact (iA := MMP.Mori.sectionAlgebra f ((C.c.W : V.Opens) ⊓ D.U))
      (iB := (V.presheaf.map
        (homOfLE (inf_le_left : (C.c.W : V.Opens) ⊓ D.U ≤ C.c.W)).op).hom.toAlgebra)
      C.twistedFacts_α C.twistedFacts_inj C.twistedFacts_smulα C.twistedFacts_dα C.twistedFacts_log
      C.twistedFacts_range C.twistedFacts_unit bL hb hcoord hpL⟩

/-- On a chart, the twisting ideal is generated by a power of the product of the boundary
coordinates. -/
private theorem EulerChart.exists_eq_pow_smul (C : EulerChart D) (m q : ℕ) {s : Γ(D.K q, C.c.W)}
    (hs : s ∈ divisorIdealPow D m C.c.W • (⊤ : Submodule Γ(V, C.c.W) Γ(D.K q, C.c.W))) :
    ∃ s₀ : Γ(D.K q, C.c.W), s = C.h ^ m • s₀ := by
  obtain ⟨v, -, hv⟩ := C.exists_prod_t
  obtain ⟨y, hy⟩ := exists_eq_pow_smul_of_mem D C.ht m hs
  refine ⟨v ^ m • y, ?_⟩
  rw [hy, hv, smul_smul, mul_pow, mul_comm]

private theorem EulerChart.pow_mem (C : EulerChart D) (m : ℕ) :
    C.h ^ m ∈ divisorIdealPow D m C.c.W := by
  obtain ⟨v, hv, hprod⟩ := C.exists_prod_t
  obtain ⟨v', hv'⟩ := hv.exists_left_inv
  have hh : C.h = v' * ∏ j, C.t j := by rw [hprod, ← mul_assoc, hv', one_mul]
  have hmem : ∏ j, C.t j ∈ ∏ j, (D.J j).ideal C.c.W :=
    Ideal.prod_mem_prod fun j _ => by rw [C.ht j]; exact Ideal.mem_span_singleton_self _
  rw [hh, mul_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hmem m)

/-- A multiple of `h^m` on a chart is a section of `I_S^m Ω^q(log S)`. -/
private theorem EulerChart.isLocallyIn_pow_smul (C : EulerChart D) (m q : ℕ)
    (s₀ : Γ(D.K q, C.c.W)) :
    IsLocallyIn (D.K q) (divisorIdealPow D m) (C.h ^ m • s₀ : Γ(D.K q, C.c.W)) := by
  intro x hx
  refine ⟨C.c.W, le_rfl, hx, ?_⟩
  rw [MMP.DeRham.presheaf_map_id]
  exact Submodule.smul_mem_smul (C.pow_mem m) trivial

variable (D) in
/-- **Twisted forms on a chart**: near every point, inside any open neighbourhood, a twisted
form is `h^m` times a form on a chart. -/
private theorem exists_eulerChart_pow_smul (m q : ℕ) {W : V.Opens} (s : Γ(twistedLog D m q, W))
    {x : V} (hx : x ∈ W) {O : V.Opens} (hxO : x ∈ O) :
    ∃ (C : EulerChart D) (hC : (C.c.W : V.Opens) ≤ W), (C.c.W : V.Opens) ≤ O ∧
      x ∈ (C.c.W : V.Opens) ∧
      (D.K q).presheaf.map (homOfLE hC).op s.1 ∈
        divisorIdealPow D m C.c.W • (⊤ : Submodule Γ(V, C.c.W) Γ(D.K q, C.c.W)) := by
  have hs : IsLocallyIn (D.K q) (divisorIdealPow D m) s.1 := s.2
  obtain ⟨W₁, h₁, hx₁, hle, hmem⟩ := hs.restrict (D.K q) _ (map_divisorIdealPow_le D m) hx hxO
  obtain ⟨C, hCW, hxC⟩ := exists_eulerChart D hx₁
  refine ⟨C, hCW.trans h₁, hCW.trans hle, hxC, ?_⟩
  have := map_mem_ideal_smul_top (D.K q) _ (map_divisorIdealPow_le D m) hCW hmem
  have e := MMP.DeRham.presheaf_map_map (F := D.K q) (homOfLE h₁) (homOfLE hCW)
    (homOfLE (hCW.trans h₁)) s.1
  convert this using 2
  exact e.symm

variable (D) in
/-- **The ideal of the divisor is the product of the component ideals**, locally: near every
point, inside any open neighbourhood, there is an affine open on which `∏ⱼ Jⱼ` is the ideal of
the support of a divisor `Δ` with complement `U`. -/
private theorem exists_affineOpens_divisorIdealPow_one_eq (Δ : MMP.Mori.Divisor V)
    (hΔ : D.U = (Δ.supp.compl : V.Opens)) {O : V.Opens} {x : V} (hx : x ∈ O) :
    ∃ W'' : V.affineOpens, x ∈ (W'' : V.Opens) ∧ (W'' : V.Opens) ≤ O ∧
      divisorIdealPow D 1 W'' = Δ.suppIdeal.ideal W'' := by
  classical
  obtain ⟨C, hCO, hxC⟩ := exists_eulerChart D hx
  have hZ : (((⨅ j, D.J j).support : TopologicalSpace.Closeds V) : Set V) = (Δ.supp : Set V) := by
    ext y
    have := SetLike.ext_iff.1 (D.hU.symm.trans hΔ) y
    exact not_iff_not.1 this
  obtain ⟨g, σ, r'', hr'', -, hxg, hσS, hunitk, -, -, -, hDW⟩ :=
    exists_snc_chart_explicit (A := CommRingCat.of k) f Δ (exists_mem_support_genericPoint_eq Δ)
      (C.c.ofEq hZ) x hxC
  let W'' : V.affineOpens := ⟨V.basicOpen g, C.c.W.2.basicOpen g⟩
  have hW''C : (W'' : V.Opens) ≤ C.c.W := V.basicOpen_le g
  refine ⟨W'', hxg, hW''C.trans hCO, ?_⟩
  set ρ := (V.presheaf.map (homOfLE hW''C).op).hom
  have ht : ∀ j, (D.J j).ideal W'' = Ideal.span {ρ (C.t j)} := fun j => by
    rw [← (D.J j).map_ideal hW''C, C.ht j, Ideal.map_span, Set.image_singleton]
    rfl
  rw [divisorIdealPow_eq_span D ht, pow_one]
  change _ = Ideal.span {∏ m, ρ (C.c.t (σ (Fin.castLE hr'' m)))} at hDW
  rw [hDW]
  obtain ⟨v, hv, hprod⟩ := C.exists_prod_t
  have hσS' : ∀ m : Fin r'', ∃ k : Fin C.c.r, σ (Fin.castLE hr'' m) = Fin.castLE C.c.hr k := hσS
  have hunitk' : ∀ k : Fin C.c.r, (∀ m : Fin r'', σ (Fin.castLE hr'' m) ≠ Fin.castLE C.c.hr k) →
      IsUnit (ρ (C.c.t (Fin.castLE C.c.hr k))) := hunitk
  choose κ hκ using hσS'
  have hκinj : Function.Injective κ := fun a b hab => by
    have h1 := (hκ a).trans ((congrArg (Fin.castLE C.c.hr) hab).trans (hκ b).symm)
    exact Fin.castLE_injective hr'' (σ.injective h1)
  have hsplit : ∏ k : Fin C.c.r, ρ (C.c.t (Fin.castLE C.c.hr k)) =
      (∏ m, ρ (C.c.t (σ (Fin.castLE hr'' m)))) *
        ∏ k ∈ (Finset.univ.image κ)ᶜ, ρ (C.c.t (Fin.castLE C.c.hr k)) := by
    rw [← Finset.prod_mul_prod_compl (Finset.univ.image κ), Finset.prod_image fun a _ b _ h =>
      hκinj h]
    exact congrArg (· * _) (Finset.prod_congr rfl fun m _ => by rw [hκ m])
  have hunit : IsUnit (∏ k ∈ (Finset.univ.image κ)ᶜ, ρ (C.c.t (Fin.castLE C.c.hr k))) :=
    Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one fun k hk => by
      refine hunitk' k fun m hm => ?_
      have : κ m = k := Fin.castLE_injective C.c.hr ((hκ m).symm.trans hm)
      exact (Finset.mem_compl.1 hk) (Finset.mem_image.2 ⟨m, Finset.mem_univ _, this⟩)
  rw [← map_prod, hprod, map_mul, Ideal.span_singleton_mul_left_unit (hv.map ρ), map_prod, hsplit,
    Ideal.span_singleton_mul_right_unit hunit]

variable (D)

/-- **The differential preserves `I_S Ω^•(log S)`.** -/
private theorem isLocallyIn_d_one (q : ℕ) {W : V.Opens} (s : Γ(twistedLog D 1 q, W)) :
    IsLocallyIn (D.K (q + 1)) (divisorIdealPow D 1) ((D.d q).app W s.1) := by
  intro x hx
  obtain ⟨C, hC, -, hxC, hmem⟩ := exists_eulerChart_pow_smul D 1 q s hx hx
  obtain ⟨s₀, hs₀⟩ := C.exists_eq_pow_smul 1 q hmem
  obtain ⟨s₁, hs₁⟩ := (C.twisted_facts).1 q s₀
  refine ⟨C.c.W, hC, hxC, ?_⟩
  have hnat := (app_presheaf_map (D.d q) (homOfLE hC) s.1).symm
  have key : ((D.K (q + 1)).presheaf.map (homOfLE hC).op ((D.d q).app W s.1) :
      Γ(D.K (q + 1), C.c.W)) = C.h ^ 1 • s₁ := by
    refine hnat.trans ?_
    have e1 := congrArg (fun t : Γ(D.K q, C.c.W) => (show Γ(D.K (q + 1), C.c.W) from
      (D.d q).app C.c.W t)) (hs₀.trans (by rw [pow_one] : C.h ^ 1 • s₀ = C.h • s₀))
    exact e1.trans (hs₁.trans (by rw [pow_one] : C.h • s₁ = C.h ^ 1 • s₁))
  rw [key]
  exact Submodule.smul_mem_smul (C.pow_mem 1) trivial

/-- The differential of `F_*(I_S Ω^•(log S))`. -/
private noncomputable def twistedD1 (q : ℕ) :
    (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (twistedLog D 1 q) ⟶
      (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (twistedLog D 1 (q + 1)) :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun s => ⟨(D.d q).app W.unop s.1, isLocallyIn_d_one D q s⟩
          map_zero' := Subtype.ext (map_zero _)
          map_add' := fun a b => Subtype.ext (map_add _ a.1 b.1) }
      naturality := fun W W' g => by
        ext s
        exact Subtype.ext (app_presheaf_map (D.d q) (homOfLE (leOfHom g.unop)) s.1) }
    fun W r s => Subtype.ext (Scheme.Modules.Hom.app_smul (U := W.unop) (D.d q) r s.1)⟩

private theorem twistedD1_comp (q : ℕ) : twistedD1 D q ≫ twistedD1 D (q + 1) = 0 := by
  ext W s
  exact Subtype.ext (congrArg (fun φ => φ.app W s.1) (D.hd q))

/-- The complex `F_*(I_S Ω^•(log S))`, indexed by `ℕ`. -/
private noncomputable abbrev twistedComplex1 : CochainComplex V.Modules ℕ :=
  CochainComplex.of (fun q => (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj
    (twistedLog D 1 q)) (twistedD1 D) (twistedD1_comp D)

private theorem isLocallyIn_one_of_pow {q : ℕ} {W : V.Opens} {s : Γ(D.K q, W)}
    (hs : IsLocallyIn (D.K q) (divisorIdealPow D p) s) :
    IsLocallyIn (D.K q) (divisorIdealPow D 1) s := by
  intro x hx
  obtain ⟨W', h, hx', hm⟩ := hs x hx
  refine ⟨W', h, hx', Submodule.smul_mono_left ?_ hm⟩
  exact Ideal.pow_le_pow_right (Fact.out : p.Prime).one_lt.le

/-- The inclusion `I_S^p Ω^q(log S) ⊆ I_S Ω^q(log S)`. -/
private noncomputable def twistedPowIncl (q : ℕ) : twistedLog D p q ⟶ twistedLog D 1 q :=
  ⟨PresheafOfModules.Submodule.homOfLE (N₁ := (twistedLogSubmodule D p q).toSubmodule)
    (N₂ := (twistedLogSubmodule D 1 q).toSubmodule) fun _ _ hs => isLocallyIn_one_of_pow D hs⟩

/-- The inclusion of complexes `F_*(I_S^p Ω^•(log S)) ⟶ F_*(I_S Ω^•(log S))`. -/
private noncomputable def twistedIncl1p : twistedComplex D ⟶ twistedComplex1 D :=
  CochainComplex.ofHom
    (fun q => (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (twistedPowIncl D q))
    (fun q => by
      have h1 := CochainComplex.of_d (fun q => (Scheme.Modules.pushforward
        (absoluteFrobenius V p D.hV)).obj (twistedLog D 1 q)) (twistedD1 D) q
      have h2 := CochainComplex.of_d (fun q => (Scheme.Modules.pushforward
        (absoluteFrobenius V p D.hV)).obj (twistedLog D p q)) (twistedD D) q
      have h3 : (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (twistedPowIncl D q) ≫
          twistedD1 D q = twistedD D q ≫
            (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map
              (twistedPowIncl D (q + 1)) := by
        ext W s
        exact Subtype.ext rfl
      exact (congrArg (_ ≫ ·) h1).trans (h3.trans (congrArg (· ≫ _) h2.symm)))

private theorem twistedComplex_d_succ_val (q : ℕ) {W : V.Opens}
    (y : Γ((twistedComplex D).X q, W)) :
    (show Γ(twistedLog D p (q + 1), W) from ((twistedComplex D).d q (q + 1)).app W y).1 =
      (D.d q).app W (show Γ(twistedLog D p q, W) from y).1 :=
  congrArg (fun φ : (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj
      (twistedLog D p q) ⟶ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj
        (twistedLog D p (q + 1)) => (show Γ(twistedLog D p (q + 1), W) from φ.app W y).1)
    (CochainComplex.of_d (fun q => (Scheme.Modules.pushforward
      (absoluteFrobenius V p D.hV)).obj (twistedLog D p q)) (twistedD D) q)

private theorem twistedComplex1_d_succ_val (q : ℕ) {W : V.Opens}
    (y : Γ((twistedComplex1 D).X q, W)) :
    (show Γ(twistedLog D 1 (q + 1), W) from ((twistedComplex1 D).d q (q + 1)).app W y).1 =
      (D.d q).app W (show Γ(twistedLog D 1 q, W) from y).1 :=
  congrArg (fun φ : (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj
      (twistedLog D 1 q) ⟶ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj
        (twistedLog D 1 (q + 1)) => (show Γ(twistedLog D 1 (q + 1), W) from φ.app W y).1)
    (CochainComplex.of_d (fun q => (Scheme.Modules.pushforward
      (absoluteFrobenius V p D.hV)).obj (twistedLog D 1 q)) (twistedD1 D) q)

variable {D} in
private theorem EulerChart.isLocallyIn_smul (C : EulerChart D) (q : ℕ) (s₀ : Γ(D.K q, C.c.W)) :
    IsLocallyIn (D.K q) (divisorIdealPow D 1) (C.h • s₀ : Γ(D.K q, C.c.W)) := by
  have := C.isLocallyIn_pow_smul 1 q s₀
  rwa [pow_one] at this

/-- **The inclusion `F_*(I_S^p Ω^•(log S)) ⊆ F_*(I_S Ω^•(log S))` is a quasi-isomorphism**, by the
Euler homotopy on the charts adapted to the divisor. -/
private theorem quasiIso_twistedIncl1p : QuasiIso (twistedIncl1p D) := by
  refine ⟨fun q => ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  refine isIso_homologyMap_of_local _ q ?_ ?_
  · intro W z hz x hx
    let z' : Γ(twistedLog D 1 q, W) := z
    obtain ⟨C, hC, -, hxC, hmem⟩ := exists_eulerChart_pow_smul D 1 q z' hx hx
    obtain ⟨z₀, hz₀⟩ := C.exists_eq_pow_smul 1 q hmem
    rw [pow_one] at hz₀
    have hdz : (show Γ(D.K (q + 1), C.c.W) from
        (D.d q).app C.c.W (C.h • z₀ : Γ(D.K q, C.c.W))) = 0 := by
      have h1 : (show Γ(D.K (q + 1), W) from (D.d q).app W z'.1) = 0 :=
        (twistedComplex1_d_succ_val D q z).symm.trans (congrArg Subtype.val hz)
      have h2 := app_presheaf_map (D.d q) (homOfLE hC) z'.1
      have h3 : (D.K (q + 1)).presheaf.map (homOfLE hC).op
          (show Γ(D.K (q + 1), W) from (D.d q).app W z'.1) = 0 :=
        (congrArg ((D.K (q + 1)).presheaf.map (homOfLE hC).op) h1).trans (map_zero _)
      exact (congrArg (fun t : Γ(D.K q, C.c.W) => (show Γ(D.K (q + 1), C.c.W) from
        (D.d q).app C.c.W t)) hz₀.symm).trans (h2.trans h3)
    cases q with
    | zero =>
      obtain ⟨w₀, hw₀⟩ := C.twisted_facts.2.1 z₀ hdz
      refine ⟨C.c.W, hC, hxC,
        (show Γ(twistedLog D p 0, C.c.W) from ⟨C.h ^ p • w₀, C.isLocallyIn_pow_smul p 0 w₀⟩),
        0, ?_, ?_⟩
      · apply Subtype.ext
        refine (twistedComplex_d_succ_val D 0 _).trans ?_
        exact (congrArg (fun t : Γ(D.K 0, C.c.W) => (show Γ(D.K 1, C.c.W) from
          (D.d 0).app C.c.W t)) hw₀.symm).trans hdz
      · rw [map_zero, add_zero]
        apply Subtype.ext
        exact hz₀.trans hw₀
    | succ i =>
      rw [CochainComplex.prev_nat_succ]
      obtain ⟨y₀, w₀, hyw⟩ := C.twisted_facts.2.2.1 i z₀ hdz
      let yy : Γ(twistedLog D 1 i, C.c.W) := ⟨C.h • y₀, C.isLocallyIn_smul i y₀⟩
      refine ⟨C.c.W, hC, hxC,
        (show Γ(twistedLog D p (i + 1), C.c.W) from
          ⟨C.h ^ p • w₀, C.isLocallyIn_pow_smul p (i + 1) w₀⟩), yy, ?_, ?_⟩
      · apply Subtype.ext
        refine (twistedComplex_d_succ_val D (i + 1) _).trans ?_
        have hdd := congrArg (fun φ => φ.app (C.c.W : V.Opens)
          (C.h • y₀ : Γ(D.K i, C.c.W))) (D.hd i)
        simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app] at hdd
        have e1 : (show Γ(D.K (i + 1), C.c.W) from C.h ^ p • w₀) = C.h • z₀ -
            (show Γ(D.K (i + 1), C.c.W) from (D.d i).app C.c.W (C.h • y₀ : Γ(D.K i, C.c.W))) :=
          hyw.symm
        refine (congrArg (fun t : Γ(D.K (i + 1), C.c.W) => (show Γ(D.K (i + 2), C.c.W) from
          (D.d (i + 1)).app C.c.W t)) e1).trans ?_
        refine (map_sub _ _ _).trans ?_
        change (show Γ(D.K (i + 2), C.c.W) from (D.d (i + 1)).app C.c.W
          (C.h • z₀ : Γ(D.K (i + 1), C.c.W))) - _ = 0
        rw [hdz]
        exact (zero_sub _).trans (neg_eq_zero.2 hdd)
      · apply Subtype.ext
        have e1 := twistedComplex1_d_succ_val D i (W := C.c.W) yy
        have e2 : (D.K (i + 1)).presheaf.map (homOfLE hC).op z'.1 = C.h ^ p • w₀ +
            (show Γ(D.K (i + 1), C.c.W) from (D.d i).app C.c.W (C.h • y₀ : Γ(D.K i, C.c.W))) :=
          hz₀.trans (sub_eq_iff_eq_add.1 hyw)
        exact e2.trans (congrArg (C.h ^ p • w₀ + ·) e1.symm)
  · cases q with
    | zero =>
      intro W w y hw hφ x hx
      have hY : (twistedComplex1 D).d ((ComplexShape.up ℕ).prev 0) 0 = 0 :=
        (twistedComplex1 D).shape _ _ (by simp [ComplexShape.up_Rel])
      have hw0 : w = 0 := by
        apply Subtype.ext
        have h1 := congrArg Subtype.val (hφ.trans (by rw [hY]))
        exact h1
      refine ⟨W, le_rfl, hx, 0, ?_⟩
      rw [map_zero]
      exact (congrArg (((twistedComplex D).X 0).presheaf.map (homOfLE le_rfl).op) hw0).trans
        (map_zero _)
    | succ i =>
      rw [CochainComplex.prev_nat_succ]
      intro W w y hw hφ x hx
      let w' : Γ(twistedLog D p (i + 1), W) := w
      let y' : Γ(twistedLog D 1 i, W) := y
      obtain ⟨C₁, hC₁, -, hxC₁, hm₁⟩ := exists_eulerChart_pow_smul D p (i + 1) w' hx hx
      obtain ⟨C, hC, hCC₁, hxC, hmemy⟩ := exists_eulerChart_pow_smul D 1 i y' hx hxC₁
      have hmemw : (D.K (i + 1)).presheaf.map (homOfLE hC).op w'.1 ∈
          divisorIdealPow D p C.c.W • (⊤ : Submodule Γ(V, C.c.W) Γ(D.K (i + 1), C.c.W)) := by
        have := map_mem_ideal_smul_top (D.K (i + 1)) _ (map_divisorIdealPow_le D p) hCC₁ hm₁
        have e := MMP.DeRham.presheaf_map_map (F := D.K (i + 1)) (homOfLE hC₁) (homOfLE hCC₁)
          (homOfLE hC) w'.1
        convert this using 2
        exact e.symm
      obtain ⟨w₀, hw₀⟩ := C.exists_eq_pow_smul p (i + 1) hmemw
      obtain ⟨y₀, hy₀⟩ := C.exists_eq_pow_smul 1 i hmemy
      rw [pow_one] at hy₀
      have hφ' : w'.1 = (D.d i).app W y'.1 :=
        (congrArg Subtype.val hφ).trans (twistedComplex1_d_succ_val D i y)
      have hdy : (show Γ(D.K (i + 1), C.c.W) from
          (D.d i).app C.c.W (C.h • y₀ : Γ(D.K i, C.c.W))) = C.h ^ p • w₀ := by
        refine (congrArg (fun t : Γ(D.K i, C.c.W) => (show Γ(D.K (i + 1), C.c.W) from
          (D.d i).app C.c.W t)) hy₀.symm).trans ?_
        refine (app_presheaf_map (D.d i) (homOfLE hC) y'.1).trans ?_
        refine Eq.trans ?_ hw₀
        exact congrArg ((D.K (i + 1)).presheaf.map (homOfLE hC).op) hφ'.symm
      obtain ⟨y'₀, hy'₀⟩ := C.twisted_facts.2.2.2 i y₀ w₀ hdy
      refine ⟨C.c.W, hC, hxC, (show Γ(twistedLog D p i, C.c.W) from
        ⟨C.h ^ p • y'₀, C.isLocallyIn_pow_smul p i y'₀⟩), ?_⟩
      apply Subtype.ext
      refine Eq.trans ?_ (twistedComplex_d_succ_val D i _).symm
      exact hw₀.trans (hdy.symm.trans hy'₀.symm)

end EulerCharts

/-! ### The cone of `F_*(I_S Ω^•(log S)) ⟶ F_*Ω^•` -/

section Cone

private theorem twistedToRegular_app_val (q : ℕ) (W : V.Opens) (s : Γ(twistedLog D 1 q, W)) :
    (regularIncl D q).app W ((twistedToRegular D 1 q le_rfl).app W s) = s.1 :=
  congrArg (fun φ => φ.app W s) (twistedToRegular_comp_regularIncl D 1 q le_rfl)

private theorem twistedToRegular_comp_d (q : ℕ) :
    (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map
        (twistedToRegular D 1 q le_rfl) ≫ frobeniusDeRhamD f p D.hV q =
      twistedD1 D q ≫ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map
        (twistedToRegular D 1 (q + 1) le_rfl) := by
  ext W s
  apply regularIncl_app_injective D (q + 1) W
  have e1 := congrArg (fun φ => φ.app W ((twistedToRegular D 1 q le_rfl).app W s))
    (regularIncl_comp_d D q)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at e1
  refine e1.symm.trans ?_
  change (D.d q).app W ((regularIncl D q).app W ((twistedToRegular D 1 q le_rfl).app W s)) =
    (regularIncl D (q + 1)).app W ((twistedToRegular D 1 (q + 1) le_rfl).app W
      ((twistedD1 D q).app W s))
  exact (congrArg (fun t => (D.d q).app W t)
    (twistedToRegular_app_val D q W (show Γ(twistedLog D 1 q, W) from s))).trans
    (twistedToRegular_app_val D (q + 1) W
      (show Γ(twistedLog D 1 (q + 1), W) from (twistedD1 D q).app W s)).symm

/-- The inclusion of complexes `F_*(I_S Ω^•(log S)) ⟶ F_*Ω^•`. -/
private noncomputable def twistedToRegularComplex : twistedComplex1 D ⟶ (ordinaryData D).complex :=
  CochainComplex.ofHom
    (fun q => (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map
      (twistedToRegular D 1 q le_rfl))
    (fun q => by
      have h1 := CochainComplex.of_d (fun q ↦ (Scheme.Modules.pushforward
        (absoluteFrobenius V p (ordinaryData D).hV)).obj ((ordinaryData D).K q))
        (ordinaryData D).d q
      have h2 := CochainComplex.of_d (fun q => (Scheme.Modules.pushforward
        (absoluteFrobenius V p D.hV)).obj (twistedLog D 1 q)) (twistedD1 D) q
      exact (congrArg (_ ≫ ·) h1).trans ((twistedToRegular_comp_d D q).trans
        (congrArg (· ≫ _) h2.symm)))

private theorem extendMap_app_injective {K L : CochainComplex V.Modules ℕ} (φ : K ⟶ L)
    (h : ∀ (q : ℕ) (W : V.Opens), Function.Injective ((φ.f q).app W)) (a : ℤ) (W : V.Opens) :
    Function.Injective (((HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat).f a).app W) := by
  by_cases ha : 0 ≤ a
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    have key : Function.Injective
        (((K.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
          φ.f q ≫ (L.extendXIso ComplexShape.embeddingUpNat rfl).inv).app W) := by
      intro y y' hy
      simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hy
      exact app_injective_of_mono _ W (h q W
        (app_injective_of_mono (L.extendXIso ComplexShape.embeddingUpNat rfl).inv W hy))
    exact (HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat (i := q)
      (i' := (q : ℤ)) rfl) ▸ key
  · haveI := subsingleton_sections_of_isZero (HomologicalComplex.isZero_extend_X
      K ComplexShape.embeddingUpNat a (fun i hi => ha (hi ▸ by
        change (0 : ℤ) ≤ (i : ℤ); omega))) W
    exact fun _ _ _ => Subsingleton.elim _ _

private theorem twistedToRegular_app_injective (q : ℕ) (W : V.Opens) :
    Function.Injective ((twistedToRegular D 1 q le_rfl).app W) := fun a b hab =>
  Subtype.ext ((twistedToRegular_app_val D q W a).symm.trans
    ((congrArg _ hab).trans (twistedToRegular_app_val D q W b)))

/-- `F_*(I_S Ω^•(log S)) ⟶ F_*Ω^•`, extended to `ℤ`. -/
private noncomputable abbrev coneMap :
    (twistedComplex1 D).extend ComplexShape.embeddingUpNat ⟶ (ordinaryData D).complexZ :=
  HomologicalComplex.extendMap (twistedToRegularComplex D) ComplexShape.embeddingUpNat

private theorem mono_coneMap : Mono (coneMap D) :=
  HomologicalComplex.mono_of_mono_f _ fun a => mono_of_app_injective _
    (extendMap_app_injective _ (fun q W => twistedToRegular_app_injective D q W) a)

private theorem twistedIncl_eq_comp :
    twistedIncl1p D ≫ twistedToRegularComplex D ≫ regularComplexMap D = twistedIncl D := by
  ext q : 1
  simp only [HomologicalComplex.comp_f]
  change (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (twistedPowIncl D q) ≫
    (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (twistedToRegular D 1 q le_rfl) ≫
    (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (regularIncl D q) =
    (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (twistedLogSubmodule D p q).ι
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext W s
  exact twistedToRegular_app_val D q W _

private theorem twistedInclZ_eq_comp :
    HomologicalComplex.extendMap (twistedIncl1p D) ComplexShape.embeddingUpNat ≫ coneMap D ≫
      regularComplexMapZ D = twistedInclZ D := by
  simp only [coneMap, regularComplexMapZ, twistedInclZ, ← HomologicalComplex.extendMap_comp]
  rw [twistedIncl_eq_comp]

private theorem isZero_twistedComplex1_homology (m : ℤ)
    (hm : ∀ q : Fin (n + 1), ((q : ℕ) : ℤ) ≠ m) :
    IsZero (((twistedComplex1 D).extend ComplexShape.embeddingUpNat).homology m) := by
  refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
  change IsZero (((twistedComplex1 D).extend ComplexShape.embeddingUpNat).X m)
  by_cases h : 0 ≤ m
  · obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le h
    have hm' : n < m' := by
      by_contra hc
      exact hm ⟨m', by omega⟩ rfl
    refine IsZero.of_iso ?_ ((twistedComplex1 D).extendXIso ComplexShape.embeddingUpNat rfl)
    refine (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map_isZero ?_
    exact IsZero.of_mono (twistedLogSubmodule D 1 m').ι (D.isZero_K_of_lt hm')
  · exact HomologicalComplex.isZero_extend_X _ _ m (fun i hi => h (hi ▸ by
      change (0 : ℤ) ≤ (i : ℤ); omega))

end Cone

section Charts

variable {D}

/-- A chart of the lifted pair, forgetting the divisor. -/
private noncomputable def chartToOrdinary (C : D.FrobeniusLiftChart) :
    (ordinaryData D).FrobeniusLiftChart where
  𝒲 := C.𝒲
  isAffineOpen := C.isAffineOpen
  t := PEmpty.elim
  ideal_eq j := j.elim
  F := C.F
  isFrobeniusLift := C.isFrobeniusLift
  F_t j := j.elim

private theorem liftOpen_le_top : D.liftOpen D.U ≤ D.liftOpen ⊤ := fun _ ⟨y, _, hy⟩ => ⟨y, trivial, hy⟩

private theorem pieceAffine_le_ordinary (C : D.FrobeniusLiftChart) {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) :
    (D.pieceAffine Õ h.isAffineOpen_inf_U : V.Opens) ≤
      (ordinaryData D).pieceAffine Õ (show (chartToOrdinary C).IsBasic Õ from h).isAffineOpen_inf_U :=
  inf_le_inf_left _ le_top

/-- **The local Frobenius forms of the ordinary and the logarithmic data agree** on regular
forms: both are `F̃^*/p` for the same Frobenius lift. -/
private theorem frobeniusForm_toOrdinary (C : D.FrobeniusLiftChart) {Õ : D.𝒱.Opens} (h : C.IsBasic Õ)
    (ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ),
      (ordinaryData D).pieceAffine Õ (show (chartToOrdinary C).IsBasic Õ from h).isAffineOpen_inf_U)) :
    C.frobeniusForm h ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE (pieceAffine_le_ordinary C h)).op ω) =
      (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE (pieceAffine_le_ordinary C h)).op
          ((chartToOrdinary C).frobeniusForm (show (chartToOrdinary C).IsBasic Õ from h) ω) := by
  have h₀ : (chartToOrdinary C).IsBasic Õ := h
  have hA := pieceAffine_le_ordinary C h
  by_cases hL' : Nontrivial Γ(V, (D.pieceAffine Õ h.isAffineOpen_inf_U))
  swap
  · have : Subsingleton Γ(V, (D.pieceAffine Õ h.isAffineOpen_inf_U)) :=
      not_nontrivial_iff_subsingleton.1 hL'
    have := Module.subsingleton Γ(V, (D.pieceAffine Õ h.isAffineOpen_inf_U))
      Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), (D.pieceAffine Õ h.isAffineOpen_inf_U))
    exact Subsingleton.elim _ _
  have : Nontrivial Γ(V, ((ordinaryData D).pieceAffine Õ h₀.isAffineOpen_inf_U)) :=
    FrobeniusSplittingData.nontrivial_of_le D hA
  have := FrobeniusSplittingData.charP_of_nontrivial D (D.pieceAffine Õ h.isAffineOpen_inf_U)
  have := FrobeniusSplittingData.charP_of_nontrivial (ordinaryData D) ((ordinaryData D).pieceAffine Õ h₀.isAffineOpen_inf_U)
  let := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h.isAffineOpen_inf_U)
  let := MMP.Mori.sectionAlgebra f ((ordinaryData D).pieceAffine Õ h₀.isAffineOpen_inf_U)
  let : Algebra Γ(V, ((ordinaryData D).pieceAffine Õ h₀.isAffineOpen_inf_U))
      Γ(V, (D.pieceAffine Õ h.isAffineOpen_inf_U)) :=
    (V.presheaf.map (homOfLE hA).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f hA
  refine (formsAlgEquiv f 1 (D.pieceAffine Õ h.isAffineOpen_inf_U)).injective ?_
  rw [C.formsAlgEquiv_frobeniusForm h, formsAlgEquiv_restrict f 1 hA,
    formsAlgEquiv_restrict f 1 hA, (chartToOrdinary C).formsAlgEquiv_frobeniusForm h₀]
  have := frobeniusLiftForm_mapExteriorPower k
    (D.𝒱.presheaf.map (homOfLE (inf_le_inf_left Õ liftOpen_le_top)).op).hom
    ((ordinaryData D).isReductionModP_pieceReductionAt Õ h₀.isAffineOpen_inf_U h₀.inf_U.isAffineOpen)
    (D.isReductionModP_pieceReductionAt Õ h.isAffineOpen_inf_U h.inf_U.isAffineOpen)
    ((chartToOrdinary C).isFrobeniusLift_liftOn h₀.inf_U) (C.isFrobeniusLift_liftOn h.inf_U)
    (fun a => by
      change (D.𝒱.presheaf.map _ ≫ D.i.appLE _ _ _) a = (D.i.appLE _ _ _ ≫ V.presheaf.map _) a
      rw [Scheme.Hom.map_appLE]
      erw [Scheme.Hom.appLE_map])
    (fun a => C.liftOn_map_of_le (h₀.inf_U : C.IsBasic (Õ ⊓ D.liftOpen ⊤)) h.inf_U _ a)
    (formsAlgEquiv f 1 ((ordinaryData D).pieceAffine Õ h₀.isAffineOpen_inf_U) ω)
  convert this using 1
  rfl

/-- **The ordinary and logarithmic local splittings agree on regular forms**, on a piece of a
chart. -/
private theorem regularIncl_phiPiece (C : D.FrobeniusLiftChart) {Õ : D.𝒱.Opens} (h : C.IsBasic Õ)
    (t : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.i ⁻¹ᵁ Õ)) :
    (regularIncl D 1).app _ ((chartToOrdinary C).phiPiece (show (chartToOrdinary C).IsBasic Õ from h) t) =
      C.phiPiece h ((regularIncl D 1).app _ t) := by
  have h₀ : (chartToOrdinary C).IsBasic Õ := h
  refine D.he_inj 1 _ ?_
  have e1 := e_regularIncl_app D 1 _ ((chartToOrdinary C).phiPiece h₀ t)
  have e2 := (chartToOrdinary C).e_phiPiece h₀ t
  have e3 := C.e_phiPiece h ((regularIncl D 1).app _ t)
  have e4 := e_regularIncl_app D 1 _ t
  have e5 := frobeniusForm_toOrdinary C h ((ordinaryData D).e 1 _ t)
  have e6 : (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
      (homOfLE (inf_le_left : D.i ⁻¹ᵁ Õ ⊓ D.U ≤ D.i ⁻¹ᵁ Õ)).op t =
      (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE (pieceAffine_le_ordinary C h)).op ((ordinaryData D).e 1 _ t) :=
    (MMP.DeRham.presheaf_map_map _ _ _ _).symm
  refine e1.trans (Eq.trans ?_ e3.symm)
  refine Eq.trans ?_ (congrArg (C.frobeniusForm h) e4).symm
  refine Eq.trans ?_ (congrArg (C.frobeniusForm h) e6).symm
  refine Eq.trans ?_ e5.symm
  refine Eq.trans ?_ (congrArg _ e2)
  exact (MMP.DeRham.presheaf_map_map _ _ _ _).symm

/-- **The ordinary and logarithmic local splittings of a chart agree on regular forms.** -/
private theorem regularIncl_phi (C : D.FrobeniusLiftChart) {W : V.Opens}
    (hW : W ≤ D.i ⁻¹ᵁ C.𝒲) (s : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), W)) :
    (regularIncl D 1).app W ((chartToOrdinary C).phi hW s) =
      C.phi hW ((regularIncl D 1).app W s) := by
  refine MMP.DeRham.eq_of_locally_eq_sections _ _ fun x hx => ?_
  obtain ⟨Õ, hÕ, hxÕ, hÕW⟩ := C.exists_isBasic hx (hW hx)
  refine ⟨_, hÕW, hxÕ, ?_⟩
  have e1 := (regularSec_res D 1 hÕW ((chartToOrdinary C).phi hW s)).symm
  have e2 := (chartToOrdinary C).phi_spec hW s (show (chartToOrdinary C).IsBasic Õ from hÕ) hÕW
  have e3 := regularIncl_phiPiece C hÕ
    ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hÕW).op s)
  have e4 := regularSec_res D 1 hÕW s
  have e5 := C.phi_spec hW ((regularIncl D 1).app W s) hÕ hÕW
  refine e1.trans (Eq.trans ?_ e5.symm)
  refine (congrArg (regularSec D 1 _) e2).trans ?_
  refine e3.trans ?_
  exact congrArg (C.phiPiece hÕ) e4

/-- **The homotopies of the ordinary and the logarithmic data agree** on regular forms, on a
piece of two charts. -/
private theorem homotopyForm_toOrdinary (C₁ C₂ : D.FrobeniusLiftChart) {Õ : D.𝒱.Opens}
    (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ)
    (ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ),
      (ordinaryData D).pieceAffine Õ (show (chartToOrdinary C₁).IsBasic Õ from h₁).isAffineOpen_inf_U)) :
    FrobeniusSplittingData.homotopyForm C₁ C₂ h₁ h₂
        ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
          (homOfLE (pieceAffine_le_ordinary C₁ h₁)).op ω) =
      (f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map
        (homOfLE (pieceAffine_le_ordinary C₁ h₁)).op
          (FrobeniusSplittingData.homotopyForm (chartToOrdinary C₁) (chartToOrdinary C₂)
            (show (chartToOrdinary C₁).IsBasic Õ from h₁)
            (show (chartToOrdinary C₂).IsBasic Õ from h₂) ω) := by
  have h₁₀ : (chartToOrdinary C₁).IsBasic Õ := h₁
  have h₂₀ : (chartToOrdinary C₂).IsBasic Õ := h₂
  have hA := pieceAffine_le_ordinary C₁ h₁
  by_cases hL' : Nontrivial Γ(V, (D.pieceAffine Õ h₁.isAffineOpen_inf_U))
  swap
  · have : Subsingleton Γ(V, (D.pieceAffine Õ h₁.isAffineOpen_inf_U)) :=
      not_nontrivial_iff_subsingleton.1 hL'
    have := Module.subsingleton Γ(V, (D.pieceAffine Õ h₁.isAffineOpen_inf_U))
      Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), (D.pieceAffine Õ h₁.isAffineOpen_inf_U))
    exact Subsingleton.elim _ _
  have : Nontrivial Γ(V, ((ordinaryData D).pieceAffine Õ h₁₀.isAffineOpen_inf_U)) :=
    FrobeniusSplittingData.nontrivial_of_le D hA
  have := FrobeniusSplittingData.charP_of_nontrivial D (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  have := FrobeniusSplittingData.charP_of_nontrivial (ordinaryData D)
    ((ordinaryData D).pieceAffine Õ h₁₀.isAffineOpen_inf_U)
  let := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h₁.isAffineOpen_inf_U)
  let := MMP.Mori.sectionAlgebra f ((ordinaryData D).pieceAffine Õ h₁₀.isAffineOpen_inf_U)
  let : Algebra Γ(V, ((ordinaryData D).pieceAffine Õ h₁₀.isAffineOpen_inf_U))
      Γ(V, (D.pieceAffine Õ h₁.isAffineOpen_inf_U)) :=
    (V.presheaf.map (homOfLE hA).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f hA
  refine (formsAlgEquiv f 0 (D.pieceAffine Õ h₁.isAffineOpen_inf_U)).injective ?_
  have e0 := FrobeniusSplittingData.formsAlgEquiv_homotopyForm (chartToOrdinary C₁)
    (chartToOrdinary C₂) h₁₀ h₂₀ ω
  rw [FrobeniusSplittingData.formsAlgEquiv_homotopyForm, formsAlgEquiv_restrict f 1 hA,
    formsAlgEquiv_restrict f 0 hA, e0]
  have := frobeniusLiftHomotopy_mapExteriorPower k
    (D.𝒱.presheaf.map (homOfLE (inf_le_inf_left Õ liftOpen_le_top)).op).hom
    ((ordinaryData D).isReductionModP_pieceReductionAt Õ h₁₀.isAffineOpen_inf_U h₁₀.inf_U.isAffineOpen)
    (D.isReductionModP_pieceReductionAt Õ h₁.isAffineOpen_inf_U h₁.inf_U.isAffineOpen)
    ((chartToOrdinary C₁).isFrobeniusLift_liftOn h₁₀.inf_U)
    ((chartToOrdinary C₂).isFrobeniusLift_liftOn h₂₀.inf_U)
    (C₁.isFrobeniusLift_liftOn h₁.inf_U) (C₂.isFrobeniusLift_liftOn h₂.inf_U)
    (fun a => by
      change (D.𝒱.presheaf.map _ ≫ D.i.appLE _ _ _) a = (D.i.appLE _ _ _ ≫ V.presheaf.map _) a
      rw [Scheme.Hom.map_appLE]
      erw [Scheme.Hom.appLE_map])
    (fun a => C₁.liftOn_map_of_le (h₁₀.inf_U : C₁.IsBasic (Õ ⊓ D.liftOpen ⊤)) h₁.inf_U _ a)
    (fun a => C₂.liftOn_map_of_le (h₂₀.inf_U : C₂.IsBasic (Õ ⊓ D.liftOpen ⊤)) h₂.inf_U _ a)
    (formsAlgEquiv f 1 ((ordinaryData D).pieceAffine Õ h₁₀.isAffineOpen_inf_U) ω)
  convert this using 1
  rfl

/-- **The homotopies of the ordinary and logarithmic splittings agree on regular forms**, on a
piece of two charts. -/
private theorem regularIncl_etaPiece (C₁ C₂ : D.FrobeniusLiftChart) {Õ : D.𝒱.Opens}
    (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ)
    (t : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.i ⁻¹ᵁ Õ)) :
    (regularIncl D 0).app _ (FrobeniusSplittingData.etaPiece (chartToOrdinary C₁)
        (chartToOrdinary C₂) (show (chartToOrdinary C₁).IsBasic Õ from h₁)
        (show (chartToOrdinary C₂).IsBasic Õ from h₂) t) =
      FrobeniusSplittingData.etaPiece C₁ C₂ h₁ h₂ ((regularIncl D 1).app _ t) := by
  have h₁₀ : (chartToOrdinary C₁).IsBasic Õ := h₁
  have h₂₀ : (chartToOrdinary C₂).IsBasic Õ := h₂
  refine D.he_inj 0 _ ?_
  have e1 := e_regularIncl_app D 0 _
    (FrobeniusSplittingData.etaPiece (chartToOrdinary C₁) (chartToOrdinary C₂) h₁₀ h₂₀ t)
  have e2 := FrobeniusSplittingData.e_etaPiece (chartToOrdinary C₁) (chartToOrdinary C₂) h₁₀ h₂₀ t
  have e3 := FrobeniusSplittingData.e_etaPiece C₁ C₂ h₁ h₂ ((regularIncl D 1).app _ t)
  have e4 := e_regularIncl_app D 1 _ t
  have e5 := homotopyForm_toOrdinary C₁ C₂ h₁ h₂ ((ordinaryData D).e 1 _ t)
  have e6 : (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
      (homOfLE (inf_le_left : D.i ⁻¹ᵁ Õ ⊓ D.U ≤ D.i ⁻¹ᵁ Õ)).op t =
      (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE (pieceAffine_le_ordinary C₁ h₁)).op ((ordinaryData D).e 1 _ t) :=
    (MMP.DeRham.presheaf_map_map _ _ _ _).symm
  refine e1.trans (Eq.trans ?_ e3.symm)
  refine Eq.trans ?_ (congrArg (FrobeniusSplittingData.homotopyForm C₁ C₂ h₁ h₂) e4).symm
  refine Eq.trans ?_ (congrArg (FrobeniusSplittingData.homotopyForm C₁ C₂ h₁ h₂) e6).symm
  refine Eq.trans ?_ e5.symm
  refine Eq.trans ?_ (congrArg _ e2)
  exact (MMP.DeRham.presheaf_map_map _ _ _ _).symm

/-- **The glued homotopies of the ordinary and logarithmic splittings agree on regular forms.** -/
private theorem regularIncl_homotopy (C₁ C₂ : D.FrobeniusLiftChart) {W : V.Opens}
    (hW : W ≤ D.i ⁻¹ᵁ C₁.𝒲 ⊓ D.i ⁻¹ᵁ C₂.𝒲)
    (s : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), W)) :
    (regularIncl D 0).app W
        ((ordinaryData D).homotopy (chartToOrdinary C₁) (chartToOrdinary C₂) hW s) =
      D.homotopy C₁ C₂ hW ((regularIncl D 1).app W s) := by
  refine MMP.DeRham.eq_of_locally_eq_sections _ _ fun x hx => ?_
  obtain ⟨Õ, ⟨hÕ₁, hÕ₂⟩, hxÕ, hÕW⟩ :=
    FrobeniusSplittingData.FrobeniusLiftChart.exists_isBasic₂ C₁ C₂ hx (hW hx).1 (hW hx).2
  refine ⟨_, hÕW, hxÕ, ?_⟩
  have e1 := (regularSec_res D 0 hÕW
    ((ordinaryData D).homotopy (chartToOrdinary C₁) (chartToOrdinary C₂) hW s)).symm
  have e2 := (ordinaryData D).homotopy_spec (chartToOrdinary C₁) (chartToOrdinary C₂) hW s
    (show (chartToOrdinary C₁).IsBasic Õ from hÕ₁) (show (chartToOrdinary C₂).IsBasic Õ from hÕ₂)
    hÕW
  have e3 := regularIncl_etaPiece C₁ C₂ hÕ₁ hÕ₂
    ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hÕW).op s)
  have e4 := regularSec_res D 1 hÕW s
  have e5 := D.homotopy_spec C₁ C₂ hW ((regularIncl D 1).app W s) hÕ₁ hÕ₂ hÕW
  refine e1.trans (Eq.trans ?_ e5.symm)
  refine (congrArg (regularSec D 0 _) e2).trans ?_
  refine e3.trans ?_
  exact congrArg (FrobeniusSplittingData.etaPiece C₁ C₂ hÕ₁ hÕ₂) e4

section Splittings

variable (charts : V → D.FrobeniusLiftChart) (hcharts : ∀ x, D.i x ∈ (charts x).𝒲)

/-- The local Frobenius splittings of the logarithmic data from a family of charts. -/
private noncomputable abbrev logSplitting : D.LocalFrobeniusSplitting :=
  D.localFrobeniusSplittingOfCharts charts hcharts

/-- The local Frobenius splittings of the ordinary data from the same charts. -/
private noncomputable abbrev ordSplitting : (ordinaryData D).LocalFrobeniusSplitting :=
  (ordinaryData D).localFrobeniusSplittingOfCharts (fun x => chartToOrdinary (charts x)) hcharts

/-- **The degree-one cocycles of the ordinary and logarithmic splittings are compatible.** -/
private theorem oneCocycle_compat (p : ℤ) (m : ℕ) (h : p + m = (0 : ℤ) + 1) :
    regularIncl D 1 ≫ (logSplitting charts hcharts).oneCocycle.g p m h =
      (ordSplitting charts hcharts).oneCocycle.g p m h ≫
        ((cechBicomplexMap (U := (logSplitting charts hcharts).U) (regularComplexMapZ D)).f p).f m := by
  refine toCechCocycleData_g_comp (regularComplexMapZ D) (regularIncl D 1) _ _ (fun α => ?_)
    (fun α β => ?_) p m h
  · refine cechDiagramOpens_hom_ext fun W s => ?_
    change D.toComplexZ 1 (W ⊓ D.i ⁻¹ᵁ (charts α).𝒲) ((charts α).phi inf_le_right
        ((D.K 1).presheaf.map (homOfLE inf_le_left).op ((regularIncl D 1).app W s))) =
      ((regularComplexMapZ D).f ((1 : ℕ) : ℤ)).app (W ⊓ D.i ⁻¹ᵁ (charts α).𝒲)
        ((ordinaryData D).toComplexZ 1 _ ((chartToOrdinary (charts α)).phi inf_le_right
          ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE inf_le_left).op s)))
    have e1 := regularComplexMapZ_toComplexZ D 1 (W ⊓ D.i ⁻¹ᵁ (charts α).𝒲)
      ((chartToOrdinary (charts α)).phi inf_le_right
        ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE inf_le_left).op s))
    have e2 := regularIncl_phi (charts α) (inf_le_right : W ⊓ D.i ⁻¹ᵁ (charts α).𝒲 ≤ _)
      ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE inf_le_left).op s)
    have e3 := regularSec_res D 1 (inf_le_left : W ⊓ D.i ⁻¹ᵁ (charts α).𝒲 ≤ W) s
    refine Eq.trans ?_ e1.symm
    refine congrArg (D.toComplexZ 1 _) ?_
    refine Eq.trans ?_ e2.symm
    exact congrArg ((charts α).phi inf_le_right) e3.symm
  · refine cechDiagramOpens_hom_ext fun W s => ?_
    change D.toComplexZ 0 (W ⊓ (D.i ⁻¹ᵁ (charts α).𝒲 ⊓ D.i ⁻¹ᵁ (charts β).𝒲))
        (D.homotopy (charts α) (charts β) inf_le_right
          ((D.K 1).presheaf.map (homOfLE inf_le_left).op ((regularIncl D 1).app W s))) =
      ((regularComplexMapZ D).f ((0 : ℕ) : ℤ)).app _
        ((ordinaryData D).toComplexZ 0 _ ((ordinaryData D).homotopy (chartToOrdinary (charts α))
          (chartToOrdinary (charts β)) inf_le_right
          ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE inf_le_left).op s)))
    have e1 := regularComplexMapZ_toComplexZ D 0
      (W ⊓ (D.i ⁻¹ᵁ (charts α).𝒲 ⊓ D.i ⁻¹ᵁ (charts β).𝒲))
      ((ordinaryData D).homotopy (chartToOrdinary (charts α)) (chartToOrdinary (charts β))
        inf_le_right
        ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE inf_le_left).op s))
    have e2 := regularIncl_homotopy (charts α) (charts β)
      (inf_le_right : W ⊓ (D.i ⁻¹ᵁ (charts α).𝒲 ⊓ D.i ⁻¹ᵁ (charts β).𝒲) ≤ _)
      ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE inf_le_left).op s)
    have e3 := regularSec_res D 1
      (inf_le_left : W ⊓ (D.i ⁻¹ᵁ (charts α).𝒲 ⊓ D.i ⁻¹ᵁ (charts β).𝒲) ≤ W) s
    refine Eq.trans ?_ e1.symm
    refine congrArg (D.toComplexZ 0 _) ?_
    refine Eq.trans ?_ e2.symm
    exact congrArg (D.homotopy (charts α) (charts β) inf_le_right) e3.symm

private theorem isMulMap_regularComplexMapZ :
    IsMulMap (ordinaryData D).sectionProduct D.sectionProduct (regularComplexMapZ D) :=
  fun a b c h A x y => regularComplexMapZ_mul D a b c h A x y

/-- **The degree-one Čech cochains of a regular form agree** for the two splittings. -/
private theorem oneCochain_regularIncl (W : V.Opens)
    (s : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), W)) :
    (logSplitting charts hcharts).oneCochain W ((regularIncl D 1).app W s) =
      mapTotal (regularComplexMapZ D) ((ordSplitting charts hcharts).oneCochain W s) := by
  funext p m h x
  have e := congrArg (fun φ => secCochain (U := (logSplitting charts hcharts).U) (φ.app W s) x)
    (oneCocycle_compat charts hcharts p m (by omega))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at e
  exact e.trans (secCochain_comp_cechBicomplexMap (regularComplexMapZ D) _ W s x)

/-- **The cup-product cochains of regular `1`-forms agree** for the two splittings. -/
private theorem cupCochain_regularIncl (q : ℕ) (W : V.Opens)
    (θ : Fin (q + 1) → Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), W)) :
    (logSplitting charts hcharts).cupCochain q W (fun i => (regularIncl D 1).app W (θ i)) =
      mapTotal (regularComplexMapZ D) ((ordSplitting charts hcharts).cupCochain q W θ) := by
  funext p m h
  simp only [FrobeniusSplittingData.LocalFrobeniusSplitting.cupCochain, mapTotal,
    mapCochain_sum, mapCochain_zsmul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e := mapTotal_cupFin (isMulMap_regularComplexMapZ (D := D)) q
    (fun i => (ordSplitting charts hcharts).oneCochain W (θ (σ i)))
  have e' : (fun i => mapTotal (regularComplexMapZ D)
      ((ordSplitting charts hcharts).oneCochain W (θ (σ i)))) =
      fun i => (logSplitting charts hcharts).oneCochain W ((regularIncl D 1).app W (θ (σ i))) :=
    funext fun i => (oneCochain_regularIncl charts hcharts W (θ (σ i))).symm
  rw [e'] at e
  exact congrFun (congrFun (congrFun e p) m) h

private theorem regularIncl_list_sum_wedgeFin (q : ℕ) {W : V.Opens}
    (l : List (Fin (q + 1) → Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), W))) :
    (regularIncl D (q + 1)).app W ((l.map ((ordinaryData D).wedgeFin q)).sum) =
      ((l.map fun θ i => (regularIncl D 1).app W (θ i)).map (D.wedgeFin q)).sum := by
  induction l with
  | nil => exact map_zero _
  | cons θ l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) (regularIncl_wedgeFin D q θ) ih)

/-- **The cup-product cocycles of the two splittings are compatible.** -/
private theorem cupComponent_compat (q : ℕ) (p : ℤ) (m : ℕ) (h : p + m = (q : ℤ) + 1) :
    regularIncl D (q + 1) ≫ (logSplitting charts hcharts).cupComponent q p m h =
      (ordSplitting charts hcharts).cupComponent q p m h ≫
        ((cechBicomplexMap (U := (logSplitting charts hcharts).U) (regularComplexMapZ D)).f p).f m := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext s
  refine MMP.DeRham.eq_of_locally_eq_sections _ _ fun x hx => ?_
  obtain ⟨W', hW', hxW', l, hl⟩ := (ordinaryData D).exists_list_wedgeFin_eq_map q s hx
  refine ⟨W', hW', hxW', ?_⟩
  have a1 := app_presheaf_map
    (regularIncl D (q + 1) ≫ (logSplitting charts hcharts).cupComponent q p m h) (homOfLE hW') s
  have a2 := app_presheaf_map ((ordSplitting charts hcharts).cupComponent q p m h ≫
    ((cechBicomplexMap (U := (logSplitting charts hcharts).U) (regularComplexMapZ D)).f p).f m)
    (homOfLE hW') s
  have hl' : (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hW').op s =
      (l.map ((ordinaryData D).wedgeFin q)).sum := hl.symm
  refine a1.symm.trans (Eq.trans ?_ a2)
  refine (congrArg (fun t => ((regularIncl D (q + 1) ≫
    (logSplitting charts hcharts).cupComponent q p m h).app W') t) hl').trans
    (Eq.trans ?_ (congrArg (fun t => (((ordSplitting charts hcharts).cupComponent q p m h ≫
      ((cechBicomplexMap (U := (logSplitting charts hcharts).U) (regularComplexMapZ D)).f p).f m).app
        W') t) hl'.symm))
  refine secCochain_injective (U := (logSplitting charts hcharts).U) ?_
  funext y
  have b1 := secCochain_comp_cechBicomplexMap (U := (logSplitting charts hcharts).U)
    (regularComplexMapZ D) ((ordSplitting charts hcharts).cupComponent q p m h) W'
    ((l.map ((ordinaryData D).wedgeFin q)).sum) y
  refine Eq.trans ?_ b1.symm
  have b2 := congrFun ((ordSplitting charts hcharts).secCochain_cupComponent_app q p m h W' l) y
  have b3 := congrFun ((logSplitting charts hcharts).secCochain_cupComponent_app q p m h W'
    (l.map fun θ i => (regularIncl D 1).app W' (θ i))) y
  have b4 := regularIncl_list_sum_wedgeFin (D := D) q l
  have c1 : secCochain ((regularIncl D (q + 1) ≫
      (logSplitting charts hcharts).cupComponent q p m h).app W'
        ((l.map ((ordinaryData D).wedgeFin q)).sum)) y =
      secCochain (((logSplitting charts hcharts).cupComponent q p m h).app W'
        ((l.map fun θ i => (regularIncl D 1).app W' (θ i)).map (D.wedgeFin q)).sum) y :=
    congrArg (fun t => secCochain (((logSplitting charts hcharts).cupComponent q p m h).app W' t) y)
      b4
  refine c1.trans (b3.trans ?_)
  refine Eq.trans ?_ (congrArg _ b2).symm
  clear a1 a2 hl hl' b1 b2 b3 b4 c1
  induction l with
  | nil => exact (map_zero _).symm
  | cons θ l ih =>
    simp only [List.map_cons, List.sum_cons]
    refine Eq.trans ?_ (map_add _ _ _).symm
    exact congrArg₂ (· + ·) (congrFun (congrFun (congrFun (congrFun
      (cupCochain_regularIncl charts hcharts q W' θ) p) m) h) y) ih

/-- **The Frobenius power maps of the two data are compatible** with the inclusion. -/
private theorem regularIncl_comp_frobeniusPow :
    regularIncl D 0 ≫ D.frobeniusPow = (ordinaryData D).frobeniusPow ≫
      (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (regularIncl D 0) := by
  ext W s
  exact (regularIncl_powSection D W s).symm

/-- **The degree-zero cocycles of the two splittings are compatible.** -/
private theorem zeroCocycle_compat (p' : ℤ) (m : ℕ) (h : p' + m = ((0 : ℕ) : ℤ)) :
    regularIncl D 0 ≫ (D.zeroCocycle (logSplitting charts hcharts).U D.frobeniusPow
        D.cartierRep_frobeniusPow).g p' m h =
      ((ordinaryData D).zeroCocycle (logSplitting charts hcharts).U (ordinaryData D).frobeniusPow
        (ordinaryData D).cartierRep_frobeniusPow).g p' m h ≫
        ((cechBicomplexMap (U := (logSplitting charts hcharts).U) (regularComplexMapZ D)).f p').f m := by
  rcases m with _ | m
  · obtain rfl : p' = ((0 : ℕ) : ℤ) := by push_cast at h ⊢; omega
    change regularIncl D 0 ≫ D.frobeniusPow ≫ (D.complexZXIso 0).inv ≫
        (D.complexZ.XIsoOfEq rfl).hom ≫ cechAugBi D.complexZ ((0 : ℕ) : ℤ) =
      ((ordinaryData D).frobeniusPow ≫ ((ordinaryData D).complexZXIso 0).inv ≫
        ((ordinaryData D).complexZ.XIsoOfEq rfl).hom ≫
          cechAugBi (ordinaryData D).complexZ ((0 : ℕ) : ℤ)) ≫ _
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
    have n1 := cechAugBi_naturality_map (U := (logSplitting charts hcharts).U)
      (regularComplexMapZ D) ((0 : ℕ) : ℤ)
    have n2 : ((ordinaryData D).complexZXIso 0).inv ≫ (regularComplexMapZ D).f ((0 : ℕ) : ℤ) =
        (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).map (regularIncl D 0) ≫
          (D.complexZXIso 0).inv := by
      rw [regularComplexMapZ_f, Iso.inv_hom_id_assoc]
      rfl
    have n3 := regularIncl_comp_frobeniusPow (D := D)
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [n3]
    refine (Category.assoc _ _ _).trans ?_
    have n2' := (Category.assoc _ _ _).symm.trans ((congrArg
      (· ≫ cechAugBi (U := (logSplitting charts hcharts).U) D.complexZ ((0 : ℕ) : ℤ))
      n2.symm).trans (Category.assoc _ _ _))
    refine (congrArg ((ordinaryData D).frobeniusPow ≫ ·) n2').trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine congrArg ((ordinaryData D).frobeniusPow ≫ ·) ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (((ordinaryData D).complexZXIso 0).inv ≫ ·) n1.symm
  · exact comp_zero.trans zero_comp.symm

variable (c : Fin n → ℕ)

/-- The Čech cocycles of the logarithmic splitting representing the inverse Cartier map. -/
private noncomputable def logCocycle : ∀ q : Fin (n + 1),
    CechCocycleData (logSplitting charts hcharts).U D.complexZ (D.K q) ((q : ℕ) : ℤ) :=
  Fin.cases (D.zeroCocycle (logSplitting charts hcharts).U D.frobeniusPow
    D.cartierRep_frobeniusPow) (fun q ↦ (logSplitting charts hcharts).cupCocycle q (c q))

/-- The Čech cocycles of the ordinary splitting representing the inverse Cartier map. -/
private noncomputable def ordCocycle : ∀ q : Fin (n + 1),
    CechCocycleData (logSplitting charts hcharts).U (ordinaryData D).complexZ
      ((ordinaryData D).K q) ((q : ℕ) : ℤ) :=
  Fin.cases ((ordinaryData D).zeroCocycle (logSplitting charts hcharts).U
    (ordinaryData D).frobeniusPow (ordinaryData D).cartierRep_frobeniusPow)
    (fun q ↦ (ordSplitting charts hcharts).cupCocycle q (c q))

/-- **The ordinary and logarithmic cocycles are compatible** with the inclusion of regular
forms, in every degree. -/
private theorem logCocycle_compat (q : Fin (n + 1)) (p' : ℤ) (m : ℕ) (h : p' + m = ((q : ℕ) : ℤ)) :
    regularIncl D q ≫ (logCocycle charts hcharts c q).g p' m h =
      (ordCocycle charts hcharts c q).g p' m h ≫
        ((cechBicomplexMap (U := (logSplitting charts hcharts).U) (regularComplexMapZ D)).f p').f m := by
  induction q using Fin.cases with
  | zero => exact zeroCocycle_compat charts hcharts p' m h
  | succ q =>
    change regularIncl D (q + 1) ≫ ((c q : ℤ) • (logSplitting charts hcharts).cupComponent q p' m _) =
      ((c q : ℤ) • (ordSplitting charts hcharts).cupComponent q p' m _) ≫ _
    exact (Preadditive.comp_zsmul _ _ _).trans ((congrArg ((c q : ℤ) • ·)
      (cupComponent_compat charts hcharts q p' m _)).trans (Preadditive.zsmul_comp _ _ _).symm)

private theorem isCartierCocycle_logCocycle (hc : ∀ q : Fin n, c q * ((q : ℕ) + 1).factorial % p = 1)
    (q : Fin (n + 1)) : D.IsCartierCocycle q (logCocycle charts hcharts c q) := by
  induction q using Fin.cases with
  | zero =>
    exact D.isCartierCocycle_zeroCocycle _ D.frobeniusPow D.cartierRep_frobeniusPow
      (logSplitting charts hcharts).iSup_U
  | succ q => exact (logSplitting charts hcharts).isCartierCocycle_cupCocycle q (hc q)

private theorem isCartierCocycle_ordCocycle (hc : ∀ q : Fin n, c q * ((q : ℕ) + 1).factorial % p = 1)
    (q : Fin (n + 1)) : (ordinaryData D).IsCartierCocycle q (ordCocycle charts hcharts c q) := by
  induction q using Fin.cases with
  | zero =>
    exact (ordinaryData D).isCartierCocycle_zeroCocycle _ (ordinaryData D).frobeniusPow
      (ordinaryData D).cartierRep_frobeniusPow (logSplitting charts hcharts).iSup_U
  | succ q => exact (ordSplitting charts hcharts).isCartierCocycle_cupCocycle q (hc q)

private theorem regularComplexMapZ_app_injective (a : ℤ) (W : V.Opens) :
    Function.Injective (((regularComplexMapZ D).f a).app W) :=
  extendMap_app_injective (regularComplexMap D) (fun q W' => by
    change Function.Injective ((regularIncl D q).app (absoluteFrobenius V p D.hV ⁻¹ᵁ W'))
    exact regularIncl_app_injective D q _) a W

include charts hcharts in
/-- **The decomposition of `F_*(Ω^• / I_S Ω^•(log S))`**: the cone of the inclusion of
`F_*(I_S Ω^•(log S))` into `F_*Ω^•` is isomorphic in the derived category to
`⨁_{q ≤ n} (Ω^q / I_S Ω^q(log S))[-q]`. -/
private theorem nonempty_iso_cone (hc : ∀ q : Fin n, c q * ((q : ℕ) + 1).factorial % p = 1) :
    Nonempty ((⨁ fun q : Fin (n + 1) => (DerivedCategory.singleFunctor V.Modules ((q : ℕ) : ℤ)).obj
        (cokernel (twistedToRegular D 1 q le_rfl))) ≅
      DerivedCategory.Q.obj (cokernel (coneMap D))) := by
  set U := (logSplitting charts hcharts).U
  have hU := (logSplitting charts hcharts).iSup_U
  haveI := mono_coneMap D
  haveI := quasiIso_twistedIncl1p D
  let S := ShortComplex.mk (coneMap D) (cokernel.π (coneMap D)) (cokernel.condition _)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (S.exact_of_g_is_cokernel (cokernelIsCokernel _)) inferInstance inferInstance
  let s : Fin (n + 1) → ShortComplex V.Modules := fun q => ShortComplex.mk
    (twistedToRegular D 1 q le_rfl) (cokernel.π _) (cokernel.condition _)
  have hs : ∀ q, (s q).ShortExact := fun q => by
    haveI : Mono (twistedToRegular D 1 q le_rfl) :=
      mono_of_app_injective _ (twistedToRegular_app_injective D q)
    exact ShortComplex.ShortExact.mk' ((s q).exact_of_g_is_cokernel (cokernelIsCokernel _))
      inferInstance inferInstance
  let Ψ₁ : ∀ q : Fin (n + 1), CechCocycleData U S.X₁ (s q).X₁ ((q : ℕ) : ℤ) := fun q =>
    cocyclePostcomp (HomologicalComplex.extendMap (twistedIncl1p D) ComplexShape.embeddingUpNat)
      (twistedCocycle D q (logCocycle charts hcharts c q))
  let Ψ₂ : ∀ q : Fin (n + 1), CechCocycleData U S.X₂ (s q).X₂ ((q : ℕ) : ℤ) := fun q =>
    ordCocycle charts hcharts c q
  refine nonempty_iso_of_compatible_cocycles hU hS s hs Ψ₁ Ψ₂ (fun q => ?_) (fun q => ?_)
    (isZero_twistedComplex1_homology D) (fun m hm => ?_) (fun q p' m h => ?_)
  · exact isIso_homologyMap_cocyclePostcomp hU _ _
      (isIso_homologyMap_twistedCocycle D hU q _ (isCartierCocycle_logCocycle charts hcharts c hc q))
  · exact (ordinaryData D).isIso_homologyMap_of_isCartierCocycle hU _
      (isCartierCocycle_ordCocycle charts hcharts c hc q)
  · exact ShortComplex.isZero_homology_of_isZero_X₂ _ ((ordinaryData D).isZero_complexZ_X hm)
  · haveI : Mono (((cechBicomplexMap (U := U) (regularComplexMapZ D)).f p').f m) :=
      mono_of_app_injective _ (injective_cechBicomplexMap (U := U) _
        (regularComplexMapZ_app_injective (D := D)) p' m)
    rw [← cancel_mono (((cechBicomplexMap (U := U) (regularComplexMapZ D)).f p').f m)]
    have e1 := logCocycle_compat charts hcharts c q p' m h
    have e2 := twistedCocycle_g_comp D q (logCocycle charts hcharts c q) p' m h
    have e3 : ((cechBicomplexMap (U := U) (HomologicalComplex.extendMap (twistedIncl1p D)
          ComplexShape.embeddingUpNat)).f p').f m ≫ ((cechBicomplexMap (U := U) S.f).f p').f m ≫
        ((cechBicomplexMap (U := U) (regularComplexMapZ D)).f p').f m =
        ((cechBicomplexMap (U := U) (twistedInclZ D)).f p').f m := by
      have := congrArg (fun φ => ((cechBicomplexMap (U := U) φ).f p').f m) (twistedInclZ_eq_comp D)
      simp only [cechBicomplexMap, Functor.map_comp, HomologicalComplex.comp_f] at this ⊢
      exact this
    have lhs := (Category.assoc _ _ _).trans ((congrArg (twistedToRegular D 1 q le_rfl ≫ ·)
      e1.symm).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (logCocycle charts hcharts c q).g p' m h)
          (twistedToRegular_comp_regularIncl D 1 q le_rfl))))
    have rhs := ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans
      ((congrArg ((twistedCocycle D q (logCocycle charts hcharts c q)).g p' m h ≫ ·) e3).trans e2)
    exact lhs.trans rhs.symm

end Splittings

end Charts

/-- **The decomposition of `F_*(Ω^• / I_S Ω^•(log S))`** for a lifted pair. -/
private theorem nonempty_iso_cone_of_lift :
    Nonempty ((⨁ fun q : Fin (n + 1) => (DerivedCategory.singleFunctor V.Modules ((q : ℕ) : ℤ)).obj
        (cokernel (twistedToRegular D 1 q le_rfl))) ≅
      DerivedCategory.Q.obj (cokernel (coneMap D))) := by
  choose charts hcharts using D.exists_frobeniusLiftChart
  have hc : ∀ q : Fin n, ∃ c : ℕ, c * ((q : ℕ) + 1).factorial % p = 1 := fun q ↦ by
    have hp : Nat.Coprime p ((q : ℕ) + 1).factorial := by
      rw [Nat.Prime.coprime_iff_not_dvd Fact.out, Nat.Prime.dvd_factorial Fact.out]
      have := D.hpn
      omega
    obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hp.symm (Fact.out : p.Prime).one_lt
    exact ⟨c, by rw [mul_comm]; exact hc⟩
  choose c hc using hc
  exact nonempty_iso_cone charts hcharts c hc

end OrdinaryData

/-! ### The twisted forms on a fibre are `Ω^q(log D)(-D)` -/

section FibreTwist

open MMP.DeRham Stacks.Frobenius

variable (n : ℕ) {R : Type} [CommRing R]
    {𝒳 : Scheme.{0}} (g : 𝒳 ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n g]
    (hg : IsProjective g) (𝒟 : MMP.Mori.Divisor 𝒳) (h𝒟 : 𝒟.IsRelativeSNC n g)
    (s : Spec (CommRingCat.of R)) (p : ℕ) [Fact p.Prime] (hnp : n < p)
    [Finite ((Spec (CommRingCat.of R)).residueField s)]
    [CharP ((Spec (CommRingCat.of R)).residueField s) p]
    (ρ : R →+* (Spec (CommRingCat.of R)).residueField s)
    (hρ : Spec.map (CommRingCat.ofHom ρ) = (Spec (CommRingCat.of R)).fromSpecResidueField s)
    (φ : R →+* TruncatedWittVector p 2 ((Spec (CommRingCat.of R)).residueField s))
    (hφ : ∀ r, (φ r).coeff 0 = ρ r)
    [SmoothOfRelativeDimension n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))]
    (Ds : MMP.Mori.Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hDs : Ds.IsRelativeSNC n (pullback.snd _ _))
    (hsupp : (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
      (𝒟.supp : Set 𝒳) = (Ds.supp : Set _))
    [HasDerivedCategory.{0}
      (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules]
    (hV : IsInCharacteristic (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p)
    (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs ⊤ (q + 1)))
    (hd : ∀ q, d q ≫ d (q + 1) = 0)
    (hdR : ∀ (q : ℕ) (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opens)
        (x : Γ(G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q, W)),
        (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs ⊤ (q + 1)).obj (op W))
          from (d q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU Ds).ι ≫ pullback.snd _ _)).d q (q + 1)).val.app
          (op ((G1.LU Ds).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs ⊤ q).obj (op W))
            from x).1)

/-- **On a fibre, the twisted logarithmic forms are `Ω^q(log 𝒟_s)(-𝒟_s)`.** -/
private noncomputable def twistedLogFibreIso (q : ℕ) :
    haveI : IsProper g := hg.isProper
    twistedLog (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd
      hdR) 1 q ≅ G1.logModule n (pullback.snd _ _) Ds hDs Ds.suppIdeal q := by
  haveI : IsProper g := hg.isProper
  let FD := fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR
  have hΔ : FD.U = (Ds.supp.compl : _) := rfl
  refine submoduleIsoOfIff (M := G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q)
    (twistedLogSubmodule FD 1 q) (idealLogSubmodule n _ Ds hDs Ds.suppIdeal q) (fun W x => ?_) ≪≫
    (logModuleIdealIso n _ Ds hDs Ds.suppIdeal q).symm
  constructor
  · intro hx
    exact isLocallyIn_of_locally_eq _ (map_divisorIdealPow_le FD 1)
      (fun hx' => exists_affineOpens_divisorIdealPow_one_eq FD Ds hΔ hx') hx
  · intro hx
    exact isLocallyIn_of_locally_eq _ (fun _ _ h => (Ds.suppIdeal.map_ideal h).le)
      (fun hx' => let ⟨W'', h1, h2, h3⟩ := exists_affineOpens_divisorIdealPow_one_eq FD Ds hΔ hx'
        ⟨W'', h1, h2, h3.symm⟩) hx

end FibreTwist

/-! ### The restriction of forms to the complement of the divisor -/

section FormsRestriction

/-- **The canonical map of forms to an open subscheme is restriction.** -/
private theorem deRhamFormsPushforwardHom_app_eq {X S : Scheme.{0}} (f : X ⟶ S) (U : X.Opens)
    (n : ℤ) (h : U.ι ≫ f = (U.ι ≫ f) ≫ 𝟙 S) :
    (Scheme.Hom.deRhamFormsPushforwardHom U.ι f (U.ι ≫ f) (𝟙 S) h).app n =
      (Scheme.Modules.restrictAdjunction U.ι).unit.app _ ≫ (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app _ ≫
          Scheme.Hom.relativeDifferentialFormsMap U.ι f (U.ι ≫ f) (𝟙 S) h n) := by
  have e1 : (Scheme.Hom.deRhamFormsPushforwardHom U.ι f (U.ι ≫ f) (𝟙 S) h).app n =
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι).homEquiv _ _
        (Scheme.Hom.relativeDifferentialFormsMap U.ι f (U.ι ≫ f) (𝟙 S) h n) :=
    (Scheme.Hom.homEquiv_relativeDifferentialFormsMap U.ι f (U.ι ≫ f) (𝟙 S) h n).symm
  rw [e1, Adjunction.homEquiv_unit]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction U.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι) (f.relativeDifferentialForms n)
  rw [← hu, Category.assoc, ← Functor.map_comp]
  rfl

variable {Y : Scheme.{0}} {k : Type} [Field k] (f : Y ⟶ Spec (CommRingCat.of k)) (U : Y.Opens)

/-- **The restriction of a regular form to `U`, read on `Y`, is its restriction to `W ∩ U`.** -/
private theorem ambientFormsEquiv_deRhamPushforwardChain (q : ℕ) (W : Y.Opens)
    (t : Γ(f.relativeDifferentialForms (q : ℤ), W)) :
    ambientFormsEquiv f U q W
        (((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι U) f).f q).val.app
          (op W) t) =
      (f.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (inf_le_left : W ⊓ U ≤ W)).op t := by
  have e0 : ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι U) f).f q).val.app
      (op W) t = ((Scheme.Hom.deRhamFormsPushforwardHom U.ι f (U.ι ≫ f) (𝟙 _)
        (Category.comp_id _).symm).app (q : ℤ)).val.app (op W) t := by
    change ((Stacks.DeRhamPullback.pushforwardSquareIso (Scheme.Opens.ι U) f).inv.app
        (Scheme.Hom.relativeDifferentialForms (U.ι ≫ f) ((q : ℕ) : ℤ))).val.app (op W)
        (((Stacks.DeRhamPullback.formsPushforwardComponent (Scheme.Opens.ι U) f q).val.app (op W))
          t) = _
    exact Stacks.DeRhamPullback.pushforwardSquareIso_inv_val_app (Scheme.Opens.ι U) f
      (Scheme.Hom.relativeDifferentialForms (U.ι ≫ f) ((q : ℕ) : ℤ)) (op W)
      (((Stacks.DeRhamPullback.formsPushforwardComponent (Scheme.Opens.ι U) f q).val.app (op W)) t)
  rw [e0, deRhamFormsPushforwardHom_app_eq]
  refine (ambientFormsEquiv_apply f U q W _).trans ?_
  change (f.relativeDifferentialForms (q : ℤ)).presheaf.map _
      (Scheme.Modules.Hom.app (formsRestrictIso f U q).inv (U.ι ⁻¹ᵁ W)
        (Scheme.Modules.Hom.app (formsRestrictIso f U q).hom (U.ι ⁻¹ᵁ W)
          ((f.relativeDifferentialForms (q : ℤ)).presheaf.map
            (homOfLE (U.ι.image_preimage_le W)).op t))) = _
  have hinv := congrArg (fun φ => Scheme.Modules.Hom.app φ (U.ι ⁻¹ᵁ W)
    ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE (U.ι.image_preimage_le W)).op t))
    (formsRestrictIso f U q).hom_inv_id
  refine (congrArg _ hinv).trans ?_
  exact MMP.DeRham.presheaf_map_map _ _ _ _

end FormsRestriction

/-! ### The terms of the logarithmic de Rham complex -/

section RelLogTerms

open MMP.Mori.Divisor.LogSpreadingProof.G1

variable {X S : Scheme.{u}} (n : ℕ) (f : X ⟶ S) [SmoothOfRelativeDimension n f]
  (D : MMP.Mori.Divisor X) (hD : D.IsRelativeSNC n f)

/-- **The terms of the logarithmic de Rham complex are the logarithmic forms.** -/
private theorem mem_relativeLogDeRhamTerms_iff (ε : Bool) (p : ℕ) (W : X.Opensᵒᵖ)
    (ω : ((complementDeRhamPushforward f D).X p).val.obj W) :
    ω ∈ (relativeLogDeRhamTerms n f D hD (bif ε then D.suppIdeal else ⊤) p).obj W ↔
      ω ∈ relativeLogForms n f D hD (bif ε then D.suppIdeal else ⊤) p W.unop := by
  have hT : (relativeLogDeRhamTerms n f D hD (bif ε then D.suppIdeal else ⊤) :
      ∀ p : ℕ, (KX f (LU D) p).Submodule) =
        logSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) := by
    apply le_antisymm
    · exact sInf_le ⟨fun q W ω hω => hω,
        fun q W ω hω => deRham_mem_relativeLogForms hD ε q W.unop ω hω⟩
    · refine le_sInf ?_
      rintro M ⟨hM1, -⟩ q
      exact SheafOfModules.Submodule.le_iff.mpr
        (PresheafOfModules.Submodule.le_iff.mpr fun W ω hω => hM1 q W.unop ω hω)
  exact Iff.of_eq (congrArg (fun N : ∀ p : ℕ, (KX f (LU D) p).Submodule => ω ∈ (N p).obj W) hT)

/-- **The terms of the logarithmic de Rham complex, read as `𝒪_X`-modules.** -/
private noncomputable def relLogXIso (ε : Bool) (q : ℕ) :
    (relativeLogDeRhamComplex n f D hD (bif ε then D.suppIdeal else ⊤)).X q ≅
      (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).obj
        (logModule n f D hD (bif ε then D.suppIdeal else ⊤) q) :=
  submoduleIsoOfIff (relativeLogDeRhamTerms n f D hD (bif ε then D.suppIdeal else ⊤) q)
      (logSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) q)
      (fun W s => mem_relativeLogDeRhamTerms_iff n f D hD ε q W s) ≪≫
    logSubmoduleIso n f D hD _ q

private theorem relLogXIso_inv_app (ε : Bool) (q : ℕ) (W : X.Opensᵒᵖ)
    (x : ((pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).obj
      (logModule n f D hD (bif ε then D.suppIdeal else ⊤) q)).val.obj W) :
    ((relLogXIso n f D hD ε q).inv.val.app W x).1 = x.1 := rfl

end RelLogTerms

section InverseImageBase

open Stacks.DeRhamDirectImage

/-- Modules over `𝒪_Y` read over `h⁻¹𝒪_T` by restriction of scalars along the structure map. -/
private noncomputable def pushforwardInverseImageBaseIso {Y T : Scheme.{0}} (h : Y ⟶ T)
    (M : Y.Modules) :
    (pushforward (toInverseImageBase h)).obj M ≅
      (_root_.SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHom
        (φ := inverseImageStructureMap h))).obj M where
  hom := ⟨PresheafOfModules.homMk (𝟙 _) fun _ _ _ => rfl⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 _) fun _ _ _ => rfl⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

end InverseImageBase

/-! ### The inclusion of the twisted forms on a fibre -/

section FibreSquare

open MMP.DeRham Stacks.Frobenius

variable (n : ℕ) {R : Type} [CommRing R]
    {𝒳 : Scheme.{0}} (g : 𝒳 ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n g]
    (hg : IsProjective g) (𝒟 : MMP.Mori.Divisor 𝒳) (h𝒟 : 𝒟.IsRelativeSNC n g)
    (s : Spec (CommRingCat.of R)) (p : ℕ) [Fact p.Prime] (hnp : n < p)
    [Finite ((Spec (CommRingCat.of R)).residueField s)]
    [CharP ((Spec (CommRingCat.of R)).residueField s) p]
    (ρ : R →+* (Spec (CommRingCat.of R)).residueField s)
    (hρ : Spec.map (CommRingCat.ofHom ρ) = (Spec (CommRingCat.of R)).fromSpecResidueField s)
    (φ : R →+* TruncatedWittVector p 2 ((Spec (CommRingCat.of R)).residueField s))
    (hφ : ∀ r, (φ r).coeff 0 = ρ r)
    [SmoothOfRelativeDimension n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))]
    (Ds : MMP.Mori.Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hDs : Ds.IsRelativeSNC n (pullback.snd _ _))
    (hsupp : (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
      (𝒟.supp : Set 𝒳) = (Ds.supp : Set _))
    [HasDerivedCategory.{0}
      (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules]
    (hV : IsInCharacteristic (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p)
    (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs ⊤ (q + 1)))
    (hd : ∀ q, d q ≫ d (q + 1) = 0)
    (hdR : ∀ (q : ℕ) (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opens)
        (x : Γ(G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q, W)),
        (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs ⊤ (q + 1)).obj (op W))
          from (d q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU Ds).ι ≫ pullback.snd _ _)).d q (q + 1)).val.app
          (op ((G1.LU Ds).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs ⊤ q).obj (op W))
            from x).1)

/-- **The embedding of the fibre data is the identification of forms off the divisor.** -/
private theorem fibreFrobeniusSplittingData_e_apply (q : ℕ)
    (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opens)
    (x : Γ(G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q, W)) :
    haveI : IsProper g := hg.isProper
    (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR).e q W x =
      ambientFormsEquiv (pullback.snd _ _) (G1.LU Ds) q W x.1 := by
  haveI : IsProper g := hg.isProper
  exact (exists_logForms_embedding (k := (Spec (CommRingCat.of R)).residueField s)
    (pullback.snd _ _) Ds hDs _ (fun T =>
      smoothOfRelativeDimension_iSup_comap_of_isPullback (IsPullback.of_hasPullback _ _) _ T _ _
        (smoothOfRelativeDimension_iSup_idealSheaf n g 𝒟 h𝒟 T))
    (LU_eq_compl_support_iInf_comap _ 𝒟 Ds hsupp)
    (exists_mem_support_genericPoint_eq Ds)).choose_spec.1 q W x

/-- **On a fibre, a pinned inclusion `Ω^•(log 𝒟_s)(-𝒟_s) ⟶ Ω^•` is the inclusion of twisted
forms into regular forms.** -/
private theorem i_app_eq_twistedToRegular (q : ℕ)
    (i : relativeLogDeRhamComplex n (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
      Ds hDs Ds.suppIdeal ⟶
        Scheme.Hom.deRhamComplex (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hi : ∀ (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n (pullback.snd g _) Ds hDs Ds.suppIdeal).X q).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι Ds.supp.compl)
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))).f q).val.app W
          ((i.f q).val.app W ω) = ω.1)
    (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opens)
    (x : ((relativeLogDeRhamComplex n (pullback.snd g _) Ds hDs Ds.suppIdeal).X q).val.obj (op W)) :
    haveI : IsProper g := hg.isProper
    ∀ y : Γ(twistedLog (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV
      d hd hdR) 1 q, W), y.1.1 = x.1 →
    (show Γ((pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).relativeDifferentialForms
        (q : ℤ), W) from (i.f q).val.app (op W) x) =
      (twistedToRegular (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV
        d hd hdR) 1 q le_rfl).app W y := by
  intro y hy
  haveI : IsProper g := hg.isProper
  show (i.f q).val.app (op W) x = _
  apply forms_res_injective
    (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR) q W
  have e1 := ambientFormsEquiv_deRhamPushforwardChain
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) (G1.LU Ds) q W
    ((i.f q).val.app (op W) x)
  have e2 := hi (op W) x
  have e3 := e_regularIncl_app
    (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR) q W
    ((twistedToRegular
      (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR)
      1 q le_rfl).app W y)
  have e4 := twistedToRegular_app_val
    (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR) q W y
  have e5 := fibreFrobeniusSplittingData_e_apply n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV
    d hd hdR q W y.1
  refine e1.symm.trans (Eq.trans ?_ e3)
  refine (congrArg (ambientFormsEquiv _ (G1.LU Ds) q W) (e2.trans hy.symm)).trans ?_
  rw [e4]
  exact e5.symm

private theorem fibreComm_submoduleIsoOfIff_hom_app {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{u} R}
    (N N' : M.Submodule) (h : ∀ (W : Cᵒᵖ) (s : M.val.obj W), s ∈ N.obj W ↔ s ∈ N'.obj W)
    (W : Cᵒᵖ) (x : N.toSheafOfModules.val.obj W) :
    ((submoduleIsoOfIff N N' h).hom.val.app W x).1 = x.1 :=
  rfl

private theorem fibreComm_lhs_app (q : ℕ)
    (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opensᵒᵖ) :
    haveI : IsProper g := hg.isProper
    ∀ y : ((pushforward (Stacks.DeRhamDirectImage.toInverseImageBase
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))).obj
        (twistedLog (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV
          d hd hdR) 1 q)).val.obj W,
    ((pushforward (Stacks.DeRhamDirectImage.toInverseImageBase _)).map
        (twistedToRegular (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV
          d hd hdR) 1 q le_rfl) ≫
      (pushforwardInverseImageBaseIso (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
        ((pullback.snd g _).relativeDifferentialForms (q : ℤ))).hom).val.app W y =
      (twistedToRegular (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV
          d hd hdR) 1 q le_rfl).app W.unop y :=
  fun _ => rfl

private theorem fibreComm_rhs_app (q : ℕ)
    (i : relativeLogDeRhamComplex n (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
      Ds hDs Ds.suppIdeal ⟶ Scheme.Hom.deRhamComplex (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opensᵒᵖ) :
    haveI : IsProper g := hg.isProper
    ∀ y : ((pushforward (Stacks.DeRhamDirectImage.toInverseImageBase
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))).obj
        (twistedLog (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV
          d hd hdR) 1 q)).val.obj W,
    (((pushforward (Stacks.DeRhamDirectImage.toInverseImageBase _)).mapIso
        (twistedLogFibreIso n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q) ≪≫
      (relLogXIso n _ Ds hDs true q).symm).hom ≫ i.f q).val.app W y =
      (i.f q).val.app W ((relLogXIso n _ Ds hDs true q).inv.val.app W
        (((pushforward (Stacks.DeRhamDirectImage.toInverseImageBase _)).map
          (twistedLogFibreIso n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q).hom).val.app
            W y)) :=
  fun _ => rfl

private theorem fibreComm_twistedLogFibreIso_hom_app (q : ℕ)
    (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opens) :
    haveI : IsProper g := hg.isProper
    ∀ y : Γ(twistedLog (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV
          d hd hdR) 1 q, W),
    ((twistedLogFibreIso n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q).hom.app W
      y).1 = y.1.1 :=
  fun y => (logModuleIdealInv_app_val n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) Ds hDs Ds.suppIdeal q W
      _).trans (congrArg Subtype.val (fibreComm_submoduleIsoOfIff_hom_app _ _ _ (op W) y))

private theorem fibreComm_val (q : ℕ)
    (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opensᵒᵖ) :
    haveI : IsProper g := hg.isProper
    ∀ y : ((pushforward (Stacks.DeRhamDirectImage.toInverseImageBase
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))).obj
        (twistedLog (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV
          d hd hdR) 1 q)).val.obj W,
    ((relLogXIso n _ Ds hDs true q).inv.val.app W
        (((pushforward (Stacks.DeRhamDirectImage.toInverseImageBase _)).map
          (twistedLogFibreIso n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q).hom).val.app
            W y)).1 =
      ((twistedLogFibreIso n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q).hom.app
        W.unop y).1 :=
  fun y => (relLogXIso_inv_app n _ Ds hDs true q W _).trans rfl

/-- **The square of inclusions on a fibre.** -/
private theorem twistedToRegular_fibre_comm (q : ℕ)
    (i : relativeLogDeRhamComplex n (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
      Ds hDs Ds.suppIdeal ⟶
        Scheme.Hom.deRhamComplex (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hi : ∀ (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n (pullback.snd g _) Ds hDs Ds.suppIdeal).X q).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι Ds.supp.compl)
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))).f q).val.app W
          ((i.f q).val.app W ω) = ω.1) :
    haveI : IsProper g := hg.isProper
    (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase _)).map
        (twistedToRegular (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV
          d hd hdR) 1 q le_rfl) ≫
      (pushforwardInverseImageBaseIso (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
        ((pullback.snd g _).relativeDifferentialForms (q : ℤ))).hom =
    ((pushforward (Stacks.DeRhamDirectImage.toInverseImageBase _)).mapIso
        (twistedLogFibreIso n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q) ≪≫
      (relLogXIso n _ Ds hDs true q).symm).hom ≫ i.f q := by
  haveI : IsProper g := hg.isProper
  ext W y
  refine (fibreComm_lhs_app n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q W y).trans
    (Eq.trans ?_ (fibreComm_rhs_app n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q i W
      y).symm)
  exact (i_app_eq_twistedToRegular n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q i hi
    W.unop _ y ((fibreComm_twistedLogFibreIso_hom_app n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp
      hV d hd hdR q W.unop y).symm.trans
        (fibreComm_val n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q W y).symm)).symm

/-- **The terms of the restriction complex of a fibre**: the cokernel of the inclusion of twisted
forms into regular forms, read over `f⁻¹𝒪`, is the term of a cokernel of `Ω^•(log)(-𝒟_s) ⟶ Ω^•`. -/
private noncomputable def cokernelFibreIso (q : ℕ)
    (i : relativeLogDeRhamComplex n (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
      Ds hDs Ds.suppIdeal ⟶
        Scheme.Hom.deRhamComplex (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hi : ∀ (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n (pullback.snd g _) Ds hDs Ds.suppIdeal).X q).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι Ds.supp.compl)
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))).f q).val.app W
          ((i.f q).val.app W ω) = ω.1)
    (Dc : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0}
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base).obj
          (Spec ((Spec (CommRingCat.of R)).residueField s)).sheaf))) ℕ)
    (qc : Scheme.Hom.deRhamComplex (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
      ⟶ Dc) (hiq : i ≫ qc = 0) (hq : IsColimit (CokernelCofork.ofπ qc hiq)) :
    haveI : IsProper g := hg.isProper
    (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase _)).obj
        (cokernel (twistedToRegular (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds
          hDs hsupp hV d hd hdR) 1 q le_rfl)) ≅ Dc.X q := by
  haveI : IsProper g := hg.isProper
  haveI := Stacks.DeRhamDirectImage.preservesFiniteColimits_pushforward_toInverseImageBase
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
  have hq0 : IsColimit (CokernelCofork.ofπ (qc.f q)
      (by rw [← HomologicalComplex.comp_f, hiq, HomologicalComplex.zero_f]) :
        Cofork (i.f q) 0) :=
    isColimitCoforkMapOfIsColimit' (HomologicalComplex.eval _ _ q) _ hq
  exact PreservesCokernel.iso _ _ ≪≫
    cokernel.mapIso _ (i.f q) _ _
      (twistedToRegular_fibre_comm n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q i hi) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hq0

end FibreSquare

/-! ### The Frobenius twist on a fibre over a finite field -/

section FrobeniusTwistIso

open Stacks.DeRhamDirectImage Stacks.Frobenius

attribute [local instance] additive_restrictScalars_underlyingRingSheaf

variable {Y : Scheme.{0}} {κ : CommRingCat.{0}} (f : Y ⟶ Spec κ) (p : ℕ) [Fact p.Prime]
  (hp : (p : κ) = 0) (hpt : ∀ a b : Spec κ, a = b) {m : ℕ} (hm : 1 ≤ m)
  (hκ : ∀ x : κ, x ^ p ^ m = x) (hV : IsInCharacteristic Y p)

private theorem frobenius_structureMap_eq (W : (TopologicalSpace.Opens Y)ᵒᵖ) (r) :
    (absoluteFrobenius Y p hV).app W.unop (((inverseImageStructureMap f).hom.app W).hom r) =
      ((inverseImageStructureMap f).hom.app W).hom
        ((frobeniusRingSheafIso f p hp hpt hm hκ).hom.hom.app W r) :=
  (absoluteFrobenius_app_apply Y p hV _ _).trans ((map_pow _ _ _).symm.trans
    (congrArg _ (frobeniusRingSheafIso_hom_app f p hp hpt hm hκ W r).symm))

/-- **The Frobenius pushforward read over `f⁻¹𝒪`** is the restriction of scalars along the
Frobenius of `f⁻¹𝒪`: both have the sections of `M`. -/
private noncomputable def frobTwistIso (M : Y.Modules) :
    (pushforward (toInverseImageBase f)).obj
        ((Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj M) ≅
      (_root_.SheafOfModules.restrictScalars.{0}
        (frobeniusRingSheafIso f p hp hpt hm hκ).hom).obj
        ((pushforward (toInverseImageBase f)).obj M) where
  hom := ⟨PresheafOfModules.homMk (𝟙 _) fun W r x => by
    let W' : Y.Opens := W.unop
    exact congrArg (fun c => (show Γ(Y, W') from c) • (show Γ(M, W') from x))
      (frobenius_structureMap_eq f p hp hpt hm hκ hV W r)⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 _) fun W r x => by
    let W' : Y.Opens := W.unop
    exact congrArg (fun c => (show Γ(Y, W') from c) • (show Γ(M, W') from x))
      (frobenius_structureMap_eq f p hp hpt hm hκ hV W r).symm⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **Hypercohomology dimensions of a complex split after the Frobenius twist.** Let `X` be a
bounded below complex of `𝒪_Y`-modules isomorphic in the derived category to
`⨁_{q ≤ n} M_q[-q]`, and `L` a complex of `f⁻¹𝒪`-modules whose Frobenius twist is the image of
`X`. Then `dim ℍ^k(L) = ∑_q dim H^{k-q}(M_q)`. -/
private theorem finrank_hyp_eq_sum_of_split (n : ℕ) (X : CochainComplex.Plus Y.Modules)
    [HasDerivedCategory Y.Modules] (M : Fin (n + 1) → Y.Modules)
    (Φ : DerivedCategory.Q.obj X.obj ≅
      ⨁ fun q : Fin (n + 1) => (DerivedCategory.singleFunctor Y.Modules (q : ℤ)).obj (M q))
    (L : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf))))
    (eL : (pushforward (toInverseImageBase f)).mapCochainComplexPlus.obj X ≅
      (_root_.SheafOfModules.restrictScalars.{0}
        (frobeniusRingSheafIso f p hp hpt hm hκ).hom).mapCochainComplexPlus.obj L)
    (Mt : Fin (n + 1) → SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf)))
    (eM : ∀ q, (pushforward (toInverseImageBase f)).obj (M q) ≅ Mt q)
    [StrongRankCondition Γ(Spec κ, ⊤)]
    (hfin : ∀ q (j : ℤ), Module.Finite Γ(Spec κ, ⊤) (Hc f (single0 f (Mt q)) j))
    (hfree : ∀ q (j : ℤ), Module.Free Γ(Spec κ, ⊤) (Hc f (single0 f (Mt q)) j))
    (k : ℤ) :
    Module.finrank Γ(Spec κ, ⊤) (Hc f L k) =
      ∑ q : Fin (n + 1), Module.finrank Γ(Spec κ, ⊤)
        (Hc f (single0 f (Mt q)) (k - q)) := by
  let G : Y.Modules ⥤ SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec κ).sheaf)) :=
    pushforward (toInverseImageBase f)
  haveI : G.Additive := inferInstanceAs (pushforward (toInverseImageBase f)).Additive
  haveI : PreservesFiniteLimits G := preservesFiniteLimits_pushforward_toInverseImageBase f
  haveI : PreservesFiniteColimits G := preservesFiniteColimits_pushforward_toInverseImageBase f
  rw [← finrank_hyp_frobeniusTwist f p hp hpt hm hκ L k,
    ← (hypIsoOfIso f eL k).toLinearEquiv.finrank_eq]
  exact finrank_hyp_eq_sum_of_iso f (G.mapCochainComplexPlus.obj X) Mt
    (plusQMapIsoBiproductOfIso G X M Φ ≪≫ biproduct.mapIso fun q =>
      (DerivedCategory.Plus.singleFunctor _ (q : ℤ)).mapIso (eM q)) hfin hfree k

end FrobeniusTwistIso

/-! ### The Frobenius twist of the de Rham complex -/

section FrobeniusDeRhamTwist

open Stacks.DeRhamDirectImage Stacks.Frobenius

attribute [local instance] additive_restrictScalars_underlyingRingSheaf

variable {Y : Scheme.{0}} {k : Type} [Field k] (f : Y ⟶ Spec (CommRingCat.of k)) (p : ℕ)
  [Fact p.Prime] (hp : (p : CommRingCat.of k) = 0) (hpt : ∀ a b : Spec (CommRingCat.of k), a = b)
  {m : ℕ} (hm : 1 ≤ m) (hκ : ∀ x : CommRingCat.of k, x ^ p ^ m = x) (hV : IsInCharacteristic Y p)

/-- **The Frobenius pushforward of the de Rham complex, read over `f⁻¹𝒪`**, is the de Rham
complex with scalars restricted along the Frobenius of `f⁻¹𝒪`. -/
private noncomputable def frobDeRhamComplexIso :
    ((pushforward (toInverseImageBase f)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (CochainComplex.of (fun q => (Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj
          (f.relativeDifferentialForms (q : ℤ))) (frobeniusDeRhamD f p hV)
          (frobeniusDeRhamD_comp f p hV)) ≅
      ((_root_.SheafOfModules.restrictScalars.{0}
        (frobeniusRingSheafIso f p hp hpt hm hκ).hom).mapHomologicalComplex _).obj
        (Scheme.Hom.deRhamComplex f) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => frobTwistIso f p hp hpt hm hκ hV _ ≪≫
      (_root_.SheafOfModules.restrictScalars.{0} (frobeniusRingSheafIso f p hp hpt hm hκ).hom).mapIso
        (pushforwardInverseImageBaseIso f (f.relativeDifferentialForms (q : ℤ))))
    (by
      rintro i _ rfl
      rw [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_d]
      ext W x
      have hB := congrArg (fun φ => φ.val.app W x) (CochainComplex.of_d
        (fun q : ℕ => (Scheme.Modules.pushforward (absoluteFrobenius Y p hV)).obj
          (f.relativeDifferentialForms (q : ℤ))) (frobeniusDeRhamD f p hV) i)
      refine Eq.trans ?_ (congrArg (fun y => ((frobTwistIso f p hp hpt hm hκ hV _ ≪≫
        (_root_.SheafOfModules.restrictScalars.{0}
          (frobeniusRingSheafIso f p hp hpt hm hκ).hom).mapIso
          (pushforwardInverseImageBaseIso f (f.relativeDifferentialForms ((i + 1 : ℕ) : ℤ)))).hom).val.app
            W y) hB).symm
      rfl)

end FrobeniusDeRhamTwist

section Exactness

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- Extension by zero along `ℕ → ℤ` preserves short exact sequences. -/
private theorem shortExact_map_extendFunctor {S : ShortComplex (CochainComplex C ℕ)}
    (hS : S.ShortExact) : (S.map (ComplexShape.embeddingUpNat.extendFunctor C)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun j' => ?_
  by_cases hj : ∃ i, ComplexShape.embeddingUpNat.f i = j'
  · obtain ⟨i, hi⟩ := hj
    have hSi : (S.map (HomologicalComplex.eval C _ i)).ShortExact := by
      have := hS.mono_f
      have := hS.epi_g
      exact hS.map (HomologicalComplex.eval C _ i)
    refine ShortComplex.shortExact_of_iso ?_ hSi
    refine ShortComplex.isoMk (S.X₁.extendXIso _ hi).symm (S.X₂.extendXIso _ hi).symm
      (S.X₃.extendXIso _ hi).symm ?_ ?_
    · change (S.X₁.extendXIso _ hi).inv ≫ (HomologicalComplex.extendMap S.f _).f j' = S.f.f i ≫ _
      rw [HomologicalComplex.extendMap_f _ _ hi]
      simp
    · change (S.X₂.extendXIso _ hi).inv ≫ (HomologicalComplex.extendMap S.g _).f j' = S.g.f i ≫ _
      rw [HomologicalComplex.extendMap_f _ _ hi]
      simp
  · push Not at hj
    have h1 := S.X₁.isZero_extend_X ComplexShape.embeddingUpNat j' hj
    have h2 := S.X₂.isZero_extend_X ComplexShape.embeddingUpNat j' hj
    have h3 := S.X₃.isZero_extend_X ComplexShape.embeddingUpNat j' hj
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ h2
            mono_f := h1.mono _
            epi_g := h3.epi _ }

end Exactness

/-- A morphism of sheaves of modules injective on all sections is a monomorphism. -/
private theorem mono_of_val_app_injective {T : TopCat.{0}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{0}} {A B : SheafOfModules.{0} R}
    (φ : A ⟶ B) (h : ∀ W, Function.Injective (φ.val.app W)) : Mono φ := by
  have hloc : Presheaf.IsLocallyInjective (Opens.grothendieckTopology T)
      ((PresheafOfModules.toPresheaf R.obj).map φ.val) :=
    Presheaf.isLocallyInjective_of_injective _ _ h
  have : Sheaf.IsLocallyInjective ((SheafOfModules.toSheaf _).map φ) := hloc
  have := Sheaf.mono_of_isLocallyInjective ((SheafOfModules.toSheaf _).map φ)
  exact (SheafOfModules.toSheaf _).mono_of_mono_map ‹_›

/-- Coherence transports along an isomorphism of `𝒪_X`-modules. -/
private theorem isCoherent_of_iso' {X : Scheme.{0}} {F G : X.Modules} (e : F ≅ G)
    (hF : F.IsCoherent) : G.IsCoherent :=
  AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
    ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).prop_of_iso e
      (AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent hF))

/-! ### Degeneration on a fibre in characteristic `p` -/

section FibreDegeneration

open MMP.DeRham Stacks.Frobenius Stacks.DeRhamDirectImage
open scoped ZeroObject

attribute [local instance] additive_restrictScalars_underlyingRingSheaf

variable (n : ℕ) {R : Type} [CommRing R]
    {𝒳 : Scheme.{0}} (g : 𝒳 ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n g]
    (hg : IsProjective g) (𝒟 : MMP.Mori.Divisor 𝒳) (h𝒟 : 𝒟.IsRelativeSNC n g)
    (s : Spec (CommRingCat.of R)) (p : ℕ) [Fact p.Prime] (hnp : n < p)
    [Finite ((Spec (CommRingCat.of R)).residueField s)]
    [CharP ((Spec (CommRingCat.of R)).residueField s) p]
    (ρ : R →+* (Spec (CommRingCat.of R)).residueField s)
    (hρ : Spec.map (CommRingCat.ofHom ρ) = (Spec (CommRingCat.of R)).fromSpecResidueField s)
    (φ : R →+* TruncatedWittVector p 2 ((Spec (CommRingCat.of R)).residueField s))
    (hφ : ∀ r, (φ r).coeff 0 = ρ r)
    [SmoothOfRelativeDimension n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))]
    (Ds : MMP.Mori.Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hDs : Ds.IsRelativeSNC n (pullback.snd _ _))
    (hsupp : (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
      (𝒟.supp : Set 𝒳) = (Ds.supp : Set _))

/-- Reindexing the sum of a Künneth-type decomposition: a sum over `q ≤ n` of terms vanishing in
negative degree and for `q > n` is the sum over `q ≤ k`. -/
private theorem finrankHyp_sum_fin_eq_sum_range (k : ℕ) (F : ℕ → ℤ → ℕ)
    (hneg : ∀ q (j : ℤ), j < 0 → F q j = 0) (hbig : ∀ q (j : ℤ), n < q → F q j = 0) :
    ∑ q : Fin (n + 1), F q ((k : ℤ) - ((q : ℕ) : ℤ)) =
      ∑ q ∈ Finset.range (k + 1), F q ((k - q : ℕ) : ℤ) := by
  rw [Fin.sum_univ_eq_sum_range (fun q => F q ((k : ℤ) - (q : ℤ))) (n + 1)]
  rw [← Finset.sum_subset (Finset.range_mono (min_le_left (n + 1) (k + 1))) ?_,
    ← Finset.sum_subset (Finset.range_mono (min_le_right (n + 1) (k + 1))) ?_]
  · refine Finset.sum_congr rfl fun q hq => ?_
    simp only [Finset.mem_range, lt_min_iff] at hq
    rw [Nat.cast_sub (by omega : q ≤ k)]
  · intro q hq hq'
    simp only [Finset.mem_range] at hq hq'
    exact hbig q _ (by omega)
  · intro q hq hq'
    simp only [Finset.mem_range] at hq hq'
    exact hneg q _ (by omega)

/-- Modules over the fibre read as modules over the inverse image of the structure sheaf of the
base point. -/
private noncomputable def finrankHyp_G :
    (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules ⥤
      SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0}
          (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base).obj
            (Spec ((Spec (CommRingCat.of R)).residueField s)).sheaf)) :=
  pushforward (toInverseImageBase
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))

private instance finrankHyp_G_additive : (finrankHyp_G g s).Additive :=
  inferInstanceAs (pushforward (toInverseImageBase
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))).Additive

private instance finrankHyp_G_preservesFiniteLimits : PreservesFiniteLimits (finrankHyp_G g s) :=
  preservesFiniteLimits_pushforward_toInverseImageBase _

private instance finrankHyp_G_preservesFiniteColimits :
    PreservesFiniteColimits (finrankHyp_G g s) :=
  preservesFiniteColimits_pushforward_toInverseImageBase _

section FinrankHypAux

variable [IsProper g]
    [HasDerivedCategory.{0}
      (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules]
    (hV : IsInCharacteristic (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p)
    (d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q) ⟶
        (Scheme.Modules.pushforward (absoluteFrobenius _ p hV)).obj
          (G1.logModule n (pullback.snd _ _) Ds hDs ⊤ (q + 1)))
    (hd : ∀ q, d q ≫ d (q + 1) = 0)
    (hdR : ∀ (q : ℕ) (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opens)
        (x : Γ(G1.logModule n (pullback.snd _ _) Ds hDs ⊤ q, W)),
        (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs ⊤ (q + 1)).obj (op W))
          from (d q).app W x).1 =
        ((Scheme.Hom.deRhamComplex ((G1.LU Ds).ι ≫ pullback.snd _ _)).d q (q + 1)).val.app
          (op ((G1.LU Ds).ι ⁻¹ᵁ W))
          (show ↥((G1.logModuleSubmodule n (pullback.snd _ _) Ds hDs ⊤ q).obj (op W))
            from x).1)
    (hp : (p : (Spec (CommRingCat.of R)).residueField s) = 0)
    (hpt : ∀ a b : Spec ((Spec (CommRingCat.of R)).residueField s), a = b)
    {m : ℕ} (hm : 1 ≤ m) (hκ : ∀ x : (Spec (CommRingCat.of R)).residueField s, x ^ p ^ m = x)
    (i : relativeLogDeRhamComplex n (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
      Ds hDs Ds.suppIdeal ⟶
        Scheme.Hom.deRhamComplex (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hi : ∀ (q : ℕ) (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n (pullback.snd g _) Ds hDs Ds.suppIdeal).X q).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι Ds.supp.compl)
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))).f q).val.app W
          ((i.f q).val.app W ω) = ω.1)
    (Dc : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0}
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base).obj
          (Spec ((Spec (CommRingCat.of R)).residueField s)).sheaf))) ℕ)
    (qc : Scheme.Hom.deRhamComplex (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
      ⟶ Dc) (hiq : i ≫ qc = 0) (hq : IsColimit (CokernelCofork.ofπ qc hiq))

include hi in
/-- The pinned inclusion `Ω^•(log 𝒟_s)(-𝒟_s) ⟶ Ω^•` is a monomorphism. -/
private theorem finrankHyp_mono : Mono i := by
  have hmonoif : ∀ q, Mono (i.f q) := fun q =>
    mono_of_val_app_injective _ fun W a b hab => Subtype.ext (by
      have h := congrArg (fun z => ((Stacks.DeRhamPullback.deRhamPushforwardChain
        (Scheme.Opens.ι Ds.supp.compl)
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))).f q).val.app W z) hab
      dsimp only at h
      rwa [hi, hi] at h)
  exact HomologicalComplex.mono_of_mono_f _ hmonoif

/-- The inclusion of twisted forms into regular forms is a monomorphism. -/
private theorem finrankHyp_monoT :
    Mono (twistedToRegularComplex
      (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR)) :=
  HomologicalComplex.mono_of_mono_f _ fun q =>
    mono_of_app_injective _ fun W => twistedToRegular_app_injective
      (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR) q _

/-- The short exact sequence `0 ⟶ twisted forms ⟶ regular forms ⟶ cokernel ⟶ 0`. -/
private theorem finrankHyp_shortExactT :
    (ShortComplex.mk (twistedToRegularComplex
      (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR))
      (cokernel.π _) (cokernel.condition _)).ShortExact := by
  haveI := finrankHyp_monoT n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

/-- The comparison of the twisted logarithmic forms, termwise. -/
private noncomputable def finrankHyp_αX (q : ℕ) :
    (((finrankHyp_G g s).mapHomologicalComplex
        _).obj (twistedComplex1
          (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR))).X q ≅
      (((_root_.SheafOfModules.restrictScalars.{0} (frobeniusRingSheafIso
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm
          hκ).hom).mapHomologicalComplex _).obj (relativeLogDeRhamComplex n
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) Ds hDs
          Ds.suppIdeal)).X q :=
  frobTwistIso (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm
      hκ (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR).hV
      (twistedLog (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd
        hdR) 1 q) ≪≫
    (_root_.SheafOfModules.restrictScalars.{0} (frobeniusRingSheafIso
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm
          hκ).hom).mapIso ((finrankHyp_G g s).mapIso
        (twistedLogFibreIso n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q) ≪≫
      (relLogXIso n _ Ds hDs true q).symm)

/-- The comparison of the regular forms. -/
private noncomputable def finrankHyp_β :
    ((finrankHyp_G g s).mapHomologicalComplex
        _).obj (ordinaryData
          (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR)).complex ≅
      ((_root_.SheafOfModules.restrictScalars.{0} (frobeniusRingSheafIso
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm
          hκ).hom).mapHomologicalComplex _).obj
        (Scheme.Hom.deRhamComplex (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))) :=
  frobDeRhamComplexIso (k := (Spec (CommRingCat.of R)).residueField s)
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm hκ
    (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR).hV

include hi in
/-- The square comparing the two inclusions. -/
private theorem finrankHyp_sq (q : ℕ) :
    (finrankHyp_αX n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ q).hom ≫
        (_root_.SheafOfModules.restrictScalars.{0} (frobeniusRingSheafIso
          (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm
            hκ).hom).map (i.f q) =
      (finrankHyp_G g s).map
          ((twistedToRegularComplex
            (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd
              hdR)).f q) ≫
        (finrankHyp_β n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ).hom.f q := by
  have hc := twistedToRegular_fibre_comm n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd
    hdR q i (hi q)
  ext W x
  exact (congrArg (fun φ => φ.val.app W x) hc).symm

include hi in
/-- The termwise comparison of the twisted logarithmic forms commutes with the differentials. -/
private theorem finrankHyp_comm (a b : ℕ) (hab : (ComplexShape.up ℕ).Rel a b) :
    (finrankHyp_αX n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ a).hom ≫
        (((_root_.SheafOfModules.restrictScalars.{0} (frobeniusRingSheafIso
          (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm
            hκ).hom).mapHomologicalComplex _).obj (relativeLogDeRhamComplex n
          (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) Ds hDs
            Ds.suppIdeal)).d a b =
      (((finrankHyp_G g s).mapHomologicalComplex
          _).obj (twistedComplex1
            (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd
              hdR))).d a b ≫
        (finrankHyp_αX n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ b).hom := by
  obtain rfl : a + 1 = b := hab
  let FD := fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR
  let G := finrankHyp_G g s
  let E := _root_.SheafOfModules.restrictScalars.{0} (frobeniusRingSheafIso
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm hκ).hom
  haveI : E.IsEquivalence := (restrictScalarsEquivalence _ (frobeniusRingSheafIso
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm
      hκ)).isEquivalence_functor
  haveI := finrankHyp_mono n g s Ds hDs i hi
  let αX := finrankHyp_αX n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ
  let β := finrankHyp_β n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ
  have hsq : ∀ q, (αX q).hom ≫ E.map (i.f q) =
      G.map ((twistedToRegularComplex FD).f q) ≫ β.hom.f q :=
    finrankHyp_sq n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ i hi
  haveI : Mono (E.map (i.f (a + 1))) := inferInstance
  refine (cancel_mono (E.map (i.f (a + 1)))).1 ?_
  have hb : β.hom.f a ≫ E.map ((Scheme.Hom.deRhamComplex
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))).d a (a + 1)) =
      G.map ((ordinaryData FD).complex.d a (a + 1)) ≫ β.hom.f (a + 1) :=
    β.hom.comm a (a + 1)
  have hT := (twistedToRegularComplex FD).comm a (a + 1)
  have hI := i.comm a (a + 1)
  change ((αX a).hom ≫ E.map ((relativeLogDeRhamComplex n
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) Ds hDs
        Ds.suppIdeal).d a (a + 1))) ≫ E.map (i.f (a + 1)) =
    (G.map ((twistedComplex1 FD).d a (a + 1)) ≫ (αX (a + 1)).hom) ≫ E.map (i.f (a + 1))
  rw [Category.assoc, ← E.map_comp, ← hI, E.map_comp, ← Category.assoc, hsq a,
    Category.assoc, hb, ← Category.assoc, ← G.map_comp, hT, G.map_comp, Category.assoc,
    ← hsq (a + 1), Category.assoc]

/-- The comparison of the restriction complexes. -/
private noncomputable def finrankHyp_ψ :
    ((finrankHyp_G g s).mapHomologicalComplex
        _).obj (cokernel (twistedToRegularComplex
          (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR))) ≅
      ((_root_.SheafOfModules.restrictScalars.{0} (frobeniusRingSheafIso
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm
          hκ).hom).mapHomologicalComplex _).obj Dc :=
  let FD := fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR
  let G := finrankHyp_G g s
  let E := _root_.SheafOfModules.restrictScalars.{0} (frobeniusRingSheafIso
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm hκ).hom
  haveI : E.IsEquivalence := (restrictScalarsEquivalence _ (frobeniusRingSheafIso
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm
      hκ)).isEquivalence_functor
  haveI := finrankHyp_monoT n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR
  haveI := finrankHyp_mono n g s Ds hDs i hi
  have hSi : (ShortComplex.mk i qc hiq).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hq)
      inferInstance (epi_of_isColimit_cofork hq)
  have hS1 := (finrankHyp_shortExactT n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd
    hdR).map_of_exact (G.mapHomologicalComplex _)
  have hS2 := hSi.map_of_exact (E.mapHomologicalComplex _)
  let αX := finrankHyp_αX n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ
  let β := finrankHyp_β n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ
  let α : (G.mapHomologicalComplex _).obj (twistedComplex1 FD) ≅
      (E.mapHomologicalComplex _).obj (relativeLogDeRhamComplex n
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) Ds hDs Ds.suppIdeal) :=
    HomologicalComplex.Hom.isoOfComponents αX
      (finrankHyp_comm n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ i hi)
  IsColimit.coconePointsIsoOfNatIso hS1.gIsCokernel hS2.gIsCokernel
    (parallelPair.ext α β (by
      refine HomologicalComplex.hom_ext _ _ fun a => ?_
      change G.map ((twistedToRegularComplex FD).f a) ≫ β.hom.f a = (αX a).hom ≫ E.map (i.f a)
      exact (finrankHyp_sq n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ i hi
        a).symm) (by
      change (0 : _ ⟶ _) ≫ β.hom = α.hom ≫ (0 : _ ⟶ _)
      rw [zero_comp, comp_zero]))

/-- The comparison of the restriction complexes, extended to `ℤ`-indexed bounded below
complexes. -/
private noncomputable def finrankHyp_eL :
    (finrankHyp_G g s).mapCochainComplexPlus.obj
        (⟨(cokernel (twistedToRegularComplex
          (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd
            hdR))).extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ :
            CochainComplex.Plus (pullback g
              ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules) ≅
      (_root_.SheafOfModules.restrictScalars.{0} (frobeniusRingSheafIso
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm
          hκ).hom).mapCochainComplexPlus.obj
        (⟨Dc.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ :
            CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
              ((TopCat.Sheaf.pullback CommRingCat.{0}
                (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base).obj
                  (Spec ((Spec (CommRingCat.of R)).residueField s)).sheaf)))) :=
  let G := finrankHyp_G g s
  let E := _root_.SheafOfModules.restrictScalars.{0} (frobeniusRingSheafIso
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm hκ).hom
  haveI : E.IsEquivalence := (restrictScalarsEquivalence _ (frobeniusRingSheafIso
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) p hp hpt hm
      hκ)).isEquivalence_functor
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (mapHomologicalComplexExtendIso G (cokernel (twistedToRegularComplex
        (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR)))
        ComplexShape.embeddingUpNat ≪≫
      (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
        (finrankHyp_ψ n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ i hi Dc
          qc hiq hq) ≪≫
      (mapHomologicalComplexExtendIso E Dc ComplexShape.embeddingUpNat).symm)

/-- The decomposition of the restriction complex of the fibre in the derived category. -/
private noncomputable def finrankHyp_Φ :
    DerivedCategory.Q.obj ((⟨(cokernel (twistedToRegularComplex
          (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd
            hdR))).extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ :
            CochainComplex.Plus (pullback g
              ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules).obj) ≅
      ⨁ fun q : Fin (n + 1) => (DerivedCategory.singleFunctor _ (q : ℤ)).obj (cokernel
        (twistedToRegular
          (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR)
            1 q le_rfl)) :=
  let FD := fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR
  have hSext := shortExact_map_extendFunctor
    (finrankHyp_shortExactT n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR)
  let e0 : cokernel (coneMap FD) ≅
      (cokernel (twistedToRegularComplex FD)).extend ComplexShape.embeddingUpNat :=
    (colimit.isColimit (parallelPair (coneMap FD) 0)).coconePointUniqueUpToIso hSext.gIsCokernel
  (DerivedCategory.Q.mapIso e0).symm ≪≫ (nonempty_iso_cone_of_lift FD).some.symm

include hg h𝒟 hnp hρ hφ hsupp hV d hd hdR hi hq in
/-- The terms of the restriction complex of a fibre vanish above the relative dimension. -/
private theorem finrankHyp_isZero (q : ℕ) (hnq : n < q) : IsZero (Dc.X q) := by
  let FD := fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR
  have h0 := Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) n q hnq
  have h1 : IsZero (cokernel (twistedToRegular FD 1 q le_rfl)) := IsZero.of_epi (cokernel.π _) h0
  exact ((finrankHyp_G g s).map_isZero h1).of_iso
      (cokernelFibreIso n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q i (hi q) Dc qc hiq
        hq).symm

include hg h𝒟 hnp hρ hφ hsupp hV d hd hdR hi hq in
/-- The cohomology of the terms of the restriction complex of a fibre is finite dimensional. -/
private theorem finrankHyp_moduleFinite
    [IsLocallyNoetherian (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s))]
    (q : ℕ) (j : ℤ) :
    Module.Finite Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
      (Hc (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
        (single0 _ (Dc.X q)) j) := by
  let FD := fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR
  let G : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules ⥤
      SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0}
          (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base).obj
            (Spec ((Spec (CommRingCat.of R)).residueField s)).sheaf)) :=
    finrankHyp_G g s
  have hcoh : (cokernel (twistedToRegular FD 1 q le_rfl)).IsCoherent := by
    haveI : (twistedLog FD 1 q).IsCoherent := isCoherent_of_iso'
      (twistedLogFibreIso n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q).symm
      (G1.logModule_isCoherent hDs true q)
    haveI : ((pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).relativeDifferentialForms
        ((q : ℕ) : ℤ)).IsCoherent :=
      Scheme.Hom.isCoherent_relativeDifferentialForms _ q
    exact AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel _
  have hK : ∀ k', ∃ M : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules,
      M.IsCoherent ∧ Nonempty ((single0 _ (G.obj (cokernel (twistedToRegular FD 1 q le_rfl)))).1.X
        k' ≅ G.obj M) := by
    intro k'
    by_cases hk : k' = 0
    · subst hk
      exact ⟨_, hcoh, ⟨HomologicalComplex.singleObjXSelf _ 0 _⟩⟩
    · exact ⟨0, Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero (isZero_zero _),
        ⟨(HomologicalComplex.isZero_single_obj_X _ _ _ _ hk).iso (isZero_pushforward_zero _)⟩⟩
  haveI := AlgebraicGeometry.DeRhamTypeComplex.moduleFinite_homology_derivedSections
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) _ hK j
  have e1 := (nonempty_hcIsoHypercohomology
    (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
    (single0 _ (G.obj (cokernel (twistedToRegular FD 1 q le_rfl)))) j).some
  have e2 := hypIsoOfIso (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
    (L := single0 _ (G.obj (cokernel (twistedToRegular FD 1 q le_rfl))))
    (L' := single0 _ (Dc.X q))
    ((ObjectProperty.fullyFaithfulι _).preimageIso
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        (cokernelFibreIso n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q i (hi q) Dc qc
          hiq hq))) j
  exact Module.Finite.equiv (e1.symm.toLinearEquiv.trans e2.toLinearEquiv)

end FinrankHypAux

include hg h𝒟 hnp hρ hφ hsupp in
/-- **Degeneration of the restriction complex on a fibre in characteristic `p`.** Let `g` be
smooth projective of relative dimension `n` with a relative snc divisor `𝒟`, and `s` a point with
finite residue field of characteristic `p > n` whose residue map lifts to `W₂(κ(s))`. For a
cokernel `𝒟_s^•` of a pinned inclusion `Ω^•(log 𝒟_s)(-𝒟_s) ⟶ Ω^•` on the fibre,
`dim ℍ^k(𝒟_s^•) = ∑_{q ≤ k} dim H^{k-q}(𝒟_s^q)`. -/
private theorem finrank_hyp_cokernel_fibre_eq_sum
    (i : relativeLogDeRhamComplex n (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
      Ds hDs Ds.suppIdeal ⟶
        Scheme.Hom.deRhamComplex (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
    (hi : ∀ (q : ℕ) (W : (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n (pullback.snd g _) Ds hDs Ds.suppIdeal).X q).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι Ds.supp.compl)
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))).f q).val.app W
          ((i.f q).val.app W ω) = ω.1)
    (Dc : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0}
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base).obj
          (Spec ((Spec (CommRingCat.of R)).residueField s)).sheaf))) ℕ)
    (qc : Scheme.Hom.deRhamComplex (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
      ⟶ Dc) (hiq : i ≫ qc = 0) (hq : IsColimit (CokernelCofork.ofπ qc hiq)) (k : ℕ) :
    Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
        (Hc (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
          ⟨Dc.extend ComplexShape.embeddingUpNat, 0,
            CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
      ∑ q ∈ Finset.range (k + 1),
        Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
          (Hc (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
            (single0 _ (Dc.X q)) ((k - q : ℕ) : ℤ)) := by
  classical
  haveI : IsProper g := hg.isProper
  have hV := isInCharacteristic_pullback_fromSpecResidueField g s p
  obtain ⟨d, hd, hdR⟩ := exists_frobeniusLinear_logDeRham_d
    (k := (Spec (CommRingCat.of R)).residueField s) n (pullback.snd _ _) Ds hDs false p hV
  letI : HasDerivedCategory.{0}
      (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules :=
    Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _
  letI : Fintype ((Spec (CommRingCat.of R)).residueField s) := Fintype.ofFinite _
  obtain ⟨m, -, hcard⟩ := FiniteField.card ((Spec (CommRingCat.of R)).residueField s) p
  have hκ : ∀ x : (Spec (CommRingCat.of R)).residueField s, x ^ p ^ (m : ℕ) = x := fun x => by
    rw [← hcard, FiniteField.pow_card]
  have hp : (p : (Spec (CommRingCat.of R)).residueField s) = 0 := CharP.cast_eq_zero _ p
  have hpt : ∀ a b : Spec ((Spec (CommRingCat.of R)).residueField s), a = b :=
    fun a b => Subsingleton.elim a b
  have hm : 1 ≤ (m : ℕ) := m.pos
  have hF : IsField Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤) :=
    MulEquiv.isField (Field.toIsField ((Spec (CommRingCat.of R)).residueField s))
      (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.toMulEquiv
  haveI : Nontrivial Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤) := ⟨hF.exists_pair_ne⟩
  haveI : StrongRankCondition Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤) :=
    commRing_strongRankCondition _
  haveI : IsLocallyNoetherian (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
  let X : CochainComplex.Plus (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).Modules :=
    ⟨(cokernel (twistedToRegularComplex
      (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd
        hdR))).extend ComplexShape.embeddingUpNat, 0,
      CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩
  let L : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0}
        (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base).obj
          (Spec ((Spec (CommRingCat.of R)).residueField s)).sheaf))) :=
    ⟨Dc.extend ComplexShape.embeddingUpNat, 0,
      CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩
  have key := finrank_hyp_eq_sum_of_split
    (f := pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)) (p := p) (hp := hp)
    (hpt := hpt) (hm := hm) (hκ := hκ) (n := n) (X := X) (L := L)
    (M := fun q : Fin (n + 1) => cokernel (twistedToRegular
      (fibreFrobeniusSplittingData n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR) 1 q le_rfl))
    (Φ := finrankHyp_Φ n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR)
    (eL := finrankHyp_eL n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR hp hpt hm hκ i hi
      Dc qc hiq hq)
    (Mt := fun q : Fin (n + 1) => Dc.X q)
    (eM := fun q => cokernelFibreIso n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR q i
      (hi q) Dc qc hiq hq)
    (hfin := fun q j => finrankHyp_moduleFinite n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd
      hdR i hi Dc qc hiq hq q j)
    (hfree := fun _ _ => by letI := hF.toField; exact Module.Free.of_divisionRing _ _) (k := k)
  exact key.trans (finrankHyp_sum_fin_eq_sum_range n k
    (fun q j => Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
      (Hc (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s))
        (single0 _ (Dc.X q)) j))
    (fun _ _ hj => finrank_hyp_single0_eq_zero _ _ _ (Or.inl hj))
    (fun q _ hnq => finrank_hyp_single0_eq_zero _ _ _ (Or.inr
      (finrankHyp_isZero n g hg 𝒟 h𝒟 s p hnp ρ hρ φ hφ Ds hDs hsupp hV d hd hdR i hi Dc qc hiq hq
        q hnq))))

end FibreDegeneration

/-! ### Finiteness of the cohomology of a quotient complex -/

section QuotientCohomology

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
  {A B C : ℤ → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)] [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  (dA : ∀ i, A i →ₗ[R] A (i + 1)) (dB : ∀ i, B i →ₗ[R] B (i + 1)) (dC : ∀ i, C i →ₗ[R] C (i + 1))
  (ι : ∀ i, A i →ₗ[R] B i) (π : ∀ i, B i →ₗ[R] C i)
  (hι : ∀ i, Function.Injective (ι i)) (hπ : ∀ i, Function.Surjective (π i))
  (hex : ∀ i, LinearMap.ker (π i) = LinearMap.range (ι i))
  (hιd : ∀ i x, ι (i + 1) (dA i x) = dB i (ι i x)) (hπd : ∀ i x, π (i + 1) (dB i x) = dC i (π i x))
  (hddB : ∀ i x, dB (i + 1) (dB i x) = 0)

include hι hπ hex hιd hπd hddB in
/-- **The cohomology of the middle of a short exact sequence of complexes is finite** when that
of the sub- and of the quotient complex is, over a Noetherian ring. -/
private theorem moduleFinite_homologyAt_middle (i : ℤ)
    (hA : Module.Finite R (homologyAt (dA i) (dA (i + 1))))
    (hC : Module.Finite R (homologyAt (dC i) (dC (i + 1)))) :
    Module.Finite R (homologyAt (dB i) (dB (i + 1))) := by
  classical
  have hπk : ∀ b : LinearMap.ker (dB (i + 1)), π (i + 1) b.1 ∈ LinearMap.ker (dC (i + 1)) :=
    fun b => by rw [LinearMap.mem_ker, ← hπd, LinearMap.mem_ker.mp b.2, map_zero]
  let πk : LinearMap.ker (dB (i + 1)) →ₗ[R] LinearMap.ker (dC (i + 1)) :=
    LinearMap.codRestrict _ ((π (i + 1)).comp (LinearMap.ker (dB (i + 1))).subtype) hπk
  let πH : homologyAt (dB i) (dB (i + 1)) →ₗ[R] homologyAt (dC i) (dC (i + 1)) :=
    Submodule.mapQ _ _ πk (by
      rintro b ⟨b', hb'⟩
      refine ⟨π i b', ?_⟩
      change dC i (π i b') = π (i + 1) b.1
      rw [← hπd, hb']
      rfl)
  have hιk : ∀ a : LinearMap.ker (dA (i + 1)), ι (i + 1) a.1 ∈ LinearMap.ker (dB (i + 1)) :=
    fun a => by rw [LinearMap.mem_ker, ← hιd, LinearMap.mem_ker.mp a.2, map_zero]
  let ιk : LinearMap.ker (dA (i + 1)) →ₗ[R] LinearMap.ker (dB (i + 1)) :=
    LinearMap.codRestrict _ ((ι (i + 1)).comp (LinearMap.ker (dA (i + 1))).subtype) hιk
  let ιH : homologyAt (dA i) (dA (i + 1)) →ₗ[R] homologyAt (dB i) (dB (i + 1)) :=
    Submodule.mapQ _ _ ιk (by
      rintro a ⟨a', ha'⟩
      refine ⟨ι i a', ?_⟩
      change dB i (ι i a') = ι (i + 1) a.1
      rw [← hιd, ha']
      rfl)
  have hker : LinearMap.ker πH ≤ LinearMap.range ιH := by
    intro w hw
    induction w using Submodule.Quotient.induction_on with
    | H b =>
      rw [LinearMap.mem_ker] at hw
      change Submodule.Quotient.mk (πk b) = 0 at hw
      rw [Submodule.Quotient.mk_eq_zero] at hw
      obtain ⟨c, hc⟩ := hw
      obtain ⟨b', rfl⟩ := hπ i c
      have hb : b.1 - dB i b' ∈ LinearMap.ker (π (i + 1)) := by
        rw [LinearMap.mem_ker, map_sub, hπd]
        change π (i + 1) b.1 - dC i (π i b') = 0
        rw [hc]
        exact sub_self _
      rw [hex] at hb
      obtain ⟨a, ha⟩ := hb
      have hak : a ∈ LinearMap.ker (dA (i + 1)) := by
        rw [LinearMap.mem_ker]
        apply hι
        rw [hιd, ha, map_sub, LinearMap.mem_ker.mp b.2, hddB, sub_zero, map_zero]
      refine ⟨Submodule.Quotient.mk ⟨a, hak⟩, ?_⟩
      change Submodule.Quotient.mk (ιk ⟨a, hak⟩) = Submodule.Quotient.mk b
      refine (Submodule.Quotient.eq _).2 ⟨-b', ?_⟩
      change dB i (-b') = ι (i + 1) a - b.1
      rw [map_neg, ha, sub_sub_cancel_left]
  haveI : Module.Finite R (LinearMap.range ιH) := Module.Finite.range ιH
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker πH ?_ ?_⟩
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq]
    have e : LinearMap.ker πH = (Submodule.comap (LinearMap.range ιH).subtype
        (LinearMap.ker πH)).map (LinearMap.range ιH).subtype := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hker]
    rw [e]
    exact (IsNoetherian.noetherian _).map _

end QuotientCohomology

/-! ### Twisted logarithmic forms have no poles -/

section RegularTwisted

open MMP.Mori.Divisor.LogSpreadingProof.G1

/-- A product over the sorted list of a finite set is the product over the set. -/
private theorem prod_map_sort {α M : Type*} [CommMonoid M] [LinearOrder α] (K : Finset α)
    (g : α → M) : ((K.sort (· ≤ ·)).map g).prod = ∏ i ∈ K, g i := by
  rw [Finset.prod_eq_multiset_prod, ← Finset.sort_eq K (· ≤ ·), Multiset.map_coe,
    Multiset.prod_coe]

variable {X S : Scheme.{0}} (f : X ⟶ S) (D : MMP.Mori.Divisor X)

/-- The restriction of forms to the complement `U` of `D`, as a unital homomorphism of graded
algebras `Ω^•_{X/S} ⟶ j_*Ω^•_{U/S}`. -/
private noncomputable abbrev resForms :=
  Scheme.Hom.deRhamFormsPushforwardHom (LU D).ι f ((LU D).ι ≫ f) (𝟙 S)
    (Category.comp_id _).symm

/-- The restriction of forms to `U ∩ W`, on the total algebras. -/
private noncomputable def resTotal (W : X.Opens) :
    (G1.TB f).Total (op W) →+* (G1.TB ((LU D).ι ≫ f)).Total (op ((LU D).ι ⁻¹ᵁ W)) :=
  Stacks.GradedAlgebra.totalRingHom
    (SheafOfModules.GradedAlgebra.UnitalHom.toPresheafGradedAlgebraHom (resForms f D)) (op W)

private theorem resTotal_incl (W : X.Opens) (k : ℤ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece k).val.obj (op W)) :
    resTotal f D W ((G1.TB f).incl k x) =
      (G1.TB ((LU D).ι ≫ f)).incl k (((resForms f D).app k).val.app (op W) x) :=
  Stacks.GradedAlgebra.totalRingHom_incl
    (SheafOfModules.GradedAlgebra.UnitalHom.toPresheafGradedAlgebraHom (resForms f D)) (op W) k x

private theorem resTotal_sm (W : X.Opens) (r : Γ(X, W)) :
    resTotal f D W ((G1.TB f).structureMap (op W) r) =
      smU (f := f) (D := D) _ (((LU D).ι.app W).hom r) := by
  have h := congrArg (fun φ => (φ.app (op W)).hom r)
    (Stacks.GradedAlgebra.structureHom_totalPresheafMap
      (SheafOfModules.GradedAlgebra.UnitalHom.toPresheafGradedAlgebraHom (resForms f D)))
  simp only [NatTrans.comp_app, RingCat.hom_comp, RingHom.comp_apply] at h
  exact h

/-- The differential of a function on `X`, as a form of degree one. -/
private noncomputable abbrev dX (W : X.Opens) (a : Γ(X, W)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece 1).val.obj (op W) :=
  (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials f)).val.app (op W)
    ((Scheme.Hom.universalRelativeDerivation f).d (X := op W) a)

private theorem resTotal_incl_dX (W : X.Opens) (a : Γ(X, W)) :
    resTotal f D W ((G1.TB f).incl 1 (dX f W a)) =
      (G1.TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ (((LU D).ι.app W).hom a)) :=
  (resTotal_incl f D W 1 _).trans (congrArg ((G1.TB ((LU D).ι ≫ f)).incl 1)
    (Scheme.Hom.deRhamFormsPushforwardHom_exactOne (LU D).ι f ((LU D).ι ≫ f) (𝟙 S) _ (op W) a))

private theorem proj_resTotal (W : X.Opens) (p : ℤ) (x : (G1.TB f).Total (op W)) :
    (G1.TB ((LU D).ι ≫ f)).proj _ p (resTotal f D W x) =
      ((resForms f D).app p).val.app (op W) ((G1.TB f).proj _ p x) := by
  induction x using (G1.TB f).incl_induction with
  | zero =>
    exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans
      ((map_zero _).symm.trans (congrArg _ (map_zero _).symm))
  | incl k y =>
    refine (congrArg _ (resTotal_incl f D W k y)).trans ?_
    by_cases hk : k = p
    · subst hk
      exact ((G1.TB _).proj_incl _ _ _).trans (congrArg _ ((G1.TB f).proj_incl _ _ _).symm)
    · exact (proj_incl_of_ne hk _).trans
        ((map_zero _).symm.trans (congrArg _ (proj_incl_of_ne hk _).symm))
  | add x y hx hy =>
    exact ((congrArg _ (map_add _ _ _)).trans (map_add _ _ _)).trans
      ((congrArg₂ (· + ·) hx hy).trans ((map_add _ _ _).symm.trans
        (congrArg _ (map_add _ _ _).symm)))

variable {n : ℕ} {A : CommRingCat.{0}} (g : X ⟶ Spec A) [SmoothOfRelativeDimension n g]
  [IsRegularRing A]

/-- **Logarithmic combinations restricting regular forms.** On a logarithmic chart, the
logarithmic combination `∑_K a_K θ_K` whose coefficients satisfy `c_K = a_K ∏_{i ∈ K} σᵢ` off the
divisor is the restriction of the regular form `∑_K c_K dt_K`. -/
private theorem resTotal_sum_eq_combo (cL : G1.LogData n g D) (p : ℕ) {W' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ cL.W) (a c : {K : Finset (Fin n) // K.card = p} → Γ(X, W'))
    (hc : ∀ K, ((LU D).ι.app W').hom (c K) =
      ((LU D).ι.app W').hom (a K) * ∏ i ∈ K.1, cL.σ hW' i) :
    resTotal g D W' (∑ K, (G1.TB g).structureMap _ (c K) *
      ((K.1.sort (· ≤ ·)).map fun i => (G1.TB g).incl 1
        (dX g (W' : X.Opens) ((X.presheaf.map (homOfLE hW').op).hom (cL.t i)))).prod) =
      cL.combo p hW' a := by
  let ρ : Γ(X, cL.W) →+* Γ(X, W') := (X.presheaf.map (homOfLE hW').op).hom
  let δX : Fin n → (G1.TB g).Total (op (W' : X.Opens)) := fun i =>
    (G1.TB g).incl 1 (dX g (W' : X.Opens) (ρ (cL.t i)))
  let δU : Fin n → (G1.TB ((LU D).ι ≫ g)).Total (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens))) := fun i =>
    (G1.TB ((LU D).ι ≫ g)).incl 1 (dOne g D _ (((LU D).ι.app W').hom (ρ (cL.t i))))
  have hK : ∀ K : {K : Finset (Fin n) // K.card = p},
      resTotal g D W' ((G1.TB g).structureMap _ (c K) * ((K.1.sort (· ≤ ·)).map δX).prod) =
        (G1.TB ((LU D).ι ≫ g)).structureMap _ (((LU D).ι.app W').hom (a K)) *
          ((K.1.sort (· ≤ ·)).map fun i => (G1.TB ((LU D).ι ≫ g)).totalRestrict
            ((Opens.map (LU D).ι.base).map (homOfLE hW')).op (cL.θ i)).prod := by
    intro K
    have hL : ((K.1.sort (· ≤ ·)).map fun i => (G1.TB ((LU D).ι ≫ g)).totalRestrict
        ((Opens.map (LU D).ι.base).map (homOfLE hW')).op (cL.θ i)) =
        (K.1.sort (· ≤ ·)).map fun i =>
          smU (f := g) (D := D) _ (cL.σ hW' i) * δU i :=
      List.map_congr_left fun i _ => cL.totalRestrict_θ hW' i
    have hR : ((K.1.sort (· ≤ ·)).map fun i => resTotal g D W' (δX i)) =
        (K.1.sort (· ≤ ·)).map δU :=
      List.map_congr_left fun i _ => resTotal_incl_dX g D W' (ρ (cL.t i))
    have e1 : resTotal g D W' (((K.1.sort (· ≤ ·)).map δX).prod) =
        ((K.1.sort (· ≤ ·)).map δU).prod :=
      (map_list_prod _ _).trans (congrArg List.prod (List.map_map.trans hR))
    have e2 := prod_map_mul_of_commute (smU (f := g) (D := D) ((LU D).ι ⁻¹ᵁ (W' : X.Opens)))
      (fun r z => (G1.TB ((LU D).ι ≫ g)).structureMap_commutes _ r z) (cL.σ hW') δU
      (K.1.sort (· ≤ ·))
    have e3 : smU (f := g) (D := D) _ (((LU D).ι.app W').hom (a K)) *
        smU (f := g) (D := D) _ (((K.1.sort (· ≤ ·)).map (cL.σ hW')).prod) =
        smU (f := g) (D := D) _ (((LU D).ι.app W').hom (c K)) := by
      rw [← map_mul, prod_map_sort K.1 (cL.σ hW'), ← hc K]
    calc resTotal g D W' ((G1.TB g).structureMap _ (c K) * ((K.1.sort (· ≤ ·)).map δX).prod)
        = smU (f := g) (D := D) _ (((LU D).ι.app W').hom (c K)) *
            ((K.1.sort (· ≤ ·)).map δU).prod :=
          (map_mul _ _ _).trans (congrArg₂ (· * ·) (resTotal_sm g D W' _) e1)
      _ = (smU (f := g) (D := D) _ (((LU D).ι.app W').hom (a K)) *
            smU (f := g) (D := D) _ (((K.1.sort (· ≤ ·)).map (cL.σ hW')).prod)) *
            ((K.1.sort (· ≤ ·)).map δU).prod := by rw [e3]
      _ = _ := by rw [mul_assoc, ← e2, ← hL]; rfl
  exact (map_sum (resTotal g D W') _ _).trans (Finset.sum_congr rfl fun K _ => hK K)

/-- **Twisted logarithmic forms have no poles.** On an affine open `W'` of a weak chart, a form of
`Ω^p(log D)(-D)` is the restriction of a regular form: on the chart it is `∑_K a_K h θ_K` with
`h = t₁ ⋯ t_r`, and `h θ_K = (∏_{i ∉ K} tᵢ) dt_K`. -/
private theorem exists_resForms_eq_of_mem_twisted (hD : D.IsRelativeSNC n g)
    (hcomp : ∀ ξ : X, ξ ∈ (D.supp : Set X) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)
    (c : WeakChart g n (D.supp : Set X)) (p : ℕ) {W' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ (c.toLogData g D).W)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ g)).piece (p : ℤ)).val.obj
      (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens))))
    (hω : ω ∈ relativeLogForms n g D hD D.suppIdeal p W') :
    ∃ y : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj
        (op (W' : X.Opens)),
      ((resForms g D).app (p : ℤ)).val.app (op (W' : X.Opens)) y = ω := by
  classical
  obtain ⟨a, ha⟩ := ((c.hasLogBasis g D hD hcomp p hW').2.2.2 ω).1 hω
  set cL := c.toLogData g D with hcL
  let ρ : Γ(X, cL.W) →+* Γ(X, W') := (X.presheaf.map (homOfLE hW').op).hom
  let m : {K : Finset (Fin n) // K.card = p} → Γ(X, W') := fun K =>
    ∏ j : Fin cL.r, if Fin.castLE cL.hr j ∈ K.1 then 1 else ρ (cL.t (Fin.castLE cL.hr j))
  let δX : Fin n → (G1.TB g).Total (op (W' : X.Opens)) := fun i =>
    (G1.TB g).incl 1 (dX g (W' : X.Opens) (ρ (cL.t i)))
  let δU : Fin n → (G1.TB ((LU D).ι ≫ g)).Total (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens))) := fun i =>
    (G1.TB ((LU D).ι ≫ g)).incl 1 (dOne g D _ (((LU D).ι.app W').hom (ρ (cL.t i))))
  let Yt : (G1.TB g).Total (op (W' : X.Opens)) := ∑ K, (G1.TB g).structureMap _ (a K * m K) *
    ((K.1.sort (· ≤ ·)).map δX).prod
  -- the coefficient identity `h ∏_{i ∈ K} σᵢ = ∏_{i ∉ K} tᵢ` off the divisor
  have hs : ∀ j : Fin cL.r, cL.σ hW' (Fin.castLE cL.hr j) *
      ((LU D).ι.app W').hom (ρ (cL.t (Fin.castLE cL.hr j))) = 1 := by
    intro j
    have h1 := congrArg ((LU D).toScheme.presheaf.map
      ((Opens.map (LU D).ι.base).map (homOfLE hW')).op).hom (WeakChart.toLogData_hs g D c j)
    rw [map_mul, map_one, app_restrict] at h1
    have h2 : cL.σ hW' (Fin.castLE cL.hr j) = (LU D).toScheme.presheaf.map
        ((Opens.map (LU D).ι.base).map (homOfLE hW')).op (cL.s j) := by
      unfold LogData.σ
      rw [dif_pos (show ((Fin.castLE cL.hr j : Fin n) : ℕ) < cL.r from j.2)]
      rfl
    rw [h2]
    exact h1
  have hσ1 : ∀ i : Fin n, ¬ (i : ℕ) < cL.r → cL.σ hW' i = 1 := fun i hi => by
    unfold LogData.σ
    rw [dif_neg hi]
  have hcoef : ∀ K : {K : Finset (Fin n) // K.card = p},
      ((LU D).ι.app W').hom (a K * m K) =
        ((LU D).ι.app W').hom (cL.h hW' * a K) * ∏ i ∈ K.1, cL.σ hW' i := by
    intro K
    have hprodσ : ∏ i ∈ K.1, cL.σ hW' i =
        ∏ j : Fin cL.r, if Fin.castLE cL.hr j ∈ K.1 then cL.σ hW' (Fin.castLE cL.hr j) else 1 := by
      rw [← Finset.prod_filter]
      have hm := Finset.prod_map (Finset.univ.filter fun j : Fin cL.r => Fin.castLE cL.hr j ∈ K.1)
        (Fin.castLEEmb cL.hr) (cL.σ hW')
      refine Eq.trans ?_ hm
      refine (Finset.prod_subset (fun i hi => ?_) fun i hiK hi' => ?_).symm
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
        exact (Finset.mem_filter.1 hj).2
      · refine hσ1 i fun hir => hi' ?_
        refine Finset.mem_map.2 ⟨⟨i, hir⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, Fin.ext rfl⟩
        have hci : Fin.castLE cL.hr ⟨i, hir⟩ = i := Fin.ext rfl
        rw [hci]
        exact hiK
    have hh : ((LU D).ι.app W').hom (cL.h hW') =
        ∏ j : Fin cL.r, ((LU D).ι.app W').hom (ρ (cL.t (Fin.castLE cL.hr j))) := by
      change ((LU D).ι.app W').hom (ρ (∏ j, cL.t (Fin.castLE cL.hr j))) = _
      rw [map_prod, map_prod]
    have e1 : ((LU D).ι.app W').hom (m K) =
        ((LU D).ι.app W').hom (cL.h hW') * ∏ i ∈ K.1, cL.σ hW' i := by
      rw [hh, hprodσ, ← Finset.prod_mul_distrib]
      change ((LU D).ι.app W').hom (∏ j : Fin cL.r, _) = _
      rw [map_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      split_ifs with hj
      · rw [map_one, mul_comm, hs j]
      · rw [mul_one]
    rw [map_mul, map_mul, e1]
    ring
  have key : resTotal g D W' Yt = cL.combo p hW' (cL.h hW' • a) :=
    resTotal_sum_eq_combo D g cL p hW' (cL.h hW' • a) (fun K => a K * m K) fun K => by
      rw [hcoef K, Pi.smul_apply, smul_eq_mul]
  exact ⟨(G1.TB g).proj _ (p : ℤ) Yt, (proj_resTotal g D W' (p : ℤ) Yt).symm.trans
    ((congrArg _ key).trans ((congrArg _ ha.symm).trans ((G1.TB _).proj_incl _ _ _)))⟩

end RegularTwisted

/-! ### The mapping cone of a map of complexes of modules -/

section ConeAlgebra

variable {R : Type*} [CommRing R] {M₀ M₁ : ℤ → Type*} [∀ i, AddCommGroup (M₀ i)]
  [∀ i, Module R (M₀ i)] [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]
  (d₀ : ∀ i, M₀ i →ₗ[R] M₀ (i + 1)) (d₁ : ∀ i, M₁ i →ₗ[R] M₁ (i + 1))
  (Ψ : ∀ i, M₀ i →ₗ[R] M₁ i)

/-- The terms `M₁^i ⊕ M₀^{i+1}` of the mapping cone of `Ψ : M₀ ⟶ M₁`. -/
private abbrev coneX (M₀ M₁ : ℤ → Type*) (i : ℤ) : Type _ := M₁ i × M₀ (i + 1)

/-- The differential `(x, y) ↦ (d x + Ψ y, -d y)` of the mapping cone. -/
private def coneD (i : ℤ) : coneX M₀ M₁ i →ₗ[R] coneX M₀ M₁ (i + 1) :=
  LinearMap.prod (d₁ i ∘ₗ LinearMap.fst R _ _ + Ψ (i + 1) ∘ₗ LinearMap.snd R _ _)
    (-(d₀ (i + 1)) ∘ₗ LinearMap.snd R _ _)

private theorem coneD_apply (i : ℤ) (x : M₁ i) (y : M₀ (i + 1)) :
    coneD d₀ d₁ Ψ i (x, y) = (d₁ i x + Ψ (i + 1) y, -d₀ (i + 1) y) := rfl

variable {d₀ d₁ Ψ}

private theorem coneD_comp (hdd₀ : ∀ i, d₀ (i + 1) ∘ₗ d₀ i = 0) (hdd₁ : ∀ i, d₁ (i + 1) ∘ₗ d₁ i = 0)
    (hΨ : ∀ i x, Ψ (i + 1) (d₀ i x) = d₁ i (Ψ i x)) (i : ℤ) :
    coneD d₀ d₁ Ψ (i + 1) ∘ₗ coneD d₀ d₁ Ψ i = 0 := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨x, y⟩ := z
  have h₀ := LinearMap.congr_fun (hdd₀ (i + 1)) y
  have h₁ := LinearMap.congr_fun (hdd₁ i) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h₀ h₁
  refine Prod.ext ?_ ?_
  · change d₁ (i + 1) (d₁ i x + Ψ (i + 1) y) + Ψ (i + 1 + 1) (-d₀ (i + 1) y) = 0
    rw [map_add, map_neg, h₁, ← hΨ (i + 1) y, zero_add, add_neg_cancel]
  · change -d₀ (i + 1 + 1) (-d₀ (i + 1) y) = 0
    rw [map_neg, neg_neg, h₀]

/-- **The mapping cone of complexes contractible in high degrees is contractible in high degrees.**
With contractions `h₀`, `h₁`, the map `(x, y) ↦ (h x + h Ψ h y, -h y)` contracts the cone. -/
private theorem cone_homotopy (hΨ : ∀ i x, Ψ (i + 1) (d₀ i x) = d₁ i (Ψ i x))
    (h₀ : ∀ j, M₀ (j + 1) →ₗ[R] M₀ j) (h₁ : ∀ j, M₁ (j + 1) →ₗ[R] M₁ j) (b : ℤ)
    (hh₀ : ∀ j, b ≤ j → ∀ x, d₀ j (h₀ j x) + h₀ (j + 1) (d₀ (j + 1) x) = x)
    (hh₁ : ∀ j, b ≤ j → ∀ x, d₁ j (h₁ j x) + h₁ (j + 1) (d₁ (j + 1) x) = x) :
    ∃ H : ∀ j, coneX M₀ M₁ (j + 1) →ₗ[R] coneX M₀ M₁ j,
      ∀ j, b ≤ j → ∀ x, coneD d₀ d₁ Ψ j (H j x) + H (j + 1) (coneD d₀ d₁ Ψ (j + 1) x) = x := by
  refine ⟨fun j => LinearMap.prod (h₁ j ∘ₗ LinearMap.fst R _ _ +
      h₁ j ∘ₗ Ψ (j + 1) ∘ₗ h₀ (j + 1) ∘ₗ LinearMap.snd R _ _)
      (-(h₀ (j + 1)) ∘ₗ LinearMap.snd R _ _), fun j hj z => ?_⟩
  obtain ⟨x, y⟩ := z
  have e₁ := hh₁ j hj x
  have e₂ := hh₀ (j + 1) (by omega) y
  have e₃ := hh₁ j hj (Ψ (j + 1) (h₀ (j + 1) y))
  have e₄ := hΨ (j + 1) (h₀ (j + 1) y)
  have e₅ : h₁ (j + 1) (Ψ (j + 1 + 1) y) =
      h₁ (j + 1) (d₁ (j + 1) (Ψ (j + 1) (h₀ (j + 1) y))) +
        h₁ (j + 1) (Ψ (j + 1 + 1) (h₀ (j + 1 + 1) (d₀ (j + 1 + 1) y))) := by
    conv_lhs => rw [← e₂]
    rw [map_add, map_add, e₄]
  refine Prod.ext ?_ ?_
  · change d₁ j (h₁ j x + h₁ j (Ψ (j + 1) (h₀ (j + 1) y))) + Ψ (j + 1) (-h₀ (j + 1) y) +
        (h₁ (j + 1) (d₁ (j + 1) x + Ψ (j + 1 + 1) y) +
          h₁ (j + 1) (Ψ (j + 1 + 1) (h₀ (j + 1 + 1) (-d₀ (j + 1 + 1) y)))) = x
    simp only [map_add, map_neg]
    rw [e₅]
    calc _ = (d₁ j (h₁ j x) + h₁ (j + 1) (d₁ (j + 1) x)) +
          ((d₁ j (h₁ j (Ψ (j + 1) (h₀ (j + 1) y))) +
            h₁ (j + 1) (d₁ (j + 1) (Ψ (j + 1) (h₀ (j + 1) y)))) - Ψ (j + 1) (h₀ (j + 1) y)) := by
          abel
      _ = x := by rw [e₁, e₃, sub_self, add_zero]
  · change -d₀ (j + 1) (-h₀ (j + 1) y) + -h₀ (j + 1 + 1) (-d₀ (j + 1 + 1) y) = y
    simp only [map_neg, neg_neg]
    exact e₂

/-- The inclusion `M₁ ⟶ cone(Ψ)`. -/
private def coneIn (i : ℤ) : M₁ i →ₗ[R] coneX M₀ M₁ i := LinearMap.inl R _ _

/-- The projection `cone(Ψ) ⟶ M₀[1]`. -/
private def coneOut (i : ℤ) : coneX M₀ M₁ i →ₗ[R] M₀ (i + 1) := LinearMap.snd R _ _

/-- **The cohomology of the mapping cone is finite** when that of the source and the target is,
over a Noetherian ring. -/
private theorem moduleFinite_homologyAt_cone [IsNoetherianRing R] (hdd₀ : ∀ i, d₀ (i + 1) ∘ₗ d₀ i = 0)
    (hdd₁ : ∀ i, d₁ (i + 1) ∘ₗ d₁ i = 0) (hΨ : ∀ i x, Ψ (i + 1) (d₀ i x) = d₁ i (Ψ i x))
    (h₀ : ∀ i, Module.Finite R (homologyAt (d₀ i) (d₀ (i + 1))))
    (h₁ : ∀ i, Module.Finite R (homologyAt (d₁ i) (d₁ (i + 1)))) (i : ℤ) :
    Module.Finite R (homologyAt (coneD d₀ d₁ Ψ i) (coneD d₀ d₁ Ψ (i + 1))) := by
  have hneg : ∀ j, Module.Finite R (homologyAt (-(d₀ (j + 1))) (-(d₀ (j + 1 + 1)))) := by
    intro j
    haveI := h₀ (j + 1)
    exact Module.Finite.equiv (homologyAtCongr (-(d₀ (j + 1))) (-(d₀ (j + 1 + 1))) (d₀ (j + 1))
      (d₀ (j + 1 + 1)) (LinearEquiv.neg R) (LinearEquiv.refl R _) (LinearEquiv.neg R)
      (LinearMap.ext fun x => by simp) (LinearMap.ext fun x => by simp)).symm
  refine moduleFinite_homologyAt_middle (A := M₁) (B := coneX M₀ M₁) (C := fun j => M₀ (j + 1))
    d₁ (coneD d₀ d₁ Ψ) (fun j => -(d₀ (j + 1))) coneIn coneOut
    (fun j => LinearMap.inl_injective) (fun j => LinearMap.snd_surjective)
    (fun j => LinearMap.ker_snd R _ _)
    (fun j x => by
      change ((d₁ j x, 0) : coneX M₀ M₁ (j + 1)) = (d₁ j x + Ψ (j + 1) 0, -d₀ (j + 1) 0)
      rw [map_zero, map_zero, add_zero, neg_zero])
    (fun j z => rfl)
    (fun j z => LinearMap.congr_fun (coneD_comp hdd₀ hdd₁ hΨ j) z) i (h₁ i) (hneg i)

/-- The cokernel `M₁ / Ψ M₀`, as a complex. -/
private abbrev cokerX (Ψ : ∀ i, M₀ i →ₗ[R] M₁ i) (i : ℤ) := M₁ i ⧸ LinearMap.range (Ψ i)

private def cokerD (hΨ : ∀ i x, Ψ (i + 1) (d₀ i x) = d₁ i (Ψ i x)) (i : ℤ) :
    cokerX Ψ i →ₗ[R] cokerX Ψ (i + 1) :=
  (LinearMap.range (Ψ i)).mapQ (LinearMap.range (Ψ (i + 1))) (d₁ i) (by
    rintro _ ⟨y, rfl⟩
    exact ⟨d₀ i y, hΨ i y⟩)

/-- **The mapping cone of an injective map of complexes computes the cokernel**: the projection
`(x, y) ↦ [x]` induces an isomorphism on cohomology. -/
private theorem nonempty_homologyAt_cone_equiv_coker (hdd₀ : ∀ i, d₀ (i + 1) ∘ₗ d₀ i = 0)
    (hdd₁ : ∀ i, d₁ (i + 1) ∘ₗ d₁ i = 0) (hΨ : ∀ i x, Ψ (i + 1) (d₀ i x) = d₁ i (Ψ i x))
    (hinj : ∀ i, Function.Injective (Ψ i)) (i : ℤ) :
    Nonempty (homologyAt (coneD d₀ d₁ Ψ i) (coneD d₀ d₁ Ψ (i + 1)) ≃ₗ[R]
      homologyAt (cokerD hΨ i) (cokerD hΨ (i + 1))) := by
  classical
  let πc : ∀ j, coneX M₀ M₁ j →ₗ[R] cokerX Ψ j := fun j =>
    (LinearMap.range (Ψ j)).mkQ ∘ₗ LinearMap.fst R _ _
  have hπc : ∀ j z, πc (j + 1) (coneD d₀ d₁ Ψ j z) = cokerD hΨ j (πc j z) := by
    rintro j ⟨x, y⟩
    change Submodule.Quotient.mk (d₁ j x + Ψ (j + 1) y) = Submodule.Quotient.mk (d₁ j x)
    refine (Submodule.Quotient.eq _).2 ⟨y, ?_⟩
    simp
  have hk : ∀ z : LinearMap.ker (coneD d₀ d₁ Ψ (i + 1)),
      πc (i + 1) z.1 ∈ LinearMap.ker (cokerD hΨ (i + 1)) := fun z => by
    rw [LinearMap.mem_ker, ← hπc, LinearMap.mem_ker.mp z.2, map_zero]
  let πk : LinearMap.ker (coneD d₀ d₁ Ψ (i + 1)) →ₗ[R] LinearMap.ker (cokerD hΨ (i + 1)) :=
    LinearMap.codRestrict _ ((πc (i + 1)).comp (LinearMap.ker (coneD d₀ d₁ Ψ (i + 1))).subtype) hk
  let πH : homologyAt (coneD d₀ d₁ Ψ i) (coneD d₀ d₁ Ψ (i + 1)) →ₗ[R]
      homologyAt (cokerD hΨ i) (cokerD hΨ (i + 1)) :=
    Submodule.mapQ _ _ πk (by
      rintro z ⟨z', hz'⟩
      refine ⟨πc i z', ?_⟩
      change cokerD hΨ i (πc i z') = πc (i + 1) z.1
      rw [← hπc, hz']
      rfl)
  refine ⟨LinearEquiv.ofBijective πH ⟨fun u v huv => ?_, fun w => ?_⟩⟩
  · -- injectivity
    rw [← sub_eq_zero, ← map_sub] at huv
    rw [← sub_eq_zero]
    generalize u - v = w at huv ⊢
    induction w using Submodule.Quotient.induction_on with
    | H z =>
      change Submodule.Quotient.mk (πk z) = 0 at huv
      rw [Submodule.Quotient.mk_eq_zero] at huv
      obtain ⟨q', hq'⟩ := huv
      obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective _ q'
      obtain ⟨⟨x, y⟩, hz⟩ := z
      have hzc := hz
      rw [LinearMap.mem_ker, coneD_apply] at hzc
      have hx : Submodule.Quotient.mk (d₁ i x') = (Submodule.Quotient.mk x :
          cokerX Ψ (i + 1)) := hq'
      obtain ⟨w', hw'⟩ := (Submodule.Quotient.eq _).1 hx
      refine (Submodule.Quotient.mk_eq_zero _).2 ⟨(x', -w'), ?_⟩
      change coneD d₀ d₁ Ψ i (x', -w') = (x, y)
      rw [coneD_apply]
      have h2 : Ψ (i + 1) w' = d₁ i x' - x := hw'
      have hd : d₁ (i + 1) (d₁ i x') = 0 := by simpa using LinearMap.congr_fun (hdd₁ i) x'
      have h1 : d₁ (i + 1) x + Ψ (i + 1 + 1) y = 0 := congrArg Prod.fst hzc
      have hy : y = d₀ (i + 1) w' := by
        apply hinj (i + 1 + 1)
        rw [hΨ, h2, map_sub, hd, zero_sub]
        exact eq_neg_of_add_eq_zero_right h1
      refine Prod.ext ?_ ?_
      · change d₁ i x' + Ψ (i + 1) (-w') = x
        rw [map_neg, h2]
        abel
      · change -d₀ (i + 1) (-w') = y
        rw [map_neg, neg_neg]
        exact hy.symm
  · -- surjectivity
    induction w using Submodule.Quotient.induction_on with
    | H q =>
      obtain ⟨q, hq⟩ := q
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
      have hq' : Submodule.Quotient.mk (d₁ (i + 1) x) = (0 : cokerX Ψ (i + 1 + 1)) := hq
      rw [Submodule.Quotient.mk_eq_zero] at hq'
      obtain ⟨y', hy'⟩ := hq'
      have hz : ((x, -y') : coneX M₀ M₁ (i + 1)) ∈ LinearMap.ker (coneD d₀ d₁ Ψ (i + 1)) := by
        have hd2 : d₁ (i + 1 + 1) (d₁ (i + 1) x) = 0 := by
          simpa using LinearMap.congr_fun (hdd₁ (i + 1)) x
        have hy0 : d₀ (i + 1 + 1) y' = 0 := by
          apply hinj (i + 1 + 1 + 1)
          rw [hΨ, hy', hd2, map_zero]
        rw [LinearMap.mem_ker, coneD_apply]
        refine Prod.ext ?_ ?_
        · change d₁ (i + 1) x + Ψ (i + 1 + 1) (-y') = 0
          rw [map_neg, hy', add_neg_cancel]
        · change -d₀ (i + 1 + 1) (-y') = 0
          rw [map_neg, neg_neg, hy0]
      exact ⟨Submodule.Quotient.mk ⟨_, hz⟩, rfl⟩

end ConeAlgebra

/-! ### The total Čech complex of a cokernel -/

section CechCoker

open Stacks.CategoryTheory.CechComplex

variable {C : Type} [Category.{0} C] [HasFiniteProducts C] {ι : Type} (U : ι → C) {R : Type}
  [CommRing R] {PK PΩ PD : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} R) ℕ}

/-- **The total Čech complex of a termwise cokernel.** If `PK ⟶ PΩ ⟶ PD` is exact on the sections
over every intersection of the cover, with the second map onto, then the cohomology of the total
Čech complex of `PD` is that of the cokernel of `Tot(PK) ⟶ Tot(PΩ)`. -/
private theorem nonempty_homologyAt_cokerD_equiv (Ψ : PK ⟶ PΩ) (π : PΩ ⟶ PD) (hΨπ : Ψ ≫ π = 0)
    (hsurj : ∀ (a p : ℕ) (t : Fin (p + 1) → ι),
      Function.Surjective ((π.f a).app (op (inter U t))).hom)
    (hex : ∀ (a p : ℕ) (t : Fin (p + 1) → ι),
      LinearMap.ker ((π.f a).app (op (inter U t))).hom =
        LinearMap.range ((Ψ.f a).app (op (inter U t))).hom) (n : ℤ) :
    Nonempty (homologyAt
        (cokerD (d₀ := totD U PK) (d₁ := totD U PΩ) (Ψ := fun i => totMap (U := U) Ψ i)
          (fun i x => totMap_totD U PK Ψ i x) n)
        (cokerD (d₀ := totD U PK) (d₁ := totD U PΩ) (Ψ := fun i => totMap (U := U) Ψ i)
          (fun i x => totMap_totD U PK Ψ i x) (n + 1)) ≃ₗ[R]
      homologyAt (totD U PD n) (totD U PD (n + 1))) := by
  classical
  have hzero : ∀ (i : ℤ) (x : TotX U PK i), totMap (U := U) π i (totMap (U := U) Ψ i x) = 0 := by
    intro i x
    funext j t
    have := congrArg (fun φ => ((φ.f j.1.2).app (op (inter U t))).hom (x j t)) hΨπ
    simp at this
    exact this
  have hEq : ∀ i, LinearMap.range (totMap (U := U) Ψ i) = LinearMap.ker (totMap (U := U) π i) := by
    intro i
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hzero i y
    · intro hx
      have h : ∀ (j : TotIndex i) (t : Fin (j.1.1 + 1) → ι),
          x j t ∈ LinearMap.range ((Ψ.f j.1.2).app (op (inter U t))).hom := by
        intro j t
        rw [← hex]
        exact congrFun (congrFun (LinearMap.mem_ker.mp hx) j) t
      choose y hy using h
      exact ⟨fun j t => y j t, funext fun j => funext fun t => hy j t⟩
  let φ : ∀ i, cokerX (fun i => totMap (U := U) Ψ i) i →ₗ[R] TotX U PD i := fun i =>
    (LinearMap.range (totMap (U := U) Ψ i)).liftQ (totMap (U := U) π i) (hEq i).le
  have hφ : ∀ i, Function.Bijective (φ i) := by
    intro i
    refine ⟨LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ (hEq i)), fun z => ?_⟩
    have h : ∀ (j : TotIndex i) (t : Fin (j.1.1 + 1) → ι),
        ∃ w, ((π.f j.1.2).app (op (inter U t))).hom w = z j t := fun j t => hsurj _ _ t (z j t)
    choose w hw using h
    exact ⟨Submodule.Quotient.mk (fun j t => w j t), funext fun j => funext fun t => hw j t⟩
  let e : ∀ i, cokerX (fun i => totMap (U := U) Ψ i) i ≃ₗ[R] TotX U PD i := fun i =>
    LinearEquiv.ofBijective (φ i) (hφ i)
  have hc : ∀ i, totD U PD i ∘ₗ (e i).toLinearMap =
      (e (i + 1)).toLinearMap ∘ₗ cokerD (d₀ := totD U PK) (d₁ := totD U PΩ)
        (Ψ := fun i => totMap (U := U) Ψ i) (fun i x => totMap_totD U PK Ψ i x) i := by
    intro i
    refine LinearMap.ext fun z => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x => exact (totMap_totD U PΩ π i x).symm
  exact ⟨homologyAtCongr _ _ _ _ (e n) (e (n + 1)) (e (n + 1 + 1)) (hc n) (hc (n + 1))⟩

end CechCoker

/-! ### The empty divisor -/

section ZeroDivisor

/-- **The zero divisor is a relative simple normal crossing divisor**, with the coordinates of any
relative snc divisor and no boundary. -/
private theorem isRelativeSNC_zero {n : ℕ} {X S : Scheme.{0}} {f : X ⟶ S}
    [SmoothOfRelativeDimension n f] {D : MMP.Mori.Divisor X} (hD : D.IsRelativeSNC n f) :
    (0 : MMP.Mori.Divisor X).IsRelativeSNC n f := by
  refine ⟨fun E hE => by simp at hE, fun x => ?_⟩
  obtain ⟨W, V, e, t, hx, hb, -⟩ := hD.2 x
  refine ⟨W, V, e, t, hx, hb, 0, Nat.zero_le n, fun i => i.elim0, fun i => i.elim0,
    fun i => i.elim0, ?_⟩
  have h0 : (0 : MMP.Mori.Divisor X).supp = ⊥ := by simp [DivisorWithCoeffs.supp]
  rw [DivisorWithCoeffs.suppIdeal, h0, Scheme.IdealSheafData.vanishingIdeal_bot,
    Fin.prod_univ_zero, Ideal.span_singleton_one, Scheme.IdealSheafData.ideal_top]
  rfl

private theorem coe_supp_zero {X : Scheme.{0}} :
    ((0 : MMP.Mori.Divisor X).supp : Set X) = ∅ := by
  simp [DivisorWithCoeffs.supp]

/-- The weak chart of the empty set with the coordinates of a weak chart. -/
private def WeakChart.forgetBoundary {X S : Scheme.{0}} {g : X ⟶ S} {n : ℕ} {Z : Set X}
    (c : WeakChart g n Z) : WeakChart g n ((0 : MMP.Mori.Divisor X).supp : Set X) where
  W := c.W
  t := c.t
  r := 0
  hr := Nat.zero_le n
  basis := c.basis
  zero := by
    rw [coe_supp_zero, Set.empty_inter, Fin.prod_univ_zero]
    symm
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hxW⟩
    exact (X.mem_zeroLocus_iff _ x).1 hx 1 rfl (by rwa [Scheme.basicOpen_one])

end ZeroDivisor

/-! ### Every form is logarithmic for the empty divisor -/

section ZeroForms

open MMP.Mori.Divisor.LogSpreadingProof.G1

variable {n : ℕ} {X S : Scheme.{0}} (f : X ⟶ S) [SmoothOfRelativeDimension n f]

/-- Homogeneous elements of equal degree that are heterogeneously equal have the same image in
the total algebra. -/
private theorem incl_eq_of_heq {O : X.Opensᵒᵖ} {i j : ℤ}
    (h : i = j) (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece i).val.obj O)
    (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece j).val.obj O) (hxy : HEq x y) :
    (G1.TB f).incl i x = (G1.TB f).incl j y := by
  subst h
  rw [eq_of_heq hxy]

/-- **An exact wedge is a product of exact one-forms** in the total algebra of forms. -/
private theorem exists_incl_eq_prod_of_isExactWedge (O : X.Opensᵒᵖ) : ∀ (p : ℕ)
      (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece (p : ℤ)).val.obj O),
      AlgebraicGeometry.SheafOfModules.IsExactWedge (Scheme.Hom.deRhamAlgebras f) O p ω →
      ∃ c : List Γ(X, O.unop), (G1.TB f).incl (p : ℤ) ω =
        (c.map fun a => (G1.TB f).incl 1 (dX f O.unop a)).prod
  | 0, ω, hω => ⟨[], by
      change ω = _ at hω
      rw [hω, List.map_nil, List.prod_nil]
      exact ((G1.TB f).one_eq_incl O).symm⟩
  | p + 1, ω, ⟨b, η, hη, hωη⟩ => by
      obtain ⟨c, hc⟩ := exists_incl_eq_prod_of_isExactWedge O p η hη
      refine ⟨b :: c, ?_⟩
      refine (incl_eq_of_heq f (by push_cast; ring) _ _ hωη).trans ?_
      refine ((G1.TB f).incl_mul_incl 1 (p : ℤ) _ η).symm.trans ?_
      exact congrArg (fun z => _ * z) hc

/-- **Every form is logarithmic for the empty divisor**: its restriction to `X ∖ 0 = X` lies in
`Ω^p(log 0)`, since forms are locally sums of multiples of exact wedges. -/
private theorem resForms_mem_relativeLogForms_zero
    (h0 : (0 : MMP.Mori.Divisor X).IsRelativeSNC n f) (p : ℕ) (W : X.Opens)
    (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece (p : ℤ)).val.obj (op W)) :
    ((resForms f 0).app (p : ℤ)).val.app (op W) y ∈ relativeLogForms n f 0 h0 ⊤ p W := by
  refine (mem_relativeLogForms_iff' n f 0 h0 ⊤ p _ _).2 fun x hx => ?_
  obtain ⟨S', hS', hgen⟩ := AlgebraicGeometry.SheafOfModules.locallyGeneratedByExactWedges
    (Scheme.Hom.deRhamAlgebras f) p (op W) y
  obtain ⟨V, i, hiS, hxV⟩ := (Opens.mem_grothendieckTopology _).mp hS' x hx
  obtain ⟨W'', hxW'', hle⟩ := G1.exists_affineOpens_le (X := X) hxV
  have hS'' : S' (homOfLE hle ≫ i) := S'.downward_closed hiS _
  have hle' : (W'' : X.Opens) ≤ W := hle.trans (leOfHom i)
  have hy : ((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece (p : ℤ)).val.map
      (homOfLE hle').op y ∈ AlgebraicGeometry.SheafOfModules.exactWedgeSubgroup
        (Scheme.Hom.deRhamAlgebras f) (op (W'' : X.Opens)) p := by
    have := hgen (homOfLE hle ≫ i) hS''
    have e : (homOfLE hle ≫ i) = homOfLE hle' := Subsingleton.elim _ _
    rw [e] at this
    exact this
  refine ⟨W'', hle', hxW'', ?_⟩
  have hnat : rs f 0 (p : ℤ) hle' (((resForms f 0).app (p : ℤ)).val.app (op W) y) =
      ((resForms f 0).app (p : ℤ)).val.app (op (W'' : X.Opens))
        (((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece (p : ℤ)).val.map
          (homOfLE hle').op y) :=
    (PresheafOfModules.naturality_apply ((resForms f 0).app (p : ℤ)).val (homOfLE hle').op y).symm
  refine (congrArg (Br f 0 ⊤ (p : ℤ) W'') hnat).mpr ?_
  generalize ((Scheme.Hom.relativeDifferentialFormsAlgebra f).piece (p : ℤ)).val.map
    (homOfLE hle').op y = z at hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, ω, hω, rfl⟩ := hz
    obtain ⟨c, hc⟩ := exists_incl_eq_prod_of_isExactWedge f (op (W'' : X.Opens)) p ω hω
    have e := (resTotal_incl f 0 W'' (p : ℤ) ω).symm.trans ((congrArg (resTotal f 0 W'') hc).trans
      (map_list_prod (resTotal f 0 W'') _))
    have hω' : Br f 0 ⊤ (p : ℤ) W''
        (((resForms f 0).app (p : ℤ)).val.app (op (W'' : X.Opens)) ω) := by
      have hζ : (List.map (resTotal f 0 W'') (c.map fun a =>
          (G1.TB f).incl 1 (dX f (op (W'' : X.Opens)).unop a))).prod ∈
            Subring.closure (gens f 0 W'') := by
        refine Subring.list_prod_mem _ fun η hη => ?_
        obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hη
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hb'
        exact (congrArg (· ∈ Subring.closure (gens f 0 W'')) (resTotal_incl_dX f 0 W'' a)).mpr
          (Subring.subset_closure (Or.inl (Or.inr ⟨a, rfl⟩)))
      refine (congrArg (· ∈ BrSet f 0 ⊤ W'') e).mpr (AddSubgroup.subset_closure
        ⟨1, Submodule.mem_top, _, hζ, ?_⟩)
      exact (one_mul _).symm.trans (congrArg (· * _)
        ((map_one ((G1.TB ((LU 0).ι ≫ f)).structureMap _)).symm.trans
          (congrArg _ (map_one ((LU 0).ι.app (W'' : X.Opens)).hom).symm)))
    have hsm := Scheme.Modules.Hom.app_smul (U := (W'' : X.Opens)) ((resForms f 0).app (p : ℤ)) b ω
    exact (congrArg (Br f 0 ⊤ (p : ℤ) W'') hsm).mpr (Br_smul f 0 ⊤ (p : ℤ) W'' b hω')
  | zero =>
    exact (congrArg (Br f 0 ⊤ (p : ℤ) W'')
      (map_zero (((resForms f 0).app (p : ℤ)).val.app (op (W'' : X.Opens))).hom)).mpr
      (Br_zero f 0 ⊤ (p : ℤ) W'')
  | add z z' _ _ hz hz' =>
    exact (congrArg (Br f 0 ⊤ (p : ℤ) W'')
      (map_add (((resForms f 0).app (p : ℤ)).val.app (op (W'' : X.Opens))).hom z z')).mpr
      (Br_add f 0 ⊤ (p : ℤ) W'' hz hz')
  | neg z _ hz =>
    exact (congrArg (Br f 0 ⊤ (p : ℤ) W'')
      (map_neg (((resForms f 0).app (p : ℤ)).val.app (op (W'' : X.Opens))).hom z)).mpr
      (Br_neg f 0 ⊤ (p : ℤ) W'' hz)

end ZeroForms

/-! ### Restriction of forms to an open subscheme, over any base -/

section FormsRestrictionGeneral

variable {X S : Scheme.{0}} (f : X ⟶ S) (U : X.Opens)

/-- `(Ω^q_{X/S})|_U ≅ Ω^q_{U/S}` for an open subscheme `U`. -/
private noncomputable abbrev restrictFormsIso' (q : ℤ) :
    (f.relativeDifferentialForms q).restrict U.ι ≅ (U.ι ≫ f).relativeDifferentialForms q :=
  Scheme.Hom.restrictFormsIso U f (U.ι ≫ f) (𝟙 _) (by rw [Category.comp_id])
    (fun n => Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ n) q

/-- **The restriction of a form to an open subscheme `U`, read back on `X`**, is its restriction
to `W ∩ U`. -/
private theorem restrictFormsIso'_inv_deRhamFormsPushforwardHom (q : ℤ) (W : X.Opens)
    (t : Γ(f.relativeDifferentialForms q, W)) :
    Scheme.Modules.Hom.app (restrictFormsIso' f U q).inv (U.ι ⁻¹ᵁ W)
        (((Scheme.Hom.deRhamFormsPushforwardHom U.ι f (U.ι ≫ f) (𝟙 S)
          (Category.comp_id _).symm).app q).val.app (op W) t) =
      (f.relativeDifferentialForms q).presheaf.map (homOfLE (U.ι.image_preimage_le W)).op t := by
  rw [deRhamFormsPushforwardHom_app_eq]
  change Scheme.Modules.Hom.app (restrictFormsIso' f U q).inv (U.ι ⁻¹ᵁ W)
      (Scheme.Modules.Hom.app (restrictFormsIso' f U q).hom (U.ι ⁻¹ᵁ W)
        ((f.relativeDifferentialForms q).presheaf.map
          (homOfLE (U.ι.image_preimage_le W)).op t)) = _
  have hinv := congrArg (fun φ => Scheme.Modules.Hom.app φ (U.ι ⁻¹ᵁ W)
    ((f.relativeDifferentialForms q).presheaf.map (homOfLE (U.ι.image_preimage_le W)).op t))
    (restrictFormsIso' f U q).hom_inv_id
  exact hinv

/-- **Restriction of forms to an open subscheme containing `W` is injective on `W`.** -/
private theorem deRhamFormsPushforwardHom_app_injective_of_le (q : ℤ) {W : X.Opens}
    (hW : W ≤ U) :
    Function.Injective (((Scheme.Hom.deRhamFormsPushforwardHom U.ι f (U.ι ≫ f) (𝟙 S)
      (Category.comp_id _).symm).app q).val.app (op W)) := by
  intro a b hab
  have h0 := congrArg (Scheme.Modules.Hom.app (restrictFormsIso' f U q).inv (U.ι ⁻¹ᵁ W)) hab
  have h := ((restrictFormsIso'_inv_deRhamFormsPushforwardHom f U q W a).symm.trans h0).trans
    (restrictFormsIso'_inv_deRhamFormsPushforwardHom f U q W b)
  have hle : W ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ W) := by
    rw [image_preimage_opens_ι]
    exact le_inf le_rfl hW
  have e : ∀ t : Γ(f.relativeDifferentialForms q, W),
      (f.relativeDifferentialForms q).presheaf.map (homOfLE hle).op
        ((f.relativeDifferentialForms q).presheaf.map
          (homOfLE (U.ι.image_preimage_le W)).op t) = t := fun t =>
    (MMP.DeRham.presheaf_map_map (F := f.relativeDifferentialForms q) _ _ (𝟙 _) t).trans
      (MMP.DeRham.presheaf_map_id (F := f.relativeDifferentialForms q) _ t)
  rw [← e a, ← e b, h]

/-- **Every form on an open subscheme containing `W` is a restriction of a form on `W`.** -/
private theorem exists_deRhamFormsPushforwardHom_app_eq_of_le (q : ℤ) {W : X.Opens} (hW : W ≤ U)
    (z : Γ((U.ι ≫ f).relativeDifferentialForms q, U.ι ⁻¹ᵁ W)) :
    ∃ t : Γ(f.relativeDifferentialForms q, W),
      ((Scheme.Hom.deRhamFormsPushforwardHom U.ι f (U.ι ≫ f) (𝟙 S)
        (Category.comp_id _).symm).app q).val.app (op W) t = z := by
  have hle : W ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ W) := by
    rw [image_preimage_opens_ι]
    exact le_inf le_rfl hW
  refine ⟨(f.relativeDifferentialForms q).presheaf.map (homOfLE hle).op
    (Scheme.Modules.Hom.app (restrictFormsIso' f U q).inv (U.ι ⁻¹ᵁ W) z), ?_⟩
  have hinv : ∀ w, Scheme.Modules.Hom.app (restrictFormsIso' f U q).hom (U.ι ⁻¹ᵁ W)
      (Scheme.Modules.Hom.app (restrictFormsIso' f U q).inv (U.ι ⁻¹ᵁ W) w) = w := fun w =>
    congrArg (fun φ => Scheme.Modules.Hom.app φ (U.ι ⁻¹ᵁ W) w) (restrictFormsIso' f U q).inv_hom_id
  have key := (restrictFormsIso'_inv_deRhamFormsPushforwardHom f U q W
    ((f.relativeDifferentialForms q).presheaf.map (homOfLE hle).op
      (Scheme.Modules.Hom.app (restrictFormsIso' f U q).inv (U.ι ⁻¹ᵁ W) z))).trans
    ((MMP.DeRham.presheaf_map_map (F := f.relativeDifferentialForms q) _ _ (𝟙 _) _).trans
      (MMP.DeRham.presheaf_map_id (F := f.relativeDifferentialForms q) _ _))
  exact ((hinv _).symm.trans (congrArg _ key)).trans (hinv z)

/-- The structure map of the de Rham chain is the restriction of forms to `U`. -/
private theorem deRhamPushforwardChain_app_eq (q : ℕ) (W : X.Opensᵒᵖ)
    (t : Γ(f.relativeDifferentialForms (q : ℤ), W.unop)) :
    ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι U) f).f q).val.app W t =
      ((Scheme.Hom.deRhamFormsPushforwardHom U.ι f (U.ι ≫ f) (𝟙 _)
        (Category.comp_id _).symm).app (q : ℤ)).val.app W t := by
  change ((Stacks.DeRhamPullback.pushforwardSquareIso (Scheme.Opens.ι U) f).inv.app
      (Scheme.Hom.relativeDifferentialForms (U.ι ≫ f) ((q : ℕ) : ℤ))).val.app W
      (((Stacks.DeRhamPullback.formsPushforwardComponent (Scheme.Opens.ι U) f q).val.app W)
        t) = _
  exact Stacks.DeRhamPullback.pushforwardSquareIso_inv_val_app (Scheme.Opens.ι U) f
    (Scheme.Hom.relativeDifferentialForms (U.ι ≫ f) ((q : ℕ) : ℤ)) W
    (((Stacks.DeRhamPullback.formsPushforwardComponent (Scheme.Opens.ι U) f q).val.app W) t)

end FormsRestrictionGeneral

/-! ### Regular forms are determined off the divisor, over any regular base -/

section ModelDensity

open MMP.Mori.Divisor.LogSpreadingProof.G1

variable {n : ℕ} {X : Scheme.{0}} {A : CommRingCat.{0}} (g : X ⟶ Spec A)
  [SmoothOfRelativeDimension n g] [IsRegularRing A] (D : MMP.Mori.Divisor X)

/-- The coefficient `∏_{i ∈ K} σᵢ` of `θ_K`, as a product over the boundary coordinates. -/
private theorem prod_σ_eq (cL : G1.LogData n g D) {W' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ cL.W) (K : Finset (Fin n)) :
    ∏ i ∈ K, cL.σ hW' i =
      ∏ j : Fin cL.r, if Fin.castLE cL.hr j ∈ K then cL.σ hW' (Fin.castLE cL.hr j) else 1 := by
  classical
  have hσ1 : ∀ i : Fin n, ¬ (i : ℕ) < cL.r → cL.σ hW' i = 1 := fun i hi => by
    unfold LogData.σ
    rw [dif_neg hi]
  rw [← Finset.prod_filter]
  have hm := Finset.prod_map (Finset.univ.filter fun j : Fin cL.r => Fin.castLE cL.hr j ∈ K)
    (Fin.castLEEmb cL.hr) (cL.σ hW')
  refine Eq.trans ?_ hm
  refine (Finset.prod_subset (fun i hi => ?_) fun i hiK hi' => ?_).symm
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    exact (Finset.mem_filter.1 hj).2
  · refine hσ1 i fun hir => hi' ?_
    refine Finset.mem_map.2 ⟨⟨i, hir⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, Fin.ext rfl⟩
    have hci : Fin.castLE cL.hr ⟨i, hir⟩ = i := Fin.ext rfl
    rw [hci]
    exact hiK

/-- **Regular forms are determined off the divisor** on an affine open `W'` of a weak chart: in
the coordinates of the chart a form is `∑_K b_K dt_K`, whose restriction is the logarithmic
combination with coefficients `(∏_{i ∈ K ∩ B} tᵢ) b_K`, and these coefficients determine `b`
because the boundary coordinates are non-zero-divisors. -/
private theorem eq_zero_of_resForms_eq_zero_of_weakChart (hD : D.IsRelativeSNC n g)
    (hcomp : ∀ ξ : X, ξ ∈ (D.supp : Set X) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)
    (c : WeakChart g n (D.supp : Set X)) (p : ℕ) {W' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ (c.toLogData g D).W)
    (y : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj
      (op (W' : X.Opens)))
    (hy : ((resForms g D).app (p : ℤ)).val.app (op (W' : X.Opens)) y = 0) : y = 0 := by
  classical
  have h0 := isRelativeSNC_zero hD
  have hcomp0 : ∀ ξ : X, ξ ∈ ((0 : MMP.Mori.Divisor X).supp : Set X) → Order.coheight ξ = 1 →
      ∃ E ∈ (0 : MMP.Mori.Divisor X).support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ := by
    intro ξ hξ
    rw [coe_supp_zero] at hξ
    exact absurd hξ (Set.notMem_empty ξ)
  set cL := c.toLogData g D with hcL
  set cL0 := (WeakChart.forgetBoundary c).toLogData g 0 with hcL0
  have hW0 : (W' : X.Opens) ≤ cL0.W := hW'
  let ρ : Γ(X, cL.W) →+* Γ(X, W') := (X.presheaf.map (homOfLE hW').op).hom
  -- the zero-divisor coefficients of `y`
  obtain ⟨b, hb⟩ := (((WeakChart.forgetBoundary c).hasLogBasis g 0 h0 hcomp0 p hW0).2.1 _).1
    (resForms_mem_relativeLogForms_zero g h0 p W' y)
  let Yb : (G1.TB g).Total (op (W' : X.Opens)) := ∑ K, (G1.TB g).structureMap _ (b K) *
    ((K.1.sort (· ≤ ·)).map fun i => (G1.TB g).incl 1 (dX g (W' : X.Opens) (ρ (cL.t i)))).prod
  have hY0 : resTotal g 0 W' Yb = cL0.combo p hW0 b :=
    resTotal_sum_eq_combo 0 g cL0 p hW0 b b fun K => by
      rw [Finset.prod_eq_one (fun i _ => ?_), mul_one]
      unfold LogData.σ
      exact dif_neg (Nat.not_lt_zero _)
  -- `y` is the form of `Yb`
  have hyY : y = (G1.TB g).proj _ (p : ℤ) Yb := by
    refine deRhamFormsPushforwardHom_app_injective_of_le g (LU 0) (p : ℤ)
      (W := (W' : X.Opens)) (fun x _ => ?_) ?_
    · show x ∈ ((0 : MMP.Mori.Divisor X).supp.compl : Set X)
      rw [TopologicalSpace.Closeds.coe_compl, coe_supp_zero, Set.compl_empty]
      trivial
    refine Eq.trans ?_ (proj_resTotal g 0 W' (p : ℤ) Yb)
    refine Eq.trans ?_ (congrArg _ (hY0.trans hb.symm)).symm
    exact ((G1.TB _).proj_incl _ _ _).symm
  -- the boundary multiples of the coefficients
  let m' : {K : Finset (Fin n) // K.card = p} → Γ(X, W') := fun K =>
    ∏ j : Fin cL.r, if Fin.castLE cL.hr j ∈ K.1 then ρ (cL.t (Fin.castLE cL.hr j)) else 1
  have hs : ∀ j : Fin cL.r, cL.σ hW' (Fin.castLE cL.hr j) *
      ((LU D).ι.app W').hom (ρ (cL.t (Fin.castLE cL.hr j))) = 1 := by
    intro j
    have h1 := congrArg ((LU D).toScheme.presheaf.map
      ((Opens.map (LU D).ι.base).map (homOfLE hW')).op).hom (WeakChart.toLogData_hs g D c j)
    rw [map_mul, map_one, app_restrict] at h1
    have h2 : cL.σ hW' (Fin.castLE cL.hr j) = (LU D).toScheme.presheaf.map
        ((Opens.map (LU D).ι.base).map (homOfLE hW')).op (cL.s j) := by
      unfold LogData.σ
      rw [dif_pos (show ((Fin.castLE cL.hr j : Fin n) : ℕ) < cL.r from j.2)]
      rfl
    rw [h2]
    exact h1
  have hYD : resTotal g D W' Yb = cL.combo p hW' (fun K => m' K * b K) :=
    resTotal_sum_eq_combo D g cL p hW' (fun K => m' K * b K) b fun K => by
      have e : ((LU D).ι.app W').hom (m' K) * ∏ i ∈ K.1, cL.σ hW' i = 1 := by
        rw [prod_σ_eq g D cL hW' K.1, map_prod, ← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun j _ => ?_
        split_ifs with hj
        · rw [mul_comm]
          exact hs j
        · rw [map_one, one_mul]
      rw [map_mul, mul_comm (((LU D).ι.app W').hom (m' K)), mul_assoc, e, mul_one]
  -- the restriction of `y` vanishes, so its boundary-multiplied coefficients vanish
  obtain ⟨ζ, hζ⟩ := cL.exists_incl_eq_combo p hW' (fun K => m' K * b K)
  have hζ0 : ζ = 0 := by
    have e1 : ((resForms g D).app (p : ℤ)).val.app (op (W' : X.Opens)) y = ζ := by
      rw [hyY]
      refine (proj_resTotal g D W' (p : ℤ) Yb).symm.trans ?_
      refine (congrArg _ (hYD.trans hζ.symm)).trans ?_
      exact (G1.TB _).proj_incl _ _ _
    exact e1.symm.trans hy
  have hcoef0 : (fun K => m' K * b K) = 0 := by
    apply (c.hasLogBasis g D hD hcomp p hW').1
    refine hζ.symm.trans ?_
    rw [hζ0, (G1.TB _).incl_zero]
    change 0 = logCombo (f := g) cL.W cL.t cL.r cL.s p hW' 0
    unfold logCombo
    refine (Finset.sum_eq_zero fun K _ => ?_).symm
    refine (congrArg (· * _) ?_).trans (zero_mul _)
    simp only [Pi.zero_apply, map_zero]
    try exact map_zero _
  -- the boundary multiples are non-zero-divisors
  have hreg : ∀ K, IsSMulRegular Γ(X, W') (m' K) := by
    intro K
    let _ := (g.appLE ⊤ c.W le_top).hom.toAlgebra
    have : Algebra.Smooth Γ(Spec A, ⊤) Γ(X, c.W) :=
      HasRingHomProperty.appLE @Smooth g (SmoothOfRelativeDimension.smooth n g)
        ⟨⊤, isAffineOpen_top _⟩ c.W le_top
    obtain ⟨bb, hbb⟩ := c.basis
    have hW'c : (W' : X.Opens) ≤ c.W := hW'
    let _ := (X.presheaf.map (homOfLE hW'c).op).hom.toAlgebra
    have := flat_map hW'c
    refine Finset.prod_induction _ _ (fun u v hu hv => hu.mul hv) (IsSMulRegular.one _)
      fun j _ => ?_
    split_ifs
    · exact (isSMulRegular_of_basis_D c.t bb hbb _).of_flat (S := Γ(X, W'))
    · exact IsSMulRegular.one _
  have hb0 : b = 0 := funext fun K => (hreg K).right_eq_zero_of_smul
    (show m' K • b K = 0 from congrFun hcoef0 K)
  have h1 : ∀ K, (G1.TB g).structureMap (op (W' : X.Opens)) (b K) = 0 := fun K => by
    rw [hb0]
    exact map_zero _
  rw [hyY]
  refine (congrArg ((G1.TB g).proj _ (p : ℤ)) (Finset.sum_eq_zero fun K _ => ?_)).trans
    (map_zero _)
  rw [h1 K, zero_mul]

end ModelDensity

/-! ### Sections of quasi-coherent modules over affine opens -/

section AffineSections

/-- **An epimorphism of quasi-coherent modules is surjective on the sections over an affine
open**: over `U ≅ Spec Γ(X, U)` quasi-coherent modules are the modules over `Γ(X, U)`. -/
private theorem surjective_app_of_epi_of_isAffineOpen {X : Scheme.{0}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Epi φ]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (φ.app U) := by
  let f := hU.fromSpec
  let φ₂ := (Scheme.Modules.restrictFunctor f).map φ
  have hEpi₂ : Epi φ₂ := inferInstance
  let P := SheafOfModules.isQuasicoherent (Spec (CommRingCat.of Γ(X, U))).ringCatSheaf
  let qM : P.FullSubcategory := ⟨M.restrict f, by infer_instance⟩
  let qN : P.FullSubcategory := ⟨N.restrict f, by infer_instance⟩
  let φq : qM ⟶ qN := ⟨φ₂⟩
  have hEpiQ : Epi φq := by
    constructor
    intro Z a b hab
    apply ObjectProperty.hom_ext _
    exact (cancel_epi φ₂).mp (congrArg (fun k => k.hom) hab)
  have hEpiΓ :
      Epi ((AlgebraicGeometry.tildeEquiv (R := CommRingCat.of Γ(X, U))).inverse.map φq) :=
    inferInstance
  have hs₂ : Function.Surjective (φ₂.app ⊤) := by
    have h := (ModuleCat.epi_iff_surjective _).mp hEpiΓ
    change Function.Surjective (φ₂.app ⊤) at h
    exact h
  have hnat : φ₂.app ⊤ ≫ (N.restrictAppIso f ⊤).hom =
      (M.restrictAppIso f ⊤).hom ≫ φ.app (f ''ᵁ ⊤) := by
    ext x
    rfl
  rw [← show f ''ᵁ ⊤ = U by simp [f]]
  intro y
  obtain ⟨x, hx⟩ := hs₂ ((N.restrictAppIso f ⊤).inv y)
  refine ⟨(M.restrictAppIso f ⊤).hom x, ?_⟩
  have h := congrArg (fun q => q x) hnat
  change (N.restrictAppIso f ⊤).hom (φ₂.app ⊤ x) =
    φ.app (f ''ᵁ ⊤) ((M.restrictAppIso f ⊤).hom x) at h
  rw [← h, hx]
  simp

end AffineSections

/-! ### Regular forms from logarithmic forms -/

section PinnedInclusion

open MMP.Mori.Divisor.LogSpreadingProof.G1 Stacks.DeRhamDirectImage

variable {n : ℕ} {X : Scheme.{0}} {A : CommRingCat.{0}} (g : X ⟶ Spec A)
  [SmoothOfRelativeDimension n g] {D : MMP.Mori.Divisor X}
  (hD : D.IsRelativeSNC n g) (I : X.IdealSheafData)

include hD in
/-- **Restricting forms to the complement of a relative snc divisor is injective**, over a regular
base: on an affine open of a weak chart this is `eq_zero_of_resForms_eq_zero_of_weakChart`, and
forms are determined locally. -/
private theorem resForms_app_injective [IsRegularRing A]
    (hC : ∀ x : X, ∃ c : WeakChart g n (D.supp : Set X), x ∈ ((c.toLogData g D).W : X.Opens))
    (p : ℕ) (O : X.Opens) :
    Function.Injective (((resForms g D).app (p : ℤ)).val.app (op O)) := by
  intro a b hab
  have h0 : ((resForms g D).app (p : ℤ)).val.app (op O) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  rw [← sub_eq_zero]
  generalize a - b = y at h0 ⊢
  refine MMP.DeRham.eq_of_locally_eq_sections (M := g.relativeDifferentialForms (p : ℤ)) y 0
    fun x hx => ?_
  obtain ⟨c, hc⟩ := hC x
  obtain ⟨W', hxW', hW'⟩ := G1.exists_affineOpens_le
    (show x ∈ O ⊓ (c.toLogData g D).W from ⟨hx, hc⟩)
  refine ⟨W', hW'.trans inf_le_left, hxW', ?_⟩
  rw [map_zero]
  refine eq_zero_of_resForms_eq_zero_of_weakChart g D hD
    (exists_mem_support_genericPoint_eq D) c p (hW'.trans inf_le_right) _ ?_
  refine (PresheafOfModules.naturality_apply ((resForms g D).app (p : ℤ)).val
    (homOfLE (hW'.trans inf_le_left)).op y).trans ?_
  rw [h0]
  exact map_zero _

variable {g} in
/-- The relation "the regular form `y` restricts to the logarithmic form `s` on the complement
of the divisor". -/
private def IsRegularExt (p : ℕ) (O : X.Opens) (_ : O ≤ ⊤)
    (s : Γ(logModule n g D hD I p, O)) (y : Γ(g.relativeDifferentialForms (p : ℤ), O)) :
    Prop :=
  ((resForms g D).app (p : ℤ)).val.app (op O) y = s.1

/-- **Logarithmic forms extending across the divisor define a morphism**, given that restriction of
forms to the complement is injective and that every section of `I · Ω^p(log D)` extends locally. -/
private theorem isLocalSectionRel_isRegularExt (p : ℕ)
    (hinj : ∀ O : X.Opens, Function.Injective (((resForms g D).app (p : ℤ)).val.app (op O)))
    (hex : ∀ (O : X.Opens) (s : Γ(logModule n g D hD I p, O)) (x : X), x ∈ O →
      ∃ (O' : X.Opens) (h : O' ≤ O), x ∈ O' ∧ ∃ y : Γ(g.relativeDifferentialForms (p : ℤ), O'),
        ((resForms g D).app (p : ℤ)).val.app (op O') y =
          ((logModule n g D hD I p).presheaf.map (homOfLE h).op s).1) :
    MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hD I p) where
  exists_local O _ s x hx := by
    obtain ⟨O', h, hx', y, hy⟩ := hex O s x hx
    exact ⟨O', h, hx', y, hy⟩
  compat {O₁ O₂ O₃} _ _ h₃₁ h₃₂ s₁ y₁ s₂ y₂ h₁ h₂ hs := by
    have h₁' : ((resForms g D).app (p : ℤ)).val.app (op O₁) y₁ = s₁.1 := h₁
    have h₂' : ((resForms g D).app (p : ℤ)).val.app (op O₂) y₂ = s₂.1 := h₂
    apply hinj O₃
    refine (PresheafOfModules.naturality_apply ((resForms g D).app (p : ℤ)).val
      (homOfLE h₃₁).op y₁).trans ?_
    refine Eq.trans ?_ (PresheafOfModules.naturality_apply ((resForms g D).app (p : ℤ)).val
      (homOfLE h₃₂).op y₂).symm
    exact (congrArg _ h₁').trans ((congrArg Subtype.val hs).trans (congrArg _ h₂').symm)
  res {O O'} _ h s y hs := by
    have hs' : ((resForms g D).app (p : ℤ)).val.app (op O) y = s.1 := hs
    show ((resForms g D).app (p : ℤ)).val.app (op O')
        ((g.relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE h).op y) = _
    exact (PresheafOfModules.naturality_apply ((resForms g D).app (p : ℤ)).val
      (homOfLE h).op y).trans (congrArg _ hs')
  add {O} _ s y s' y' hs hs' := by
    have e : ((resForms g D).app (p : ℤ)).val.app (op O) y = s.1 := hs
    have e' : ((resForms g D).app (p : ℤ)).val.app (op O) y' = s'.1 := hs'
    show ((resForms g D).app (p : ℤ)).val.app (op O) (y + y') = (s + s').1
    exact (map_add (((resForms g D).app (p : ℤ)).val.app (op O)).hom y y').trans
      (congrArg₂ (· + ·) e e')
  smul {O} _ r s y hs := by
    have e : ((resForms g D).app (p : ℤ)).val.app (op O) y = s.1 := hs
    show ((resForms g D).app (p : ℤ)).val.app (op O) (r • y) = (r • s).1
    have e' : Scheme.Modules.Hom.app ((resForms g D).app (p : ℤ)) O y =
        (s.1 : Γ((Scheme.Modules.pushforward (LU D).ι).obj
          (Scheme.Hom.relativeDifferentialForms ((LU D).ι ≫ g) (p : ℤ)), O)) := e
    exact (Scheme.Modules.Hom.app_smul (U := O) ((resForms g D).app (p : ℤ)) r y).trans
      (congrArg (fun w : Γ((Scheme.Modules.pushforward (LU D).ι).obj
        (Scheme.Hom.relativeDifferentialForms ((LU D).ι ≫ g) (p : ℤ)), O) => r • w) e')

variable {hD I} in
/-- **Regular extension of logarithmic forms**: the morphism `I · Ω^p(log D) ⟶ Ω^p` of
`𝒪_X`-modules extending a logarithmic form across the divisor, when every such form extends. -/
private noncomputable def logToForms {p : ℕ} (hR : MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hD I p)) :
    logModule n g D hD I p ⟶ g.relativeDifferentialForms (p : ℤ) :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (hR.glue W.unop le_top)
      naturality := fun W W' i => by
        ext s
        change hR.glueSec le_top
            ((logModule n g D hD I p).presheaf.map (homOfLE (leOfHom i.unop)).op s) =
          (g.relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE (leOfHom i.unop)).op
            (hR.glueSec le_top s)
        exact hR.glueSec_res le_top (leOfHom i.unop) s }
    fun W r s => hR.glueSec_smul le_top r s⟩

variable {hD I} in
/-- The regular extension of a logarithmic form restricts to it off the divisor. -/
private theorem resForms_logToForms {p : ℕ} (hR : MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hD I p))
    (O : X.Opens) (s : Γ(logModule n g D hD I p, O)) :
    ((resForms g D).app (p : ℤ)).val.app (op O) ((logToForms g hR).app O s) = s.1 := by
  change ((resForms g D).app (p : ℤ)).val.app (op O) (hR.glueSec le_top s) = s.1
  refine MMP.DeRham.eq_of_locally_eq_sections (M := (Scheme.Modules.pushforward (LU D).ι).obj
    (Scheme.Hom.relativeDifferentialForms ((LU D).ι ≫ g) (p : ℤ))) _ _ fun x hx => ?_
  obtain ⟨O', h, hx', y, hy⟩ := hR.exists_local O le_top s hx
  refine ⟨O', h, hx', ?_⟩
  have e := hR.map_glueSec le_top h s y hy
  have hy' : ((resForms g D).app (p : ℤ)).val.app (op O') y =
      ((logModule n g D hD I p).presheaf.map (homOfLE h).op s).1 := hy
  refine (PresheafOfModules.naturality_apply ((resForms g D).app (p : ℤ)).val
    (homOfLE h).op _).symm.trans ?_
  refine (congrArg (((resForms g D).app (p : ℤ)).val.app (op O')) e).trans ?_
  exact hy'

include hD in
/-- **Twisted logarithmic forms extend across the divisor**, over a regular base. -/
private theorem isLocalSectionRel_twisted [IsRegularRing A]
    (hC : ∀ x : X, ∃ c : WeakChart g n (D.supp : Set X), x ∈ ((c.toLogData g D).W : X.Opens))
    (p : ℕ) : MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hD D.suppIdeal p) :=
  isLocalSectionRel_isRegularExt g hD D.suppIdeal p (resForms_app_injective g hD hC p)
    fun O s x hx => by
      obtain ⟨c, hc⟩ := hC x
      obtain ⟨W', hxW', hW'⟩ := G1.exists_affineOpens_le
        (show x ∈ O ⊓ (c.toLogData g D).W from ⟨hx, hc⟩)
      obtain ⟨y, hy⟩ := exists_resForms_eq_of_mem_twisted D g hD
        (exists_mem_support_genericPoint_eq D) c p (hW'.trans inf_le_right)
        ((logModule n g D hD D.suppIdeal p).presheaf.map (homOfLE (hW'.trans inf_le_left)).op s).1
        ((logModule n g D hD D.suppIdeal p).presheaf.map (homOfLE (hW'.trans inf_le_left)).op s).2
      exact ⟨W', hW'.trans inf_le_left, hxW', y, hy⟩

/-- The structure map of the de Rham chain is injective on sections once restriction is. -/
private theorem deRhamPushforwardChain_app_injective (p : ℕ)
    (hinj : ∀ O : X.Opens, Function.Injective (((resForms g D).app (p : ℤ)).val.app (op O)))
    (W : X.Opensᵒᵖ) :
    Function.Injective (((Stacks.DeRhamPullback.deRhamPushforwardChain
      (Scheme.Opens.ι D.supp.compl) g).f p).val.app W) := fun a b hab =>
  hinj W.unop ((deRhamPushforwardChain_app_eq g (LU D) p W a).symm.trans
    (hab.trans (deRhamPushforwardChain_app_eq g (LU D) p W b)))

variable {hD I} in
/-- The terms `I · Ω^p(log D) ⟶ Ω^p` over `g⁻¹𝒪`, on the terms of `logCx`. -/
private noncomputable def logToFormsX {p : ℕ} (ε : Bool)
    (hR : MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hD (bif ε then D.suppIdeal else ⊤) p)) :
    (logCx hD ε).X p ⟶ (Scheme.Hom.deRhamComplex g).X p :=
  (logSubmoduleIso n g D hD (bif ε then D.suppIdeal else ⊤) p).hom ≫
    (pushforward (toInverseImageBase g)).map (logToForms g hR) ≫
      (pushforwardInverseImageBaseIso g (g.relativeDifferentialForms (p : ℤ))).hom

variable {hD} in
private theorem resForms_logToFormsX {p : ℕ} (ε : Bool)
    (hR : MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hD (bif ε then D.suppIdeal else ⊤) p))
    (W : X.Opensᵒᵖ) (ω : ((logCx hD ε).X p).val.obj W) :
    ((resForms g D).app (p : ℤ)).val.app W ((logToFormsX g ε hR).val.app W ω) = ω.1 :=
  resForms_logToForms g hR W.unop
    ((logSubmoduleIso n g D hD (bif ε then D.suppIdeal else ⊤) p).hom.val.app W ω)

variable {hD} in
/-- **The regular extension `Ω^•(log D)` (twisted by `ε`) `⟶ Ω^•`**, when every logarithmic form
extends and restriction of forms is injective. -/
private noncomputable def logToFormsCx (ε : Bool)
    (hR : ∀ p : ℕ, MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hD (bif ε then D.suppIdeal else ⊤) p))
    (hinj : ∀ (p : ℕ) (O : X.Opens),
      Function.Injective (((resForms g D).app (p : ℤ)).val.app (op O))) :
    logCx hD ε ⟶ Scheme.Hom.deRhamComplex g where
  f p := logToFormsX g ε (hR p)
  comm' := by
    rintro p _ rfl
    ext W ω
    apply deRhamPushforwardChain_app_injective g (p + 1) (hinj (p + 1)) W
    have e1 := congrArg (fun φ => φ.val.app W ((logToFormsX g ε (hR p)).val.app W ω))
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι D.supp.compl) g).comm p
        (p + 1))
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ConcreteCategory.comp_apply] at e1 ⊢
    have a1 := (deRhamPushforwardChain_app_eq g D.supp.compl p W
      ((logToFormsX g ε (hR p)).val.app W ω)).trans (resForms_logToFormsX g ε (hR p) W ω)
    have a2 := (deRhamPushforwardChain_app_eq g D.supp.compl (p + 1) W
      ((logToFormsX g ε (hR (p + 1))).val.app W (((logCx hD ε).d p (p + 1)).val.app W ω))).trans
      (resForms_logToFormsX g ε (hR (p + 1)) W (((logCx hD ε).d p (p + 1)).val.app W ω))
    exact e1.symm.trans ((congrArg _ a1).trans ((subCx_d_val g D _ _ p W ω).symm.trans a2.symm))

variable {hD} in
private theorem resForms_logToFormsCx (ε : Bool)
    (hR : ∀ p : ℕ, MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hD (bif ε then D.suppIdeal else ⊤) p))
    (hinj : ∀ (p : ℕ) (O : X.Opens),
      Function.Injective (((resForms g D).app (p : ℤ)).val.app (op O)))
    (p : ℕ) (W : X.Opensᵒᵖ) (ω : ((logCx hD ε).X p).val.obj W) :
    ((resForms g D).app (p : ℤ)).val.app W (((logToFormsCx g ε hR hinj).f p).val.app W ω) =
      ω.1 :=
  resForms_logToFormsX g ε (hR p) W ω

variable {hD} in
/-- The terms of the regular extension of twisted logarithmic forms, on the terms of the
logarithmic de Rham complex. -/
private noncomputable def relLogToFormsX {p : ℕ}
    (hR : MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hD (bif true then D.suppIdeal else ⊤) p)) :
    (relativeLogDeRhamComplex n g D hD D.suppIdeal).X p ⟶ (Scheme.Hom.deRhamComplex g).X p :=
  (relLogXIso n g D hD true p).hom ≫
    (pushforward (toInverseImageBase g)).map (logToForms g hR) ≫
      (pushforwardInverseImageBaseIso g (g.relativeDifferentialForms (p : ℤ))).hom

variable {hD} in
private theorem resForms_relLogToFormsX {p : ℕ}
    (hR : MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hD (bif true then D.suppIdeal else ⊤) p))
    (W : X.Opensᵒᵖ) (ω : ((relativeLogDeRhamComplex n g D hD D.suppIdeal).X p).val.obj W) :
    ((resForms g D).app (p : ℤ)).val.app W ((relLogToFormsX g hR).val.app W ω) = ω.1 :=
  resForms_logToForms g hR W.unop ((relLogXIso n g D hD true p).hom.val.app W ω)

variable {hD} in
/-- **The inclusion `Ω^•(log D)(-D) ⟶ Ω^•`**, when twisted logarithmic forms extend across the
divisor and restriction of forms is injective. -/
private noncomputable def relLogToFormsCx
    (hR : ∀ p : ℕ, MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hD (bif true then D.suppIdeal else ⊤) p))
    (hinj : ∀ (p : ℕ) (O : X.Opens),
      Function.Injective (((resForms g D).app (p : ℤ)).val.app (op O))) :
    relativeLogDeRhamComplex n g D hD D.suppIdeal ⟶ Scheme.Hom.deRhamComplex g where
  f p := relLogToFormsX g (hR p)
  comm' := by
    rintro p _ rfl
    ext W ω
    apply deRhamPushforwardChain_app_injective g (p + 1) (hinj (p + 1)) W
    have e1 := congrArg (fun φ => φ.val.app W ((relLogToFormsX g (hR p)).val.app W ω))
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι D.supp.compl) g).comm p
        (p + 1))
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ConcreteCategory.comp_apply] at e1 ⊢
    have a1 := (deRhamPushforwardChain_app_eq g D.supp.compl p W
      ((relLogToFormsX g (hR p)).val.app W ω)).trans (resForms_relLogToFormsX g (hR p) W ω)
    have a2 := (deRhamPushforwardChain_app_eq g D.supp.compl (p + 1) W
      ((relLogToFormsX g (hR (p + 1))).val.app W
        (((relativeLogDeRhamComplex n g D hD D.suppIdeal).d p (p + 1)).val.app W ω))).trans
      (resForms_relLogToFormsX g (hR (p + 1)) W
        (((relativeLogDeRhamComplex n g D hD D.suppIdeal).d p (p + 1)).val.app W ω))
    have a3 := congrArg (fun φ => (φ.val.app W ω).1)
      (relativeLogDeRhamComplex_d n g D hD D.suppIdeal p)
    exact e1.symm.trans ((congrArg _ a1).trans (a3.symm.trans a2.symm))

variable {hD} in
/-- **The inclusion is pinned by its restriction to the complement of the divisor.** -/
private theorem relLogToFormsCx_pinned
    (hR : ∀ p : ℕ, MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hD (bif true then D.suppIdeal else ⊤) p))
    (hinj : ∀ (p : ℕ) (O : X.Opens),
      Function.Injective (((resForms g D).app (p : ℤ)).val.app (op O)))
    (p : ℕ) (W : X.Opensᵒᵖ)
    (ω : ((relativeLogDeRhamComplex n g D hD D.suppIdeal).X p).val.obj W) :
    ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι D.supp.compl) g).f p).val.app W
      (((relLogToFormsCx g hR hinj).f p).val.app W ω) = ω.1 :=
  (deRhamPushforwardChain_app_eq g (LU D) p W _).trans (resForms_relLogToFormsX g (hR p) W ω)

end PinnedInclusion

/-! ### The forms as logarithmic forms for the empty divisor -/

section ZeroLogForms

open MMP.Mori.Divisor.LogSpreadingProof.G1 Stacks.DeRhamDirectImage

variable {n : ℕ} {X : Scheme.{0}} {A : CommRingCat.{0}} (g : X ⟶ Spec A)
  [SmoothOfRelativeDimension n g] (h0 : (0 : MMP.Mori.Divisor X).IsRelativeSNC n g)

private theorem mem_LU_zero (x : X) : x ∈ LU (0 : MMP.Mori.Divisor X) := by
  show x ∈ ((0 : MMP.Mori.Divisor X).supp.compl : Set X)
  rw [TopologicalSpace.Closeds.coe_compl, coe_supp_zero, Set.compl_empty]
  trivial

/-- Restriction of forms to the complement of the empty divisor is injective. -/
private theorem resForms_zero_app_injective (p : ℕ) (O : X.Opens) :
    Function.Injective (((resForms g 0).app (p : ℤ)).val.app (op O)) :=
  deRhamFormsPushforwardHom_app_injective_of_le g (LU 0) (p : ℤ) fun x _ => mem_LU_zero x

/-- Every form on the complement of the empty divisor is a restriction. -/
private theorem isLocalSectionRel_zero (p : ℕ) :
    MMP.DeRham.IsLocalSectionRel (A := ⊤)
      (IsRegularExt h0 (bif false then (0 : MMP.Mori.Divisor X).suppIdeal else ⊤) p) :=
  isLocalSectionRel_isRegularExt g h0 _ p (resForms_zero_app_injective g p)
    fun O s x hx => by
      obtain ⟨t, ht⟩ := exists_deRhamFormsPushforwardHom_app_eq_of_le g (LU 0) (p : ℤ)
        (W := O) (fun x _ => mem_LU_zero x)
        ((logModule n g 0 h0 (bif false then (0 : MMP.Mori.Divisor X).suppIdeal else ⊤) p).presheaf.map
          (homOfLE (le_refl O)).op s).1
      exact ⟨O, le_refl O, hx, t, ht⟩

/-- **The regular forms of the logarithmic forms for the empty divisor**:
`Ω^•(log 0) ⟶ Ω^•`, inverse to the restriction to `X ∖ 0 = X`. -/
private noncomputable abbrev zeroLogToForms : logCx h0 false ⟶ Scheme.Hom.deRhamComplex g :=
  logToFormsCx g false (isLocalSectionRel_zero g h0) (resForms_zero_app_injective g)

/-- A morphism of sheaves of modules bijective on all sections is an isomorphism. -/
private theorem isIso_of_val_app_bijective {T : TopCat.{0}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{0}} {M N : SheafOfModules.{0} R}
    (φ : M ⟶ N) (h : ∀ W, Function.Bijective (φ.val.app W)) : IsIso φ := by
  have : IsIso ((SheafOfModules.toSheaf R).map φ) := by
    have : IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf R).map φ)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro W
      exact (ConcreteCategory.isIso_iff_bijective _).2 (h W)
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf R)

/-- The regular forms of logarithmic forms for the empty divisor are bijective on sections. -/
private theorem zeroLogToForms_app_bijective (p : ℕ) (W : X.Opensᵒᵖ) :
    Function.Bijective (((zeroLogToForms g h0).f p).val.app W) := by
  constructor
  · intro z z' hzz
    exact Subtype.ext ((resForms_logToFormsCx g false (isLocalSectionRel_zero g h0)
      (resForms_zero_app_injective g) p W z).symm.trans ((congrArg _ hzz).trans
        (resForms_logToFormsCx g false (isLocalSectionRel_zero g h0)
          (resForms_zero_app_injective g) p W z')))
  · intro y
    refine ⟨⟨((resForms g 0).app (p : ℤ)).val.app W y,
      resForms_mem_relativeLogForms_zero g h0 p W.unop y⟩, ?_⟩
    exact resForms_zero_app_injective g p W.unop (resForms_logToFormsCx g false
      (isLocalSectionRel_zero g h0) (resForms_zero_app_injective g) p W _)

private theorem isIso_zeroLogToForms : IsIso (zeroLogToForms g h0) := by
  haveI : ∀ p, IsIso ((zeroLogToForms g h0).f p) := fun p =>
    isIso_of_val_app_bijective _ (zeroLogToForms_app_bijective g h0 p)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The forms as logarithmic forms for the empty divisor**: `Ω^• ⟶ Ω^•(log 0)`, the inverse of
`zeroLogToForms`, restriction to `X ∖ 0 = X`. -/
private noncomputable def formsToZeroLog : Scheme.Hom.deRhamComplex g ⟶ logCx h0 false :=
  haveI := isIso_zeroLogToForms g h0
  inv (zeroLogToForms g h0)

private theorem formsToZeroLog_comp_zeroLogToForms :
    formsToZeroLog g h0 ≫ zeroLogToForms g h0 = 𝟙 _ := by
  haveI := isIso_zeroLogToForms g h0
  exact IsIso.inv_hom_id _

private theorem zeroLogToForms_comp_formsToZeroLog :
    zeroLogToForms g h0 ≫ formsToZeroLog g h0 = 𝟙 _ := by
  haveI := isIso_zeroLogToForms g h0
  exact IsIso.hom_inv_id _

private theorem zeroLogToForms_formsToZeroLog (p : ℕ) (W : X.Opensᵒᵖ)
    (y : ((Scheme.Hom.deRhamComplex g).X p).val.obj W) :
    ((zeroLogToForms g h0).f p).val.app W (((formsToZeroLog g h0).f p).val.app W y) = y :=
  congrArg (fun φ => (φ.f p).val.app W y) (formsToZeroLog_comp_zeroLogToForms g h0)

private theorem formsToZeroLog_zeroLogToForms (p : ℕ) (W : X.Opensᵒᵖ)
    (z : ((logCx h0 false).X p).val.obj W) :
    ((formsToZeroLog g h0).f p).val.app W (((zeroLogToForms g h0).f p).val.app W z) = z :=
  congrArg (fun φ => (φ.f p).val.app W z) (zeroLogToForms_comp_formsToZeroLog g h0)

private theorem formsToZeroLog_val (p : ℕ) (W : X.Opensᵒᵖ)
    (y : ((Scheme.Hom.deRhamComplex g).X p).val.obj W) :
    (((formsToZeroLog g h0).f p).val.app W y).1 = ((resForms g 0).app (p : ℤ)).val.app W y :=
  (resForms_logToFormsCx g false (isLocalSectionRel_zero g h0) (resForms_zero_app_injective g)
    p W _).symm.trans (congrArg _ (zeroLogToForms_formsToZeroLog g h0 p W y))

end ZeroLogForms

/-! ### Hypercohomology of a cokernel by the cone of total Čech complexes -/

section FibreCone

open Stacks.CategoryTheory.CechComplex Stacks.Cohomology.CechSheaf

attribute [local instance] secCommRing

variable {Y T X : Scheme.{0}} (h : Y ⟶ T) (q : Y ⟶ X) {ι : Type} (U : ι → X.Opens)

/-- `totMap` of a map of complexes injective on the intersections of the cover is injective. -/
private theorem totMap_injective {R : Type} [CommRing R]
    {PK PΩ : CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ} (Ψ : PK ⟶ PΩ)
    (hinj : ∀ (a p : ℕ) (t : Fin (p + 1) → ι),
      Function.Injective ((Ψ.f a).app (op (inter U t))).hom) (i : ℤ) :
    Function.Injective (totMap (U := U) Ψ i) := fun x y hxy =>
  funext fun k => funext fun t => hinj _ _ t (congrFun (congrFun hxy k) t)

/-- **Hypercohomology of a quotient complex by a mapping cone.** If `PK ⟶ PΩ ⟶ P` is a short exact
sequence on the sections over the intersections of an affine cover, where `P` computes the
hypercohomology of `K` by Čech data, then `ℍ^{i+1}(K)` is the cohomology of the cone of the
total Čech complexes `Tot(PK) ⟶ Tot(PΩ)`. -/
private theorem nonempty_hc_equiv_homologyAt_coneD
    (hU : (⊤ : Y.Opens) = ⨆ i, q ⁻¹ᵁ U i)
    [IsAffineHom (pullback.diagonal (terminal.from Y))] (hUaff : ∀ i, IsAffineOpen (q ⁻¹ᵁ U i))
    (K : CochainComplex.Plus (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h)))
    (hK : ∀ k, ∃ M : Y.Modules, M.IsQuasicoherent ∧
      Nonempty (K.1.X k ≅ (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase h)).obj M))
    (P : CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat.{0} (SectionRing
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h) ⊤)) ℕ)
    (e : ∀ b : ℕ, haveI := preservesFiniteProducts_opensMap q.base
      (opensCx h (Opens.map q.base) K.1).X (b : ℤ) ≅ P.X b)
    (hz : ∀ a : ℤ, a < 0 → haveI := preservesFiniteProducts_opensMap q.base
      IsZero ((opensCx h (Opens.map q.base) K.1).X a))
    (he : ∀ b : ℕ, haveI := preservesFiniteProducts_opensMap q.base
      (opensCx h (Opens.map q.base) K.1).d b (b + 1) ≫ (e (b + 1)).hom = (e b).hom ≫ P.d b (b + 1))
    {PK PΩ : CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat.{0} Γ(T, ⊤)) ℕ} (Ψ : PK ⟶ PΩ)
    (π : PΩ ⟶ resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom h) P)
    (hΨπ : Ψ ≫ π = 0)
    (hinj : ∀ (a p : ℕ) (t : Fin (p + 1) → ι),
      Function.Injective ((Ψ.f a).app (op (inter U t))).hom)
    (hsurj : ∀ (a p : ℕ) (t : Fin (p + 1) → ι),
      Function.Surjective ((π.f a).app (op (inter U t))).hom)
    (hex : ∀ (a p : ℕ) (t : Fin (p + 1) → ι),
      LinearMap.ker ((π.f a).app (op (inter U t))).hom =
        LinearMap.range ((Ψ.f a).app (op (inter U t))).hom) (i : ℤ) :
    Nonempty (Hc h K (i + 1) ≃ₗ[Γ(T, ⊤)]
      homologyAt (coneD (totD U PK) (totD U PΩ) (fun j => totMap (U := U) Ψ j) i)
        (coneD (totD U PK) (totD U PΩ) (fun j => totMap (U := U) Ψ j) (i + 1))) := by
  haveI := preservesFiniteProducts_opensMap q.base
  refine (nonempty_hcEquivHomologyAt h (Opens.map q.base) U hU hUaff K hK P e hz he i).elim
    fun E1 => ?_
  refine (nonempty_homologyAt_cone_equiv_coker (d₀ := totD U PK) (d₁ := totD U PΩ)
    (Ψ := fun j => totMap (U := U) Ψ j) (fun j => LinearMap.ext fun x => totD_totD U PK j x)
    (fun j => LinearMap.ext fun x => totD_totD U PΩ j x) (fun j x => totMap_totD U PK Ψ j x)
    (totMap_injective U Ψ hinj) i).elim fun E2 => ?_
  refine (nonempty_homologyAt_cokerD_equiv U Ψ π hΨπ hsurj hex i).elim fun E3 => ?_
  exact ⟨E1.trans ((homologyAtResCxEquiv U _ P i).trans (E3.symm.trans E2.symm))⟩

end FibreCone

/-! ### The cokernel of the pinned inclusion on a scheme over a regular ring -/

section FibreCokernel

open MMP.Mori.Divisor.LogSpreadingProof.G1 Stacks.DeRhamDirectImage
open Stacks.CategoryTheory.CechComplex Stacks.Cohomology.CechSheaf
open scoped ZeroObject

variable {n : ℕ} {Y X : Scheme.{0}} {K : CommRingCat.{0}} (f : Y ⟶ Spec K)
  [SmoothOfRelativeDimension n f] (q : Y ⟶ X)

attribute [local instance] secCommRing in
/-- The map of presheaf complexes on a site over the opens of `Y` induced by a map of complexes
of sheaves of `f⁻¹𝒪`-modules on `Y`. -/
private noncomputable def logPresheafMap {C : Type} [Category.{0} C] [HasFiniteProducts C]
    (Φ : C ⥤ Y.Opens) [PreservesFiniteProducts Φ]
    {L L' : CochainComplex (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing f)) ℕ} (φ : L ⟶ L') :
    resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f) (siteCx f Φ L) ⟶
      resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f) (siteCx f Φ L') :=
  (((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f))).mapHomologicalComplex
      _).map
    ((((Functor.whiskeringLeft _ _ _).obj (siteFun Φ).op).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (((sectionsPresheafFunctor ⊤).mapHomologicalComplex _).map φ))

attribute [local instance] secCommRing in
private theorem logPresheafMap_comp {C : Type} [Category.{0} C] [HasFiniteProducts C]
    (Φ : C ⥤ Y.Opens) [PreservesFiniteProducts Φ]
    {L L' L'' : CochainComplex (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing f)) ℕ} (φ : L ⟶ L')
    (ψ : L' ⟶ L'') : logPresheafMap f Φ (φ ≫ ψ) = logPresheafMap f Φ φ ≫ logPresheafMap f Φ ψ := by
  unfold logPresheafMap
  simp only [Functor.map_comp]

attribute [local instance] secCommRing in
private theorem logPresheafMap_zero {C : Type} [Category.{0} C] [HasFiniteProducts C]
    (Φ : C ⥤ Y.Opens) [PreservesFiniteProducts Φ]
    {L L' : CochainComplex (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing f)) ℕ} :
    logPresheafMap f Φ (0 : L ⟶ L') = 0 := by
  unfold logPresheafMap
  simp only [Functor.map_zero]

attribute [local instance] secCommRing in
/-- The map of presheaf complexes in degree `0` on a site over the opens of `Y` induced by a map
of sheaves of `f⁻¹𝒪`-modules on `Y`. -/
private noncomputable def singlePresheafMap {C : Type} [Category.{0} C] [HasFiniteProducts C]
    (Φ : C ⥤ Y.Opens) [PreservesFiniteProducts Φ]
    {M N : SheafOfModules.{0} (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing f)}
    (φ : M ⟶ N) :
    resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
        ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj ((siteSections f Φ).obj M)) ⟶
      resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
        ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj ((siteSections f Φ).obj N)) :=
  haveI := siteSections_preservesZeroMorphisms f Φ
  (((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f))).mapHomologicalComplex
      _).map ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map ((siteSections f Φ).map φ))

attribute [local instance] secCommRing in
private theorem singlePresheafMap_comp {C : Type} [Category.{0} C] [HasFiniteProducts C]
    (Φ : C ⥤ Y.Opens) [PreservesFiniteProducts Φ]
    {M N P : SheafOfModules.{0} (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing f)}
    (φ : M ⟶ N) (ψ : N ⟶ P) :
    singlePresheafMap f Φ (φ ≫ ψ) = singlePresheafMap f Φ φ ≫ singlePresheafMap f Φ ψ := by
  unfold singlePresheafMap
  simp only [Functor.map_comp]

attribute [local instance] secCommRing in
private theorem singlePresheafMap_zero {C : Type} [Category.{0} C] [HasFiniteProducts C]
    (Φ : C ⥤ Y.Opens) [PreservesFiniteProducts Φ]
    {M N : SheafOfModules.{0} (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing f)} :
    singlePresheafMap f Φ (0 : M ⟶ N) = 0 := by
  haveI := siteSections_preservesZeroMorphisms f Φ
  unfold singlePresheafMap
  simp only [Functor.map_zero]

variable [IsRegularRing K] {DY : MMP.Mori.Divisor Y} (hDY : DY.IsRelativeSNC n f)
  (hCY : ∀ y : Y, ∃ c : WeakChart f n (DY.supp : Set Y), y ∈ ((c.toLogData f DY).W : Y.Opens))
  (h0 : (0 : MMP.Mori.Divisor Y).IsRelativeSNC n f)

/-- The regular extension of the twisted logarithmic forms, on `logCx`. -/
private noncomputable abbrev twistedToForms :
    logCx hDY true ⟶ Scheme.Hom.deRhamComplex f :=
  logToFormsCx f true (isLocalSectionRel_twisted f hDY hCY) (resForms_app_injective f hDY hCY)

/-- **The regular extension `Ω^•(log D)(-D) ⟶ Ω^•(log 0)`**, on `logCx`. -/
private noncomputable abbrev twistedToZeroLog : logCx hDY true ⟶ logCx h0 false :=
  twistedToForms f hDY hCY ≫ formsToZeroLog f h0

variable {hDY} in
/-- A pinned inclusion agrees with the regular extension. -/
private theorem twistedToForms_app_eq
    (i : relativeLogDeRhamComplex n f DY hDY DY.suppIdeal ⟶ Scheme.Hom.deRhamComplex f)
    (hi : ∀ (p : ℕ) (W : Y.Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n f DY hDY DY.suppIdeal).X p).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι DY.supp.compl) f).f p).val.app
        W ((i.f p).val.app W ω) = ω.1)
    (a : ℕ) (W : Y.Opensᵒᵖ) (ω : ((logCx hDY true).X a).val.obj W) :
    ((twistedToForms f hDY hCY).f a).val.app W ω = (i.f a).val.app W
      ⟨ω.1, (mem_relativeLogDeRhamTerms_iff n f DY hDY true a W ω.1).2 ω.2⟩ :=
  deRhamPushforwardChain_app_injective f a (resForms_app_injective f hDY hCY a) W
    (((deRhamPushforwardChain_app_eq f (LU DY) a W _).trans
      (resForms_logToFormsCx f true _ _ a W ω)).trans
      (hi a W ⟨ω.1, (mem_relativeLogDeRhamTerms_iff n f DY hDY true a W ω.1).2 ω.2⟩).symm)

variable {hDY} in
/-- The sections of a pinned inclusion: the twisted logarithmic forms among the regular forms. -/
private theorem exists_twistedToForms_app_eq
    (i : relativeLogDeRhamComplex n f DY hDY DY.suppIdeal ⟶ Scheme.Hom.deRhamComplex f)
    (hi : ∀ (p : ℕ) (W : Y.Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n f DY hDY DY.suppIdeal).X p).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι DY.supp.compl) f).f p).val.app
        W ((i.f p).val.app W ω) = ω.1)
    (a : ℕ) (W : Y.Opensᵒᵖ)
    (ω : ((relativeLogDeRhamComplex n f DY hDY DY.suppIdeal).X a).val.obj W) :
    ∃ ω' : ((logCx hDY true).X a).val.obj W,
      ((twistedToForms f hDY hCY).f a).val.app W ω' = (i.f a).val.app W ω :=
  ⟨⟨ω.1, (mem_relativeLogDeRhamTerms_iff n f DY hDY true a W ω.1).1 ω.2⟩,
    twistedToForms_app_eq f hCY i hi a W _⟩

/-- The regular extension is injective on sections. -/
private theorem twistedToForms_app_injective (a : ℕ) (W : Y.Opensᵒᵖ) :
    Function.Injective (((twistedToForms f hDY hCY).f a).val.app W) := fun x y hxy =>
  Subtype.ext ((resForms_logToFormsCx f true _ _ a W x).symm.trans
    ((congrArg _ hxy).trans (resForms_logToFormsCx f true _ _ a W y)))

/-- `twistedToZeroLog` is injective on sections. -/
private theorem twistedToZeroLog_app_injective (a : ℕ) (W : Y.Opensᵒᵖ) :
    Function.Injective (((twistedToZeroLog f hDY hCY h0).f a).val.app W) := fun x y hxy => by
  apply twistedToForms_app_injective f hDY hCY a W
  have := congrArg (((zeroLogToForms f h0).f a).val.app W) hxy
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    HomologicalComplex.comp_f] at this
  rwa [zeroLogToForms_formsToZeroLog, zeroLogToForms_formsToZeroLog] at this

variable {hDY hCY}
variable (i : relativeLogDeRhamComplex n f DY hDY DY.suppIdeal ⟶ Scheme.Hom.deRhamComplex f)
  (hi : ∀ (p : ℕ) (W : Y.Opensᵒᵖ)
    (ω : ((relativeLogDeRhamComplex n f DY hDY DY.suppIdeal).X p).val.obj W),
    ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι DY.supp.compl) f).f p).val.app
      W ((i.f p).val.app W ω) = ω.1)
  (Dc : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec K).sheaf))) ℕ)
  (qc : Scheme.Hom.deRhamComplex f ⟶ Dc) (hiq : i ≫ qc = 0)
  (hq : IsColimit (CokernelCofork.ofπ qc hiq))

include hi in
/-- A pinned inclusion is a monomorphism. -/
private theorem mono_pinned_f (a : ℕ) : Mono (i.f a) :=
  mono_of_val_app_injective _ fun W x y hxy => Subtype.ext (by
    have h := congrArg (((Stacks.DeRhamPullback.deRhamPushforwardChain
      (Scheme.Opens.ι DY.supp.compl) f).f a).val.app W) hxy
    rwa [hi, hi] at h)

/-- The cokernel term, as a cokernel cofork. -/
private noncomputable def isColimit_cokernelCofork_f (a : ℕ) :
    IsColimit (CokernelCofork.ofπ (qc.f a)
      (by rw [← HomologicalComplex.comp_f, hiq, HomologicalComplex.zero_f]) :
        Cofork (i.f a) 0) :=
  isColimitCoforkMapOfIsColimit' (HomologicalComplex.eval _ _ a) _ hq

include hi hq in
/-- **The sections of `Ω^•(log D)(-D) ⟶ Ω^• ⟶ 𝒟^•` are exact in the middle.** -/
private theorem ker_qc_app_eq_range (a : ℕ) (W : Y.Opensᵒᵖ) :
    LinearMap.ker ((qc.f a).val.app W).hom = LinearMap.range ((i.f a).val.app W).hom := by
  haveI := mono_pinned_f f i hi a
  let S := ShortComplex.mk (i.f a) (qc.f a)
    (by rw [← HomologicalComplex.comp_f, hiq, HomologicalComplex.zero_f])
  have hS : S.Exact := S.exact_of_g_is_cokernel (isColimit_cokernelCofork_f f i Dc qc hiq hq a)
  have hSW := hS.map_of_mono_of_preservesKernel (SheafOfModules.evaluation _ W)
    (inferInstanceAs (Mono (i.f a))) inferInstance
  exact hSW.moduleCat_range_eq_ker.symm

variable [IsLocallyNoetherian Y] (hR : ∀ p : ℕ,
  MMP.DeRham.IsLocalSectionRel (A := ⊤) (IsRegularExt hDY (bif true then DY.suppIdeal else ⊤) p))
  (hinj : ∀ (p : ℕ) (O : Y.Opens),
    Function.Injective (((resForms f DY).app (p : ℤ)).val.app (op O)))

/-- The cokernel of the regular extension of twisted forms, as a quasi-coherent module. -/
private noncomputable abbrev cokernelLogToForms (p : ℕ) : Y.Modules :=
  cokernel (logToForms f (hR p))

include hDY in
private theorem isCoherent_cokernelLogToForms (p : ℕ) :
    (cokernelLogToForms f hR p).IsCoherent := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  haveI : (logModule n f DY hDY (bif true then DY.suppIdeal else ⊤) p).IsCoherent :=
    G1.logModule_isCoherent hDY true p
  haveI : (f.relativeDifferentialForms ((p : ℕ) : ℤ)).IsCoherent :=
    Scheme.Hom.isCoherent_relativeDifferentialForms _ p
  exact AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel _

include hi hinj in
/-- A pinned inclusion is the regular extension. -/
private theorem pinned_f_eq (a : ℕ) :
    i.f a = (relLogXIso n f DY hDY true a).hom ≫
      (pushforward (toInverseImageBase f)).map (logToForms f (hR a)) ≫
        (pushforwardInverseImageBaseIso f (f.relativeDifferentialForms (a : ℤ))).hom := by
  ext W ω
  refine deRhamPushforwardChain_app_injective f a (hinj a) W ((hi a W ω).trans ?_)
  exact (relLogToFormsCx_pinned f hR hinj a W ω).symm

include hi hinj in
/-- The comparison square of the pinned inclusion with the regular extension of `𝒪`-modules. -/
private theorem pinned_f_comm (a : ℕ) :
    (pushforward (toInverseImageBase f)).map (logToForms f (hR a)) ≫
        (pushforwardInverseImageBaseIso f (f.relativeDifferentialForms (a : ℤ))).hom =
      (relLogXIso n f DY hDY true a).symm.hom ≫ i.f a := by
  rw [pinned_f_eq f i hi hR hinj a]
  exact (Iso.inv_hom_id_assoc _ _).symm

/-- **The terms of the cokernel are the cokernels of `𝒪`-modules.** -/
private noncomputable def cokernelIso (a : ℕ) :
    (pushforward (toInverseImageBase f)).obj (cokernelLogToForms f hR a) ≅ Dc.X a :=
  haveI := preservesFiniteColimits_pushforward_toInverseImageBase f
  let e1 : (pushforward (toInverseImageBase f)).obj (cokernel (logToForms f (hR a))) ≅
      cokernel ((pushforward (toInverseImageBase f)).map (logToForms f (hR a))) :=
    PreservesCokernel.iso _ _
  e1 ≪≫ cokernel.mapIso _ (i.f a) _ _ (pinned_f_comm f i hi hR hinj a) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso (isColimit_cokernelCofork_f f i Dc qc hiq hq a)

include hi hinj hq in
/-- The cokernel identification is compatible with the projections. -/
private theorem map_π_comp_cokernelIso_hom (a : ℕ) :
    (pushforward (toInverseImageBase f)).map (cokernel.π (logToForms f (hR a))) ≫
        (cokernelIso f i hi Dc qc hiq hq hR hinj a).hom =
      (pushforwardInverseImageBaseIso f (f.relativeDifferentialForms (a : ℤ))).hom ≫ qc.f a := by
  haveI := preservesFiniteColimits_pushforward_toInverseImageBase f
  have c1 := PreservesCokernel.π_iso_hom (pushforward (toInverseImageBase f))
    (logToForms f (hR a))
  have c2 : cokernel.π ((pushforward (toInverseImageBase f)).map (logToForms f (hR a))) ≫
      (cokernel.mapIso _ (i.f a) _ _ (pinned_f_comm f i hi hR hinj a)).hom =
      (pushforwardInverseImageBaseIso f (f.relativeDifferentialForms (a : ℤ))).hom ≫
        cokernel.π (i.f a) :=
    cokernel.π_desc _ _ _
  have c3 := (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (isColimit_cokernelCofork_f f i Dc qc hiq hq a) WalkingParallelPair.one
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) c1).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) c2).trans
      ((Category.assoc _ _ _).trans (congrArg _ c3)))))

include hi hq hinj in
/-- **The terms of the cokernel are quasi-coherent.** -/
private theorem nonempty_iso_pushforward_cokernel (a : ℕ) :
    Nonempty (Dc.X a ≅ (pushforward (toInverseImageBase f)).obj (cokernelLogToForms f hR a)) :=
  ⟨(cokernelIso f i hi Dc qc hiq hq hR hinj a).symm⟩

include hi hq hDY hR hinj in
/-- **The cokernel is onto on the sections over an affine open.** -/
private theorem surjective_qc_app (a : ℕ) (V : Y.Opens) (hV : IsAffineOpen V) :
    Function.Surjective ((qc.f a).val.app (op V)).hom := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  haveI : (f.relativeDifferentialForms ((a : ℕ) : ℤ)).IsCoherent :=
    Scheme.Hom.isCoherent_relativeDifferentialForms _ a
  haveI : (cokernelLogToForms f hR a).IsCoherent := isCoherent_cokernelLogToForms f hR a
  haveI := _root_.isQuasicoherent_of_isCoherent (f.relativeDifferentialForms ((a : ℕ) : ℤ))
  haveI := _root_.isQuasicoherent_of_isCoherent (cokernelLogToForms f hR a)
  intro d
  obtain ⟨y, hy⟩ := surjective_app_of_epi_of_isAffineOpen (cokernel.π (logToForms f (hR a))) V hV
    ((cokernelIso f i hi Dc qc hiq hq hR hinj a).inv.val.app (op V) d)
  refine ⟨y, ?_⟩
  have h1 := congrArg (fun φ => φ.val.app (op V) y) (map_π_comp_cokernelIso_hom f i hi Dc qc hiq hq hR hinj a)
  have h2 := congrArg (fun φ => φ.val.app (op V) d) (cokernelIso f i hi Dc qc hiq hq hR hinj a).inv_hom_id
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply] at h1 h2
  refine h1.symm.trans ?_
  refine Eq.trans ?_ h2
  exact congrArg (fun w => ConcreteCategory.hom
    ((cokernelIso f i hi Dc qc hiq hq hR hinj a).hom.val.app (op V)) w) hy

include hi hq hDY in
/-- `twistedToZeroLog ≫ zeroLogToForms ≫ qc = 0`. -/
private theorem twistedToZeroLog_comp_qc :
    twistedToZeroLog f hDY hCY h0 ≫ zeroLogToForms f h0 ≫ qc = 0 := by
  have h1 : formsToZeroLog f h0 ≫ zeroLogToForms f h0 = 𝟙 _ := by
    ext a W y
    exact zeroLogToForms_formsToZeroLog f h0 a W y
  have h2 : twistedToForms f hDY hCY ≫ qc = 0 := by
    ext a W ω
    change (qc.f a).val.app W (((twistedToForms f hDY hCY).f a).val.app W ω) = 0
    rw [twistedToForms_app_eq f hCY i hi]
    exact congrArg (fun φ => (φ.f a).val.app W
      (⟨ω.1, (mem_relativeLogDeRhamTerms_iff n f DY hDY true a W ω.1).2 ω.2⟩ :
        ((relativeLogDeRhamComplex n f DY hDY DY.suppIdeal).X a).val.obj W)) hiq
  rw [Category.assoc, ← Category.assoc (formsToZeroLog f h0), h1, Category.id_comp, h2]

include hi hq in
/-- **The sections of `Ω^•(log D)(-D) ⟶ Ω^•(log 0) ⟶ 𝒟^•` are exact in the middle.** -/
private theorem ker_zeroLogToForms_comp_qc (a : ℕ) (W : Y.Opensᵒᵖ) :
    LinearMap.ker (((zeroLogToForms f h0 ≫ qc).f a).val.app W).hom =
      LinearMap.range (((twistedToZeroLog f hDY hCY h0).f a).val.app W).hom := by
  ext z
  constructor
  · intro hz'
    have hz'' : (qc.f a).val.app W (((zeroLogToForms f h0).f a).val.app W z) = 0 := hz'
    have hmem : ((zeroLogToForms f h0).f a).val.app W z ∈
        LinearMap.range ((i.f a).val.app W).hom := by
      rw [← ker_qc_app_eq_range f i hi Dc qc hiq hq a]
      exact hz''
    obtain ⟨ω, hω⟩ := hmem
    obtain ⟨ω', hω'⟩ := exists_twistedToForms_app_eq f hCY i hi a W ω
    refine ⟨ω', ?_⟩
    change ((formsToZeroLog f h0).f a).val.app W (((twistedToForms f hDY hCY).f a).val.app W ω') = z
    rw [hω']
    change ((formsToZeroLog f h0).f a).val.app W ((i.f a).val.app W ω) = z
    rw [show (i.f a).val.app W ω = ((zeroLogToForms f h0).f a).val.app W z from hω]
    exact formsToZeroLog_zeroLogToForms f h0 a W z
  · rintro ⟨ω, rfl⟩
    exact congrArg (fun φ => ((φ.f a).val.app W) ω)
      (twistedToZeroLog_comp_qc (hCY := hCY) f h0 i hi Dc qc hiq hq)

include hi hq hDY hCY in
/-- **The map `Ω^•(log 0) ⟶ 𝒟^•` is onto on the sections over an affine open.** -/
private theorem surjective_zeroLogToForms_comp_qc (a : ℕ) (V : Y.Opens) (hV : IsAffineOpen V) :
    Function.Surjective (((zeroLogToForms f h0 ≫ qc).f a).val.app (op V)).hom := by
  intro d
  obtain ⟨y, hy⟩ := surjective_qc_app f i hi Dc qc hiq hq (isLocalSectionRel_twisted f hDY hCY)
    (resForms_app_injective f hDY hCY) a V hV d
  refine ⟨((formsToZeroLog f h0).f a).val.app _ y, ?_⟩
  change (qc.f a).val.app _ (((zeroLogToForms f h0).f a).val.app _
    (((formsToZeroLog f h0).f a).val.app _ y)) = d
  rw [zeroLogToForms_formsToZeroLog]
  exact hy

include hi hq hDY hCY in
/-- The terms of the extension by zero of the cokernel complex are quasi-coherent. -/
private theorem hcCoker_exists_isQuasicoherent (k' : ℤ) :
    ∃ M : Y.Modules, M.IsQuasicoherent ∧
      Nonempty ((Dc.extend ComplexShape.embeddingUpNat).X k' ≅
        (pushforward (toInverseImageBase f)).obj M) := by
  rcases lt_or_ge k' 0 with hk | hk
  · have hzk : IsZero ((Dc.extend ComplexShape.embeddingUpNat).X k') :=
      HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat k' (fun j => by
        change ((j : ℕ) : ℤ) ≠ k'; omega)
    haveI := Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
      (isZero_zero (Y.Modules))
    exact ⟨0, _root_.isQuasicoherent_of_isCoherent _,
      ⟨hzk.iso (isZero_pushforward_zero f)⟩⟩
  · obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    obtain ⟨E⟩ := nonempty_iso_pushforward_cokernel f i hi Dc qc hiq hq
      (isLocalSectionRel_twisted f hDY hCY) (resForms_app_injective f hDY hCY) b
    haveI := isCoherent_cokernelLogToForms f (isLocalSectionRel_twisted f hDY hCY) b
    exact ⟨_, _root_.isQuasicoherent_of_isCoherent _,
      ⟨Dc.extendXIso ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f b) ≪≫ E⟩⟩

attribute [local instance] secCommRing in
include hi hq hDY in
/-- **Hypercohomology of the cokernel of a pinned inclusion by a mapping cone.** For an affine
cover pulled back along `q : Y ⟶ X` whose intersections are affine, `ℍ^{k+1}(𝒟^•)` is the
cohomology of the cone of the total Čech complexes of the regular extension
`Ω^•(log D)(-D) ⟶ Ω^•(log 0)`. -/
private theorem nonempty_hc_cokernel_equiv_homologyAt_coneD {ι : Type} (U : ι → X.Opens)
    (hU : (⊤ : Y.Opens) = ⨆ j, q ⁻¹ᵁ U j) [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (hUaff : ∀ j, IsAffineOpen (q ⁻¹ᵁ U j))
    (hinter : ∀ (p : ℕ) (t : Fin (p + 1) → ι), IsAffineOpen (q ⁻¹ᵁ inter U t)) (k : ℤ) :
    haveI := preservesFiniteProducts_opensMap q.base
    Nonempty (Hc f ⟨Dc.extend ComplexShape.embeddingUpNat, 0,
        CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ (k + 1) ≃ₗ[Γ(Spec K, ⊤)]
      homologyAt (coneD (totD U (logPresheafCxPullback (q := q) hDY true))
          (totD U (logPresheafCxPullback (q := q) h0 false))
          (fun j => totMap (U := U)
            (logPresheafMap f (Opens.map q.base) (twistedToZeroLog f hDY hCY h0)) j) k)
        (coneD (totD U (logPresheafCxPullback (q := q) hDY true))
          (totD U (logPresheafCxPullback (q := q) h0 false))
          (fun j => totMap (U := U)
            (logPresheafMap f (Opens.map q.base) (twistedToZeroLog f hDY hCY h0)) j)
          (k + 1))) := by
  haveI := preservesFiniteProducts_opensMap q.base
  refine (exists_extend_cechData f (Opens.map q.base) Dc).elim fun e hez => ?_
  refine nonempty_hc_equiv_homologyAt_coneD f q U hU hUaff ⟨Dc.extend ComplexShape.embeddingUpNat,
      0, CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ (fun k' =>
        hcCoker_exists_isQuasicoherent f (hDY := hDY) (hCY := hCY) i hi Dc qc hiq hq k')
    (siteCx f (Opens.map q.base) Dc) e hez.2 hez.1
    (PK := logPresheafCxPullback (q := q) hDY true) (PΩ := logPresheafCxPullback (q := q) h0 false)
    (logPresheafMap f (Opens.map q.base) (twistedToZeroLog f hDY hCY h0))
    (logPresheafMap f (Opens.map q.base) (zeroLogToForms f h0 ≫ qc)) ?_
    (fun a p t x y hxy => twistedToZeroLog_app_injective f hDY hCY h0 a _ hxy)
    (fun a p t => surjective_zeroLogToForms_comp_qc (hCY := hCY) f h0 i hi Dc qc hiq hq a _
      (hinter p t))
    (fun a p t => by
      have h := ker_zeroLogToForms_comp_qc (hCY := hCY) f h0 i hi Dc qc hiq hq a
        (op ((Opens.map q.base).obj (inter U t)))
      ext x
      exact SetLike.ext_iff.mp h x) k
  · exact (logPresheafMap_comp f _ _ _).symm.trans
      ((congrArg (logPresheafMap f (Opens.map q.base))
        (twistedToZeroLog_comp_qc (hCY := hCY) f h0 i hi Dc qc hiq hq)).trans
        (logPresheafMap_zero f _))

attribute [local instance] secCommRing in
include hi hq hDY hCY in
/-- The terms of a cokernel term placed in degree `0` are quasi-coherent. -/
private theorem hcSingle_quasicoherent (p : ℕ) (k' : ℤ) :
    ∃ M : Y.Modules, M.IsQuasicoherent ∧
      Nonempty ((single0 f (Dc.X p)).1.X k' ≅ (pushforward (toInverseImageBase f)).obj M) := by
  by_cases hk : k' = 0
  · subst hk
    haveI := isCoherent_cokernelLogToForms f (isLocalSectionRel_twisted f hDY hCY) p
    exact (nonempty_iso_pushforward_cokernel f i hi Dc qc hiq hq
      (isLocalSectionRel_twisted f hDY hCY) (resForms_app_injective f hDY hCY) p).elim fun E =>
      ⟨_, _root_.isQuasicoherent_of_isCoherent _,
        ⟨HomologicalComplex.singleObjXSelf _ 0 _ ≪≫ E⟩⟩
  · haveI := Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
      (isZero_zero (Y.Modules))
    exact ⟨0, _root_.isQuasicoherent_of_isCoherent _,
      ⟨(HomologicalComplex.isZero_single_obj_X _ _ _ _ hk).iso (isZero_pushforward_zero f)⟩⟩

attribute [local instance] secCommRing in
include hi hq hDY in
/-- The degree-`p` terms of `Ω^•(log D)(-D) ⟶ Ω^•(log 0) ⟶ 𝒟^•` compose to zero on sections. -/
private theorem hcSingle_comp_eq_zero (p : ℕ) :
    haveI := preservesFiniteProducts_opensMap q.base
    singlePresheafMap f (Opens.map q.base) ((twistedToZeroLog f hDY hCY h0).f p) ≫
      singlePresheafMap f (Opens.map q.base) ((zeroLogToForms f h0 ≫ qc).f p) = 0 := by
  haveI := preservesFiniteProducts_opensMap q.base
  exact (singlePresheafMap_comp f _ _ _).symm.trans
    ((congrArg (singlePresheafMap f (Opens.map q.base))
      ((HomologicalComplex.comp_f _ _ p).symm.trans
        ((congrArg (fun φ => HomologicalComplex.Hom.f φ p)
          (twistedToZeroLog_comp_qc (hCY := hCY) f h0 i hi Dc qc hiq hq)).trans
          (HomologicalComplex.zero_f _ _ p)))).trans
      (singlePresheafMap_zero f _))

attribute [local instance] secCommRing in
/-- The degree-`p` term of `Ω^•(log D)(-D) ⟶ Ω^•(log 0)` is injective on sections. -/
private theorem hcSingle_injective (p : ℕ) {ι : Type} (U : ι → X.Opens) (a p' : ℕ)
    (t : Fin (p' + 1) → ι) :
    haveI := preservesFiniteProducts_opensMap q.base
    Function.Injective (((singlePresheafMap f (Opens.map q.base)
      ((twistedToZeroLog f hDY hCY h0).f p)).f a).app (op (inter U t))).hom := by
  haveI := preservesFiniteProducts_opensMap q.base
  rcases a with _ | b
  · intro x y hxy
    exact twistedToZeroLog_app_injective f hDY hCY h0 p _ hxy
  · haveI := subsingleton_resCx_single
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
      ((siteSections f (Opens.map q.base)).obj
      ((logCx hDY true).X p)) b (op (inter U t))
    exact Function.injective_of_subsingleton _

attribute [local instance] secCommRing in
include hi hq hDY hCY in
/-- The degree-`p` term of `Ω^•(log 0) ⟶ 𝒟^•` is onto on the sections over an affine open. -/
private theorem hcSingle_surjective (p : ℕ) {ι : Type} (U : ι → X.Opens) (a p' : ℕ)
    (t : Fin (p' + 1) → ι) (hV : IsAffineOpen (q ⁻¹ᵁ inter U t)) :
    haveI := preservesFiniteProducts_opensMap q.base
    Function.Surjective (((singlePresheafMap f (Opens.map q.base)
      ((zeroLogToForms f h0 ≫ qc).f p)).f a).app (op (inter U t))).hom := by
  haveI := preservesFiniteProducts_opensMap q.base
  rcases a with _ | b
  · exact surjective_zeroLogToForms_comp_qc (hCY := hCY) f h0 i hi Dc qc hiq hq p _ hV
  · haveI := subsingleton_resCx_single
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
      ((siteSections f (Opens.map q.base)).obj (Dc.X p)) b (op (inter U t))
    exact fun d => ⟨0, Subsingleton.elim _ _⟩

attribute [local instance] secCommRing in
include hi hq in
/-- The degree-`p` terms of `Ω^•(log D)(-D) ⟶ Ω^•(log 0) ⟶ 𝒟^•` are exact on sections. -/
private theorem hcSingle_ker_eq_range (p : ℕ) {ι : Type} (U : ι → X.Opens) (a p' : ℕ)
    (t : Fin (p' + 1) → ι) :
    haveI := preservesFiniteProducts_opensMap q.base
    LinearMap.ker (((singlePresheafMap f (Opens.map q.base)
        ((zeroLogToForms f h0 ≫ qc).f p)).f a).app (op (inter U t))).hom =
      LinearMap.range (((singlePresheafMap f (Opens.map q.base)
        ((twistedToZeroLog f hDY hCY h0).f p)).f a).app (op (inter U t))).hom := by
  haveI := preservesFiniteProducts_opensMap q.base
  rcases a with _ | b
  · have h := ker_zeroLogToForms_comp_qc (hCY := hCY) f h0 i hi Dc qc hiq hq p
      (op ((Opens.map q.base).obj (inter U t)))
    ext x
    exact SetLike.ext_iff.mp h x
  · haveI := subsingleton_resCx_single
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
      ((siteSections f (Opens.map q.base)).obj
      ((logCx h0 false).X p)) b (op (inter U t))
    haveI := subsingleton_resCx_single
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
      ((siteSections f (Opens.map q.base)).obj (Dc.X p)) b (op (inter U t))
    ext z
    exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩

attribute [local instance] secCommRing in
include hi hq hDY in
/-- **Coherent cohomology of the cokernel terms by a mapping cone.** For an affine cover pulled
back along `q : Y ⟶ X` whose intersections are affine, `H^{k+1}(𝒟^p)` is the cohomology of the
cone of the total Čech complexes of the regular extension `Ω^p(log D)(-D) ⟶ Ω^p(log 0)`, placed
in degree `0`. -/
private theorem nonempty_hc_single_cokernel_equiv_homologyAt_coneD (p : ℕ) {ι : Type}
    (U : ι → X.Opens)
    (hU : (⊤ : Y.Opens) = ⨆ j, q ⁻¹ᵁ U j) [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (hUaff : ∀ j, IsAffineOpen (q ⁻¹ᵁ U j))
    (hinter : ∀ (p : ℕ) (t : Fin (p + 1) → ι), IsAffineOpen (q ⁻¹ᵁ inter U t)) (k : ℤ) :
    haveI := preservesFiniteProducts_opensMap q.base
    Nonempty (Hc f (single0 f (Dc.X p)) (k + 1) ≃ₗ[Γ(Spec K, ⊤)]
      homologyAt (coneD
          (totD U (resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
            ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
              ((siteSections f (Opens.map q.base)).obj ((logCx hDY true).X p)))))
          (totD U (resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
            ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
              ((siteSections f (Opens.map q.base)).obj ((logCx h0 false).X p)))))
          (fun j => totMap (U := U)
            (singlePresheafMap f (Opens.map q.base) ((twistedToZeroLog f hDY hCY h0).f p)) j) k)
        (coneD
          (totD U (resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
            ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
              ((siteSections f (Opens.map q.base)).obj ((logCx hDY true).X p)))))
          (totD U (resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
            ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
              ((siteSections f (Opens.map q.base)).obj ((logCx h0 false).X p)))))
          (fun j => totMap (U := U)
            (singlePresheafMap f (Opens.map q.base) ((twistedToZeroLog f hDY hCY h0).f p)) j)
          (k + 1))) := by
  haveI := preservesFiniteProducts_opensMap q.base
  refine (exists_single_cechData f (Opens.map q.base) (Dc.X p)).elim fun e hez => ?_
  exact nonempty_hc_equiv_homologyAt_coneD f q U hU hUaff (single0 f (Dc.X p))
    (hcSingle_quasicoherent (hCY := hCY) f i hi Dc qc hiq hq p)
    ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
      ((siteSections f (Opens.map q.base)).obj (Dc.X p))) e hez.2 hez.1
    (singlePresheafMap f (Opens.map q.base) ((twistedToZeroLog f hDY hCY h0).f p))
    (singlePresheafMap f (Opens.map q.base) ((zeroLogToForms f h0 ≫ qc).f p))
    (hcSingle_comp_eq_zero (hCY := hCY) f q h0 i hi Dc qc hiq hq p)
    (fun a p' t => hcSingle_injective f q h0 p U a p' t)
    (fun a p' t => hcSingle_surjective (hCY := hCY) f q h0 i hi Dc qc hiq hq p U a p' t
      (hinter p' t))
    (fun a p' t => hcSingle_ker_eq_range (hCY := hCY) f q h0 i hi Dc qc hiq hq p U a p' t) k

end FibreCokernel

/-! ### Generic constancy and base change for the cone of total Čech complexes -/

section TotCone

open Stacks.CategoryTheory.CechComplex TensorProduct

variable {C : Type} [Category.{0} C] [HasFiniteProducts C] {ι : Type} (U : ι → C)

/-- A product of flat modules is flat: tensoring distributes over the product. -/
private theorem flat_prod {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N] :
    Module.Flat R (M × N) := by
  refine Module.Flat.iff_lTensor_preserves_injective_linearMap.2 fun P Q _ _ _ _ L hL => ?_
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := M) L hL
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := N) L hL
  have key : ∀ z, TensorProduct.prodLeft R R M N Q (L.lTensor (M × N) z) =
      ((L.lTensor M).prodMap (L.lTensor N)) (TensorProduct.prodLeft R R M N P z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      obtain ⟨m, n⟩ := x
      simp only [LinearMap.lTensor_tmul, TensorProduct.prodLeft_tmul, LinearMap.prodMap_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  intro a b hab
  apply (TensorProduct.prodLeft R R M N P).injective
  have hab' := congrArg (TensorProduct.prodLeft R R M N Q) hab
  rw [key, key] at hab'
  exact h1.prodMap h2 hab'

/-- **The cone of total Čech complexes has generic cohomology.** Over a Noetherian domain, if the
two complexes of presheaves vanish in high degrees on the intersections of a finite cover and
have flat total complexes with finite cohomology, then the cohomology of the cone of a map
between them has constant rank over the fields where some `s ≠ 0` does not vanish. -/
private theorem exists_s_coneD {Z : TopCat.{0}} {ι : Type} [Finite ι] (U : ι → Opens Z) {R : Type}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {P₀ P₁ : CochainComplex ((Opens Z)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ} (Ψ : P₀ ⟶ P₁) (A : ℕ)
    (hvan₀ : ∀ (a : ℕ), A < a → ∀ (p : ℕ) (t : Fin (p + 1) → ι),
      Subsingleton ((P₀.X a).obj (op (inter U t))))
    (hvan₁ : ∀ (a : ℕ), A < a → ∀ (p : ℕ) (t : Fin (p + 1) → ι),
      Subsingleton ((P₁.X a).obj (op (inter U t))))
    (hflat₀ : ∀ i, Module.Flat R (TotX U P₀ i)) (hflat₁ : ∀ i, Module.Flat R (TotX U P₁ i))
    (hfin₀ : ∀ i, Module.Finite R (homologyAt (totD U P₀ i) (totD U P₀ (i + 1))))
    (hfin₁ : ∀ i, Module.Finite R (homologyAt (totD U P₁ i) (totD U P₁ (i + 1)))) :
    ∃ s : R, s ≠ 0 ∧ ∀ (L : Type) [Field L] [Algebra R L], algebraMap R L s ≠ 0 → ∀ i,
      Module.finrank L (homologyAt
        ((coneD (totD U P₀) (totD U P₁) (fun j => totMap (U := U) Ψ j) i).baseChange L)
        ((coneD (totD U P₀) (totD U P₁) (fun j => totMap (U := U) Ψ j) (i + 1)).baseChange L)) =
      Module.finrank (FractionRing R) (homologyAt
        ((coneD (totD U P₀) (totD U P₁) (fun j => totMap (U := U) Ψ j) i).baseChange
          (FractionRing R))
        ((coneD (totD U P₀) (totD U P₁) (fun j => totMap (U := U) Ψ j) (i + 1)).baseChange
          (FractionRing R))) := by
  refine (exists_totHomotopy U P₀ A hvan₀).elim fun h₀ hh₀ => ?_
  refine (exists_totHomotopy U P₁ A hvan₁).elim fun h₁ hh₁ => ?_
  have hdd₀ : ∀ i, totD U P₀ (i + 1) ∘ₗ totD U P₀ i = 0 := fun i =>
    LinearMap.ext fun x => totD_totD U P₀ i x
  have hdd₁ : ∀ i, totD U P₁ (i + 1) ∘ₗ totD U P₁ i = 0 := fun i =>
    LinearMap.ext fun x => totD_totD U P₁ i x
  have hΨ : ∀ i x, totMap (U := U) Ψ (i + 1) (totD U P₀ i x) = totD U P₁ i (totMap (U := U) Ψ i x) :=
    fun i x => totMap_totD U P₀ Ψ i x
  refine (cone_homotopy hΨ h₀ h₁ ((Nat.card ι + A : ℕ) : ℤ)
    (fun j hj x => hh₀ j hj x) (fun j hj x => hh₁ j hj x)).elim fun H hH => ?_
  refine (exists_finrank_homology_baseChange_eq (coneX (TotX U P₀) (TotX U P₁))
    (coneD (totD U P₀) (totD U P₁) (fun j => totMap (U := U) Ψ j)) (coneD_comp hdd₀ hdd₁ hΨ)
    (fun i => haveI := hflat₁ i; haveI := hflat₀ (i + 1); flat_prod) (-1)
    ((Nat.card ι + A : ℕ) : ℤ)
    (fun i hi => haveI := subsingleton_totX_of_neg U P₁ i (by omega)
      haveI := subsingleton_totX_of_neg U P₀ (i + 1) (by omega); inferInstance) H hH
    (moduleFinite_homologyAt_cone hdd₀ hdd₁ hΨ hfin₀ hfin₁)).elim fun s hs => ?_
  exact ⟨s, hs.1, fun L _ _ hL i => hs.2 L hL i⟩

/-- **Termwise maps commute with the total Čech differential**, for any map of total complexes
given componentwise by maps of the coefficients compatible with restrictions and differentials. -/
private theorem comp_totD_of_apply {R₀ L : Type} [CommRing R₀] [CommRing L] [Algebra R₀ L]
    (P₀ : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} R₀) ℕ) (P₁ : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} L) ℕ)
    (Φ : ∀ (a : ℕ) (V : Cᵒᵖ), (P₀.X a).obj V →+ (P₁.X a).obj V)
    (hnat : ∀ (a : ℕ) {V V' : Cᵒᵖ} (g : V ⟶ V') (x : (P₀.X a).obj V),
      Φ a V' (((P₀.X a).map g).hom x) = ((P₁.X a).map g).hom (Φ a V x))
    (hd : ∀ (a : ℕ) (V : Cᵒᵖ) (x : (P₀.X a).obj V),
      Φ (a + 1) V (((P₀.d a (a + 1)).app V).hom x) = ((P₁.d a (a + 1)).app V).hom (Φ a V x))
    (F : ∀ n, TotX U P₀ n → TotX U P₁ n)
    (hF : ∀ n x (j : TotIndex n) t, F n x j t = Φ j.1.2 _ (x j t)) (n : ℤ) (x : TotX U P₀ n) :
    F (n + 1) (totD U P₀ n x) = totD U P₁ n (F n x) := by
  have hF' : ∀ n x (j : TotIndex n), F n x j = fun t => Φ j.1.2 _ (x j t) :=
    fun n x j => funext (hF n x j)
  funext ⟨⟨p, a⟩, h⟩ t
  rcases p with _ | q <;> rcases a with _ | b
  · simp [hF, totD_apply]
  · simp only [hF, totD_apply, totDCech_zero, totDCoef_succ, zero_add, Pi.smul_apply,
      cochainMap_apply, map_zsmul, Pi.zero_apply]
    rw [hd]
  · simp only [hF', totD_apply, totDCech_succ, totDCoef_zero, add_zero, Pi.add_apply,
      Pi.zero_apply]
    exact Φ_cechD U P₀ P₁ Φ hnat _ _ _ _
  · simp only [hF', totD_apply, totDCech_succ, totDCoef_succ, Pi.add_apply, Pi.smul_apply,
      cochainMap_apply, map_add, map_zsmul]
    rw [Φ_cechD U P₀ P₁ Φ hnat, hd]

/-- **Base change for the cone of total Čech complexes.** Termwise base change maps of the two
complexes, compatible with the restrictions, the differentials and the maps between them,
identify the cohomology of the cone over `L` with that of the base change of the cone. -/
private theorem nonempty_homologyAt_coneD_baseChange_equiv [Finite ι] {R₀ L : Type} [CommRing R₀]
    [CommRing L] [Algebra R₀ L]
    {P₀ P₁ : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} R₀) ℕ}
    {Q₀ Q₁ : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} L) ℕ} (Ψ : P₀ ⟶ P₁) (Ψ' : Q₀ ⟶ Q₁)
    (Φ₀ : ∀ (a : ℕ) (V : Cᵒᵖ), (P₀.X a).obj V →+ (Q₀.X a).obj V)
    (Φ₁ : ∀ (a : ℕ) (V : Cᵒᵖ), (P₁.X a).obj V →+ (Q₁.X a).obj V)
    (hnat₀ : ∀ (a : ℕ) {V V' : Cᵒᵖ} (g : V ⟶ V') (x : (P₀.X a).obj V),
      Φ₀ a V' (((P₀.X a).map g).hom x) = ((Q₀.X a).map g).hom (Φ₀ a V x))
    (hnat₁ : ∀ (a : ℕ) {V V' : Cᵒᵖ} (g : V ⟶ V') (x : (P₁.X a).obj V),
      Φ₁ a V' (((P₁.X a).map g).hom x) = ((Q₁.X a).map g).hom (Φ₁ a V x))
    (hd₀ : ∀ (a : ℕ) (V : Cᵒᵖ) (x : (P₀.X a).obj V),
      Φ₀ (a + 1) V (((P₀.d a (a + 1)).app V).hom x) = ((Q₀.d a (a + 1)).app V).hom (Φ₀ a V x))
    (hd₁ : ∀ (a : ℕ) (V : Cᵒᵖ) (x : (P₁.X a).obj V),
      Φ₁ (a + 1) V (((P₁.d a (a + 1)).app V).hom x) = ((Q₁.d a (a + 1)).app V).hom (Φ₁ a V x))
    (hsm₀ : ∀ (a : ℕ) (V : Cᵒᵖ) (r : R₀) (x : (P₀.X a).obj V),
      Φ₀ a V (r • x) = algebraMap R₀ L r • Φ₀ a V x)
    (hsm₁ : ∀ (a : ℕ) (V : Cᵒᵖ) (r : R₀) (x : (P₁.X a).obj V),
      Φ₁ a V (r • x) = algebraMap R₀ L r • Φ₁ a V x)
    (hbc₀ : ∀ (a p : ℕ) (t : Fin (p + 1) → ι),
      ∃ e : L ⊗[R₀] (P₀.X a).obj (op (inter U t)) ≃ₗ[L] (Q₀.X a).obj (op (inter U t)),
        ∀ x, e (1 ⊗ₜ x) = Φ₀ a _ x)
    (hbc₁ : ∀ (a p : ℕ) (t : Fin (p + 1) → ι),
      ∃ e : L ⊗[R₀] (P₁.X a).obj (op (inter U t)) ≃ₗ[L] (Q₁.X a).obj (op (inter U t)),
        ∀ x, e (1 ⊗ₜ x) = Φ₁ a _ x)
    (hΨ : ∀ (a : ℕ) (V : Cᵒᵖ) (x : (P₀.X a).obj V),
      Φ₁ a V (((Ψ.f a).app V).hom x) = ((Ψ'.f a).app V).hom (Φ₀ a V x)) (i : ℤ) :
    Nonempty (homologyAt
        ((coneD (totD U P₀) (totD U P₁) (fun j => totMap (U := U) Ψ j) i).baseChange L)
        ((coneD (totD U P₀) (totD U P₁) (fun j => totMap (U := U) Ψ j) (i + 1)).baseChange L)
          ≃ₗ[L]
      homologyAt (coneD (totD U Q₀) (totD U Q₁) (fun j => totMap (U := U) Ψ' j) i)
        (coneD (totD U Q₀) (totD U Q₁) (fun j => totMap (U := U) Ψ' j) (i + 1))) := by
  letI inst₀ : ∀ (a : ℕ) (V : Cᵒᵖ), Module R₀ ((Q₀.X a).obj V) := fun a V =>
    Module.compHom _ (algebraMap R₀ L)
  letI inst₁ : ∀ (a : ℕ) (V : Cᵒᵖ), Module R₀ ((Q₁.X a).obj V) := fun a V =>
    Module.compHom _ (algebraMap R₀ L)
  haveI : ∀ (a : ℕ) (V : Cᵒᵖ), IsScalarTower R₀ L ((Q₀.X a).obj V) := fun a V =>
    ⟨fun r k x => by
      show (r • k) • x = algebraMap R₀ L r • k • x
      rw [Algebra.smul_def, mul_smul]⟩
  haveI : ∀ (a : ℕ) (V : Cᵒᵖ), IsScalarTower R₀ L ((Q₁.X a).obj V) := fun a V =>
    ⟨fun r k x => by
      show (r • k) • x = algebraMap R₀ L r • k • x
      rw [Algebra.smul_def, mul_smul]⟩
  let Φc₀ : ∀ (a : ℕ) (V : Cᵒᵖ), (P₀.X a).obj V →ₗ[R₀] (Q₀.X a).obj V := fun a V =>
    { toFun := Φ₀ a V
      map_add' := map_add _
      map_smul' := hsm₀ a V }
  let Φc₁ : ∀ (a : ℕ) (V : Cᵒᵖ), (P₁.X a).obj V →ₗ[R₀] (Q₁.X a).obj V := fun a V =>
    { toFun := Φ₁ a V
      map_add' := map_add _
      map_smul' := hsm₁ a V }
  have hΦc₀ : ∀ (a p : ℕ) (t : Fin (p + 1) → ι), IsBaseChange L (Φc₀ a (op (inter U t))) := by
    intro a p t
    obtain ⟨e, he⟩ := hbc₀ a p t
    exact IsBaseChange.of_equiv e he
  have hΦc₁ : ∀ (a p : ℕ) (t : Fin (p + 1) → ι), IsBaseChange L (Φc₁ a (op (inter U t))) := by
    intro a p t
    obtain ⟨e, he⟩ := hbc₁ a p t
    exact IsBaseChange.of_equiv e he
  let Φn₀ : ∀ n, TotX U P₀ n →ₗ[R₀] TotX U Q₀ n := fun n =>
    LinearMap.pi fun j => (LinearMap.pi fun t => Φc₀ j.1.2 _ ∘ₗ LinearMap.proj t) ∘ₗ
      LinearMap.proj j
  let Φn₁ : ∀ n, TotX U P₁ n →ₗ[R₀] TotX U Q₁ n := fun n =>
    LinearMap.pi fun j => (LinearMap.pi fun t => Φc₁ j.1.2 _ ∘ₗ LinearMap.proj t) ∘ₗ
      LinearMap.proj j
  have hΦn₀ : ∀ n, IsBaseChange L (Φn₀ n) := by
    intro n
    haveI := finite_totIndex n
    exact IsBaseChange.pi _ fun j => IsBaseChange.pi _ fun t => hΦc₀ _ _ t
  have hΦn₁ : ∀ n, IsBaseChange L (Φn₁ n) := by
    intro n
    haveI := finite_totIndex n
    exact IsBaseChange.pi _ fun j => IsBaseChange.pi _ fun t => hΦc₁ _ _ t
  have hc₀ : ∀ n x, Φn₀ (n + 1) (totD U P₀ n x) = totD U Q₀ n (Φn₀ n x) :=
    comp_totD_of_apply U P₀ Q₀ Φ₀ hnat₀ hd₀ (fun n x => Φn₀ n x) fun _ _ _ _ => rfl
  have hc₁ : ∀ n x, Φn₁ (n + 1) (totD U P₁ n x) = totD U Q₁ n (Φn₁ n x) :=
    comp_totD_of_apply U P₁ Q₁ Φ₁ hnat₁ hd₁ (fun n x => Φn₁ n x) fun _ _ _ _ => rfl
  have hcΨ : ∀ n x, Φn₁ n (totMap (U := U) Ψ n x) = totMap (U := U) Ψ' n (Φn₀ n x) := by
    intro n x
    funext j t
    exact hΨ j.1.2 _ (x j t)
  let Φcone : ∀ n, coneX (TotX U P₀) (TotX U P₁) n →ₗ[R₀] coneX (TotX U Q₀) (TotX U Q₁) n :=
    fun n => (Φn₁ n).prodMap (Φn₀ (n + 1))
  have hΦcone : ∀ n, IsBaseChange L (Φcone n) := fun n =>
    IsBaseChange.prodMap (S := L) (Φn₁ n) (Φn₀ (n + 1)) (hΦn₁ n) (hΦn₀ (n + 1))
  refine ⟨homologyAtEquivOfIsBaseChange _ _ Φcone hΦcone (fun n z => ?_) i⟩
  obtain ⟨x, y⟩ := z
  change ((Φn₁ (n + 1) (totD U P₁ n x + totMap (U := U) Ψ (n + 1) y)),
      Φn₀ (n + 1 + 1) (-totD U P₀ (n + 1) y)) =
    (totD U Q₁ n (Φn₁ n x) + totMap (U := U) Ψ' (n + 1) (Φn₀ (n + 1) y),
      -totD U Q₀ (n + 1) (Φn₀ (n + 1) y))
  rw [map_add, map_neg, hc₁, hcΨ, hc₀]

end TotCone

/-! ### Pullback of forms commutes with restriction to the complement of the divisor -/

section PullbackRestriction

open MMP.Mori.Divisor.LogSpreadingProof.G1

/-- Sections over equal opens that are heterogeneously equal agree after restriction. -/
private theorem val_map_eq_of_heq {T : TopCat.{0}} {R : (Opens T)ᵒᵖ ⥤ RingCat.{0}}
    (M : PresheafOfModules.{0} R) {A B : Opens T} (h : A = B) (x : M.obj (op B))
    (y : M.obj (op A)) (hxy : HEq x y) : M.map (homOfLE h.le).op x = y := by
  subst h
  rw [eq_of_heq hxy]
  exact (congrArg (fun φ => (M.map φ).hom y) (Subsingleton.elim _ (𝟙 _))).trans
    (by rw [M.map_id]; rfl)

variable {X Y S T : Scheme.{0}} {g : X ⟶ S} {f : Y ⟶ T} {q : Y ⟶ X} {φ : T ⟶ S}
  (hcomm : q ≫ g = f ≫ φ) (DX : MMP.Mori.Divisor X) (DY : MMP.Mori.Divisor Y)
  (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (DX.supp : Set X))

include hsupp in
/-- **Pullback of forms commutes with restriction to the complement of the divisor.** -/
private theorem resForms_deRhamFormsPushforwardHom (k : ℕ) (W : X.Opens)
    (u : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (k : ℤ)).val.obj (op W)) :
    ((resForms f DY).app (k : ℤ)).val.app (op (q ⁻¹ᵁ W))
        (((Scheme.Hom.deRhamFormsPushforwardHom q g f φ hcomm).app (k : ℤ)).val.app (op W) u) =
      ψW hcomm DX DY hsupp k W (((resForms g DX).app (k : ℤ)).val.app (op W) u) := by
  have e1 := Scheme.Hom.deRhamFormsPushforwardHom_comp_apply (LU DY).ι q g f ((LU DY).ι ≫ f) φ
    (𝟙 T) hcomm (Category.comp_id _).symm
    (by simp only [Category.assoc, Category.id_comp, hcomm]) k (op W) u
  have e2 := Scheme.Hom.deRhamFormsPushforwardHom_comp_apply (qU DX DY hsupp) (LU DX).ι g
    ((LU DX).ι ≫ g) ((LU DY).ι ≫ f) (𝟙 S) φ (Category.comp_id _).symm
    (qU_comm hcomm DX DY hsupp)
    (by simp only [Category.assoc, Category.comp_id, qU_comm hcomm DX DY hsupp]) k (op W) u
  have he : qU DX DY hsupp ≫ (LU DX).ι = (LU DY).ι ≫ q := Scheme.Hom.resLE_comp_ι _ _
  have hh := Scheme.Hom.deRhamFormsPushforwardHom_apply_heq (s := g)
    (s'₁ := (LU DY).ι ≫ f) (s'₂ := (LU DY).ι ≫ f) (g₁ := φ ≫ 𝟙 S) (g₂ := 𝟙 T ≫ φ) he rfl
    (by rw [Category.comp_id, Category.id_comp])
    (by simp only [Category.assoc, Category.comp_id, qU_comm hcomm DX DY hsupp])
    (by simp only [Category.assoc, Category.id_comp, hcomm])
    (k : ℤ) (op W) u
  refine e1.trans ?_
  unfold ψW
  exact (val_map_eq_of_heq _ (congrArg (fun m => m ⁻¹ᵁ W) he).symm _ _ hh).symm.trans
    (congrArg _ e2.symm)

end PullbackRestriction

/-! ### The cokernel of the pinned inclusion spreads out -/

section ModelFibre

open MMP.Mori.Divisor.LogSpreadingProof.G1 Stacks.CategoryTheory.CechComplex TensorProduct

attribute [local instance] secCommRing

variable (n : ℕ) {R₀ : Type} [CommRing R₀] [IsRegularRing R₀]
  {𝒳₀ : Scheme.{0}} (g₀ : 𝒳₀ ⟶ Spec (CommRingCat.of R₀)) [SmoothOfRelativeDimension n g₀]
  [IsProper g₀] {𝒟₀ : MMP.Mori.Divisor 𝒳₀} (h𝒟₀ : 𝒟₀.IsRelativeSNC n g₀) {ι : Type} [Finite ι]
  (C : ι → WeakChart g₀ n (𝒟₀.supp : Set 𝒳₀)) (hC : ⨆ i, ((C i).W : 𝒳₀.Opens) = ⊤)

include hC in
private theorem forall_mem_weakChart :
    ∀ x : 𝒳₀, ∃ c : WeakChart g₀ n (𝒟₀.supp : Set 𝒳₀),
      x ∈ ((c.toLogData g₀ 𝒟₀).W : 𝒳₀.Opens) := by
  intro x
  have : x ∈ (⨆ i, ((C i).W : 𝒳₀.Opens)) := by rw [hC]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
  exact ⟨C i, hi⟩

/-- **The regular extension on the model**, on the presheaves of its opens. -/
private noncomputable abbrev modelConeMap :
    logPresheafCx h𝒟₀ true ⟶ logPresheafCx (isRelativeSNC_zero h𝒟₀) false :=
  logPresheafMap g₀ (𝟭 𝒳₀.Opens)
    (twistedToZeroLog g₀ h𝒟₀ (forall_mem_weakChart n g₀ C hC) (isRelativeSNC_zero h𝒟₀))

/-- The logarithmic forms vanish above the relative dimension on the Čech intersections of a
cover by weak charts. -/
private theorem sModelCone_subsingleton {D : MMP.Mori.Divisor 𝒳₀} (hD : D.IsRelativeSNC n g₀)
    (C' : ι → WeakChart g₀ n (D.supp : Set 𝒳₀)) (ε : Bool) :
    ∀ (a : ℕ), n < a → ∀ (p : ℕ) (t : Fin (p + 1) → ι),
      Subsingleton (((logPresheafCx hD ε).X a).obj
        (op (inter (fun i => ((C' i).W : 𝒳₀.Opens)) t))) :=
  fun a ha k t => let ⟨haff, c, hle⟩ := inter_charts hD C' k t
    subsingleton_logComponent hD ε a ha _ haff c hle

/-- The total Čech complex of the logarithmic forms on a cover by weak charts is flat over the
base. -/
private theorem sModelCone_flat {D : MMP.Mori.Divisor 𝒳₀} (hD : D.IsRelativeSNC n g₀)
    (C' : ι → WeakChart g₀ n (D.supp : Set 𝒳₀)) (ε : Bool) (i : ℤ) :
    Module.Flat Γ(Spec (CommRingCat.of R₀), ⊤)
      (TotX (fun i => ((C' i).W : 𝒳₀.Opens)) (logPresheafCx hD ε) i) := by
  haveI := finite_totIndex i
  refine flat_pi' fun j => flat_pi' fun t => ?_
  obtain ⟨haff, c, hle⟩ := inter_charts hD C' _ t
  exact flat_logComponent hD ε _ _ haff c hle

include hC in
/-- The cohomology of the total Čech complex of the logarithmic forms on the chart cover is
finite over the base. -/
private theorem sModelCone_finite {D : MMP.Mori.Divisor 𝒳₀} (hD : D.IsRelativeSNC n g₀)
    (ε : Bool) (i : ℤ) :
    Module.Finite Γ(Spec (CommRingCat.of R₀), ⊤) (homologyAt
      (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx hD ε) i)
      (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx hD ε) (i + 1))) := by
  haveI : IsLocallyNoetherian 𝒳₀ := LocallyOfFiniteType.isLocallyNoetherian g₀
  exact moduleFinite_logDeRham g₀ hD _ hC.symm (fun i => (C i).W.2) ε i

/-- `exists_s_coneD` for complexes of presheaves on the opens of a scheme. -/
private theorem sModelCone_coneD {𝒳 : Scheme.{0}} {κ : Type} [Finite κ] (U : κ → 𝒳.Opens)
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {P₀ P₁ : CochainComplex ((𝒳.Opens)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ} (Ψ : P₀ ⟶ P₁) (A : ℕ)
    (hvan₀ : ∀ (a : ℕ), A < a → ∀ (p : ℕ) (t : Fin (p + 1) → κ),
      Subsingleton ((P₀.X a).obj (op (inter U t))))
    (hvan₁ : ∀ (a : ℕ), A < a → ∀ (p : ℕ) (t : Fin (p + 1) → κ),
      Subsingleton ((P₁.X a).obj (op (inter U t))))
    (hflat₀ : ∀ i, Module.Flat R (TotX U P₀ i)) (hflat₁ : ∀ i, Module.Flat R (TotX U P₁ i))
    (hfin₀ : ∀ i, Module.Finite R (homologyAt (totD U P₀ i) (totD U P₀ (i + 1))))
    (hfin₁ : ∀ i, Module.Finite R (homologyAt (totD U P₁ i) (totD U P₁ (i + 1)))) :
    ∃ s : R, s ≠ 0 ∧ ∀ (L : Type) [Field L] [Algebra R L], algebraMap R L s ≠ 0 → ∀ i,
      Module.finrank L (homologyAt
        ((coneD (totD U P₀) (totD U P₁) (fun j => totMap (U := U) Ψ j) i).baseChange L)
        ((coneD (totD U P₀) (totD U P₁) (fun j => totMap (U := U) Ψ j) (i + 1)).baseChange L)) =
      Module.finrank (FractionRing R) (homologyAt
        ((coneD (totD U P₀) (totD U P₁) (fun j => totMap (U := U) Ψ j) i).baseChange
          (FractionRing R))
        ((coneD (totD U P₀) (totD U P₁) (fun j => totMap (U := U) Ψ j) (i + 1)).baseChange
          (FractionRing R))) :=
  exists_s_coneD U Ψ A hvan₀ hvan₁ hflat₀ hflat₁ hfin₀ hfin₁

/-- **A generic base change constant for the cone of the regular extension on the model.** -/
private theorem exists_s_modelCone [IsDomain R₀] :
    haveI := (baseRing_facts (R₀ := R₀)).1
    ∃ s : Γ(Spec (CommRingCat.of R₀), ⊤), s ≠ 0 ∧
      ∀ (L : Type) [Field L] [Algebra Γ(Spec (CommRingCat.of R₀), ⊤) L],
      algebraMap Γ(Spec (CommRingCat.of R₀), ⊤) L s ≠ 0 → ∀ i,
        Module.finrank L (homologyAt
          ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
            (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
            (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
              (modelConeMap n g₀ h𝒟₀ C hC) j) i).baseChange L)
          ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
            (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
            (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
              (modelConeMap n g₀ h𝒟₀ C hC) j) (i + 1)).baseChange L)) =
        Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)) (homologyAt
          ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
            (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
            (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
              (modelConeMap n g₀ h𝒟₀ C hC) j) i).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
          ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
            (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
            (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
              (modelConeMap n g₀ h𝒟₀ C hC) j) (i + 1)).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))) := by
  have hbr := baseRing_facts (R₀ := R₀)
  haveI := hbr.1
  haveI := hbr.2
  exact sModelCone_coneD (U := fun i => ((C i).W : 𝒳₀.Opens)) (R := Γ(Spec (CommRingCat.of R₀), ⊤))
    (P₀ := logPresheafCx h𝒟₀ true) (P₁ := logPresheafCx (isRelativeSNC_zero h𝒟₀) false)
    (modelConeMap n g₀ h𝒟₀ C hC) n
    (sModelCone_subsingleton n g₀ h𝒟₀ C true)
    (sModelCone_subsingleton n g₀ (isRelativeSNC_zero h𝒟₀)
      (fun i => WeakChart.forgetBoundary (C i)) false)
    (sModelCone_flat n g₀ h𝒟₀ C true)
    (sModelCone_flat n g₀ (isRelativeSNC_zero h𝒟₀) (fun i => WeakChart.forgetBoundary (C i)) false)
    (sModelCone_finite n g₀ C hC h𝒟₀ true)
    (sModelCone_finite n g₀ C hC (isRelativeSNC_zero h𝒟₀) false)

include hC in
/-- Weak charts of a fibre, by base change from the model. -/
private theorem forall_mem_weakChart_of_isPullback {K : CommRingCat.{0}} (φ : CommRingCat.of R₀ ⟶ K)
    {Y : Scheme.{0}} (f : Y ⟶ Spec K) [SmoothOfRelativeDimension n f] (q : Y ⟶ 𝒳₀) (H : IsPullback q f g₀ (Spec.map φ))
    (DY : MMP.Mori.Divisor Y) (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (𝒟₀.supp : Set 𝒳₀)) :
    ∀ y : Y, ∃ c : WeakChart f n (DY.supp : Set Y), y ∈ ((c.toLogData f DY).W : Y.Opens) := by
  intro y
  have : q.base y ∈ (⨆ i, ((C i).W : 𝒳₀.Opens)) := by rw [hC]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
  obtain ⟨c', hW, -, -⟩ := (C i).exists_baseChange H
  refine ⟨c'.ofEq hsupp.symm, ?_⟩
  show y ∈ (c'.W : Y.Opens)
  rw [hW]
  exact ⟨hi, trivial⟩

/-- **Base change commutes with the regular extension**: the pullback of logarithmic forms for
`𝒟₀` and for the empty divisor commute with `twistedToZeroLog`. -/
private theorem logΦ_twistedToZeroLog [IsDomain R₀] {K : CommRingCat.{0}} [IsRegularRing K]
    (φ : CommRingCat.of R₀ ⟶ K) {Y : Scheme.{0}} (f : Y ⟶ Spec K)
    [SmoothOfRelativeDimension n f] (q : Y ⟶ 𝒳₀) (H : IsPullback q f g₀ (Spec.map φ))
    {DY : MMP.Mori.Divisor Y} (hDY : DY.IsRelativeSNC n f)
    (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (𝒟₀.supp : Set 𝒳₀))
    (hCY : ∀ y : Y, ∃ c : WeakChart f n (DY.supp : Set Y), y ∈ ((c.toLogData f DY).W : Y.Opens))
    (hsupp0 : ((0 : MMP.Mori.Divisor Y).supp : Set Y) =
      q.base ⁻¹' ((0 : MMP.Mori.Divisor 𝒳₀).supp : Set 𝒳₀))
    (hpairs : ∀ y : Y, ∃ pr : ChartPair (DX := 𝒟₀) (DY := DY) (q := q) h𝒟₀ hDY,
      q.base y ∈ (pr.c.W : 𝒳₀.Opens) ∧ y ∈ (pr.c'.W : Y.Opens))
    (hpairs0 : ∀ y : Y, ∃ pr : ChartPair (DX := (0 : MMP.Mori.Divisor 𝒳₀))
      (DY := (0 : MMP.Mori.Divisor Y)) (q := q) (isRelativeSNC_zero h𝒟₀) (isRelativeSNC_zero hDY),
      q.base y ∈ (pr.c.W : 𝒳₀.Opens) ∧ y ∈ (pr.c'.W : Y.Opens))
    (a : ℕ) (V : (𝒳₀.Opens)ᵒᵖ) (x : ((logPresheafCx h𝒟₀ true).X a).obj V) :
    haveI := preservesFiniteProducts_opensMap q.base
    logΦ H.w hsupp0 (isRelativeSNC_zero h𝒟₀) (isRelativeSNC_zero hDY) hpairs0 false a V
        ((((modelConeMap n g₀ h𝒟₀ C hC).f a).app V).hom x) =
      (((logPresheafMap f (Opens.map q.base)
        (twistedToZeroLog f hDY hCY (isRelativeSNC_zero hDY))).f a).app V).hom
        (logΦ H.w hsupp h𝒟₀ hDY hpairs true a V x) := by
  haveI := preservesFiniteProducts_opensMap q.base
  apply Subtype.ext
  set u := ((twistedToForms g₀ h𝒟₀ (forall_mem_weakChart n g₀ C hC)).f a).val.app V x with hu
  have hz : ((((modelConeMap n g₀ h𝒟₀ C hC).f a).app V).hom x).1 =
      ((resForms g₀ 0).app (a : ℤ)).val.app V u :=
    formsToZeroLog_val g₀ (isRelativeSNC_zero h𝒟₀) a V u
  rw [logΦ_val, hz]
  have hw : ((twistedToForms f hDY hCY).f a).val.app (op (q ⁻¹ᵁ V.unop))
      (logΦ H.w hsupp h𝒟₀ hDY hpairs true a V x) =
      ((Scheme.Hom.deRhamFormsPushforwardHom q g₀ f (Spec.map φ) H.w).app (a : ℤ)).val.app V u := by
    apply resForms_app_injective f hDY hCY a (q ⁻¹ᵁ V.unop)
    refine (resForms_logToFormsCx f true (isLocalSectionRel_twisted f hDY hCY)
      (resForms_app_injective f hDY hCY) a _ _).trans ?_
    rw [logΦ_val]
    refine Eq.trans ?_ (resForms_deRhamFormsPushforwardHom H.w 𝒟₀ DY hsupp a V.unop u).symm
    exact congrArg _ (resForms_logToFormsCx g₀ true
      (isLocalSectionRel_twisted g₀ h𝒟₀ (forall_mem_weakChart n g₀ C hC))
      (resForms_app_injective g₀ h𝒟₀ (forall_mem_weakChart n g₀ C hC)) a V x).symm
  change _ = (((formsToZeroLog f (isRelativeSNC_zero hDY)).f a).val.app _
    (((twistedToForms f hDY hCY).f a).val.app _ (logΦ H.w hsupp h𝒟₀ hDY hpairs true a V x))).1
  rw [formsToZeroLog_val]
  exact (resForms_deRhamFormsPushforwardHom H.w 0 0 hsupp0 a V.unop u).symm.trans
    (congrArg _ hw.symm)

include h𝒟₀ hC in
/-- The hypercohomology of the cokernel on the fibre, as the cohomology of the cone of the
pulled-back regular extension. -/
private theorem finrankHcCoker_hc (K : CommRingCat.{0}) [IsRegularRing K]
    (φ : CommRingCat.of R₀ ⟶ K) {Y : Scheme.{0}} (f : Y ⟶ Spec K)
    [SmoothOfRelativeDimension n f] (q : Y ⟶ 𝒳₀) (H : IsPullback q f g₀ (Spec.map φ))
    (DY : MMP.Mori.Divisor Y) (hDY : DY.IsRelativeSNC n f)
    (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (𝒟₀.supp : Set 𝒳₀))
    (hCY : ∀ y : Y, ∃ c : WeakChart f n (DY.supp : Set Y), y ∈ ((c.toLogData f DY).W : Y.Opens))
    (i : relativeLogDeRhamComplex n f DY hDY DY.suppIdeal ⟶ Scheme.Hom.deRhamComplex f)
    (hi : ∀ (p : ℕ) (W : Y.Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n f DY hDY DY.suppIdeal).X p).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι DY.supp.compl) f).f p).val.app
        W ((i.f p).val.app W ω) = ω.1)
    (Dc : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec K).sheaf))) ℕ)
    (qc : Scheme.Hom.deRhamComplex f ⟶ Dc) (hiq : i ≫ qc = 0)
    (hq : IsColimit (CokernelCofork.ofπ qc hiq)) (k : ℤ) :
    haveI := preservesFiniteProducts_opensMap q.base
    Module.finrank Γ(Spec K, ⊤) (Hc f ⟨Dc.extend ComplexShape.embeddingUpNat, 0,
        CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ (k + 1)) =
      Module.finrank Γ(Spec K, ⊤) (homologyAt
        (coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCxPullback (q := q) hDY true))
          (totD (fun i => ((C i).W : 𝒳₀.Opens))
            (logPresheafCxPullback (q := q) (isRelativeSNC_zero hDY) false))
          (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
            (logPresheafMap f (Opens.map q.base) (twistedToZeroLog f hDY
              hCY
              (isRelativeSNC_zero hDY))) j) k)
        (coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCxPullback (q := q) hDY true))
          (totD (fun i => ((C i).W : 𝒳₀.Opens))
            (logPresheafCxPullback (q := q) (isRelativeSNC_zero hDY) false))
          (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
            (logPresheafMap f (Opens.map q.base) (twistedToZeroLog f hDY
              hCY
              (isRelativeSNC_zero hDY))) j) (k + 1))) := by
  haveI := preservesFiniteProducts_opensMap q.base
  haveI : IsAffineHom q :=
    MorphismProperty.of_isPullback H.flip (inferInstance : IsAffineHom (Spec.map φ))
  haveI : IsProper f := MorphismProperty.of_isPullback H inferInstance
  haveI := AlgebraicGeometry.DeRhamTypeComplex.isAffineHom_diagonal_of_isProper f
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have hUY : (⊤ : Y.Opens) = ⨆ i, q ⁻¹ᵁ ((C i).W : 𝒳₀.Opens) := by
    rw [← Scheme.Hom.preimage_iSup, hC]
    rfl
  have hUaffY : ∀ i, IsAffineOpen (q ⁻¹ᵁ ((C i).W : 𝒳₀.Opens)) := fun i => (C i).W.2.preimage q
  refine (exists_chartPairs n g₀ 𝒟₀ h𝒟₀ C K φ f q H DY hDY hsupp).elim fun pr hpr => ?_
  have hcov := (chartPairs_cover (n := n) (R₀ := R₀) (g₀ := g₀) (h𝒟₀ := h𝒟₀)
    (hDY := hDY) (K := K) (φ := φ) (f := f) (q := q) C hC H pr hpr).2
  exact (nonempty_hc_cokernel_equiv_homologyAt_coneD f q
    (hCY := hCY)
    (isRelativeSNC_zero hDY) i hi Dc qc hiq hq
    (fun i => ((C i).W : 𝒳₀.Opens)) hUY hUaffY (fun p t => (hcov p t).2.1) k).elim
    fun E => E.finrank_eq

/-- The cohomology of the cone of the pulled-back regular extension is the base change of the
cohomology of the model cone, for given covering chart pairs. -/
private theorem finrankHcCoker_baseChange_of_pairs [IsDomain R₀] (K : CommRingCat.{0})
    [IsRegularRing K] (φ : CommRingCat.of R₀ ⟶ K) {Y : Scheme.{0}} (f : Y ⟶ Spec K)
    [SmoothOfRelativeDimension n f] (q : Y ⟶ 𝒳₀) (H : IsPullback q f g₀ (Spec.map φ))
    (DY : MMP.Mori.Divisor Y) (hDY : DY.IsRelativeSNC n f)
    (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (𝒟₀.supp : Set 𝒳₀))
    (hCY : ∀ y : Y, ∃ c : WeakChart f n (DY.supp : Set Y), y ∈ ((c.toLogData f DY).W : Y.Opens))
    (hpairs : ∀ y : Y, ∃ pr' : ChartPair (DX := 𝒟₀) (DY := DY) (q := q) h𝒟₀ hDY,
      q.base y ∈ (pr'.c.W : 𝒳₀.Opens) ∧ y ∈ (pr'.c'.W : Y.Opens))
    (hcov : ∀ (p : ℕ) (t : Fin (p + 1) → ι),
      IsAffineOpen (inter (fun i => ((C i).W : 𝒳₀.Opens)) t) ∧
      IsAffineOpen (q ⁻¹ᵁ inter (fun i => ((C i).W : 𝒳₀.Opens)) t) ∧
      ∃ pr' : ChartPair (DX := 𝒟₀) (DY := DY) (q := q) h𝒟₀ hDY,
        inter (fun i => ((C i).W : 𝒳₀.Opens)) t ≤ pr'.c.W ∧
        q ⁻¹ᵁ inter (fun i => ((C i).W : 𝒳₀.Opens)) t ≤ pr'.c'.W)
    (hpairs0 : ∀ y : Y, ∃ pr' : ChartPair (DX := (0 : MMP.Mori.Divisor 𝒳₀))
      (DY := (0 : MMP.Mori.Divisor Y)) (q := q) (isRelativeSNC_zero h𝒟₀) (isRelativeSNC_zero hDY),
      q.base y ∈ (pr'.c.W : 𝒳₀.Opens) ∧ y ∈ (pr'.c'.W : Y.Opens))
    (hcov0 : ∀ (p : ℕ) (t : Fin (p + 1) → ι),
      IsAffineOpen (inter (fun i => ((WeakChart.forgetBoundary (C i)).W : 𝒳₀.Opens)) t) ∧
      IsAffineOpen (q ⁻¹ᵁ inter (fun i => ((WeakChart.forgetBoundary (C i)).W : 𝒳₀.Opens)) t) ∧
      ∃ pr' : ChartPair (DX := (0 : MMP.Mori.Divisor 𝒳₀)) (DY := (0 : MMP.Mori.Divisor Y))
          (q := q) (isRelativeSNC_zero h𝒟₀) (isRelativeSNC_zero hDY),
        inter (fun i => ((WeakChart.forgetBoundary (C i)).W : 𝒳₀.Opens)) t ≤ pr'.c.W ∧
        q ⁻¹ᵁ inter (fun i => ((WeakChart.forgetBoundary (C i)).W : 𝒳₀.Opens)) t ≤ pr'.c'.W)
    (k : ℤ) :
    letI : Algebra Γ(Spec (CommRingCat.of R₀), ⊤) Γ(Spec K, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
    haveI := preservesFiniteProducts_opensMap q.base
    Module.finrank Γ(Spec K, ⊤) (homologyAt
        ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
          (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
          (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
            (modelConeMap n g₀ h𝒟₀ C hC) j) k).baseChange Γ(Spec K, ⊤))
        ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
          (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
          (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
            (modelConeMap n g₀ h𝒟₀ C hC) j) (k + 1)).baseChange Γ(Spec K, ⊤))) =
      Module.finrank Γ(Spec K, ⊤) (homologyAt
        (coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCxPullback (q := q) hDY true))
          (totD (fun i => ((C i).W : 𝒳₀.Opens))
            (logPresheafCxPullback (q := q) (isRelativeSNC_zero hDY) false))
          (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
            (logPresheafMap f (Opens.map q.base) (twistedToZeroLog f hDY
              hCY
              (isRelativeSNC_zero hDY))) j) k)
        (coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCxPullback (q := q) hDY true))
          (totD (fun i => ((C i).W : 𝒳₀.Opens))
            (logPresheafCxPullback (q := q) (isRelativeSNC_zero hDY) false))
          (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
            (logPresheafMap f (Opens.map q.base) (twistedToZeroLog f hDY
              hCY
              (isRelativeSNC_zero hDY))) j) (k + 1))) := by
  letI : Algebra Γ(Spec (CommRingCat.of R₀), ⊤) Γ(Spec K, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
  haveI := preservesFiniteProducts_opensMap q.base
  have h0Y := isRelativeSNC_zero hDY
  have hsupp0 : ((0 : MMP.Mori.Divisor Y).supp : Set Y) =
      q.base ⁻¹' ((0 : MMP.Mori.Divisor 𝒳₀).supp : Set 𝒳₀) := by
    rw [coe_supp_zero, coe_supp_zero, Set.preimage_empty]
  haveI : IsAffineHom q :=
    MorphismProperty.of_isPullback H.flip (inferInstance : IsAffineHom (Spec.map φ))
  haveI : IsProper f := MorphismProperty.of_isPullback H inferInstance
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  exact ((nonempty_homologyAt_coneD_baseChange_equiv (C := 𝒳₀.Opens)
    (R₀ := Γ(Spec (CommRingCat.of R₀), ⊤)) (L := Γ(Spec K, ⊤))
    (P₀ := logPresheafCx h𝒟₀ true) (P₁ := logPresheafCx (isRelativeSNC_zero h𝒟₀) false)
    (Q₀ := logPresheafCxPullback (q := q) hDY true)
    (Q₁ := logPresheafCxPullback (q := q) h0Y false)
    (fun i => ((C i).W : 𝒳₀.Opens))
    (modelConeMap n g₀ h𝒟₀ C hC)
    (logPresheafMap f (Opens.map q.base) (twistedToZeroLog f hDY hCY h0Y))
    (logΦ H.w hsupp h𝒟₀ hDY hpairs true)
    (logΦ H.w hsupp0 (isRelativeSNC_zero h𝒟₀) h0Y hpairs0 false)
    (fun a _ _ i x => logΦ_nat H.w hsupp h𝒟₀ hDY hpairs true a i x)
    (fun a _ _ i x => logΦ_nat H.w hsupp0 (isRelativeSNC_zero h𝒟₀) h0Y hpairs0 false a i x)
    (fun a V x => logΦ_d H.w hsupp h𝒟₀ hDY hpairs true a V x)
    (fun a V x => logΦ_d H.w hsupp0 (isRelativeSNC_zero h𝒟₀) h0Y hpairs0 false a V x)
    (fun a V r x => logΦ_smul H.w hsupp h𝒟₀ hDY hpairs true a V r x)
    (fun a V r x => logΦ_smul H.w hsupp0 (isRelativeSNC_zero h𝒟₀) h0Y hpairs0 false a V r x)
    (fun a p t => by
      obtain ⟨h1, h2, pr', h3, h4⟩ := hcov p t
      exact exists_logΦ_baseChange H.w hsupp h𝒟₀ hDY H hpairs pr' true a _ h1 h3 h2 h4)
    (fun a p t => by
      obtain ⟨h1, h2, pr', h3, h4⟩ := hcov0 p t
      exact exists_logΦ_baseChange H.w hsupp0 (isRelativeSNC_zero h𝒟₀) h0Y H hpairs0 pr' false a _
        h1 h3 h2 h4)
    (fun a V x => logΦ_twistedToZeroLog n g₀ h𝒟₀ C hC φ f q H hDY hsupp hCY hsupp0 hpairs hpairs0
      a V x) k).elim fun E => E.finrank_eq)

/-- The cohomology of the cone of the pulled-back regular extension is the base change of the
cohomology of the model cone. -/
private theorem finrankHcCoker_baseChange [IsDomain R₀] (K : CommRingCat.{0}) [IsRegularRing K]
    (φ : CommRingCat.of R₀ ⟶ K) {Y : Scheme.{0}} (f : Y ⟶ Spec K)
    [SmoothOfRelativeDimension n f] (q : Y ⟶ 𝒳₀) (H : IsPullback q f g₀ (Spec.map φ))
    (DY : MMP.Mori.Divisor Y) (hDY : DY.IsRelativeSNC n f)
    (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (𝒟₀.supp : Set 𝒳₀))
    (hCY : ∀ y : Y, ∃ c : WeakChart f n (DY.supp : Set Y), y ∈ ((c.toLogData f DY).W : Y.Opens))
    (k : ℤ) :
    letI : Algebra Γ(Spec (CommRingCat.of R₀), ⊤) Γ(Spec K, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
    haveI := preservesFiniteProducts_opensMap q.base
    Module.finrank Γ(Spec K, ⊤) (homologyAt
        ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
          (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
          (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
            (modelConeMap n g₀ h𝒟₀ C hC) j) k).baseChange Γ(Spec K, ⊤))
        ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
          (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
          (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
            (modelConeMap n g₀ h𝒟₀ C hC) j) (k + 1)).baseChange Γ(Spec K, ⊤))) =
      Module.finrank Γ(Spec K, ⊤) (homologyAt
        (coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCxPullback (q := q) hDY true))
          (totD (fun i => ((C i).W : 𝒳₀.Opens))
            (logPresheafCxPullback (q := q) (isRelativeSNC_zero hDY) false))
          (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
            (logPresheafMap f (Opens.map q.base) (twistedToZeroLog f hDY
              hCY
              (isRelativeSNC_zero hDY))) j) k)
        (coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCxPullback (q := q) hDY true))
          (totD (fun i => ((C i).W : 𝒳₀.Opens))
            (logPresheafCxPullback (q := q) (isRelativeSNC_zero hDY) false))
          (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
            (logPresheafMap f (Opens.map q.base) (twistedToZeroLog f hDY
              hCY
              (isRelativeSNC_zero hDY))) j) (k + 1))) := by
  have hsupp0 : ((0 : MMP.Mori.Divisor Y).supp : Set Y) =
      q.base ⁻¹' ((0 : MMP.Mori.Divisor 𝒳₀).supp : Set 𝒳₀) := by
    rw [coe_supp_zero, coe_supp_zero, Set.preimage_empty]
  refine (exists_chartPairs n g₀ 𝒟₀ h𝒟₀ C K φ f q H DY hDY hsupp).elim fun pr hpr => ?_
  refine (exists_chartPairs n g₀ 0 (isRelativeSNC_zero h𝒟₀)
    (fun i => WeakChart.forgetBoundary (C i)) K φ f q H 0 (isRelativeSNC_zero hDY)
    hsupp0).elim fun pr0 hpr0 => ?_
  have hc := chartPairs_cover (n := n) (R₀ := R₀) (g₀ := g₀) (h𝒟₀ := h𝒟₀)
    (hDY := hDY) (K := K) (φ := φ) (f := f) (q := q) C hC H pr hpr
  have hc0 := chartPairs_cover (n := n) (R₀ := R₀) (g₀ := g₀)
    (h𝒟₀ := isRelativeSNC_zero h𝒟₀) (hDY := isRelativeSNC_zero hDY) (K := K) (φ := φ)
    (f := f) (q := q) (fun i => WeakChart.forgetBoundary (C i)) hC H pr0 hpr0
  exact finrankHcCoker_baseChange_of_pairs n g₀ h𝒟₀ C hC K φ f q H DY hDY hsupp hCY
    hc.1 hc.2 hc0.1 hc0.2 k

/-- **The cokernel of a pinned inclusion on a fibre has generic hypercohomology.** On a fibre of
the model over a field where the base change constant of the model cone does not vanish,
`dim ℍ^{k+1}(𝒟^•)` is the rank of the cohomology of the model cone. -/
private theorem finrank_hc_cokernel_eq [IsDomain R₀] (K : CommRingCat.{0}) (hK : IsField K)
    (φ : CommRingCat.of R₀ ⟶ K) {Y : Scheme.{0}} (f : Y ⟶ Spec K)
    [SmoothOfRelativeDimension n f] (q : Y ⟶ 𝒳₀) (H : IsPullback q f g₀ (Spec.map φ))
    (DY : MMP.Mori.Divisor Y) (hDY : DY.IsRelativeSNC n f)
    (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (𝒟₀.supp : Set 𝒳₀))
    (i : relativeLogDeRhamComplex n f DY hDY DY.suppIdeal ⟶ Scheme.Hom.deRhamComplex f)
    (hi : ∀ (p : ℕ) (W : Y.Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n f DY hDY DY.suppIdeal).X p).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι DY.supp.compl) f).f p).val.app
        W ((i.f p).val.app W ω) = ω.1)
    (Dc : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec K).sheaf))) ℕ)
    (qc : Scheme.Hom.deRhamComplex f ⟶ Dc) (hiq : i ≫ qc = 0)
    (hq : IsColimit (CokernelCofork.ofπ qc hiq))
    (s : Γ(Spec (CommRingCat.of R₀), ⊤))
    (hs : φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom s) ≠ 0)
    (Hs : ∀ (L : Type) [Field L] [Algebra Γ(Spec (CommRingCat.of R₀), ⊤) L],
      algebraMap Γ(Spec (CommRingCat.of R₀), ⊤) L s ≠ 0 → ∀ i,
        Module.finrank L (homologyAt
          ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
            (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
            (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
              (modelConeMap n g₀ h𝒟₀ C hC) j) i).baseChange L)
          ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
            (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
            (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
              (modelConeMap n g₀ h𝒟₀ C hC) j) (i + 1)).baseChange L)) =
        Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)) (homologyAt
          ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
            (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
            (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
              (modelConeMap n g₀ h𝒟₀ C hC) j) i).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
          ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
            (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
            (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
              (modelConeMap n g₀ h𝒟₀ C hC) j) (i + 1)).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))))
    (k : ℤ) :
    Module.finrank Γ(Spec K, ⊤) (Hc f ⟨Dc.extend ComplexShape.embeddingUpNat, 0,
        CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ (k + 1)) =
      Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)) (homologyAt
          ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
            (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
            (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
              (modelConeMap n g₀ h𝒟₀ C hC) j) k).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
          ((coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ true))
            (totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx (isRelativeSNC_zero h𝒟₀) false))
            (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens))
              (modelConeMap n g₀ h𝒟₀ C hC) j) (k + 1)).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))) := by
  letI : Algebra Γ(Spec (CommRingCat.of R₀), ⊤) Γ(Spec K, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
  haveI : IsRegularRing K := by
    letI := hK.toField
    exact inferInstance
  have hCY := forall_mem_weakChart_of_isPullback n g₀ C hC φ f q H DY hsupp
  refine (finrankHcCoker_hc n g₀ h𝒟₀ C hC K φ f q H DY hDY hsupp hCY i hi Dc qc hiq hq k).trans ?_
  refine (finrankHcCoker_baseChange n g₀ h𝒟₀ C hC K φ f q H DY hDY hsupp hCY k).symm.trans ?_
  letI : Field Γ(Spec K, ⊤) :=
    (MulEquiv.isField hK (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.toMulEquiv).toField
  exact Hs Γ(Spec K, ⊤) (algebraMap_ne_zero_of_hom_ne_zero K φ s hs) k

end ModelFibre

/-! ### The Hodge pieces of the cokernel spread out -/

section ModelHodge

open MMP.Mori.Divisor.LogSpreadingProof.G1 Stacks.CategoryTheory.CechComplex TensorProduct

attribute [local instance] secCommRing

/-- Both ranks of the cohomology of a complex of subsingleton modules vanish after base change. -/
private theorem finrank_homologyAt_baseChange_eq_zero {R : Type} [CommRing R] {M : ℤ → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (d : ∀ i, M i →ₗ[R] M (i + 1))
    (hsub : ∀ i, Subsingleton (M i)) (L : Type) [Field L] [Algebra R L] (i : ℤ) :
    Module.finrank L (homologyAt ((d i).baseChange L) ((d (i + 1)).baseChange L)) = 0 := by
  haveI := hsub (i + 1)
  haveI : Subsingleton (L ⊗[R] M (i + 1)) := subsingleton_tensor_right L (M (i + 1))
  haveI := subsingleton_homologyAt ((d i).baseChange L) ((d (i + 1)).baseChange L)
  exact Module.finrank_zero_of_subsingleton

variable (n : ℕ) {R₀ : Type} [CommRing R₀] [IsRegularRing R₀]
  {𝒳₀ : Scheme.{0}} (g₀ : 𝒳₀ ⟶ Spec (CommRingCat.of R₀)) [SmoothOfRelativeDimension n g₀]
  [IsProper g₀] {𝒟₀ : MMP.Mori.Divisor 𝒳₀} (h𝒟₀ : 𝒟₀.IsRelativeSNC n g₀) {ι : Type} [Finite ι]
  (C : ι → WeakChart g₀ n (𝒟₀.supp : Set 𝒳₀)) (hC : ⨆ i, ((C i).W : 𝒳₀.Opens) = ⊤)

/-- **The regular extension on the model in degree `p`**, placed in degree `0`. -/
private noncomputable abbrev modelHodgeConeMap (p : ℕ) :
    hodgePresheafCx h𝒟₀ true p ⟶ hodgePresheafCx (isRelativeSNC_zero h𝒟₀) false p :=
  singlePresheafMap g₀ (𝟭 𝒳₀.Opens)
    ((twistedToZeroLog g₀ h𝒟₀ (forall_mem_weakChart n g₀ C hC) (isRelativeSNC_zero h𝒟₀)).f p)

/-- The cone of the regular extension in degree `p` on the model, as a complex of modules. -/
private noncomputable abbrev modelHodgeConeD (p : ℕ) (i : ℤ) :=
  coneD (totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ true p))
    (totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx (isRelativeSNC_zero h𝒟₀) false p))
    (fun j => totMap (U := fun i => ((C i).W : 𝒳₀.Opens)) (modelHodgeConeMap n g₀ h𝒟₀ C hC p) j) i

/-- **A generic base change constant for the cone of the regular extension in degree `p`**, equal
to `1` above the dimension. -/
private theorem exists_s_modelHodgeCone [IsDomain R₀] (p : ℕ) :
    haveI := (baseRing_facts (R₀ := R₀)).1
    ∃ s : Γ(Spec (CommRingCat.of R₀), ⊤), s ≠ 0 ∧ (n < p → s = 1) ∧
      ∀ (L : Type) [Field L] [Algebra Γ(Spec (CommRingCat.of R₀), ⊤) L],
      algebraMap Γ(Spec (CommRingCat.of R₀), ⊤) L s ≠ 0 → ∀ i,
        Module.finrank L (homologyAt ((modelHodgeConeD n g₀ h𝒟₀ C hC p i).baseChange L)
          ((modelHodgeConeD n g₀ h𝒟₀ C hC p (i + 1)).baseChange L)) =
        Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)) (homologyAt
          ((modelHodgeConeD n g₀ h𝒟₀ C hC p i).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
          ((modelHodgeConeD n g₀ h𝒟₀ C hC p (i + 1)).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))) := by
  haveI := (baseRing_facts (R₀ := R₀)).1
  haveI := (baseRing_facts (R₀ := R₀)).2
  haveI : Nontrivial Γ(Spec (CommRingCat.of R₀), ⊤) := IsDomain.toNontrivial
  haveI : IsLocallyNoetherian 𝒳₀ := LocallyOfFiniteType.isLocallyNoetherian g₀
  have hX := inter_charts h𝒟₀ C
  have hX0 := inter_charts (isRelativeSNC_zero h𝒟₀) (fun i => WeakChart.forgetBoundary (C i))
  have hsubHo : ∀ (D' : MMP.Mori.Divisor 𝒳₀) (hD' : D'.IsRelativeSNC n g₀) (ε : Bool) (a : ℕ),
      0 < a → ∀ (k : ℕ) (t : Fin (k + 1) → ι),
      Subsingleton (((hodgePresheafCx hD' ε p).X a).obj
        (op (inter (fun i => ((C i).W : 𝒳₀.Opens)) t))) := by
    intro D' hD' ε a ha k t
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    exact subsingleton_resCx_single _ _ b _
  by_cases hp : n < p
  · refine ⟨1, one_ne_zero, fun _ => rfl, fun L _ _ _ i => ?_⟩
    have hsub : ∀ i, Subsingleton (coneX
        (TotX (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ true p))
        (TotX (fun i => ((C i).W : 𝒳₀.Opens))
          (hodgePresheafCx (isRelativeSNC_zero h𝒟₀) false p)) i) := by
      intro i
      have h₀ : Subsingleton (TotX (fun i => ((C i).W : 𝒳₀.Opens))
          (hodgePresheafCx h𝒟₀ true p) (i + 1)) := by
        refine @Pi.instSubsingleton _ _ fun j => ?_
        rcases j with ⟨⟨k, a⟩, hka⟩
        refine @Pi.instSubsingleton _ _ fun t => ?_
        rcases a with _ | b
        · obtain ⟨haff, c, hle⟩ := hX _ t
          exact (subsingleton_logComponent h𝒟₀ true p hp _ haff c hle : _)
        · exact hsubHo 𝒟₀ h𝒟₀ true (b + 1) (Nat.succ_pos b) _ t
      have h₁ : Subsingleton (TotX (fun i => ((C i).W : 𝒳₀.Opens))
          (hodgePresheafCx (isRelativeSNC_zero h𝒟₀) false p) i) := by
        refine @Pi.instSubsingleton _ _ fun j => ?_
        rcases j with ⟨⟨k, a⟩, hka⟩
        refine @Pi.instSubsingleton _ _ fun t => ?_
        rcases a with _ | b
        · obtain ⟨haff, c, hle⟩ := hX0 _ t
          exact (subsingleton_logComponent (isRelativeSNC_zero h𝒟₀) false p hp _ haff c hle : _)
        · exact hsubHo 0 (isRelativeSNC_zero h𝒟₀) false (b + 1) (Nat.succ_pos b) _ t
      infer_instance
    exact (finrank_homologyAt_baseChange_eq_zero (modelHodgeConeD n g₀ h𝒟₀ C hC p) hsub L i).trans
      (finrank_homologyAt_baseChange_eq_zero (modelHodgeConeD n g₀ h𝒟₀ C hC p) hsub
        (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)) i).symm
  · have hflat : ∀ (D' : MMP.Mori.Divisor 𝒳₀) (hD' : D'.IsRelativeSNC n g₀) (ε : Bool)
        (C' : ι → WeakChart g₀ n (D'.supp : Set 𝒳₀)), (∀ i, (C' i).W = (C i).W) → ∀ i,
        Module.Flat Γ(Spec (CommRingCat.of R₀), ⊤)
          (TotX (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx hD' ε p) i) := by
      intro D' hD' ε C' hC' i
      have hX' := inter_charts hD' C'
      haveI := finite_totIndex i
      refine flat_pi' fun j => ?_
      rcases j with ⟨⟨k, a⟩, hka⟩
      refine flat_pi' fun t => ?_
      rcases a with _ | b
      · obtain ⟨haff, c, hle⟩ := hX' _ t
        simp only [hC'] at haff hle
        exact (flat_logComponent hD' ε p _ haff c hle : _)
      · haveI := hsubHo D' hD' ε (b + 1) (Nat.succ_pos b) _ t
        infer_instance
    have hs := exists_s_coneD (fun i => ((C i).W : 𝒳₀.Opens))
      (modelHodgeConeMap n g₀ h𝒟₀ C hC p) 0
      (fun a ha k t => hsubHo 𝒟₀ h𝒟₀ true a ha k t)
      (fun a ha k t => hsubHo 0 (isRelativeSNC_zero h𝒟₀) false a ha k t)
      (hflat 𝒟₀ h𝒟₀ true C fun _ => rfl)
      (hflat 0 (isRelativeSNC_zero h𝒟₀) false (fun i => WeakChart.forgetBoundary (C i))
        fun _ => rfl)
      (fun i => moduleFinite_logHodge g₀ h𝒟₀ _ hC.symm (fun i => (C i).W.2) true p i)
      (fun i => moduleFinite_logHodge g₀ (isRelativeSNC_zero h𝒟₀) _ hC.symm
        (fun i => (C i).W.2) false p i)
    exact ⟨hs.choose, hs.choose_spec.1, fun h => absurd h hp, hs.choose_spec.2⟩

/-- **The Hodge pieces of the cokernel of a pinned inclusion on a fibre are generic.** On a fibre
of the model over a field where the base change constant of the model cone in degree `p` does
not vanish, `dim H^{k+1}(𝒟^p)` is the rank of the cohomology of the model cone. -/
private theorem finrank_hc_single_cokernel_eq [IsDomain R₀] (K : CommRingCat.{0}) (hK : IsField K)
    (φ : CommRingCat.of R₀ ⟶ K) {Y : Scheme.{0}} (f : Y ⟶ Spec K)
    [SmoothOfRelativeDimension n f] (q : Y ⟶ 𝒳₀) (H : IsPullback q f g₀ (Spec.map φ))
    (DY : MMP.Mori.Divisor Y) (hDY : DY.IsRelativeSNC n f)
    (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (𝒟₀.supp : Set 𝒳₀))
    (i : relativeLogDeRhamComplex n f DY hDY DY.suppIdeal ⟶ Scheme.Hom.deRhamComplex f)
    (hi : ∀ (p : ℕ) (W : Y.Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n f DY hDY DY.suppIdeal).X p).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι DY.supp.compl) f).f p).val.app
        W ((i.f p).val.app W ω) = ω.1)
    (Dc : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj (Spec K).sheaf))) ℕ)
    (qc : Scheme.Hom.deRhamComplex f ⟶ Dc) (hiq : i ≫ qc = 0)
    (hq : IsColimit (CokernelCofork.ofπ qc hiq)) (p : ℕ)
    (s : Γ(Spec (CommRingCat.of R₀), ⊤))
    (hs : φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom s) ≠ 0)
    (Hs : ∀ (L : Type) [Field L] [Algebra Γ(Spec (CommRingCat.of R₀), ⊤) L],
      algebraMap Γ(Spec (CommRingCat.of R₀), ⊤) L s ≠ 0 → ∀ i,
        Module.finrank L (homologyAt ((modelHodgeConeD n g₀ h𝒟₀ C hC p i).baseChange L)
          ((modelHodgeConeD n g₀ h𝒟₀ C hC p (i + 1)).baseChange L)) =
        Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)) (homologyAt
          ((modelHodgeConeD n g₀ h𝒟₀ C hC p i).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
          ((modelHodgeConeD n g₀ h𝒟₀ C hC p (i + 1)).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))))
    (k : ℤ) :
    Module.finrank Γ(Spec K, ⊤) (Hc f (single0 f (Dc.X p)) (k + 1)) =
      Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)) (homologyAt
        ((modelHodgeConeD n g₀ h𝒟₀ C hC p k).baseChange
          (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
        ((modelHodgeConeD n g₀ h𝒟₀ C hC p (k + 1)).baseChange
          (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))) := by
  letI : Field Γ(Spec K, ⊤) :=
    (MulEquiv.isField hK (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.toMulEquiv).toField
  letI : Algebra Γ(Spec (CommRingCat.of R₀), ⊤) Γ(Spec K, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
  haveI : IsRegularRing K := by
    letI := hK.toField
    exact inferInstance
  have hCY := forall_mem_weakChart_of_isPullback n g₀ C hC φ f q H DY hsupp
  have h0Y := isRelativeSNC_zero hDY
  have hsupp0 : ((0 : MMP.Mori.Divisor Y).supp : Set Y) =
      q.base ⁻¹' ((0 : MMP.Mori.Divisor 𝒳₀).supp : Set 𝒳₀) := by
    rw [coe_supp_zero, coe_supp_zero, Set.preimage_empty]
  have hpr := exists_chartPairs n g₀ 𝒟₀ h𝒟₀ C K φ f q H DY hDY hsupp
  have hpc := chartPairs_cover (n := n) (R₀ := R₀) (g₀ := g₀) (h𝒟₀ := h𝒟₀)
    (hDY := hDY) (K := K) (φ := φ) (f := f) (q := q) C hC H hpr.choose hpr.choose_spec
  have hpairs := hpc.1
  have hcov := hpc.2
  have hpr0 := exists_chartPairs n g₀ 0 (isRelativeSNC_zero h𝒟₀)
    (fun i => WeakChart.forgetBoundary (C i)) K φ f q H 0 h0Y hsupp0
  have hpc0 := chartPairs_cover (n := n) (R₀ := R₀) (g₀ := g₀)
    (h𝒟₀ := isRelativeSNC_zero h𝒟₀) (hDY := h0Y) (K := K) (φ := φ) (f := f) (q := q)
    (fun i => WeakChart.forgetBoundary (C i)) hC H hpr0.choose hpr0.choose_spec
  have hpairs0 := hpc0.1
  have hcov0 := hpc0.2
  haveI : IsAffineHom q :=
    MorphismProperty.of_isPullback H.flip (inferInstance : IsAffineHom (Spec.map φ))
  haveI : IsProper f := MorphismProperty.of_isPullback H inferInstance
  haveI := AlgebraicGeometry.DeRhamTypeComplex.isAffineHom_diagonal_of_isProper f
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  haveI := preservesFiniteProducts_opensMap q.base
  have hUY : (⊤ : Y.Opens) = ⨆ i, q ⁻¹ᵁ ((C i).W : 𝒳₀.Opens) := by
    rw [← Scheme.Hom.preimage_iSup, hC]
    rfl
  have hUaffY : ∀ i, IsAffineOpen (q ⁻¹ᵁ ((C i).W : 𝒳₀.Opens)) := fun i => (C i).W.2.preimage q
  have E1 := Nonempty.some <| nonempty_hc_single_cokernel_equiv_homologyAt_coneD f q
    (hCY := hCY) h0Y i hi Dc
    qc hiq hq p (fun i => ((C i).W : 𝒳₀.Opens)) hUY hUaffY (fun p t => (hcov p t).2.1) k
  -- the base change maps in degree `p`, placed in degree `0`
  let Φ₀ : ∀ (a : ℕ) (V : (𝒳₀.Opens)ᵒᵖ), ((hodgePresheafCx h𝒟₀ true p).X a).obj V →+
      ((resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
        ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
          ((siteSections f (Opens.map q.base)).obj ((logCx hDY true).X p)))).X a).obj V :=
    fun a V => match a with
      | 0 => logΦ H.w hsupp h𝒟₀ hDY hpairs true p V
      | _ + 1 => 0
  let Φ₁ : ∀ (a : ℕ) (V : (𝒳₀.Opens)ᵒᵖ),
      ((hodgePresheafCx (isRelativeSNC_zero h𝒟₀) false p).X a).obj V →+
      ((resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
        ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
          ((siteSections f (Opens.map q.base)).obj ((logCx h0Y false).X p)))).X a).obj V :=
    fun a V => match a with
      | 0 => logΦ H.w hsupp0 (isRelativeSNC_zero h𝒟₀) h0Y hpairs0 false p V
      | _ + 1 => 0
  have hsY : ∀ (D' : MMP.Mori.Divisor Y) (hD' : D'.IsRelativeSNC n f) (ε : Bool) (b : ℕ)
      (V : (𝒳₀.Opens)ᵒᵖ), Subsingleton (((resCx
        (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
        ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
          ((siteSections f (Opens.map q.base)).obj ((logCx hD' ε).X p)))).X (b + 1)).obj V) :=
    fun D' hD' ε b V => subsingleton_resCx_single _ _ b V
  have hsX : ∀ (D' : MMP.Mori.Divisor 𝒳₀) (hD' : D'.IsRelativeSNC n g₀) (ε : Bool) (b : ℕ)
      (V : (𝒳₀.Opens)ᵒᵖ), Subsingleton (((hodgePresheafCx hD' ε p).X (b + 1)).obj V) :=
    fun D' hD' ε b V => subsingleton_resCx_single _ _ b V
  have E2 := Nonempty.some <| nonempty_homologyAt_coneD_baseChange_equiv
    (fun i => ((C i).W : 𝒳₀.Opens))
    (modelHodgeConeMap n g₀ h𝒟₀ C hC p)
    (singlePresheafMap f (Opens.map q.base) ((twistedToZeroLog f hDY hCY h0Y).f p)) Φ₀ Φ₁
    (fun a V V' j x => by
      rcases a with _ | b
      · exact logΦ_nat H.w hsupp h𝒟₀ hDY hpairs true p j x
      · exact (hsY DY hDY true b V').elim _ _)
    (fun a V V' j x => by
      rcases a with _ | b
      · exact logΦ_nat H.w hsupp0 (isRelativeSNC_zero h𝒟₀) h0Y hpairs0 false p j x
      · exact (hsY 0 h0Y false b V').elim _ _)
    (fun a V x => (hsY DY hDY true a V).elim _ _)
    (fun a V x => (hsY 0 h0Y false a V).elim _ _)
    (fun a V r x => by
      rcases a with _ | b
      · exact logΦ_smul H.w hsupp h𝒟₀ hDY hpairs true p V r x
      · exact (hsY DY hDY true b V).elim _ _)
    (fun a V r x => by
      rcases a with _ | b
      · exact logΦ_smul H.w hsupp0 (isRelativeSNC_zero h𝒟₀) h0Y hpairs0 false p V r x
      · exact (hsY 0 h0Y false b V).elim _ _)
    (fun a p' t => by
      rcases a with _ | b
      · exact exists_logΦ_baseChange H.w hsupp h𝒟₀ hDY H hpairs (hcov p' t).2.2.choose true p _
          (hcov p' t).1 (hcov p' t).2.2.choose_spec.1 (hcov p' t).2.1
          (hcov p' t).2.2.choose_spec.2
      · haveI := hsY DY hDY true b (op (inter (fun i => ((C i).W : 𝒳₀.Opens)) t))
        haveI := hsX 𝒟₀ h𝒟₀ true b (op (inter (fun i => ((C i).W : 𝒳₀.Opens)) t))
        haveI : Subsingleton (Γ(Spec K, ⊤) ⊗[Γ(Spec (CommRingCat.of R₀), ⊤)]
            ((hodgePresheafCx h𝒟₀ true p).X (b + 1)).obj
              (op (inter (fun i => ((C i).W : 𝒳₀.Opens)) t))) := subsingleton_tensor_right _ _
        exact ⟨LinearEquiv.ofSubsingleton _ _, fun x => Subsingleton.elim _ _⟩)
    (fun a p' t => by
      rcases a with _ | b
      · exact exists_logΦ_baseChange H.w hsupp0 (isRelativeSNC_zero h𝒟₀) h0Y H hpairs0
          (hcov0 p' t).2.2.choose false p _ (hcov0 p' t).1 (hcov0 p' t).2.2.choose_spec.1
          (hcov0 p' t).2.1 (hcov0 p' t).2.2.choose_spec.2
      · haveI := hsY 0 h0Y false b (op (inter (fun i => ((C i).W : 𝒳₀.Opens)) t))
        haveI := hsX 0 (isRelativeSNC_zero h𝒟₀) false b
          (op (inter (fun i => ((C i).W : 𝒳₀.Opens)) t))
        haveI : Subsingleton (Γ(Spec K, ⊤) ⊗[Γ(Spec (CommRingCat.of R₀), ⊤)]
            ((hodgePresheafCx (isRelativeSNC_zero h𝒟₀) false p).X (b + 1)).obj
              (op (inter (fun i => ((C i).W : 𝒳₀.Opens)) t))) := subsingleton_tensor_right _ _
        exact ⟨LinearEquiv.ofSubsingleton _ _, fun x => Subsingleton.elim _ _⟩)
    (fun a V x => by
      rcases a with _ | b
      · exact logΦ_twistedToZeroLog n g₀ h𝒟₀ C hC φ f q H hDY hsupp hCY hsupp0 hpairs hpairs0 p V x
      · exact (hsY 0 h0Y false b V).elim _ _) k
  exact (E1.trans E2.symm).finrank_eq.trans
    (Hs Γ(Spec K, ⊤) (algebraMap_ne_zero_of_hom_ne_zero K φ s hs) k)

end ModelHodge

/-! ### Degeneration of the restriction complex over `ℂ` -/

section Assembly

open MMP.Mori.Divisor.LogSpreadingProof.G1 Stacks.CategoryTheory.CechComplex TensorProduct

attribute [local instance] secCommRing

/-- **`E₁`-degeneration of the restriction complex.** For a smooth projective complex variety `Z`
with a relative snc divisor `E` and a cokernel `𝒟_E^•` of the pinned inclusion
`Ω^•_Z(log E)(-E) ⟶ Ω^•_Z`, `dim ℍ^k(𝒟_E^•) = ∑_{q ≤ k} dim H^{k-q}(𝒟_E^q)`: spread out to a
model over a smooth `ℤ`-domain, where the dimensions are generic, and compare with a fibre of
characteristic `p > n` with a `W₂` lift, where the complex decomposes. -/
private theorem finrank_hc_cokernel_eq_sum (n : ℕ) {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n sZ] (hZ : IsProjective sZ)
    (E : MMP.Mori.Divisor Z) (hE : E.IsRelativeSNC n sZ)
    (i : relativeLogDeRhamComplex n sZ E hE E.suppIdeal ⟶ Scheme.Hom.deRhamComplex sZ)
    (hi : ∀ (p : ℕ) (W : Z.Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n sZ E hE E.suppIdeal).X p).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι E.supp.compl) sZ).f p).val.app
        W ((i.f p).val.app W ω) = ω.1)
    (D : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
    (q : Scheme.Hom.deRhamComplex sZ ⟶ D) (hiq : i ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hiq)) (k : ℕ) :
    Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (Hc sZ ⟨D.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
      ∑ p ∈ Finset.range (k + 1), Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (Hc sZ (single0 sZ (D.X p)) ((k - p : ℕ) : ℤ)) := by
  classical
  -- the model
  obtain ⟨R₀, iR₀, dR₀, sR₀, ι₀, hι₀, 𝒳₀, g₀, sg₀, hproj₀, q₀, hpb₀, Z₀, hZ₀c, hZ₀, ιC, fιC, C,
    hC⟩ := exists_model n sZ hZ E hE
  haveI := isRegularRing_of_smooth_int R₀
  haveI : IsProper g₀ := hproj₀.isProper
  obtain ⟨𝒟₀, h𝒟₀, h𝒟₀supp⟩ := exists_isRelativeSNC_of_isPullback n (𝟙 _) g₀ Z₀ hZ₀c
    C hC g₀ (𝟙 𝒳₀) (isPullback_id_spec g₀)
  have hZ₀eq : (𝒟₀.supp : Set 𝒳₀) = Z₀ := by rw [h𝒟₀supp]; rfl
  subst hZ₀eq
  have hbr := baseRing_facts (R₀ := R₀)
  obtain ⟨hb1, hb2⟩ := hbr
  -- the generic constants
  obtain ⟨s₁, hs₁, H₁⟩ := exists_s_modelCone n g₀ h𝒟₀ C hC
  choose s₂ hs₂ hs₂1 H₂ using fun p : ℕ => exists_s_modelHodgeCone n g₀ h𝒟₀ C hC p
  obtain ⟨sT, hsT⟩ : ∃ sT : Γ(Spec (CommRingCat.of R₀), ⊤),
      sT = s₁ * ∏ p ∈ Finset.range (n + 1), s₂ p := ⟨_, rfl⟩
  haveI : Nontrivial Γ(Spec (CommRingCat.of R₀), ⊤) := @IsDomain.toNontrivial _ _ hb1
  haveI : NoZeroDivisors Γ(Spec (CommRingCat.of R₀), ⊤) := @IsDomain.to_noZeroDivisors _ _ hb1
  have hsT0 : sT ≠ 0 := by
    rw [hsT]
    exact mul_ne_zero hs₁ (Finset.prod_ne_zero_iff.mpr fun p _ => hs₂ p)
  have hs₂' : ∀ p, ∃ c, sT = s₂ p * c := by
    intro p
    by_cases hp : n < p
    · exact ⟨sT, by rw [hs₂1 p hp, one_mul]⟩
    · refine ⟨s₁ * ∏ p' ∈ (Finset.range (n + 1)).erase p, s₂ p', ?_⟩
      rw [hsT, ← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr (Nat.lt_succ_of_le (not_lt.mp hp)))]
      ring
  obtain ⟨s, hs⟩ : ∃ s : R₀, s = (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom sT := ⟨_, rfl⟩
  have hs0 : s ≠ 0 := fun h => hsT0
    ((Scheme.ΓSpecIso (CommRingCat.of R₀)).commRingCatIsoToRingEquiv.injective
      (hs.symm.trans (h.trans (map_zero _).symm)))
  -- nonvanishing of the constants along a ring map not killing `s`
  have hnz : ∀ {K : CommRingCat.{0}} (φ : CommRingCat.of R₀ ⟶ K), φ.hom s ≠ 0 →
      φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom s₁) ≠ 0 ∧
        ∀ p, φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom (s₂ p)) ≠ 0 := by
    intro K φ hφ
    refine ⟨fun h => hφ ?_, fun p h => hφ ?_⟩
    · rw [hs, hsT, map_mul, map_mul, h, zero_mul]
    · obtain ⟨c, hc⟩ := hs₂' p
      rw [hs, hc, map_mul, map_mul, h, zero_mul]
  -- the base `R = R₀[1/s]`
  obtain ⟨R, iR, dR, sR, a, ι, has, hι, hιcomp⟩ := exists_away_smooth_int ι₀ hι₀ s hs0
  haveI := isRegularRing_of_smooth_int R
  let gR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R₀) := Spec.map (CommRingCat.ofHom a)
  let g : pullback g₀ gR ⟶ Spec (CommRingCat.of R) := pullback.snd g₀ gR
  have hsq : IsPullback (pullback.fst g₀ gR) g g₀ gR := IsPullback.of_hasPullback g₀ gR
  haveI : SmoothOfRelativeDimension n g := smoothOfRelativeDimension_of_isPullback hsq
  have hprojg : IsProjective g := IsProjective.of_isPullback hsq.flip hproj₀
  obtain ⟨𝒟, h𝒟, h𝒟supp⟩ := exists_isRelativeSNC_of_isPullback n (CommRingCat.ofHom a) g₀
    (𝒟₀.supp : Set 𝒳₀) hZ₀c C hC g (pullback.fst g₀ gR) hsq
  -- a closed point with a `W₂` lift in characteristic `p > n`
  haveI : Nonempty (PrimeSpectrum R) := inferInstance
  obtain ⟨𝔪, h𝔪, -, hfin, p, hp, hnp, hchar, φW, hφW⟩ :=
    MMP.exists_isMaximal_mem_smoothLocus_witt_lift (R := R) Set.univ isOpen_univ Set.univ_nonempty
      (fun x _ => by rw [Algebra.smoothLocus_eq_univ_iff.mpr inferInstance]; trivial) n
  haveI := hp
  haveI := hfin
  haveI := hchar
  obtain ⟨hfinκ, hcharκ, ρ, hρ, φ', hφ'⟩ := exists_wittTwoLift_residueField 𝔪 p φW hφW
  haveI := hfinκ
  haveI := hcharκ
  let pt : Spec (CommRingCat.of R) := ⟨𝔪, h𝔪.isPrime⟩
  let γ := (Spec (CommRingCat.of R)).fromSpecResidueField pt
  have hfsq : IsPullback (pullback.fst g γ) (pullback.snd g γ) g γ :=
    IsPullback.of_hasPullback g γ
  haveI : SmoothOfRelativeDimension n (pullback.snd g γ) :=
    smoothOfRelativeDimension_of_isPullback hfsq
  have hbig' := IsPullback.paste_horiz hfsq hsq
  let φs : CommRingCat.of R₀ ⟶ (Spec (CommRingCat.of R)).residueField pt :=
    CommRingCat.ofHom a ≫ Spec.preimage γ
  have hφs : Spec.map φs = γ ≫ gR := by
    rw [Spec.map_comp, Spec.map_preimage]
  have hφss : φs.hom s ≠ 0 := by
    have : φs.hom s = (Spec.preimage γ).hom (a s) := rfl
    rw [this]
    exact (has.map (Spec.preimage γ).hom).ne_zero
  have hsq' : IsPullback (pullback.fst g γ ≫ pullback.fst g₀ gR) (pullback.snd g γ) g₀
      (Spec.map φs) := by
    rw [hφs]
    exact hbig'
  obtain ⟨Ds, hDs, hDssupp⟩ := exists_isRelativeSNC_of_isPullback n φs g₀
    (𝒟₀.supp : Set 𝒳₀) hZ₀c C hC (pullback.snd g γ) _ hsq'
  have hsupp_s : (pullback.fst g γ).base ⁻¹' (𝒟.supp : Set _) = (Ds.supp : Set _) := by
    rw [hDssupp, h𝒟supp, ← Set.preimage_comp]
    rfl
  -- the pinned inclusion on the fibre and its cokernel
  haveI : IsRegularRing ((Spec (CommRingCat.of R)).residueField pt) := inferInstance
  have hCs := forall_mem_weakChart_of_isPullback n g₀ C hC φs (pullback.snd g γ) _ hsq' Ds hDssupp
  let is := relLogToFormsCx (pullback.snd g γ) (isLocalSectionRel_twisted (pullback.snd g γ) hDs hCs)
    (resForms_app_injective (pullback.snd g γ) hDs hCs)
  have his := relLogToFormsCx_pinned (pullback.snd g γ)
    (isLocalSectionRel_twisted (pullback.snd g γ) hDs hCs)
    (resForms_app_injective (pullback.snd g γ) hDs hCs)
  have hfib := finrank_hyp_cokernel_fibre_eq_sum n g hprojg 𝒟 h𝒟 pt p hnp ρ hρ φ' hφ' Ds hDs
    hsupp_s is his (cokernel is) (cokernel.π is) (cokernel.condition is) (cokernelIsCokernel is) k
  -- the two fibres have the same dimensions
  have hC₁ := (hnz (CommRingCat.ofHom ι₀) ((map_ne_zero_iff _ hι₀).mpr hs0))
  have hC₂ := hnz φs hφss
  have hk : ((k : ℕ) : ℤ) = ((k : ℤ) - 1) + 1 := by ring
  have edR : Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
      (Hc sZ ⟨D.extend ComplexShape.embeddingUpNat, 0,
        CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
      Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField pt), ⊤)
        (Hc (pullback.snd g γ) ⟨(cokernel is).extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) := by
    rw [hk]
    exact (finrank_hc_cokernel_eq n g₀ h𝒟₀ C hC (CommRingCat.of ℂ) (Field.toIsField _)
      (CommRingCat.ofHom ι₀) sZ q₀ hpb₀ E hE hZ₀.symm i hi D q hiq hq s₁ hC₁.1 H₁ _).trans
      (finrank_hc_cokernel_eq n g₀ h𝒟₀ C hC _ (Field.toIsField _) φs (pullback.snd g γ) _ hsq'
        Ds hDs hDssupp is his (cokernel is) (cokernel.π is) (cokernel.condition is)
        (cokernelIsCokernel is) s₁ hC₂.1 H₁ _).symm
  have eHo : ∀ p' : ℕ, ∀ j : ℕ, Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
      (Hc sZ (single0 sZ (D.X p')) (j : ℤ)) =
      Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField pt), ⊤)
        (Hc (pullback.snd g γ) (single0 (pullback.snd g γ) ((cokernel is).X p')) (j : ℤ)) := by
    intro p' j
    have hj : ((j : ℕ) : ℤ) = ((j : ℤ) - 1) + 1 := by ring
    rw [hj]
    exact (finrank_hc_single_cokernel_eq n g₀ h𝒟₀ C hC (CommRingCat.of ℂ) (Field.toIsField _)
      (CommRingCat.ofHom ι₀) sZ q₀ hpb₀ E hE hZ₀.symm i hi D q hiq hq p' (s₂ p') (hC₁.2 p')
      (H₂ p') _).trans
      (finrank_hc_single_cokernel_eq n g₀ h𝒟₀ C hC _ (Field.toIsField _) φs (pullback.snd g γ) _
        hsq' Ds hDs hDssupp is his (cokernel is) (cokernel.π is) (cokernel.condition is)
        (cokernelIsCokernel is) p' (s₂ p') (hC₂.2 p') (H₂ p') _).symm
  exact edR.trans (hfib.trans (Finset.sum_congr rfl fun p' _ => (eHo p' (k - p')).symm))

end Assembly

/-! ### Hypercohomology along a closed embedding -/

section ClosedEmbedding

open MMP.Analytic

variable {T T' : TopCat.{0}} (f : T' ⟶ T)

/-- **Hypercohomology along a closed embedding.** For a closed embedding `f` and a complex `K` of
sheaves whose terms have trivial stalks off the image of `f`, the pullback
`ℍ^n(T, K) ⟶ ℍ^n(T', f⁻¹ K)` is an isomorphism. -/
private theorem isIso_hypercohomologyPullback_of_isClosedEmbedding (hf : Topology.IsClosedEmbedding f)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} T) ℤ)
    (hK : ∀ q, ∀ x ∉ Set.range f, Subsingleton ((K.X q).presheaf.stalk x)) (n : ℤ) :
    IsIso (hypercohomologyPullback f K n) := by
  have hsec : ∀ q, IsIso (godementSectionsPullback f (K.X q)) := by
    intro q
    have : IsIso (((globalSections T).mapHomologicalComplex _).map
        (godementResolutionPullback f (K.X q))) := by
      have : ∀ k, IsIso ((((globalSections T).mapHomologicalComplex _).map
          (godementResolutionPullback f (K.X q))).f k) := fun k =>
        (ConcreteCategory.isIso_iff_bijective _).2
          (CoherentAnalytic.godementResolutionPullback_app_bijective_of_isClosedEmbedding hf
            (K.X q) (hK q) k ⊤)
      exact HomologicalComplex.Hom.isIso_of_components _
    exact ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{0}).mapIso
      (asIso (((globalSections T).mapHomologicalComplex _).map
        (godementResolutionPullback f (K.X q))))).isIso_hom
  have h1 : IsIso (godementSectionsDoubleComplexPullback f K) := by
    have : ∀ q, IsIso ((godementSectionsDoubleComplexPullback f K).f q) := hsec
    exact HomologicalComplex.Hom.isIso_of_components _
  let e := asIso (godementSectionsDoubleComplexPullback f K)
  have h2 : IsIso (HomologicalComplex₂.total.map (godementSectionsDoubleComplexPullback f K)
      (ComplexShape.up ℤ)) :=
    ⟨HomologicalComplex₂.total.map e.inv (ComplexShape.up ℤ), by
      rw [← HomologicalComplex₂.total.map_comp]
      simp [e], by
      rw [← HomologicalComplex₂.total.map_comp]
      simp [e]⟩
  unfold hypercohomologyPullback
  exact (HomologicalComplex.homologyFunctor _ _ n).map_isIso _

end ClosedEmbedding

/-! ### The constant sheaf and inverse images -/

section ConstantPullback

variable {T T' : TopCat.{0}} (f : T' ⟶ T)

/-- The adjunction `f⁻¹ ℂ_T ⊣ Γ(T', -)` obtained by composing `ℂ_T ⊣ Γ(T, -)` with
`f⁻¹ ⊣ f_*`. -/
private noncomputable def constantSheafPullbackAdj :
    constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0} ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{0} f ⊣
      (sheafSections (Opens.grothendieckTopology T') AddCommGrpCat.{0}).obj (op ⊤) :=
  ((constantSheafAdj _ _ isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)).ofNatIsoRight (Iso.refl _)

/-- **The inverse image of a constant sheaf is constant**: `ℂ_{T'} ≅ f⁻¹ ℂ_T`, both being left
adjoint to global sections. -/
private noncomputable def constantSheafPullbackIso :
    constantSheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0} ≅
      constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0} ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{0} f :=
  (constantSheafAdj _ _ isTerminalTop).leftAdjointUniq (constantSheafPullbackAdj f)

/-- The unit of `ℂ_T ⊣ Γ(T, -)` sends `a` to the global section `a` of the sheafified constant
presheaf. -/
private theorem constantSheafAdj_unit_app (A : AddCommGrpCat.{0}) :
    (constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0} isTerminalTop).unit.app A =
      (toSheafify (Opens.grothendieckTopology T) ((Functor.const (Opens T)ᵒᵖ).obj A)).app
        (op ⊤) := by
  simp [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj]
  rfl

/-- The adjoint of a map out of `ℂ_{T'}` through `ℂ_{T'} ≅ f⁻¹ ℂ_T`. -/
private theorem homEquiv_constantSheafPullbackIso_hom_app_comp (A : AddCommGrpCat.{0})
    {G : Sheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0}}
    (g : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj
      ((constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj A) ⟶ G) :
    (constantSheafAdj _ _ isTerminalTop).homEquiv _ _
        ((constantSheafPullbackIso f).hom.app A ≫ g) =
      (constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0} isTerminalTop).unit.app A ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app _ ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map g).hom.app (op ⊤) := by
  refine ((constantSheafAdj _ _ isTerminalTop).homEquiv_naturality_right _ _).trans ?_
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have hu : (constantSheafPullbackAdj f).unit.app A =
      (constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0} isTerminalTop).unit.app A ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app _).hom.app
        (op ⊤) := by
    simp [constantSheafPullbackAdj, Adjunction.comp_unit_app]
    rfl
  rw [hu]
  exact Category.assoc _ _ _

/-- Surjectivity of a composite. -/
private theorem surjective_comp_of_surjective {A B C : AddCommGrpCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) : Function.Surjective (f ≫ g) := by
  intro c
  obtain ⟨b, rfl⟩ := hg c
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨a, rfl⟩

/-- A complex concentrated in degree `0` has trivial stalks where its degree-zero term does. -/
private theorem subsingleton_stalk_single_obj_X (A : TopCat.Sheaf AddCommGrpCat.{0} T) (x : T)
    (h : Subsingleton (A.presheaf.stalk x)) (q : ℤ) :
    Subsingleton ((((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{0} T)
      (ComplexShape.up ℤ) 0).obj A).X q).presheaf.stalk x) := by
  by_cases hq : q = 0
  · subst hq
    exact @Function.Injective.subsingleton _ _ _
      (ConcreteCategory.bijective_of_isIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).mapIso
        ((sheafToPresheaf _ _).mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A))).hom).1 h
  · exact MMP.Analytic.CoherentAnalytic.subsingleton_stalk_of_isZero
      (HomologicalComplex.isZero_single_obj_X _ 0 A q hq) x

/-- A morphism of schemes over `ℂ` carries structure constants to structure constants. -/
private theorem app_top_baseRingHom {Y Y' : Scheme.{0}} (g : Y' ⟶ Y)
    (sY : Y ⟶ Spec (CommRingCat.of ℂ)) (a : ℂ) :
    (g.app ⊤).hom (MMP.Analytic.ComplexPoints.baseRingHom sY ⊤ a) =
      MMP.Analytic.ComplexPoints.baseRingHom (g ≫ sY) ⊤ a := by
  have e1 : Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ :=
    (congrArg Y.presheaf.map (Subsingleton.elim _ _)).trans (Y.presheaf.map_id _)
  have e2 : Y'.presheaf.map (homOfLE (le_top : (⊤ : Y'.Opens) ≤ ⊤)).op = 𝟙 _ :=
    (congrArg Y'.presheaf.map (Subsingleton.elim _ _)).trans (Y'.presheaf.map_id _)
  change (g.app ⊤).hom ((Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op).hom
      (sY.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))) =
    (Y'.presheaf.map (homOfLE (le_top : (⊤ : Y'.Opens) ≤ ⊤)).op).hom
      ((g ≫ sY).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
  rw [e1, e2, Scheme.Hom.comp_appTop]
  rfl

/-- A cancellation of isomorphisms, in the form produced by the degree-zero terms of maps to
complexes concentrated in degree `0`. -/
private theorem iso_chain_comp_eq {𝒟 : Type*} [Category 𝒟] {P Q A' B C T : 𝒟} (x : P ≅ Q)
    (g : Q ≅ A') (u : A' ≅ B) (w : A' ≅ C) (k : P ⟶ T) :
    x.hom ≫ (g.hom ≫ u.hom) ≫ (u.inv ≫ w.hom) ≫ w.inv ≫ (x ≪≫ g).inv ≫ k = 𝟙 P ≫ k := by
  simp

/-- A cancellation of isomorphisms through a functor, in the form produced by the degree-zero
terms of maps to complexes concentrated in degree `0`. -/
private theorem map_iso_chain_comp_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {X Y : 𝒞} {X' Y' Z' : 𝒟} (s : Y ≅ X) (s' : X' ≅ F.obj X) (ι : F.obj X ⟶ Z') (s'' : Y' ≅ Z') :
    F.map (𝟙 X ≫ s.inv) ≫ (F.map s.hom ≫ s'.inv) ≫ (s'.hom ≫ ι ≫ s''.inv) =
      ι ≫ 𝟙 Z' ≫ s''.inv := by
  simp

/-- A cancellation through a functor, in the form produced by degree-zero terms. -/
private theorem comp_map_iso_chain_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {W' W V : 𝒟} {X Y : 𝒞} (s : W' ⟶ W) (e : W ⟶ F.obj X) (t : Y ≅ X) (k : F.obj X ⟶ V) :
    s ≫ e ≫ k = s ≫ e ≫ F.map (𝟙 X ≫ t.inv) ≫ (F.map t.hom ≫ k) := by
  simp

end ConstantPullback

/-! ### Derived and Godement hypercohomology -/

section Bridge

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

open MMP.Analytic

variable (X : RingedSpace.{0, 0})

/-- Surjectivity transported along a commutative square whose vertical maps are isomorphisms. -/
private theorem surjective_of_comm {A B A' B' : AddCommGrpCat.{0}} (f : A ⟶ B) (g : A' ⟶ B')
    (u : A ≅ A') (v : B ≅ B') (w : f ≫ v.hom = u.hom ≫ g) (hf : Function.Surjective f) :
    Function.Surjective g := by
  intro b
  obtain ⟨a, ha⟩ := hf (v.inv b)
  refine ⟨u.hom a, ?_⟩
  have := ConcreteCategory.congr_hom w a
  simp only [ConcreteCategory.comp_apply] at this
  rw [← this, ha]; simp

/-- **Surjectivity passes from derived to Godement hypercohomology**: for a morphism of bounded
below complexes of `𝒪_X`-modules which is surjective on derived hypercohomology, the induced map on
the Godement hypercohomology of the underlying complexes of abelian sheaves is surjective. -/
private theorem surjective_hypercohomology_map_toSheaf_of_surjective
    {K K' : CochainComplex.Plus (SheafOfModules.{0} (structureSheafRing X))}
    (f : K ⟶ K') (n : ℤ)
    (hf : Function.Surjective ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map f)))) :
    Function.Surjective ((hypercohomology X.carrier n).map
      (((SheafOfModules.toSheaf _).mapHomologicalComplex _).map f.hom)) := by
  -- the comparison of [Stacks, Tag 01F1]
  have hab : Function.Surjective ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} n).map
      ((Stacks.Cohomology.Leray.sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map
          ((SheafOfModules.toSheaf _).mapCochainComplexPlus.map f)))) :=
    surjective_of_comm ((DerivedCategory.Plus.Q ⋙
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ n ⋙
          forget₂ (ModuleCat.{0} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{0}).map f)
      _ ((Stacks.Cech.Hypercohomology.realizationNatIso X n).app K).symm
      ((Stacks.Cech.Hypercohomology.realizationNatIso X n).app K').symm
      ((Stacks.Cech.Hypercohomology.realizationNatIso X n).inv.naturality f) hf
  -- the Godement bridge
  exact surjective_of_comm _ _
    (MMP.DeRhamBetti.GodPull.hypercohomologyIsoGodementTotal X.carrier
      ((SheafOfModules.toSheaf _).mapCochainComplexPlus.obj K) n)
    (MMP.DeRhamBetti.GodPull.hypercohomologyIsoGodementTotal X.carrier
      ((SheafOfModules.toSheaf _).mapCochainComplexPlus.obj K') n)
    (MMP.DeRhamBetti.GodPull.hypercohomologyIsoGodementTotal_hom_naturality X.carrier
      ((SheafOfModules.toSheaf _).mapCochainComplexPlus.map f) n) hab

end Bridge

section DegreeZeroAlg

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **In degree zero the comparison of forms is the identification `Ω^0 ≅ 𝒪`**: on an affine open
it carries the degree-zero form of a function `g` to `g` in `⋀^0`. -/
private theorem formsAlgEquiv_zeroIso_inv (W : X.affineOpens) (g : Γ(X, W)) :
    letI := MMP.Mori.sectionAlgebra f W
    MMP.DeRham.formsAlgEquiv f 0 W
        ((Scheme.Hom.relativeDifferentialFormsZeroIso f).inv.val.app (op (W : X.Opens)) g) =
      (exteriorPower.zeroEquiv Γ(X, W) Ω[Γ(X, W)⁄k]).symm g := by
  letI := MMP.Mori.sectionAlgebra f W
  apply (exteriorPower.zeroEquiv Γ(X, W) Ω[Γ(X, W)⁄k]).injective
  have h1 : (Scheme.Hom.relativeDifferentialFormsZeroIso f).inv.val.app (op (W : X.Opens)) g =
      g • (show Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), (W : X.Opens)) from
        (Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op (W : X.Opens))) :=
    zeroIso_inv_eq_smul_one f (W : X.Opens) g
  rw [LinearEquiv.apply_symm_apply, h1, LinearEquiv.map_smul, LinearEquiv.map_smul,
    MMP.DeRham.formsAlgEquiv_apply]
  have h2 := Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_one f W.2
    (isAffineOpen_top _) (by simp)
  erw [h2]
  have h3 := LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality (R := Γ(X, W))
    (MMP.DeRham.kaehlerSpecEquiv f (W : X.Opens)).toLinearMap)
    (exteriorPower.ιMulti Γ(X, W) 0 Fin.elim0)
  rw [LinearMap.comp_apply] at h3
  erw [h3, exteriorPower.zeroEquiv_ιMulti]
  exact mul_one g

end DegreeZeroAlg

/-! ### The edge map of the restriction complex -/

section EdgeMap

open MMP.Mori.Divisor.LogSpreadingProof.G1 Stacks.DeRhamDirectImage
open scoped ZeroObject

variable (n : ℕ) {Z : Scheme.{0}} (sZ : Z ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n sZ] (hZ : IsProjective sZ)
  (E : MMP.Mori.Divisor Z) (hE : E.IsRelativeSNC n sZ)
  (i : relativeLogDeRhamComplex n sZ E hE E.suppIdeal ⟶ Scheme.Hom.deRhamComplex sZ)
  (hi : ∀ (p : ℕ) (W : Z.Opensᵒᵖ)
    (ω : ((relativeLogDeRhamComplex n sZ E hE E.suppIdeal).X p).val.obj W),
    ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι E.supp.compl) sZ).f p).val.app
      W ((i.f p).val.app W ω) = ω.1)
  (D : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
  (q : Scheme.Hom.deRhamComplex sZ ⟶ D) (hiq : i ≫ q = 0)
  (hq : IsColimit (CokernelCofork.ofπ q hiq))

include hE in
/-- Weak charts of a relative snc divisor of a smooth complex scheme cover it. -/
private theorem forall_mem_weakChart_of_isRelativeSNC :
    ∀ y : Z, ∃ c : WeakChart sZ n (E.supp : Set Z), y ∈ ((c.toLogData sZ E).W : Z.Opens) :=
  fun y => let ⟨c, hc⟩ := exists_weakChart_of_isRelativeSNC sZ hE y; ⟨c, hc⟩

include hZ hi hq in
/-- **The cohomology of the terms of the restriction complex is finite dimensional.** -/
private theorem moduleFinite_hc_single_cokernel (p : ℕ) (j : ℤ) :
    Module.Finite Γ(Spec (CommRingCat.of ℂ), ⊤) (Hc sZ (single0 sZ (D.X p)) j) := by
  haveI : IsProper sZ := hZ.isProper
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hCZ := forall_mem_weakChart_of_isRelativeSNC n sZ E hE
  obtain ⟨e⟩ := nonempty_iso_pushforward_cokernel sZ i hi D q hiq hq
    (isLocalSectionRel_twisted sZ hE hCZ) (resForms_app_injective sZ hE hCZ) p
  haveI := isCoherent_cokernelLogToForms sZ (isLocalSectionRel_twisted sZ hE hCZ) p
  have hK : ∀ k, ∃ M : Z.Modules, M.IsCoherent ∧
      Nonempty ((single0 sZ (D.X p)).1.X k ≅
        (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase sZ)).obj M) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      exact ⟨_, inferInstance, ⟨HomologicalComplex.singleObjXSelf _ 0 _ ≪≫ e⟩⟩
    · haveI := Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
        (isZero_zero (Z.Modules))
      exact ⟨0, inferInstance,
        ⟨(HomologicalComplex.isZero_single_obj_X _ _ _ _ hk).iso (isZero_pushforward_zero sZ)⟩⟩
  haveI := AlgebraicGeometry.DeRhamTypeComplex.moduleFinite_homology_derivedSections sZ
    (single0 sZ (D.X p)) hK j
  exact Module.Finite.equiv
    (nonempty_hcIsoHypercohomology sZ (single0 sZ (D.X p)) j).some.symm.toLinearEquiv

include hZ hi hq in
/-- **The edge map of the restriction complex is surjective.** By `E₁`-degeneration
(`finrank_hc_cokernel_eq_sum`), the projection `σ^{≥0}𝒟_E^• ⟶ 𝒟_E^0` of the stupid filtration
is onto on hypercohomology in every degree. -/
private theorem surjective_hypFunctor_map_truncGEπ0_cokernel (k : ℕ) :
    Function.Surjective ((MMP.FourfoldProofs.FractionalLogComplexProof.hypFunctor sZ k).map
      (DerivedCategory.Plus.Q.map
        (MMP.LcBpf.truncGEπ0 sZ (D.extend ComplexShape.embeddingUpNat)))).hom := by
  have hT : IsField Γ(Spec (CommRingCat.of ℂ), ⊤) := MulEquiv.isField (Field.toIsField ℂ)
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.toMulEquiv
  exact MMP.LcBpf.surjective_hypFunctor_map_truncGEπ0_extend_of_finrank_eq_sum sZ hT D k
    (fun p _ => moduleFinite_hc_single_cokernel n sZ hZ E hE i hi D q hiq hq p _)
    (finrank_hc_cokernel_eq_sum n sZ hZ E hE i hi D q hiq hq k)

/-- Restriction of degree-zero forms to `E`, as a map of `𝒪_Z`-modules `Ω^0_Z ⟶ i_*𝒪_E`. -/
private noncomputable abbrev restrictFormsZero :
    sZ.relativeDifferentialForms ((0 : ℕ) : ℤ) ⟶
      (Scheme.Modules.pushforward E.suppIdeal.subschemeι).obj (SheafOfModules.unit _) :=
  (Scheme.Hom.relativeDifferentialFormsZeroIso sZ).hom ≫
    SheafOfModules.unitToPushforwardObjUnit E.suppIdeal.subschemeι.toRingCatSheafHom

include hi in
/-- **Twisted functions vanish on the divisor**: the regular extension of the twisted degree-zero
forms, followed by restriction to `E`, is zero. -/
private theorem logToForms_comp_unitToPushforward_eq_zero :
    logToForms sZ ((isLocalSectionRel_twisted sZ hE
        (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0) ≫ restrictFormsZero sZ E = 0 := by
  have hCZ := forall_mem_weakChart_of_isRelativeSNC n sZ E hE
  haveI : Smooth sZ := SmoothOfRelativeDimension.smooth n sZ
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hi0 : ∀ (W : Z.Opens) (ω : ((relativeLogDeRhamComplex n sZ E hE E.suppIdeal).X 0).val.obj
      (op W)), ρ0 sZ E W ((i.f 0).val.app (op W) ω) = ω.1 := fun W ω => hi 0 (op W) ω
  have hzero := comp_toSubschemeFunctions_eq_zero sZ hE (i.f 0) hi0
  have hpin := pinned_f_eq sZ i hi (isLocalSectionRel_twisted sZ hE hCZ)
    (resForms_app_injective sZ hE hCZ) 0
  ext W x
  have h1 := congrArg (fun φ => φ.val.app (op W)
    ((relLogXIso n sZ E hE true 0).inv.val.app (op W) x)) hpin
  have h3 : (relLogXIso n sZ E hE true 0).hom.val.app (op W)
      ((relLogXIso n sZ E hE true 0).inv.val.app (op W) x) = x :=
    congrArg (fun φ => φ.val.app (op W) x) (relLogXIso n sZ E hE true 0).inv_hom_id
  have h4 : (i.f 0).val.app (op W) ((relLogXIso n sZ E hE true 0).inv.val.app (op W) x) =
      (logToForms sZ ((isLocalSectionRel_twisted sZ hE hCZ) 0)).val.app (op W) x :=
    h1.trans (congrArg (fun y => (logToForms sZ ((isLocalSectionRel_twisted sZ hE hCZ) 0)).val.app
      (op W) y) h3)
  exact (congrArg (fun y => (toSubschemeFunctions sZ E.suppIdeal).val.app (op W) y) h4).symm.trans
    (hzero W _)

/-- A morphism of `𝒪_X`-modules bijective on the sections over every affine open is an
isomorphism. -/
private theorem isIso_of_bijective_app_affineOpens {X : Scheme.{0}} {M N : X.Modules} (a : M ⟶ N)
    (ha : ∀ U : X.affineOpens, Function.Bijective (a.val.app (op U.1)).hom) : IsIso a := by
  let M' : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  let N' : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf, N.isSheaf⟩
  let a' : M' ⟶ N' := ⟨a.mapPresheaf⟩
  have ha' : IsIso a' := TopCat.Sheaf.isIso_iff_isIso_basis
    (B := fun U : X.affineOpens => U.1)
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using X.isBasis_affineOpens)
    (fun U => (ConcreteCategory.isIso_iff_bijective _).2 (ha U))
  have : IsIso ((Scheme.Modules.toPresheaf X).map a) :=
    (TopCat.Sheaf.forget AddCommGrpCat X).map_isIso a'
  exact isIso_of_reflects_iso a (Scheme.Modules.toPresheaf X)

/-- **The degree-zero term of the restriction complex is `𝒪_E`**: the cokernel of the twisted
functions `𝒪_Z(-E) ⟶ 𝒪_Z` maps to the functions on `E`. -/
private noncomputable def zeroToSubscheme :
    cokernelLogToForms sZ (isLocalSectionRel_twisted sZ hE
        (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0 ⟶
      (Scheme.Modules.pushforward E.suppIdeal.subschemeι).obj (SheafOfModules.unit _) :=
  cokernel.desc _ (restrictFormsZero sZ E) (logToForms_comp_unitToPushforward_eq_zero n sZ E hE i hi)

include hi in
/-- **`𝒟_E^0 ≅ 𝒪_E` as `𝒪_Z`-modules.** -/
private theorem isIso_zeroToSubscheme : IsIso (zeroToSubscheme n sZ E hE i hi) := by
  haveI : Smooth sZ := SmoothOfRelativeDimension.smooth n sZ
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hCZ := forall_mem_weakChart_of_isRelativeSNC n sZ E hE
  let L := logToForms sZ ((isLocalSectionRel_twisted sZ hE hCZ) 0)
  let e0 := Scheme.Hom.relativeDifferentialFormsZeroIso sZ
  let u0 := SheafOfModules.unitToPushforwardObjUnit E.suppIdeal.subschemeι.toRingCatSheafHom
  haveI : (sZ.relativeDifferentialForms ((0 : ℕ) : ℤ)).IsCoherent :=
    Scheme.Hom.isCoherent_relativeDifferentialForms _ 0
  haveI := _root_.isQuasicoherent_of_isCoherent (sZ.relativeDifferentialForms ((0 : ℕ) : ℤ))
  haveI := isCoherent_cokernelLogToForms sZ (isLocalSectionRel_twisted sZ hE hCZ) 0
  haveI := _root_.isQuasicoherent_of_isCoherent
    (cokernelLogToForms sZ (isLocalSectionRel_twisted sZ hE hCZ) 0)
  have hfac : cokernel.π L ≫ zeroToSubscheme n sZ E hE i hi = restrictFormsZero sZ E :=
    cokernel.π_desc _ _ _
  have hi0 : ∀ (W : Z.Opens) (ω : ((relativeLogDeRhamComplex n sZ E hE E.suppIdeal).X 0).val.obj
      (op W)), ρ0 sZ E W ((i.f 0).val.app (op W) ω) = ω.1 := fun W ω => hi 0 (op W) ω
  have hpin := pinned_f_eq sZ i hi (isLocalSectionRel_twisted sZ hE hCZ)
    (resForms_app_injective sZ hE hCZ) 0
  refine isIso_of_bijective_app_affineOpens _ fun W =>
    ⟨(injective_iff_map_eq_zero _).2 fun a hab => ?_, fun t => ?_⟩
  · obtain ⟨ω, rfl⟩ := surjective_app_of_epi_of_isAffineOpen (cokernel.π L) W.1 W.2 a
    have hψω : ((zeroToSubscheme n sZ E hE i hi).val.app (op W.1)).hom
        (((cokernel.π L).val.app (op W.1)).hom ω) = 0 := hab
    have hψπ := congrArg (fun φ => (φ.val.app (op W.1)).hom ω) hfac
    have hg' : (E.suppIdeal.subschemeι.app W).hom ((e0.hom.val.app (op W.1)).hom ω) = 0 :=
      hψπ.symm.trans hψω
    have hg : (e0.hom.val.app (op W.1)).hom ω ∈ E.suppIdeal.ideal W := by
      have h := (RingHom.mem_ker (f := (E.suppIdeal.subschemeι.app W).hom)).2 hg'
      rwa [E.suppIdeal.ker_subschemeι_app W] at h
    obtain ⟨x, hx⟩ := exists_relativeLogDeRhamComplex_X_zero sZ hE E.suppIdeal W hg
    have hx' : (i.f 0).val.app (op W.1) x = z0 sZ ((e0.hom.val.app (op W.1)).hom ω) :=
      ρ0_injective sZ hE W (by rw [hi0, hx])
    have hz : z0 sZ ((e0.hom.val.app (op W.1)).hom ω) = ω :=
      congrArg (fun φ => (φ.val.app (op W.1)).hom ω) e0.hom_inv_id
    have hpin' := congrArg (fun φ => φ.val.app (op W.1) x) hpin
    have hc := congrArg (fun φ => (φ.val.app (op W.1)).hom
      ((relLogXIso n sZ E hE true 0).hom.val.app (op W.1) x)) (cokernel.condition L)
    refine (congrArg (fun y => ((cokernel.π L).val.app (op W.1)).hom y) hz).symm.trans ?_
    refine (congrArg (fun y => ((cokernel.π L).val.app (op W.1)).hom y) hx').symm.trans ?_
    refine (congrArg (fun y => ((cokernel.π L).val.app (op W.1)).hom y) hpin').trans ?_
    exact hc
  · obtain ⟨g, hg⟩ := E.suppIdeal.subschemeι_app_surjective W t
    refine ⟨((cokernel.π L).val.app (op W.1)).hom (z0 sZ g), ?_⟩
    have h1 := congrArg (fun φ => (φ.val.app (op W.1)).hom (z0 sZ g)) hfac
    refine h1.trans ?_
    have h3 : (e0.hom.val.app (op W.1)).hom (z0 sZ g) = g :=
      congrArg (fun φ => (φ.val.app (op W.1)).hom g) e0.inv_hom_id
    exact (congrArg (fun y => (u0.val.app (op W.1)).hom y) h3).trans hg

/-- The realization `κ : E^an ⟶ Z^an` of the inclusion of `E`. -/
private noncomputable abbrev κE : MMP.Analytic.Analytification.space
    (E.suppIdeal.subschemeι ≫ sZ) ⟶ MMP.Analytic.Analytification.space sZ :=
  MMP.Analytic.ComplexPoints.analyticMap E.suppIdeal.subschemeι rfl

include hZ hi in
/-- **`(𝒟_E^0)^an` is the direct image of `𝒪_{E^an}`**, as sheaves of abelian groups on `Z^an`,
by an isomorphism sending the analytification of the class of a function `g` to the analytic
function `i^♯ g` on `E^an`. -/
private theorem exists_toSheaf_analytify_cokernel_zero_iso :
    ∃ θ : (SheafOfModules.toSheaf _).obj ((MMP.Analytic.analytifyModule sZ).obj
        (cokernelLogToForms sZ (isLocalSectionRel_twisted sZ hE
          (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0)) ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (κE sZ E)).obj
        ((sheafCompose (Opens.grothendieckTopology
          (MMP.Analytic.Analytification.space (E.suppIdeal.subschemeι ≫ sZ)))
          (forget₂ RingCat AddCommGrpCat)).obj
            (MMP.Analytic.ringCatSheaf (E.suppIdeal.subschemeι ≫ sZ))),
      ∀ (V : Z.Opens) (g : Γ(Z, V)),
        θ.hom.hom.app (op ((Opens.map (MMP.Analytic.Analytification.toSchemeHom sZ)).obj V))
          (((MMP.Analytic.analytifyModuleUnit sZ (cokernelLogToForms sZ (isLocalSectionRel_twisted
            sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0)).val.app (op V)).hom
            (((cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
              (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0))).val.app (op V)).hom
              (((Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.app (op V)).hom g))) =
        ((MMP.Analytic.ringCatSheafHom (E.suppIdeal.subschemeι ≫ sZ)).hom.app
          (op (E.suppIdeal.subschemeι ⁻¹ᵁ V))).hom ((E.suppIdeal.subschemeι.app V).hom g) := by
  haveI : Smooth sZ := SmoothOfRelativeDimension.smooth n sZ
  haveI : IsProper sZ := hZ.isProper
  haveI := isIso_zeroToSubscheme n sZ E hE i hi
  let e1 := (MMP.Analytic.analytifyModule sZ).mapIso (asIso (zeroToSubscheme n sZ E hE i hi))
  obtain ⟨-, -, θR, -, hF⟩ := (MMP.Analytic.analytification_stalks
    (E.suppIdeal.subschemeι ≫ sZ)).2.2.2.2.2.2.2.2.2.2 sZ E.suppIdeal.subschemeι rfl
  obtain ⟨e2, he2, -⟩ := hF (SheafOfModules.unit _)
  have hfin : (Opens.map (MMP.Analytic.Analytification.toSchemeHom
      (E.suppIdeal.subschemeι ≫ sZ))).Final := by
    rw [Functor.final_iff_of_isFiltered]
    exact ⟨fun _ => ⟨⊤, ⟨homOfLE le_top⟩⟩, fun {_ c} _ _ => ⟨c, 𝟙 c, Subsingleton.elim _ _⟩⟩
  let e3 : (MMP.Analytic.analytifyModule (E.suppIdeal.subschemeι ≫ sZ)).obj
      (SheafOfModules.unit _) ≅ SheafOfModules.unit _ :=
    @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit
      (MMP.Analytic.ringCatSheafHom (E.suppIdeal.subschemeι ≫ sZ)))
      (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _)
  haveI : (Opens.map (κE sZ E)).IsContinuous
      (Opens.grothendieckTopology (MMP.Analytic.Analytification.space sZ))
      (Opens.grothendieckTopology
        (MMP.Analytic.Analytification.space (E.suppIdeal.subschemeι ≫ sZ))) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map _)
      (coverPreserving_opens_map _)
  refine ⟨(SheafOfModules.toSheaf _).mapIso
    (e1 ≪≫ e2 ≪≫ (SheafOfModules.pushforward.{0} θR).mapIso e3), fun V g => ?_⟩
  have hCZ := forall_mem_weakChart_of_isRelativeSNC n sZ E hE
  let L := logToForms sZ ((isLocalSectionRel_twisted sZ hE hCZ) 0)
  let e0 := Scheme.Hom.relativeDifferentialFormsZeroIso sZ
  let u0 := SheafOfModules.unitToPushforwardObjUnit E.suppIdeal.subschemeι.toRingCatSheafHom
  let x := ((cokernel.π L).val.app (op V)).hom ((e0.inv.val.app (op V)).hom g)
  -- the class of `g` is sent to `i^♯ g`
  have hψ : ((zeroToSubscheme n sZ E hE i hi).val.app (op V)).hom x =
      (E.suppIdeal.subschemeι.app V).hom g := by
    have h1 := congrArg (fun φ => (φ.val.app (op V)).hom ((e0.inv.val.app (op V)).hom g))
      (cokernel.π_desc L (restrictFormsZero sZ E)
        (logToForms_comp_unitToPushforward_eq_zero n sZ E hE i hi))
    refine h1.trans ?_
    have h3 : (e0.hom.val.app (op V)).hom ((e0.inv.val.app (op V)).hom g) = g :=
      congrArg (fun φ => (φ.val.app (op V)).hom g) e0.inv_hom_id
    exact congrArg (fun y => (u0.val.app (op V)).hom y) h3
  -- naturality of the unit of analytification
  have hnat := (SheafOfModules.pullbackPushforwardAdjunction.{0}
    (MMP.Analytic.ringCatSheafHom sZ)).unit.naturality (zeroToSubscheme n sZ E hE i hi)
  have s1 := congrArg (fun φ => (φ.val.app (op V)).hom x) hnat.symm
  have s3 := he2 V ((E.suppIdeal.subschemeι.app V).hom g)
  -- the analytification of the unit module is the structure sheaf
  have h := (SheafOfModules.pullbackPushforwardAdjunction.{0}
    (MMP.Analytic.ringCatSheafHom (E.suppIdeal.subschemeι ≫ sZ))).homEquiv_unit
      (SheafOfModules.unit _) (SheafOfModules.unit _)
      (SheafOfModules.pullbackObjUnitToUnit
        (MMP.Analytic.ringCatSheafHom (E.suppIdeal.subschemeι ≫ sZ)))
  have h' := h.symm.trans (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (MMP.Analytic.ringCatSheafHom (E.suppIdeal.subschemeι ≫ sZ)))
  have s4 := congrArg (fun φ => (φ.val.app (op (E.suppIdeal.subschemeι ⁻¹ᵁ V))).hom
    ((E.suppIdeal.subschemeι.app V).hom g)) h'
  let F2 := fun y => (e2.hom.val.app
    (op ((Opens.map (MMP.Analytic.Analytification.toSchemeHom sZ)).obj V))).hom y
  let F3 := fun y => (((SheafOfModules.pushforward.{0} θR).map e3.hom).val.app
    (op ((Opens.map (MMP.Analytic.Analytification.toSchemeHom sZ)).obj V))).hom y
  have step : F2 ((((MMP.Analytic.analytifyModule sZ).map
      (zeroToSubscheme n sZ E hE i hi)).val.app
        (op ((Opens.map (MMP.Analytic.Analytification.toSchemeHom sZ)).obj V))).hom
      (((MMP.Analytic.analytifyModuleUnit sZ _).val.app (op V)).hom x)) =
      ((MMP.Analytic.analytifyModuleUnit (E.suppIdeal.subschemeι ≫ sZ)
        (SheafOfModules.unit _)).val.app (op (E.suppIdeal.subschemeι ⁻¹ᵁ V))).hom
          ((E.suppIdeal.subschemeι.app V).hom g) :=
    (congrArg F2 (s1.trans (congrArg (fun y => ((MMP.Analytic.analytifyModuleUnit sZ _).val.app
      (op V)).hom y) hψ))).trans s3
  exact (congrArg F3 step).trans s4

include hZ hi in
/-- **`𝒟_E^0` restricted to `E^an` is `𝒪_{E^an}`**: an isomorphism
`κ⁻¹ (𝒟_E^0)^an ≅ 𝒪_{E^an}` whose adjoint sends the analytification of the class of a function `g`
to the analytic function `i^♯ g` on `E^an`. -/
private theorem exists_pullback_toSheaf_analytify_cokernel_zero_iso :
    ∃ θ : (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).obj
        ((SheafOfModules.toSheaf _).obj ((MMP.Analytic.analytifyModule sZ).obj
          (cokernelLogToForms sZ (isLocalSectionRel_twisted sZ hE
            (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0))) ≅
      (sheafCompose (Opens.grothendieckTopology
          (MMP.Analytic.Analytification.space (E.suppIdeal.subschemeι ≫ sZ)))
          (forget₂ RingCat AddCommGrpCat)).obj
            (MMP.Analytic.ringCatSheaf (E.suppIdeal.subschemeι ≫ sZ)),
      ∀ (V : Z.Opens) (g : Γ(Z, V)),
        (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (κE sZ E)).unit.app _ ≫
            (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (κE sZ E)).map θ.hom).hom.app
          (op ((Opens.map (MMP.Analytic.Analytification.toSchemeHom sZ)).obj V)))
          (((MMP.Analytic.analytifyModuleUnit sZ (cokernelLogToForms sZ (isLocalSectionRel_twisted
            sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0)).val.app (op V)).hom
            (((cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
              (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0))).val.app (op V)).hom
              (((Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.app (op V)).hom g))) =
        ((MMP.Analytic.ringCatSheafHom (E.suppIdeal.subschemeι ≫ sZ)).hom.app
          (op (E.suppIdeal.subschemeι ⁻¹ᵁ V))).hom ((E.suppIdeal.subschemeι.app V).hom g) := by
  haveI : Smooth sZ := SmoothOfRelativeDimension.smooth n sZ
  haveI : IsProper sZ := hZ.isProper
  obtain ⟨θb, hθb⟩ := exists_toSheaf_analytify_cokernel_zero_iso n sZ hZ E hE i hi
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (κE sZ E)
  have hemb : Topology.IsClosedEmbedding (κE sZ E) :=
    ((MMP.Analytic.analytification_stalks (E.suppIdeal.subschemeι ≫ sZ)).2.2.2.2.2.2.2.2.2.2
      sZ E.suppIdeal.subschemeι rfl).1
  have hcounit := MMP.Analytic.CoherentAnalytic.isIso_pullbackPushforwardAdjunction_counit
    hemb.isInducing
    ((sheafCompose (Opens.grothendieckTopology
      (MMP.Analytic.Analytification.space (E.suppIdeal.subschemeι ≫ sZ)))
      (forget₂ RingCat AddCommGrpCat)).obj
        (MMP.Analytic.ringCatSheaf (E.suppIdeal.subschemeι ≫ sZ)))
  let φ := (adj.homEquiv _ _).symm θb.hom
  have hφ : φ = (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map θb.hom ≫
      adj.counit.app _ := adj.homEquiv_counit _ _ _
  haveI : IsIso φ := by
    rw [hφ]
    haveI : IsIso θb.hom := Iso.isIso_hom θb
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ θb.hom) hcounit
  refine ⟨asIso φ, fun V g => ?_⟩
  have hu : adj.unit.app _ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (κE sZ E)).map φ =
      θb.hom :=
    (adj.homEquiv_unit _ _ φ).symm.trans ((adj.homEquiv _ _).apply_symm_apply θb.hom)
  exact (congrArg (fun ψ => ψ.hom.app
    (op ((Opens.map (MMP.Analytic.Analytification.toSchemeHom sZ)).obj V))
      (((MMP.Analytic.analytifyModuleUnit sZ (cokernelLogToForms sZ (isLocalSectionRel_twisted
        sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0)).val.app (op V)).hom
        (((cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
          (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0))).val.app (op V)).hom
          (((Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.app (op V)).hom g)))) hu).trans
    (hθb V g)

/-- **Adapted algebraic coordinates are a weak chart.** An affine open `W` with functions `z`
whose differentials form a basis of `Ω[Γ(Z, W)⁄ℂ]` and whose first `k` cut out the support of `E`
on `W` is a weak chart of `E`. -/
private noncomputable abbrev weakChartOfAdapted (W : Z.affineOpens) {k : ℕ} (hk : k ≤ n)
    (z : Fin n → Γ(Z, W))
    (hb : letI := MMP.Mori.sectionAlgebra sZ W
      ∃ b : Module.Basis (Fin n) Γ(Z, W) Ω[Γ(Z, W)⁄ℂ],
        ∀ i, b i = KaehlerDifferential.D ℂ Γ(Z, W) (z i))
    (hzero : ∀ w ∈ (W : Z.Opens), (∃ D ∈ E.support, w ∈ D.support) ↔
      w ∉ Z.basicOpen (∏ i : Fin k, z (Fin.castLE hk i))) :
    WeakChart sZ n (E.supp : Set Z) where
  W := W
  t := z
  r := k
  hr := hk
  basis := by
    letI := MMP.Mori.sectionAlgebra sZ W
    obtain ⟨b, hb⟩ := hb
    refine ⟨b.map (MMP.DeRham.kaehlerSpecEquiv sZ (W : Z.Opens)).symm, fun i => ?_⟩
    have h1 : (MMP.DeRham.kaehlerSpecEquiv sZ (W : Z.Opens))
        (CommRingCat.KaehlerDifferential.d (z i)) = KaehlerDifferential.D ℂ Γ(Z, W) (z i) :=
      MMP.DeRham.kaehlerBaseEquiv_d _ _ _ (z i)
    refine (Module.Basis.map_apply _ _ i).trans ?_
    refine (congrArg (MMP.DeRham.kaehlerSpecEquiv sZ (W : Z.Opens)).symm (hb i)).trans ?_
    refine (congrArg (MMP.DeRham.kaehlerSpecEquiv sZ (W : Z.Opens)).symm h1).symm.trans ?_
    exact (MMP.DeRham.kaehlerSpecEquiv sZ (W : Z.Opens)).symm_apply_apply _
  zero := by
    ext w
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Scheme.zeroLocus_singleton, Set.mem_compl_iff]
    constructor
    · rintro ⟨hw, hwW⟩
      refine ⟨(hzero w hwW).1 ?_, hwW⟩
      obtain ⟨D, hD, hwD⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.1 hw
      exact ⟨D, Finsupp.mem_support_iff.2 hD, hwD⟩
    · rintro ⟨hw, hwW⟩
      obtain ⟨D, hD, hwD⟩ := (hzero w hwW).2 hw
      exact ⟨MMP.Mori.DivisorWithCoeffs.mem_supp_iff.2 ⟨D, Finsupp.mem_support_iff.1 hD, hwD⟩, hwW⟩

/-- Cancelling the poles of the logarithmic scalars against the product of the coordinates. -/
private theorem prod_mul_prod_inverse {M : Type*} [CommRing M] (P s : Finset (Fin n))
    (a : Fin n → M) (ha : ∀ j ∈ P, IsUnit (a j)) :
    (∏ j ∈ P, a j) * ∏ j ∈ s, (if j ∈ P then Ring.inverse (a j) else 1) =
      ∏ j ∈ sᶜ, (if j ∈ P then a j else 1) := by
  classical
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_ite, Finset.prod_const_one,
    mul_one, ← Finset.prod_filter_mul_prod_filter_not P (· ∈ s)]
  have h1 : P.filter (· ∈ s) = s.filter (· ∈ P) := by
    ext j; simp only [Finset.mem_filter]; tauto
  have h2 : P.filter (fun j => j ∉ s) = sᶜ.filter (· ∈ P) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_compl]; tauto
  rw [h1, h2, mul_comm (∏ j ∈ s.filter (· ∈ P), a j), mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.prod_eq_one fun j hj => Ring.mul_inverse_cancel _ (ha j (Finset.mem_filter.1 hj).2),
    mul_one]

/-- The algebraic generators `τ_I = (∏_{j ∉ I, j < k} z_j) dz_I` of `Ω^p(log E)(-E)` on an
adapted chart. -/
private noncomputable def twistedGen (W : Z.affineOpens) (k : ℕ) (z : Fin n → Γ(Z, W)) (p : ℕ)
    (I : Set.powersetCard (Fin n) p) :
    letI := MMP.Mori.sectionAlgebra sZ W
    ⋀[Γ(Z, W)]^p Ω[Γ(Z, W)⁄ℂ] :=
  letI := MMP.Mori.sectionAlgebra sZ W
  (∏ j ∈ (I : Finset (Fin n))ᶜ, if (j : ℕ) < k then z j else 1) •
    exteriorPower.ιMulti Γ(Z, W) p fun a =>
      KaehlerDifferential.D ℂ Γ(Z, W) (z (Set.powersetCard.ofFinEmbEquiv.symm I a))

/-- The restriction of a regular form to the complement of `E`, read on `Z`, is its restriction
to `W ∩ LU E`. -/
private theorem ambientFormsEquiv_resForms_app (W : Z.Opens) (p : ℕ)
    (t : Γ(sZ.relativeDifferentialForms (p : ℤ), W)) :
    ambientFormsEquiv sZ (LU E) p W (((resForms sZ E).app (p : ℤ)).val.app (op W) t) =
      (sZ.relativeDifferentialForms (p : ℤ)).presheaf.map
        (homOfLE (inf_le_left : W ⊓ LU E ≤ W)).op t :=
  (congrArg (ambientFormsEquiv sZ (LU E) p W)
      (deRhamPushforwardChain_app_eq sZ (LU E) p (op W) t).symm).trans
    (ambientFormsEquiv_deRhamPushforwardChain sZ (LU E) p W t)

/-- The map of forms induced by a tower `A → B → L` on a combination of scaled wedges of
differentials. -/
private theorem mapExteriorPower_sum_smul_smul_ιMulti {A B L : Type} [CommRing A] [CommRing B]
    [CommRing L] [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L] {p : ℕ}
    {ι : Type} [Fintype ι] (c g : ι → B) (v : ι → Fin p → B) :
    KaehlerDifferential.mapExteriorPower A B L p
        (∑ I, c I • g I • exteriorPower.ιMulti B p fun a => KaehlerDifferential.D A B (v I a)) =
      ∑ I, algebraMap B L (c I) • (algebraMap B L (g I) •
        exteriorPower.ιMulti L p fun a => KaehlerDifferential.D A L (algebraMap B L (v I a))) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_smul, algebraMap_smul, map_smul, algebraMap_smul,
    KaehlerDifferential.mapExteriorPower_ιMulti]
  simp only [KaehlerDifferential.map_D]

/-- The wedges of the logarithmic basis, multiplied by the product of the poles, are the
wedges of the differentials of the coordinates scaled by the coordinates off the wedge. -/
private theorem prod_smul_logBasis_exteriorPower {A B L : Type} [CommRing A] [CommRing B]
    [CommRing L] [Algebra A L] [Algebra B L] {k p : ℕ} {P : Finset (Fin n)} {z : Fin n → B}
    {bL : Module.Basis (Fin n) L Ω[L⁄A]} (hP : ∀ j ∈ P, IsUnit (algebraMap B L (z j)))
    (hbL : ∀ j, bL j = KaehlerDifferential.D A L (algebraMap B L (z j)))
    (hPmem : ∀ j : Fin n, j ∈ P ↔ (j : ℕ) < k) (I : Set.powersetCard (Fin n) p) :
    (∏ j ∈ P, algebraMap B L (z j)) • (MMP.DeRham.logBasis bL hP).exteriorPower p I =
      algebraMap B L (∏ j ∈ (I : Finset (Fin n))ᶜ, if (j : ℕ) < k then z j else 1) •
        exteriorPower.ιMulti L p fun a => KaehlerDifferential.D A L
          (algebraMap B L (z (Set.powersetCard.ofFinEmbEquiv.symm I a))) := by
  rw [MMP.DeRham.logBasis_exteriorPower_apply, smul_smul, exteriorPower.basis_apply]
  congr 1
  · rw [MMP.DeRham.prod_enum]
    unfold MMP.DeRham.logScale
    rw [prod_mul_prod_inverse n P I _ hP, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : (j : ℕ) < k
    · rw [if_pos ((hPmem j).2 hj), if_pos hj]
    · rw [if_neg (fun h => hj ((hPmem j).1 h)), if_neg hj, map_one]
  · unfold exteriorPower.ιMulti_family
    congr 1
    funext a
    exact hbL _

/-- Scaling a combination termwise. -/
private theorem smul_eq_sum_smul_of_eq {R M ι : Type} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype ι] {f : R} {x : M} {c : ι → R} {b g : ι → M}
    (hx : x = ∑ I, c I • b I) (hg : ∀ I, f • b I = g I) : f • x = ∑ I, c I • g I := by
  rw [hx, Finset.smul_sum]
  exact Finset.sum_congr rfl fun I _ => by rw [smul_comm, hg I]

set_option maxRecDepth 40000 in
include hE in
/-- **Twisted forms on an adapted chart are combinations of the `τ_I`.** -/
private theorem exists_formsAlgEquiv_logToForms_eq_sum (W : Z.affineOpens) {k : ℕ} (hk : k ≤ n)
    (z : Fin n → Γ(Z, W))
    (hb : letI := MMP.Mori.sectionAlgebra sZ W
      ∃ b : Module.Basis (Fin n) Γ(Z, W) Ω[Γ(Z, W)⁄ℂ],
        ∀ i, b i = KaehlerDifferential.D ℂ Γ(Z, W) (z i))
    (hzero : ∀ w ∈ (W : Z.Opens), (∃ D ∈ E.support, w ∈ D.support) ↔
      w ∉ Z.basicOpen (∏ i : Fin k, z (Fin.castLE hk i))) (p : ℕ)
    (ℓ : Γ(logModule n sZ E hE E.suppIdeal p, W)) :
    letI := MMP.Mori.sectionAlgebra sZ W
    ∃ a : Set.powersetCard (Fin n) p → Γ(Z, W),
      MMP.DeRham.formsAlgEquiv sZ p W ((logToForms sZ ((isLocalSectionRel_twisted sZ hE
          (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p)).val.app (op (W : Z.Opens)) ℓ) =
        ∑ I, a I • twistedGen n sZ W k z p I := by
  letI := MMP.Mori.sectionAlgebra sZ W
  have hCZ := forall_mem_weakChart_of_isRelativeSNC n sZ E hE
  let c := weakChartOfAdapted n sZ E W hk z hb hzero
  let f0 : Γ(Z, W) := ∏ i : Fin k, z (Fin.castLE hk i)
  have hWU : (W : Z.Opens) ⊓ LU E = Z.basicOpen f0 := weakChart_inf_LU sZ E c
  let WA : Z.affineOpens :=
    ⟨(W : Z.Opens) ⊓ LU E, MMP.DeRham.isAffineOpen_of_eq_basicOpen f0 hWU⟩
  letI := MMP.Mori.sectionAlgebra sZ ((W : Z.Opens) ⊓ LU E)
  letI : Algebra Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) :=
    (Z.presheaf.map (homOfLE (inf_le_left : (W : Z.Opens) ⊓ LU E ≤ W)).op).hom.toAlgebra
  haveI : IsScalarTower ℂ Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) :=
    MMP.Flips.ResolutionInputs.isScalarTower_section_res sZ inf_le_left
  obtain ⟨ω₀, hω₀, hℓ⟩ := (mem_relativeLogForms_suppIdeal_iff sZ E hE
    (exists_mem_support_genericPoint_eq E) c p ℓ.1).1 ℓ.2
  have hlog := (mem_relativeLogForms_iff_mem_logForms sZ E hE
    (exists_mem_support_genericPoint_eq E) c p ω₀).1 hω₀
  obtain ⟨bL, hbL, hcoord⟩ := exists_basis_inf_LU_of_weakChart sZ E c
  let P : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hk)
  have hf0 : IsUnit (algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) f0) := by
    have h1 := (Z.toRingedSpace.isUnit_res_basicOpen f0).map
      (Z.presheaf.map (homOfLE hWU.le).op).hom
    convert h1 using 1
    exact (congrArg (fun φ => (Z.presheaf.map φ).hom f0) (Subsingleton.elim _ _)).trans
      (congrArg (fun φ => φ.hom f0) (Z.presheaf.map_comp (homOfLE (Z.basicOpen_le f0)).op
        (homOfLE hWU.le).op))
  have hP : ∀ j ∈ P, IsUnit (algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) (z j)) := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun i => z (Fin.castLE hk i))
      (Finset.mem_univ i))) hf0
  have hu₁ : ∀ i : Fin k, ∃ j ∈ P, z j = z (Fin.castLE hk i) :=
    fun i => ⟨_, Finset.mem_map_of_mem _ (Finset.mem_univ i), rfl⟩
  obtain ⟨cc, hcc⟩ := MMP.DeRham.exists_eq_sum_logBasis hP hbL hu₁ hcoord _ hlog
  refine ⟨cc, ?_⟩
  -- compare after restricting to the complement of `E`, where forms are determined
  let y := (logToForms sZ ((isLocalSectionRel_twisted sZ hE hCZ) p)).val.app (op (W : Z.Opens)) ℓ
  have hy : ((resForms sZ E).app (p : ℤ)).val.app (op (W : Z.Opens)) y = ℓ.1 :=
    resForms_logToForms sZ ((isLocalSectionRel_twisted sZ hE hCZ) p) W ℓ
  have hamb := ambientFormsEquiv_resForms_app sZ E (W : Z.Opens) p
  have hrestr : ∀ t : Γ(sZ.relativeDifferentialForms (p : ℤ), (W : Z.Opens)),
      MMP.DeRham.formsAlgEquiv sZ p WA ((sZ.relativeDifferentialForms (p : ℤ)).presheaf.map
        (homOfLE (inf_le_left : (W : Z.Opens) ⊓ LU E ≤ W)).op t) =
      KaehlerDifferential.mapExteriorPower ℂ Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) p
        (MMP.DeRham.formsAlgEquiv sZ p W t) := fun t =>
    MMP.DeRham.formsAlgEquiv_restrict sZ p (W := W) (W' := WA) inf_le_left t
  -- the restriction of `y` is `f₀` times the logarithmic form `ω₀`
  have hL : KaehlerDifferential.mapExteriorPower ℂ Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) p
      (MMP.DeRham.formsAlgEquiv sZ p W y) =
      algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) f0 •
        MMP.DeRham.formsAlgEquiv sZ p WA (ambientFormsEquiv sZ (LU E) p W ω₀) := by
    refine (hrestr y).symm.trans ?_
    refine (congrArg (MMP.DeRham.formsAlgEquiv sZ p WA) (hamb y).symm).trans ?_
    refine (congrArg (fun t => MMP.DeRham.formsAlgEquiv sZ p WA
      (ambientFormsEquiv sZ (LU E) p W t)) (hy.trans hℓ)).trans ?_
    refine (congrArg (MMP.DeRham.formsAlgEquiv sZ p WA) (ambientFormsEquiv_smul sZ (LU E) p W
      _ ω₀)).trans ?_
    refine (map_smul (MMP.DeRham.formsAlgEquiv sZ p WA) _ _).trans ?_
    exact congrArg (· • _) (ambientRingHom_app (LU E) W f0)
  -- the restriction of the combination of the `τ_I`
  have hR : KaehlerDifferential.mapExteriorPower ℂ Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) p
      (∑ I, cc I • twistedGen n sZ W k z p I) =
      ∑ I, algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) (cc I) •
        (algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E)
          (∏ j ∈ (I : Finset (Fin n))ᶜ, if (j : ℕ) < k then z j else 1) •
          exteriorPower.ιMulti Γ(Z, (W : Z.Opens) ⊓ LU E) p fun a => KaehlerDifferential.D ℂ Γ(Z, (W : Z.Opens) ⊓ LU E)
            (algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) (z (Set.powersetCard.ofFinEmbEquiv.symm I a)))) :=
    mapExteriorPower_sum_smul_smul_ιMulti cc
      (fun I => ∏ j ∈ (I : Finset (Fin n))ᶜ, if (j : ℕ) < k then z j else 1)
      (fun I a => z (Set.powersetCard.ofFinEmbEquiv.symm I a))
  -- the logarithmic basis forms, multiplied by `f₀`, are the restrictions of the `τ_I`
  have hPmem : ∀ j : Fin n, j ∈ P ↔ (j : ℕ) < k := fun j => by
    simp only [P, Finset.mem_map, Finset.mem_univ, true_and, Fin.castLEEmb_apply]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ i.2, fun h => ⟨⟨j, h⟩, rfl⟩⟩
  have hf0' : algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) f0 =
      ∏ j ∈ P, algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) (z j) := by
    simp only [f0, map_prod, P, Finset.prod_map, Fin.castLEEmb_apply]
  have hterm : ∀ I : Set.powersetCard (Fin n) p,
      algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) f0 • (MMP.DeRham.logBasis bL hP).exteriorPower p I =
        algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E)
          (∏ j ∈ (I : Finset (Fin n))ᶜ, if (j : ℕ) < k then z j else 1) •
          exteriorPower.ιMulti Γ(Z, (W : Z.Opens) ⊓ LU E) p fun a => KaehlerDifferential.D ℂ Γ(Z, (W : Z.Opens) ⊓ LU E)
            (algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) (z (Set.powersetCard.ofFinEmbEquiv.symm I a))) :=
    fun I => (congrArg (· • (MMP.DeRham.logBasis bL hP).exteriorPower p I) hf0').trans
      (prod_smul_logBasis_exteriorPower n hP hbL hPmem I)
  have hLsum : algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) f0 •
      MMP.DeRham.formsAlgEquiv sZ p WA (ambientFormsEquiv sZ (LU E) p W ω₀) =
      ∑ I, algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) (cc I) •
        (algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E)
          (∏ j ∈ (I : Finset (Fin n))ᶜ, if (j : ℕ) < k then z j else 1) •
          exteriorPower.ιMulti Γ(Z, (W : Z.Opens) ⊓ LU E) p fun a => KaehlerDifferential.D ℂ Γ(Z, (W : Z.Opens) ⊓ LU E)
            (algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) (z (Set.powersetCard.ofFinEmbEquiv.symm I a)))) :=
    smul_eq_sum_smul_of_eq hcc hterm
  have key := hL.trans (hLsum.trans hR.symm)
  -- conclude by injectivity of restriction to the complement of `E`
  have hres : ((resForms sZ E).app (p : ℤ)).val.app (op (W : Z.Opens)) y =
      ((resForms sZ E).app (p : ℤ)).val.app (op (W : Z.Opens))
        ((MMP.DeRham.formsAlgEquiv sZ p W).symm (∑ I, cc I • twistedGen n sZ W k z p I)) := by
    apply (ambientFormsEquiv sZ (LU E) p W).injective
    refine (hamb y).trans (Eq.trans ?_ (hamb _).symm)
    apply (MMP.DeRham.formsAlgEquiv sZ p WA).injective
    refine (hrestr y).trans (Eq.trans ?_ (hrestr _).symm)
    exact key.trans (congrArg (KaehlerDifferential.mapExteriorPower ℂ Γ(Z, W)
      Γ(Z, (W : Z.Opens) ⊓ LU E) p) (LinearEquiv.apply_symm_apply _ _).symm)
  have hyy := resForms_app_injective sZ hE hCZ p W hres
  exact (congrArg (MMP.DeRham.formsAlgEquiv sZ p W) hyy).trans (LinearEquiv.apply_symm_apply _ _)

/-- Base change of the Kähler forms `c • dv₁ ∧ ⋯ ∧ dv_p` along an algebra map `B → L`. -/
private theorem mapExteriorPower_smul_ιMulti_D {B L : Type} [CommRing B] [CommRing L] [Algebra ℂ B]
    [Algebra ℂ L] [Algebra B L] [IsScalarTower ℂ B L] (p : ℕ) (c : B) (v : Fin p → B) :
    KaehlerDifferential.mapExteriorPower ℂ B L p
        (c • exteriorPower.ιMulti B p fun a => KaehlerDifferential.D ℂ B (v a)) =
      algebraMap B L c • exteriorPower.ιMulti L p fun a =>
        KaehlerDifferential.D ℂ L (algebraMap B L (v a)) := by
  rw [map_smul, algebraMap_smul, KaehlerDifferential.mapExteriorPower_ιMulti]
  simp only [KaehlerDifferential.map_D]

/-- **Poles times a logarithmic wedge**: multiplying the wedge `ε_I` of the logarithmic basis by
the product of the poles gives `(∏_{j ∉ I, j < k} z_j) dz_I`. -/
private theorem smul_logBasis_exteriorPower_eq_castLE {B L : Type} [CommRing B] [CommRing L]
    [Algebra ℂ L] [Algebra B L] {k : ℕ} (hk : k ≤ n) (z : Fin n → B)
    {bL : Module.Basis (Fin n) L Ω[L⁄ℂ]}
    (hbL : ∀ i, bL i = KaehlerDifferential.D ℂ L (algebraMap B L (z i)))
    (hP : ∀ j ∈ Finset.univ.map (Fin.castLEEmb hk), IsUnit (algebraMap B L (z j)))
    (p : ℕ) (I : Set.powersetCard (Fin n) p) :
    algebraMap B L (∏ i : Fin k, z (Fin.castLE hk i)) •
        (MMP.DeRham.logBasis bL hP).exteriorPower p I =
      algebraMap B L (∏ j ∈ (I : Finset (Fin n))ᶜ, if (j : ℕ) < k then z j else 1) •
        exteriorPower.ιMulti L p fun a =>
          KaehlerDifferential.D ℂ L
            (algebraMap B L (z (Set.powersetCard.ofFinEmbEquiv.symm I a))) := by
  have hPmem : ∀ j : Fin n, j ∈ Finset.univ.map (Fin.castLEEmb hk) ↔ (j : ℕ) < k := fun j => by
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.castLEEmb_apply]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ i.2, fun h => ⟨⟨j, h⟩, rfl⟩⟩
  rw [show algebraMap B L (∏ i : Fin k, z (Fin.castLE hk i)) =
      ∏ j ∈ Finset.univ.map (Fin.castLEEmb hk), algebraMap B L (z j) by
    simp only [map_prod, Finset.prod_map, Fin.castLEEmb_apply]]
  exact prod_smul_logBasis_exteriorPower n hP hbL hPmem I

/-- Membership transported along an equation of elements. -/
private theorem mem_of_eq_of_mem_of_eq {M S : Type*} [SetLike S M] {s : S} {x y : M}
    (h : x = y) (hy : y ∈ s) : x ∈ s := h ▸ hy

set_option maxRecDepth 40000 in
include hE in
/-- **Off `E`, each `τ_I` is `f₀` times a logarithmic form**, `f₀ = ∏_{j < k} z_j` the product of
the coordinates cutting out `E` on an adapted chart. -/
private theorem exists_mem_relativeLogForms_resForms_twistedGen_eq (W : Z.affineOpens) {k : ℕ}
    (hk : k ≤ n) (z : Fin n → Γ(Z, W))
    (hb : letI := MMP.Mori.sectionAlgebra sZ W
      ∃ b : Module.Basis (Fin n) Γ(Z, W) Ω[Γ(Z, W)⁄ℂ],
        ∀ i, b i = KaehlerDifferential.D ℂ Γ(Z, W) (z i))
    (hzero : ∀ w ∈ (W : Z.Opens), (∃ D ∈ E.support, w ∈ D.support) ↔
      w ∉ Z.basicOpen (∏ i : Fin k, z (Fin.castLE hk i))) (p : ℕ)
    (I : Set.powersetCard (Fin n) p) :
    letI := MMP.Mori.sectionAlgebra sZ W
    ∃ ω₀ : Γ(((LU E).ι ≫ sZ).relativeDifferentialForms (p : ℤ), (LU E).ι ⁻¹ᵁ (W : Z.Opens)),
      ω₀ ∈ relativeLogForms n sZ E hE ⊤ p W ∧
      ((resForms sZ E).app (p : ℤ)).val.app (op (W : Z.Opens))
          ((MMP.DeRham.formsAlgEquiv sZ p W).symm (twistedGen n sZ W k z p I)) =
        ((LU E).ι.app W).hom (∏ i : Fin k, z (Fin.castLE hk i)) • ω₀ := by
  letI := MMP.Mori.sectionAlgebra sZ W
  let c := weakChartOfAdapted n sZ E W hk z hb hzero
  let f0 : Γ(Z, W) := ∏ i : Fin k, z (Fin.castLE hk i)
  have hWU : (W : Z.Opens) ⊓ LU E = Z.basicOpen f0 := weakChart_inf_LU sZ E c
  let WA : Z.affineOpens :=
    ⟨(W : Z.Opens) ⊓ LU E, MMP.DeRham.isAffineOpen_of_eq_basicOpen f0 hWU⟩
  letI := MMP.Mori.sectionAlgebra sZ ((W : Z.Opens) ⊓ LU E)
  letI : Algebra Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) :=
    (Z.presheaf.map (homOfLE (inf_le_left : (W : Z.Opens) ⊓ LU E ≤ W)).op).hom.toAlgebra
  haveI : IsScalarTower ℂ Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) :=
    MMP.Flips.ResolutionInputs.isScalarTower_section_res sZ inf_le_left
  obtain ⟨bL, hbL, -⟩ := exists_basis_inf_LU_of_weakChart sZ E c
  let P : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hk)
  have hf0 : IsUnit (algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) f0) := by
    have h1 := (Z.toRingedSpace.isUnit_res_basicOpen f0).map
      (Z.presheaf.map (homOfLE hWU.le).op).hom
    convert h1 using 1
    exact (congrArg (fun φ => (Z.presheaf.map φ).hom f0) (Subsingleton.elim _ _)).trans
      (congrArg (fun φ => φ.hom f0) (Z.presheaf.map_comp (homOfLE (Z.basicOpen_le f0)).op
        (homOfLE hWU.le).op))
  have hP : ∀ j ∈ P, IsUnit (algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) (z j)) := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun i => z (Fin.castLE hk i))
      (Finset.mem_univ i))) hf0
  have hu₂ : ∀ j ∈ P, ∃ i : Fin k, z (Fin.castLE hk i) = z j := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
    exact ⟨i, rfl⟩
  have hamb : ∀ t : Γ(sZ.relativeDifferentialForms (p : ℤ), (W : Z.Opens)),
      ambientFormsEquiv sZ (LU E) p W
        (((resForms sZ E).app (p : ℤ)).val.app (op (W : Z.Opens)) t) =
      (sZ.relativeDifferentialForms (p : ℤ)).presheaf.map
        (homOfLE (inf_le_left : (W : Z.Opens) ⊓ LU E ≤ W)).op t :=
    ambientFormsEquiv_resForms_app sZ E (W : Z.Opens) p
  have hrestr : ∀ t : Γ(sZ.relativeDifferentialForms (p : ℤ), (W : Z.Opens)),
      MMP.DeRham.formsAlgEquiv sZ p WA ((sZ.relativeDifferentialForms (p : ℤ)).presheaf.map
        (homOfLE (inf_le_left : (W : Z.Opens) ⊓ LU E ≤ W)).op t) =
      KaehlerDifferential.mapExteriorPower ℂ Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) p
        (MMP.DeRham.formsAlgEquiv sZ p W t) := fun t =>
    MMP.DeRham.formsAlgEquiv_restrict sZ p (W := W) (W' := WA) inf_le_left t
  -- the logarithmic form `ω₀` with `τ_I = f₀ ω₀` off `E`
  let ω₀ := (ambientFormsEquiv sZ (LU E) p W).symm
    ((MMP.DeRham.formsAlgEquiv sZ p WA).symm ((MMP.DeRham.logBasis bL hP).exteriorPower p I))
  have hω₀ : MMP.DeRham.formsAlgEquiv sZ p WA (ambientFormsEquiv sZ (LU E) p W ω₀) =
      (MMP.DeRham.logBasis bL hP).exteriorPower p I :=
    (congrArg (MMP.DeRham.formsAlgEquiv sZ p WA) (AddEquiv.apply_symm_apply _ _)).trans
      (LinearEquiv.apply_symm_apply _ _)
  have h0 : ω₀ ∈ relativeLogForms n sZ E hE ⊤ p W :=
    (mem_relativeLogForms_iff_mem_logForms sZ E hE
      (exists_mem_support_genericPoint_eq E) c p ω₀).2
      (mem_of_eq_of_mem_of_eq (congrArg Subtype.val hω₀)
        (MMP.DeRham.coe_logBasis_exteriorPower_mem_logForms hP hbL hu₂ I))
  have hmapτ : KaehlerDifferential.mapExteriorPower ℂ Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) p
      (twistedGen n sZ W k z p I) =
      algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E)
          (∏ j ∈ (I : Finset (Fin n))ᶜ, if (j : ℕ) < k then z j else 1) •
          exteriorPower.ιMulti Γ(Z, (W : Z.Opens) ⊓ LU E) p fun a =>
            KaehlerDifferential.D ℂ Γ(Z, (W : Z.Opens) ⊓ LU E)
              (algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E)
                (z (Set.powersetCard.ofFinEmbEquiv.symm I a))) := by
    rw [twistedGen]
    exact mapExteriorPower_smul_ιMulti_D p _ _
  refine ⟨ω₀, h0, ?_⟩
  apply (ambientFormsEquiv sZ (LU E) p W).injective
  refine (hamb _).trans ?_
  refine Eq.trans ?_ (ambientFormsEquiv_smul sZ (LU E) p W _ ω₀).symm
  rw [ambientRingHom_app]
  apply (MMP.DeRham.formsAlgEquiv sZ p WA).injective
  refine (hrestr _).trans ?_
  refine (congrArg (KaehlerDifferential.mapExteriorPower ℂ Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) p)
    (LinearEquiv.apply_symm_apply _ _)).trans ?_
  refine hmapτ.trans ?_
  refine (smul_logBasis_exteriorPower_eq_castLE n hk z hbL hP p I).symm.trans ?_
  refine Eq.trans ?_ (map_smul (MMP.DeRham.formsAlgEquiv sZ p WA) _ _).symm
  exact congrArg (algebraMap Γ(Z, W) Γ(Z, (W : Z.Opens) ⊓ LU E) f0 • ·) hω₀.symm

set_option maxRecDepth 40000 in
include hE in
/-- **The `τ_I` are twisted forms**: each is the regular extension of a section of
`Ω^p(log E)(-E)` on an adapted chart. -/
private theorem exists_formsAlgEquiv_logToForms_eq_twistedGen (W : Z.affineOpens) {k : ℕ}
    (hk : k ≤ n) (z : Fin n → Γ(Z, W))
    (hb : letI := MMP.Mori.sectionAlgebra sZ W
      ∃ b : Module.Basis (Fin n) Γ(Z, W) Ω[Γ(Z, W)⁄ℂ],
        ∀ i, b i = KaehlerDifferential.D ℂ Γ(Z, W) (z i))
    (hzero : ∀ w ∈ (W : Z.Opens), (∃ D ∈ E.support, w ∈ D.support) ↔
      w ∉ Z.basicOpen (∏ i : Fin k, z (Fin.castLE hk i))) (p : ℕ)
    (I : Set.powersetCard (Fin n) p) :
    letI := MMP.Mori.sectionAlgebra sZ W
    ∃ ℓ : Γ(logModule n sZ E hE E.suppIdeal p, W),
      MMP.DeRham.formsAlgEquiv sZ p W ((logToForms sZ ((isLocalSectionRel_twisted sZ hE
          (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p)).val.app (op (W : Z.Opens)) ℓ) =
        twistedGen n sZ W k z p I := by
  letI := MMP.Mori.sectionAlgebra sZ W
  have hCZ := forall_mem_weakChart_of_isRelativeSNC n sZ E hE
  let c := weakChartOfAdapted n sZ E W hk z hb hzero
  obtain ⟨ω₀, h0, h1⟩ :=
    exists_mem_relativeLogForms_resForms_twistedGen_eq n sZ E hE W hk z hb hzero p I
  have hmem : ((resForms sZ E).app (p : ℤ)).val.app (op (W : Z.Opens))
      ((MMP.DeRham.formsAlgEquiv sZ p W).symm (twistedGen n sZ W k z p I)) ∈
        relativeLogForms n sZ E hE E.suppIdeal p W :=
    (mem_relativeLogForms_suppIdeal_iff sZ E hE (exists_mem_support_genericPoint_eq E) c p
      _).2 ⟨ω₀, h0, h1⟩
  refine ⟨⟨_, hmem⟩, ?_⟩
  have h2 := resForms_logToForms sZ ((isLocalSectionRel_twisted sZ hE hCZ) p) W ⟨_, hmem⟩
  have hyy' : (logToForms sZ ((isLocalSectionRel_twisted sZ hE
      (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p)).val.app (op (W : Z.Opens))
        ⟨_, hmem⟩ = (MMP.DeRham.formsAlgEquiv sZ p W).symm (twistedGen n sZ W k z p I) :=
    resForms_app_injective sZ hE hCZ p W h2
  rw [hyy', LinearEquiv.apply_symm_apply]

variable [IsLocallyNoetherian Z]

/-- The terms `𝒟_E^p` of the restriction complex, as `𝒪_Z`-modules. -/
private noncomputable abbrev cokZ (p : ℕ) : Z.Modules :=
  cokernelLogToForms sZ (isLocalSectionRel_twisted sZ hE
    (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p

/-- The underlying abelian sheaf of `𝒟_E^p` is that of `D^p`. -/
private noncomputable def toSheafCokZIso (p : ℕ) :
    (SheafOfModules.toSheaf _).obj (cokZ n sZ E hE p) ≅ (SheafOfModules.toSheaf _).obj (D.X p) :=
  eqToIso rfl ≪≫ (SheafOfModules.toSheaf _).mapIso (cokernelIso sZ i hi D q hiq hq
    (isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE))
    (resForms_app_injective sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p)

/-- The differential of the restriction complex on the abelian sheaves of the `𝒪_Z`-modules
`𝒟_E^p`. -/
private noncomputable def cokZd (p : ℕ) :
    (SheafOfModules.toSheaf _).obj (cokZ n sZ E hE p) ⟶
      (SheafOfModules.toSheaf _).obj (cokZ n sZ E hE (p + 1)) :=
  (toSheafCokZIso n sZ E hE i hi D q hiq hq p).hom ≫ (SheafOfModules.toSheaf _).map (D.d p (p + 1)) ≫
    (toSheafCokZIso n sZ E hE i hi D q hiq hq (p + 1)).inv

private theorem cokZd_comp (p : ℕ) :
    cokZd n sZ E hE i hi D q hiq hq p ≫ cokZd n sZ E hE i hi D q hiq hq (p + 1) = 0 := by
  unfold cokZd
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, D.d_comp_d, Functor.map_zero, zero_comp, comp_zero]

omit [IsLocallyNoetherian Z] in
/-- The constants `ℂ ⟶ 𝒪_Z(U)` come from the inverse image `sZ⁻¹𝒪` of the base. -/
private theorem exists_inverseImageStructureMap_eq_baseRingHom (U : Z.Opens) (c : ℂ) :
    ∃ t : ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (.of ℂ)).sheaf).obj.obj
        (op U),
      ((inverseImageStructureMap sZ).hom.app (op U)).hom t = MMP.Analytic.ComplexPoints.baseRingHom sZ U c := by
  refine ⟨(((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (.of ℂ)).sheaf).obj.map
    (homOfLE (le_top : U ≤ ⊤)).op).hom
      ((Scheme.Hom.inverseImageGlobalSections sZ).hom ((Scheme.ΓSpecIso (.of ℂ)).inv.hom c)), ?_⟩
  have h1 := ConcreteCategory.congr_hom
    ((inverseImageStructureMap sZ).hom.naturality (homOfLE (le_top : U ≤ ⊤)).op)
    ((Scheme.Hom.inverseImageGlobalSections sZ).hom ((Scheme.ΓSpecIso (.of ℂ)).inv.hom c))
  have h2 := ConcreteCategory.congr_hom
    (Scheme.Hom.inverseImageGlobalSections_comp_inverseImageStructureMap_app sZ)
    ((Scheme.ΓSpecIso (.of ℂ)).inv.hom c)
  refine h1.trans ?_
  change (Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
    (((inverseImageStructureMap sZ).hom.app (op ⊤)).hom
      ((Scheme.Hom.inverseImageGlobalSections sZ).hom ((Scheme.ΓSpecIso (.of ℂ)).inv.hom c))) = _
  erw [h2]
  rfl

omit [IsLocallyNoetherian Z] in
/-- A morphism of `sZ⁻¹𝒪`-modules between `𝒪_Z`-modules is `ℂ`-linear on sections. -/
private theorem app_baseRingHom_smul {M N : Z.Modules}
    (g : (pushforward (toInverseImageBase sZ)).obj M ⟶ (pushforward (toInverseImageBase sZ)).obj N)
    (U : Z.Opens) (c : ℂ) (s : M.val.obj (op U)) :
    g.val.app (op U) ((show Z.ringCatSheaf.obj.obj (op U) from MMP.Analytic.ComplexPoints.baseRingHom sZ U c) • s) =
      (show Z.ringCatSheaf.obj.obj (op U) from MMP.Analytic.ComplexPoints.baseRingHom sZ U c) •
        (show N.val.obj (op U) from g.val.app (op U) s) := by
  obtain ⟨t, ht⟩ := exists_inverseImageStructureMap_eq_baseRingHom sZ U c
  rw [← ht]
  exact (g.val.app (op U)).hom.map_smul t s

omit [IsLocallyNoetherian Z] in
/-- The quotient map `Ω^• ⟶ 𝒟_E^•`, on underlying abelian sheaves, intertwines the de Rham
differential with the differential of the restriction complex. -/
private theorem toSheaf_π_comp_cokZd [IsLocallyNoetherian Z] (k : ℕ) :
    (SheafOfModules.toSheaf _).map (cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
        (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) k))) ≫
        cokZd n sZ E hE i hi D q hiq hq k =
      MMP.DeRhamBetti.DRCmp.dZ sZ k ≫ (SheafOfModules.toSheaf _).map (cokernel.π (logToForms sZ
        ((isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE))
          (k + 1)))) := by
  have hR := isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)
  have hinj := resForms_app_injective sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)
  have h1 := map_π_comp_cokernelIso_hom sZ i hi D q hiq hq hR hinj k
  have h2 := map_π_comp_cokernelIso_hom sZ i hi D q hiq hq hR hinj (k + 1)
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
  ext s
  have e1 := fun x => ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app U) h1) x
  have e2 := fun x => ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app U) h2) x
  have e3 := fun x => ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.val.app U) (q.comm k (k + 1))) x
  have e4 := fun x => ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app U)
    (cokernelIso sZ i hi D q hiq hq hR hinj (k + 1)).hom_inv_id) x
  change (cokernelIso sZ i hi D q hiq hq hR hinj (k + 1)).inv.val.app U ((D.d k (k + 1)).val.app U
      ((cokernelIso sZ i hi D q hiq hq hR hinj k).hom.val.app U
        ((cokernel.π (logToForms sZ (hR k))).val.app U s))) =
    (cokernel.π (logToForms sZ (hR (k + 1)))).val.app U
      ((MMP.DeRhamBetti.DRCmp.dZ sZ k).hom.app U s)
  erw [MMP.DeRhamBetti.DRCmp.dZ_app sZ k U.unop s, e1]
  refine (congrArg ((cokernelIso sZ i hi D q hiq hq hR hinj (k + 1)).inv.val.app U) (e3 s)).trans ?_
  refine (congrArg ((cokernelIso sZ i hi D q hiq hq hR hinj (k + 1)).inv.val.app U)
    (e2 (((Scheme.Hom.deRhamComplex sZ).d k (k + 1)).val.app U s)).symm).trans ?_
  exact e4 _

/-- The terms of the restriction complex indexed by `ℤ`, zero in negative degrees. -/
private noncomputable abbrev cokZF : ℤ → Z.Modules
  | Int.ofNat p => cokZ n sZ E hE p
  | Int.negSucc _ => 0

/-- The differentials of the restriction complex indexed by `ℤ`. -/
private noncomputable def cokZδ : ∀ p : ℤ, (SheafOfModules.toSheaf _).obj (cokZF n sZ E hE p) ⟶
    (SheafOfModules.toSheaf _).obj (cokZF n sZ E hE (p + 1))
  | Int.ofNat p => cokZd n sZ E hE i hi D q hiq hq p
  | Int.negSucc _ => 0

private theorem cokZδ_comp : ∀ p : ℤ,
    cokZδ n sZ E hE i hi D q hiq hq p ≫ cokZδ n sZ E hE i hi D q hiq hq (p + 1) = 0
  | Int.ofNat p => cokZd_comp n sZ E hE i hi D q hiq hq p
  | Int.negSucc _ => zero_comp

/-- The differentials of the restriction complex are `ℂ`-linear. -/
private theorem cokZδ_smul : ∀ (p : ℤ) (U : Z.Opens) (c : ℂ)
    (s : (cokZF n sZ E hE p).val.obj (op U)),
    (cokZδ n sZ E hE i hi D q hiq hq p).hom.app (op U)
        ((show Z.ringCatSheaf.obj.obj (op U) from MMP.Analytic.ComplexPoints.baseRingHom sZ U c) • s) =
      (show Z.ringCatSheaf.obj.obj (op U) from MMP.Analytic.ComplexPoints.baseRingHom sZ U c) •
        (show (cokZF n sZ E hE (p + 1)).val.obj (op U) from
          (cokZδ n sZ E hE i hi D q hiq hq p).hom.app (op U) s)
  | Int.ofNat k, U, c, s =>
    app_baseRingHom_smul sZ
      ((cokernelIso sZ i hi D q hiq hq
          (isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE))
          (resForms_app_injective sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) k).hom ≫
        D.d k (k + 1) ≫
        (cokernelIso sZ i hi D q hiq hq
          (isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE))
          (resForms_app_injective sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE))
          (k + 1)).inv) U c s
  | Int.negSucc j, U, c, s => by
    have h0 : ∀ x, (cokZδ n sZ E hE i hi D q hiq hq (Int.negSucc j)).hom.app (op U) x = 0 :=
      fun _ => rfl
    refine (h0 _).trans ?_
    have h1 := h0 s
    change (0 : (cokZF n sZ E hE (Int.negSucc j + 1)).val.obj (op U)) =
      (show Z.ringCatSheaf.obj.obj (op U) from
        MMP.Analytic.ComplexPoints.baseRingHom sZ U c) •
        (show (cokZF n sZ E hE (Int.negSucc j + 1)).val.obj (op U) from
          (cokZδ n sZ E hE i hi D q hiq hq (Int.negSucc j)).hom.app (op U) s)
    rw [show (show (cokZF n sZ E hE (Int.negSucc j + 1)).val.obj (op U) from
          (cokZδ n sZ E hE i hi D q hiq hq (Int.negSucc j)).hom.app (op U) s) = 0 from h1]
    exact (smul_zero _).symm

/-- **The restriction complex as a complex of abelian sheaves on `Z`**, indexed by `ℤ`, in the form
taken by GAGA for hypercohomology. -/
private noncomputable abbrev cokZK : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} Z.carrier) ℤ :=
  CochainComplex.of (fun p => (SheafOfModules.toSheaf _).obj (cokZF n sZ E hE p))
    (cokZδ n sZ E hE i hi D q hiq hq) (cokZδ_comp n sZ E hE i hi D q hiq hq)

/-- The terms of the restriction complex are coherent. -/
private theorem isCoherent_cokZF : ∀ p : ℤ, Stacks.SheafOfModules.IsCoherent (cokZF n sZ E hE p)
  | Int.ofNat p => by
    haveI := isCoherent_cokernelLogToForms sZ (isLocalSectionRel_twisted sZ hE
      (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p
    exact AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent this
  | Int.negSucc _ => by
    haveI := Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
      (isZero_zero (Z.Modules))
    exact AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent this

/-- The restriction complex is bounded: its terms vanish in negative degrees and in degrees above
some `N`. -/
private theorem exists_isZero_cokZF [CompactSpace Z] : ∃ N : ℕ, ∀ p : ℤ, p < 0 ∨ (N : ℤ) < p →
    IsZero (cokZF n sZ E hE p) := by
  haveI : Smooth sZ := SmoothOfRelativeDimension.smooth n sZ
  obtain ⟨N, hN⟩ := AlgebraicGeometry.HodgeSpreadingOut.exists_isZero_relativeDifferentialForms sZ
  refine ⟨N, fun p hp => ?_⟩
  rcases p with p | p
  · have hp' : N < p := by
      simp only [Int.ofNat_eq_coe] at hp
      rcases hp with hp | hp <;> omega
    exact IsZero.of_epi (cokernel.π _) (hN p hp')
  · exact isZero_zero _

omit [IsLocallyNoetherian Z] in
open MMP.Analytic MMP.Analytic.Analytification in
/-- **The stalks of an analytified module are generated by the algebraic sections**: every germ of
`F^an` at a point `y` is a combination, with coefficients in the analytic local ring, of germs of
images of sections of `F` near `y`. -/
private theorem mem_span_germ_analytifyModuleUnit [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (F : Z.Modules) (y : ComplexPoints sZ) :
    letI : Module ((analytification sZ).presheaf.stalk y)
        ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ)
          ((analytifyModule sZ).obj F).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        ((analytifyModule sZ).obj F).val y
    ∀ t, t ∈ Submodule.span ((analytification sZ).presheaf.stalk y)
      (Set.range fun v : Σ V : {V : Z.Opens // y.toScheme ∈ V}, F.val.obj (op V.1) =>
        TopCat.Presheaf.germ ((analytifyModule sZ).obj F).val.presheaf
          ((Opens.map (toSchemeHom sZ)).obj v.1.1) y v.1.2
          ((analytifyModuleUnit sZ F).val.app (op v.1.1) v.2)) := by
  letI : Module ((analytification sZ).presheaf.stalk y)
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ)
        ((analytifyModule sZ).obj F).val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ((analytifyModule sZ).obj F).val y
  letI : Algebra (Z.presheaf.stalk y.toScheme) ((analytification sZ).presheaf.stalk y) :=
    ((analytificationHom sZ).hom.stalkMap y).hom.toAlgebra
  letI : Module (Z.presheaf.stalk y.toScheme)
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := Z.toTopCat) F.val.presheaf
        y.toScheme) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val _
  obtain ⟨e, he⟩ := (analytification_stalks sZ).2.2.1 F y
  intro t
  rw [← e.symm_apply_apply t]
  induction e t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul a m =>
    obtain ⟨V, hy, s, rfl⟩ := TopCat.Presheaf.germ_exist F.val.presheaf m
    have key := e.symm.map_smul a (e (TopCat.Presheaf.germ ((analytifyModule sZ).obj F).val.presheaf
      ((Opens.map (toSchemeHom sZ)).obj V) y hy ((analytifyModuleUnit sZ F).val.app (op V) s)))
    erw [e.symm_apply_apply, he V hy s] at key
    rw [← mul_one a, ← smul_eq_mul]
    erw [key]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨⟨⟨V, hy⟩, s⟩, rfl⟩)
  | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv

omit [IsLocallyNoetherian Z] in
open MMP.Analytic MMP.Analytic.Analytification in
/-- The germ of the analytification of `r • m` is the germ of `r` times that of `m`. -/
private theorem germ_analytifyModuleUnit_smul (F : Z.Modules) {V : Z.Opens} (y : ComplexPoints sZ)
    (hy : y.toScheme ∈ V) (r : Γ(Z, V)) (m : Γ(F, V)) :
    letI : Module ((analytification sZ).presheaf.stalk y)
        ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ)
          ((analytifyModule sZ).obj F).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        ((analytifyModule sZ).obj F).val y
    TopCat.Presheaf.germ ((analytifyModule sZ).obj F).val.presheaf
        ((Opens.map (toSchemeHom sZ)).obj V) y hy ((analytifyModuleUnit sZ F).val.app (op V) (r • m)) =
      ((analytificationHom sZ).hom.stalkMap y).hom (Z.presheaf.germ V y.toScheme hy r) •
        TopCat.Presheaf.germ ((analytifyModule sZ).obj F).val.presheaf
          ((Opens.map (toSchemeHom sZ)).obj V) y hy ((analytifyModuleUnit sZ F).val.app (op V) m) := by
  have h1 := ((analytifyModuleUnit sZ F).val.app (op V)).hom.map_smul r m
  erw [h1, PresheafOfModules.germ_smul]
  congr 1
  exact (PresheafedSpace.stalkMap_germ_apply (analytificationHom sZ).hom V y hy r).symm

omit [IsLocallyNoetherian Z] in
open MMP.Analytic MMP.Analytic.Analytification in
/-- The germ of the analytification of a section does not change under restriction. -/
private theorem germ_analytifyModuleUnit_res (F : Z.Modules) {V W : Z.Opens} (hWV : W ≤ V)
    (y : ComplexPoints sZ) (hy : y.toScheme ∈ W) (m : F.val.obj (op V)) :
    TopCat.Presheaf.germ ((analytifyModule sZ).obj F).val.presheaf
        ((Opens.map (toSchemeHom sZ)).obj W) y hy
        ((analytifyModuleUnit sZ F).val.app (op W) (F.presheaf.map (homOfLE hWV).op m)) =
      TopCat.Presheaf.germ ((analytifyModule sZ).obj F).val.presheaf
        ((Opens.map (toSchemeHom sZ)).obj V) y (hWV hy)
        ((analytifyModuleUnit sZ F).val.app (op V) m) := by
  have h := ConcreteCategory.congr_hom
    ((analytifyModuleUnit sZ F).val.naturality (homOfLE hWV).op) m
  erw [h]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

omit [IsLocallyNoetherian Z] in
open MMP.Analytic MMP.Analytic.Analytification in
/-- **The stalks of an analytified quasi-coherent module are generated by sections over an affine
open**: for an affine open `U` containing the point under `y`, every germ of `F^an` at `y` is a
combination of germs of images of sections of `F` over `U`. -/
private theorem mem_span_germ_analytifyModuleUnit_of_isAffineOpen [LocallyOfFiniteType sZ]
    [QuasiCompact sZ] (F : Z.Modules) [F.IsQuasicoherent] {U : Z.Opens} (hU : IsAffineOpen U)
    (y : ComplexPoints sZ) (hy : y.toScheme ∈ U) :
    letI : Module ((analytification sZ).presheaf.stalk y)
        ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ)
          ((analytifyModule sZ).obj F).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        ((analytifyModule sZ).obj F).val y
    ∀ t, t ∈ Submodule.span ((analytification sZ).presheaf.stalk y)
      (Set.range fun s : F.val.obj (op U) =>
        TopCat.Presheaf.germ ((analytifyModule sZ).obj F).val.presheaf
          ((Opens.map (toSchemeHom sZ)).obj U) y hy
          ((analytifyModuleUnit sZ F).val.app (op U) s)) := by
  letI : Module ((analytification sZ).presheaf.stalk y)
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ)
        ((analytifyModule sZ).obj F).val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ((analytifyModule sZ).obj F).val y
  intro t
  refine Submodule.span_le.2 ?_ (mem_span_germ_analytifyModuleUnit sZ F y t)
  rintro _ ⟨⟨⟨V, hyV⟩, sV⟩, rfl⟩
  letI := Stacks.ModuleStalkSpecialization.stalkModule F y.toScheme
  obtain ⟨s, c, hc, hcm⟩ := Stacks.ModuleStalkSpecialization.exists_germ_smul_eq_germ F hU hy
    (F.presheaf.germ V y.toScheme hyV sV)
  -- the relation `c • sV = s` holds on a neighbourhood `W` of the point
  have hUV : y.toScheme ∈ U ⊓ V := ⟨hy, hyV⟩
  have e1 : F.presheaf.germ (U ⊓ V) y.toScheme hUV
      ((Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op c : Γ(Z, U ⊓ V)) •
        (F.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV : Γ(F, U ⊓ V))) =
      F.presheaf.germ U y.toScheme hy s := by
    erw [Stacks.ModuleStalkSpecialization.germ_smul, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply]
    exact hcm
  obtain ⟨W, hyW, iW, iW', hW⟩ := TopCat.Presheaf.germ_eq F.presheaf y.toScheme _ _ _ _ e1
  have hWU : W ≤ U := iW'.le
  have hWV : W ≤ V := iW.le.trans inf_le_right
  have hres : (F.presheaf.map (homOfLE hWU).op s : Γ(F, W)) =
      (Z.presheaf.map (homOfLE hWU).op c : Γ(Z, W)) •
        (F.presheaf.map (homOfLE hWV).op sV : Γ(F, W)) := by
    refine hW.symm.trans ?_
    erw [Scheme.Modules.map_smul]
    congr 1
    · exact (ConcreteCategory.congr_hom (Z.presheaf.map_comp _ _) c).symm
    · exact (ConcreteCategory.congr_hom (F.presheaf.map_comp _ _) sV).symm
  -- the germ of `s` is a unit multiple of the germ of `sV`
  have hu : IsUnit (Z.presheaf.germ U y.toScheme hy c) := by
    letI : Algebra Γ(Z, U) (Z.presheaf.stalk y.toScheme) :=
      (Z.presheaf.germ U _ hy).hom.toAlgebra
    haveI := hU.isLocalization_stalk ⟨y.toScheme, hy⟩
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk y.toScheme)
      (hU.primeIdealOf ⟨y.toScheme, hy⟩).asIdeal c).mpr hc
  have hu' := hu.map ((analytificationHom sZ).hom.stalkMap y).hom
  have k1 := germ_analytifyModuleUnit_res sZ F hWU y hyW s
  have k3 := germ_analytifyModuleUnit_smul sZ F y hyW (Z.presheaf.map (homOfLE hWU).op c)
    (F.presheaf.map (homOfLE hWV).op sV)
  have k4 := germ_analytifyModuleUnit_res sZ F hWV y hyW sV
  have k5 : Z.presheaf.germ W y.toScheme hyW (Z.presheaf.map (homOfLE hWU).op c) =
      Z.presheaf.germ U y.toScheme hy c :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have key : TopCat.Presheaf.germ ((analytifyModule sZ).obj F).val.presheaf
      ((Opens.map (toSchemeHom sZ)).obj U) y hy ((analytifyModuleUnit sZ F).val.app (op U) s) =
      ((analytificationHom sZ).hom.stalkMap y).hom (Z.presheaf.germ U y.toScheme hy c) •
        TopCat.Presheaf.germ ((analytifyModule sZ).obj F).val.presheaf
          ((Opens.map (toSchemeHom sZ)).obj V) y hyV ((analytifyModuleUnit sZ F).val.app (op V) sV) := by
    refine k1.symm.trans ?_
    erw [hres, k3, k4, k5]
  obtain ⟨v, hv⟩ := hu'
  have : TopCat.Presheaf.germ ((analytifyModule sZ).obj F).val.presheaf
      ((Opens.map (toSchemeHom sZ)).obj V) y hyV ((analytifyModuleUnit sZ F).val.app (op V) sV) =
      (↑v⁻¹ : (analytification sZ).presheaf.stalk y) •
        TopCat.Presheaf.germ ((analytifyModule sZ).obj F).val.presheaf
          ((Opens.map (toSchemeHom sZ)).obj U) y hy ((analytifyModuleUnit sZ F).val.app (op U) s) := by
    erw [key, ← hv, smul_smul, Units.inv_mul, one_smul]
  have hmem := Submodule.smul_mem (Submodule.span ((analytification sZ).presheaf.stalk y)
    (Set.range fun s : F.val.obj (op U) =>
      TopCat.Presheaf.germ ((analytifyModule sZ).obj F).val.presheaf
        ((Opens.map (toSchemeHom sZ)).obj U) y hy
        ((analytifyModuleUnit sZ F).val.app (op U) s))) (↑v⁻¹ : (analytification sZ).presheaf.stalk y)
    (Submodule.subset_span ⟨s, rfl⟩)
  rw [← this] at hmem
  exact hmem

end EdgeMap

/-! ### The edge map of the restriction complex on abelian sheaves -/

section AlgebraicEdge

open MMP.Mori.Divisor.LogSpreadingProof.G1 Stacks.DeRhamDirectImage MMP.Analytic
open StacksDraft.StupidTruncation
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The projection of a cochain complex with vanishing differential `d^{-1,0}` onto its
degree-zero term. -/
private noncomputable def toSingleZero {V : Type*} [Category V] [HasZeroMorphisms V]
    [HasZeroObject V] (K : CochainComplex V ℤ) (hK : K.d (-1) 0 = 0) :
    K ⟶ (HomologicalComplex.single V (ComplexShape.up ℤ) 0).obj (K.X 0) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun i hi => by
    obtain rfl : i = -1 := by change i + 1 = 0 at hi; omega
    rw [hK, zero_comp])

private theorem toSingleZero_f {V : Type*} [Category V] [HasZeroMorphisms V]
    [HasZeroObject V] (K : CochainComplex V ℤ) (hK : K.d (-1) 0 = 0) :
    (toSingleZero K hK).f 0 = 𝟙 _ ≫ (HomologicalComplex.singleObjXSelf _ 0 _).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

variable (n : ℕ) {Z : Scheme.{0}} (sZ : Z ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n sZ] (hZ : IsProjective sZ)
  (E : MMP.Mori.Divisor Z) (hE : E.IsRelativeSNC n sZ)
  (i : relativeLogDeRhamComplex n sZ E hE E.suppIdeal ⟶ Scheme.Hom.deRhamComplex sZ)
  (hi : ∀ (p : ℕ) (W : Z.Opensᵒᵖ)
    (w : ((relativeLogDeRhamComplex n sZ E hE E.suppIdeal).X p).val.obj W),
    ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι E.supp.compl) sZ).f p).val.app
      W ((i.f p).val.app W w) = w.1)
  (D : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
  (q : Scheme.Hom.deRhamComplex sZ ⟶ D) (hiq : i ≫ q = 0)
  (hq : IsColimit (CokernelCofork.ofπ q hiq))
  [IsLocallyNoetherian Z]

/-- The brutal truncation `σ^{≥0}` of the extension of `D` by zero to `ℤ`. -/
private noncomputable abbrev σD : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℤ :=
  (D.extend ComplexShape.embeddingUpNat).stupidTrunc (ComplexShape.embeddingUpIntGE 0)

/-- The terms of `σ^{≥0}` of the extension of `D`, in nonnegative degrees. -/
private noncomputable def σDXIso (k : ℕ) : (σD sZ D).X (k : ℤ) ≅ D.X k :=
  stupidTruncGEXIso _ 0 k (by omega) ≪≫ D.extendXIso ComplexShape.embeddingUpNat rfl

private theorem σD_d (k : ℕ) : (σD sZ D).d k (k + 1) =
    (σDXIso sZ D k).hom ≫ D.d k (k + 1) ≫ (σDXIso sZ D (k + 1)).inv := by
  rw [HomologicalComplex.stupidTrunc_d_eq _ _ (i' := (k : ℤ)) (j' := (k : ℤ) + 1)
      (i := ((k : ℤ) - 0).toNat) (j := (((k + 1 : ℕ) : ℤ) - 0).toNat)
      (by change 0 + _ = _; omega) (by change 0 + _ = _; omega),
    HomologicalComplex.extend_d_eq D ComplexShape.embeddingUpNat (i' := (k : ℤ))
      (j' := (k : ℤ) + 1) (i := k) (j := k + 1) (by simp) (by simp)]
  simp only [σDXIso, Iso.trans_hom, Iso.trans_inv, Category.assoc]

/-- The comparison of `𝒟_E^•` with `σ^{≥0}D`, termwise. -/
private noncomputable def cokZKXIso : ∀ p : ℤ, (cokZK n sZ E hE i hi D q hiq hq).X p ≅
    (SheafOfModules.toSheaf _).obj ((σD sZ D).X p)
  | Int.ofNat k => toSheafCokZIso n sZ E hE i hi D q hiq hq k ≪≫
      (SheafOfModules.toSheaf _).mapIso (σDXIso sZ D k).symm
  | Int.negSucc k => by
    haveI := Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits _ Z.ringCatSheaf
    exact IsZero.iso ((SheafOfModules.toSheaf _).map_isZero (isZero_zero _))
      ((SheafOfModules.toSheaf _).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE (σD sZ D) 0 _ (by omega)))

/-- **`𝒟_E^•` is `σ^{≥0}D` on underlying abelian sheaves.** -/
private noncomputable def cokZKIso : cokZK n sZ E hE i hi D q hiq hq ≅
    ((SheafOfModules.toSheaf _).mapHomologicalComplex _).obj (σD sZ D) :=
  HomologicalComplex.Hom.isoOfComponents (cokZKXIso n sZ E hE i hi D q hiq hq) (by
    rintro p _ rfl
    cases p with
    | ofNat k =>
      have e1 : (cokZK n sZ E hE i hi D q hiq hq).d (Int.ofNat k) (Int.ofNat k + 1) =
          cokZd n sZ E hE i hi D q hiq hq k :=
        CochainComplex.of_d _ (cokZδ n sZ E hE i hi D q hiq hq) (Int.ofNat k)
      have e2 : (((SheafOfModules.toSheaf _).mapHomologicalComplex _).obj (σD sZ D)).d
          (Int.ofNat k) (Int.ofNat k + 1) = (SheafOfModules.toSheaf _).map ((σD sZ D).d k (k + 1)) :=
        rfl
      rw [e1, e2, σD_d, cokZd]
      change (toSheafCokZIso n sZ E hE i hi D q hiq hq k ≪≫
          (SheafOfModules.toSheaf _).mapIso (σDXIso sZ D k).symm).hom ≫ _ = _ ≫
        (toSheafCokZIso n sZ E hE i hi D q hiq hq (k + 1) ≪≫
          (SheafOfModules.toSheaf _).mapIso (σDXIso sZ D (k + 1)).symm).hom
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
        Category.assoc, Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc]
    | negSucc k =>
      haveI := Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits _ Z.ringCatSheaf
      exact IsZero.eq_of_src ((SheafOfModules.toSheaf _).map_isZero (isZero_zero _)) _ _)

private theorem cokZKIso_hom_f (p : ℤ) :
    (cokZKIso n sZ E hE i hi D q hiq hq).hom.f p = (cokZKXIso n sZ E hE i hi D q hiq hq p).hom :=
  rfl

private theorem cokZK_d_neg_one : (cokZK n sZ E hE i hi D q hiq hq).d (-1) 0 = 0 :=
  (CochainComplex.of_d _ (cokZδ n sZ E hE i hi D q hiq hq) (-1)).trans rfl

include hZ in
/-- **The edge map of `𝒟_E^•` on abelian sheaves is onto**: the projection of `𝒟_E^•` onto its
degree-zero term is surjective on hypercohomology. -/
private theorem surjective_hypercohomology_map_toSingleZero_cokZK (m : ℕ) :
    Function.Surjective ((hypercohomology _ m).map
      (toSingleZero _ (cokZK_d_neg_one n sZ E hE i hi D q hiq hq))).hom := by
  have hder := surjective_hypFunctor_map_truncGEπ0_cokernel n sZ hZ E hE i hi D q hiq hq m
  have hbr := surjective_hypercohomology_map_toSheaf_of_surjective (inverseImageBase sZ)
    (MMP.LcBpf.truncGEπ0 sZ (D.extend ComplexShape.embeddingUpNat)) m hder
  let v : (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{0} Z.carrier)
      (ComplexShape.up ℤ) 0).obj ((cokZK n sZ E hE i hi D q hiq hq).X 0) ≅
      ((SheafOfModules.toSheaf _).mapHomologicalComplex _).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          ((D.extend ComplexShape.embeddingUpNat).X 0)) :=
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        (cokZKXIso n sZ E hE i hi D q hiq hq 0 ≪≫
          (SheafOfModules.toSheaf _).mapIso (stupidTruncGEXIso _ 0 0 le_rfl)) ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex (SheafOfModules.toSheaf _)
        (ComplexShape.up ℤ) 0).app _).symm
  have w : (cokZKIso n sZ E hE i hi D q hiq hq).hom ≫
      ((SheafOfModules.toSheaf _).mapHomologicalComplex _).map
        (MMP.LcBpf.truncGEπ0 sZ (D.extend ComplexShape.embeddingUpNat)).hom ≫ v.inv =
      toSingleZero _ (cokZK_d_neg_one n sZ E hE i hi D q hiq hq) := by
    apply HomologicalComplex.to_single_hom_ext
    erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, cokZKIso_hom_f,
      Functor.mapHomologicalComplex_map_f]
    erw [ObjectProperty.homMk_hom, stupidTruncGEπ_f]
    simp only [v]
    erw [Iso.trans_inv, HomologicalComplex.comp_f, Iso.symm_inv,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Functor.mapIso_inv,
      HomologicalComplex.single_map_f_self, toSingleZero_f]
    exact iso_chain_comp_eq (cokZKXIso n sZ E hE i hi D q hiq hq 0)
      ((SheafOfModules.toSheaf _).mapIso (stupidTruncGEXIso _ 0 0 le_rfl))
      ((SheafOfModules.toSheaf _).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm)
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm _
  have hsq : (hypercohomology Z.carrier m).map (((SheafOfModules.toSheaf _).mapHomologicalComplex
        _).map (MMP.LcBpf.truncGEπ0 sZ (D.extend ComplexShape.embeddingUpNat)).hom) ≫
        (hypercohomology Z.carrier m).map v.inv =
      (hypercohomology Z.carrier m).map (cokZKIso n sZ E hE i hi D q hiq hq).inv ≫
        (hypercohomology Z.carrier m).map
          (toSingleZero _ (cokZK_d_neg_one n sZ E hE i hi D q hiq hq)) :=
    ((hypercohomology Z.carrier m).map_comp _ _).symm.trans
      ((congrArg (hypercohomology Z.carrier m).map
        (by rw [← w]; exact (Iso.inv_hom_id_assoc _ _).symm)).trans
        ((hypercohomology Z.carrier m).map_comp _ _))
  exact surjective_of_comm _ _
    ((hypercohomology _ m).mapIso (cokZKIso n sZ E hE i hi D q hiq hq).symm)
    ((hypercohomology _ m).mapIso v.symm) hsq hbr

end AlgebraicEdge

/-! ### Holomorphic twisted logarithmic forms on `ℂⁿ` -/

section HolomorphicTwisted

open Set Filter Metric MeasureTheory ContinuousAlternatingMap MMP.DeRhamBetti
open scoped Topology

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℂ (Fin n)

/-- **Holomorphy of a parametric integral** over `[0, 1]`. -/
private theorem differentiableOn_intervalIntegral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace G] {U : Set 𝔼} (hU : IsOpen U) (F : 𝔼 → ℝ → G) (F' : 𝔼 → ℝ → 𝔼 →L[ℂ] G)
    (hF : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt (fun y => F y t) (F' x t) x)
    (hFc : ContinuousOn (fun p : 𝔼 × ℝ => F p.1 p.2) (U ×ˢ Icc 0 1))
    (hF'c : ContinuousOn (fun p : 𝔼 × ℝ => F' p.1 p.2) (U ×ˢ Icc 0 1)) :
    DifferentiableOn ℂ (fun x => ∫ t in (0 : ℝ)..1, F x t) U := by
  intro x₀ hx₀
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hRU' : closedBall x₀ (R / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hRU
  have hK : IsCompact (closedBall x₀ (R / 2) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hKU : closedBall x₀ (R / 2) ×ˢ Icc (0 : ℝ) 1 ⊆ U ×ˢ Icc 0 1 :=
    prod_mono hRU' le_rfl
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF'c.mono hKU)
  have hs : ball x₀ (R / 2) ∈ 𝓝 x₀ := ball_mem_nhds _ (by linarith)
  have hIoc : Set.uIoc (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [Set.uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  have hsec : ∀ x ∈ U, ContinuousOn (F x) (Icc 0 1) := fun x hx =>
    hFc.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hx, ht⟩)
  have hsec' : ∀ x ∈ U, ContinuousOn (F' x) (Icc 0 1) := fun x hx =>
    hF'c.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hx, ht⟩)
  have hmeas : ∀ x ∈ U, AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc 0 1)) :=
    fun x hx => ((hsec x hx).mono hIoc).aestronglyMeasurable measurableSet_uIoc
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (a := 0) (b := 1) (bound := fun _ => C) (F := F) (F' := F') (x₀ := x₀) hs
    (Filter.eventually_of_mem (hU.mem_nhds hx₀) hmeas)
    ((hsec x₀ hx₀).intervalIntegrable_of_Icc zero_le_one)
    (((hsec' x₀ hx₀).mono hIoc).aestronglyMeasurable measurableSet_uIoc)
    (Filter.Eventually.of_forall fun t ht x hx =>
      hC (x, t) ⟨ball_subset_closedBall hx, hIoc ht⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t ht x hx =>
      hF x (hRU' (ball_subset_closedBall hx)) t (hIoc ht))
  exact key.differentiableAt.differentiableWithinAt

/-- The point `v` with its `l`-th coordinate scaled by `t`. -/
private noncomputable def scaleCoord (l : Fin n) (v : 𝔼) (t : ℝ) : 𝔼 :=
  v + (((t : ℂ) - 1) * v l) • EuclideanSpace.single l (1 : ℂ)

private theorem scaleCoord_apply (l : Fin n) (v : 𝔼) (t : ℝ) (i : Fin n) :
    scaleCoord l v t i = if i = l then (t : ℂ) * v l else v i := by
  unfold scaleCoord
  by_cases h : i = l
  · subst h; simp; ring
  · simp [h]

private theorem norm_scaleCoord_le (l : Fin n) (v : 𝔼) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖scaleCoord l v t‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => ?_
  rw [scaleCoord_apply]
  split_ifs with h
  · subst h
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1, mul_pow]
    have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith [sq_nonneg ‖v i‖]
  · exact le_rfl

/-- `scaleCoord l · t` as a continuous linear map. -/
private noncomputable def scaleCoordCLM (l : Fin n) (t : ℝ) : 𝔼 →L[ℂ] 𝔼 :=
  ContinuousLinearMap.id ℂ 𝔼 + ((t : ℂ) - 1) •
    (EuclideanSpace.proj l : 𝔼 →L[ℂ] ℂ).smulRight (EuclideanSpace.single l (1 : ℂ))

private theorem scaleCoordCLM_apply (l : Fin n) (t : ℝ) (v : 𝔼) :
    scaleCoordCLM l t v = scaleCoord l v t := by
  simp [scaleCoordCLM, scaleCoord, smul_smul]

private theorem continuous_scaleCoordCLM (l : Fin n) : Continuous (scaleCoordCLM (n := n) l) := by
  unfold scaleCoordCLM
  exact continuous_const.add ((Complex.continuous_ofReal.sub continuous_const).smul continuous_const)

private theorem scaleCoord_mem_ball {r : ℝ} (l : Fin n) {v : 𝔼} (hv : v ∈ ball (0 : 𝔼) r) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : scaleCoord l v t ∈ ball (0 : 𝔼) r := by
  rw [mem_ball_zero_iff] at hv ⊢
  exact (norm_scaleCoord_le l v ht).trans_lt hv

private theorem scaleCoord_zero_apply_self (l : Fin n) (v : 𝔼) : scaleCoord l v 0 l = 0 := by
  rw [scaleCoord_apply]; simp

/-- **Division by a coordinate.** A holomorphic function on a ball about `0` vanishing on the
hyperplane `v_l = 0` is `v_l` times a holomorphic function. -/
private theorem exists_eq_mul_coord {r : ℝ} {f : 𝔼 → ℂ} (hf : DifferentiableOn ℂ f (ball 0 r))
    (l : Fin n) (h0 : ∀ v ∈ ball (0 : 𝔼) r, v l = 0 → f v = 0) :
    ∃ b : 𝔼 → ℂ, DifferentiableOn ℂ b (ball 0 r) ∧ ∀ v ∈ ball (0 : 𝔼) r, f v = v l * b v := by
  have hfa : AnalyticOnNhd ℂ f (ball 0 r) :=
    MMP.Analytic.analyticOnNhd_of_differentiableOn isOpen_ball hf
  have hf2 : ContDiffOn ℂ 2 f (ball 0 r) := hfa.contDiffOn_of_completeSpace
  set e : 𝔼 := EuclideanSpace.single l (1 : ℂ)
  set g : 𝔼 → ℂ := fun y => fderiv ℂ f y e with hg
  have hg1 : ContDiffOn ℂ 1 g (ball 0 r) := by
    have := (hf2.fderiv_of_isOpen isOpen_ball (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2))
    exact this.clm_apply contDiffOn_const
  have hgd : DifferentiableOn ℂ g (ball 0 r) := hg1.differentiableOn one_ne_zero
  have hg'c : ContinuousOn (fderiv ℂ g) (ball 0 r) :=
    hg1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, g (scaleCoordCLM l t x), ?_, fun v hv => ?_⟩
  · refine differentiableOn_intervalIntegral isOpen_ball (fun x t => g (scaleCoordCLM l t x))
      (fun x t => (fderiv ℂ g (scaleCoordCLM l t x)).comp (scaleCoordCLM l t)) ?_ ?_ ?_
    · intro x hx t ht
      have hm : scaleCoordCLM l t x ∈ ball (0 : 𝔼) r := by
        rw [scaleCoordCLM_apply]; exact scaleCoord_mem_ball l hx ht
      exact ((hgd.differentiableAt (isOpen_ball.mem_nhds hm)).hasFDerivAt).comp x
        (scaleCoordCLM l t).hasFDerivAt
    · have hc : Continuous (fun p : 𝔼 × ℝ => scaleCoordCLM l p.2 p.1) :=
        ((continuous_scaleCoordCLM l).comp continuous_snd).clm_apply continuous_fst
      refine hg1.continuousOn.comp hc.continuousOn fun p hp => ?_
      rw [scaleCoordCLM_apply]; exact scaleCoord_mem_ball l hp.1 hp.2
    · have hc : Continuous (fun p : 𝔼 × ℝ => scaleCoordCLM l p.2 p.1) :=
        ((continuous_scaleCoordCLM l).comp continuous_snd).clm_apply continuous_fst
      have h1 : ContinuousOn (fun p : 𝔼 × ℝ => fderiv ℂ g (scaleCoordCLM l p.2 p.1))
          (ball 0 r ×ˢ Icc 0 1) :=
        hg'c.comp hc.continuousOn fun p hp => by
          rw [scaleCoordCLM_apply]; exact scaleCoord_mem_ball l hp.1 hp.2
      exact h1.clm_comp ((continuous_scaleCoordCLM l).comp continuous_snd).continuousOn
  · -- the fundamental theorem of calculus along `t ↦ scaleCoord l v t`
    have hpath : ∀ t : ℝ, HasDerivAt (fun s : ℝ => scaleCoord l v s) (v l • e) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ) - 1) * v l) (v l) t := by
        simpa using (((hasDerivAt_id t).ofReal_comp).sub_const (1 : ℂ)).mul_const (v l)
      have h2 := h1.smul_const e
      have h3 := h2.const_add v
      simpa [scaleCoord] using h3
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => f (scaleCoord l v s))
        (v l * g (scaleCoord l v t)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hm := scaleCoord_mem_ball l hv ht
      have hfd : HasFDerivAt f (fderiv ℂ f (scaleCoord l v t)) (scaleCoord l v t) :=
        (hf.differentiableAt (isOpen_ball.mem_nhds hm)).hasFDerivAt
      have := (hfd.restrictScalars ℝ).comp_hasDerivAt t (hpath t)
      refine this.congr_deriv ?_
      change ((fderiv ℂ f (scaleCoord l v t)).restrictScalars ℝ) (v l • e) =
        v l * fderiv ℂ f (scaleCoord l v t) e
      rw [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
    have hint : IntervalIntegrable (fun t => v l * g (scaleCoord l v t)) volume 0 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      refine continuousOn_const.mul (hg1.continuousOn.comp ?_ fun t ht =>
        scaleCoord_mem_ball l hv ht)
      have : Continuous (fun s : ℝ => scaleCoord l v s) := by
        simp_rw [← scaleCoordCLM_apply]
        exact (continuous_scaleCoordCLM l).clm_apply continuous_const
      exact this.continuousOn
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hz : f (scaleCoord l v 0) = 0 :=
      h0 _ (scaleCoord_mem_ball l hv ⟨le_rfl, zero_le_one⟩) (scaleCoord_zero_apply_self l v)
    have h1 : scaleCoord l v 1 = v := by simp [scaleCoord]
    rw [h1, hz, sub_zero] at hftc
    rw [← hftc, intervalIntegral.integral_const_mul]
    simp_rw [scaleCoordCLM_apply]

/-- A function continuous at `v` vanishing at `v + s eₐ` for all small `s ≠ 0` vanishes at `v`. -/
private theorem eq_zero_of_eventually_eq_zero_punctured {b : 𝔼 → ℂ} {v : 𝔼} (hb : ContinuousAt b v)
    (a : Fin n) (h : ∀ᶠ s in 𝓝[≠] (0 : ℂ), b (v + s • EuclideanSpace.single a (1 : ℂ)) = 0) :
    b v = 0 := by
  have hpath : Tendsto (fun s : ℂ => v + s • EuclideanSpace.single a (1 : ℂ)) (𝓝[≠] (0 : ℂ))
      (𝓝 v) := by
    have : Continuous (fun s : ℂ => v + s • EuclideanSpace.single a (1 : ℂ)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 := this.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h1 := hb.tendsto.comp hpath
  have h2 : Tendsto (fun s : ℂ => b (v + s • EuclideanSpace.single a (1 : ℂ))) (𝓝[≠] (0 : ℂ))
      (𝓝 0) := tendsto_const_nhds.congr' (h.mono fun s hs => hs.symm)
  exact tendsto_nhds_unique h1 h2

/-- **Division by a product of coordinates.** A holomorphic function on a ball about `0` vanishing
on each hyperplane `v_l = 0`, `l ∈ S`, is `∏_{l ∈ S} v_l` times a holomorphic function. -/
private theorem exists_eq_prod_mul {r : ℝ} (S : Finset (Fin n)) {f : 𝔼 → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 r))
    (h0 : ∀ l ∈ S, ∀ v ∈ ball (0 : 𝔼) r, v l = 0 → f v = 0) :
    ∃ b : 𝔼 → ℂ, DifferentiableOn ℂ b (ball 0 r) ∧
      ∀ v ∈ ball (0 : 𝔼) r, f v = (∏ l ∈ S, v l) * b v := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => exact ⟨f, hf, fun v _ => by simp⟩
  | insert a S ha ih =>
    obtain ⟨b₁, hb₁, hfb₁⟩ := exists_eq_mul_coord hf a (h0 a (Finset.mem_insert_self a S))
    have hb₁0 : ∀ l ∈ S, ∀ v ∈ ball (0 : 𝔼) r, v l = 0 → b₁ v = 0 := by
      intro l hl v hv hvl
      have hla : l ≠ a := fun h => ha (h ▸ hl)
      have hoff : ∀ w ∈ ball (0 : 𝔼) r, w l = 0 → w a ≠ 0 → b₁ w = 0 := by
        intro w hw hwl hwa
        have := hfb₁ w hw
        rw [h0 l (Finset.mem_insert_of_mem hl) w hw hwl] at this
        exact (mul_eq_zero.mp this.symm).resolve_left hwa
      by_cases hva : v a = 0
      · refine eq_zero_of_eventually_eq_zero_punctured
          ((hb₁.differentiableAt (isOpen_ball.mem_nhds hv)).continuousAt) a ?_
        have hev : ∀ᶠ s in 𝓝 (0 : ℂ), v + s • EuclideanSpace.single a (1 : ℂ) ∈ ball (0 : 𝔼) r := by
          have hc : Continuous (fun s : ℂ => v + s • EuclideanSpace.single a (1 : ℂ)) :=
            continuous_const.add (continuous_id.smul continuous_const)
          have : (fun s : ℂ => v + s • EuclideanSpace.single a (1 : ℂ)) 0 ∈ ball (0 : 𝔼) r := by
            simpa using hv
          exact hc.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds this)
        filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s hs hs0
        refine hoff _ hs ?_ ?_
        · simp [hvl, PiLp.single_apply, hla]
        · simpa [hva, PiLp.single_apply] using hs0
      · exact hoff v hv hvl hva
    obtain ⟨b, hb, hb₁b⟩ := ih hb₁ hb₁0
    refine ⟨b, hb, fun v hv => ?_⟩
    rw [hfb₁ v hv, hb₁b v hv, Finset.prod_insert ha, mul_assoc]

/-- A form **vanishes along** the coordinate hyperplanes `v_l = 0`, `l ∈ S`, on `U`: at a point of
`U` on such a hyperplane it kills every tuple of vectors tangent to the hyperplane. -/
private def VanishesAlong (S : Finset (Fin n)) (U : Set 𝔼) {p : ℕ} (ξ : 𝔼 → 𝔼 [⋀^Fin p]→L[ℂ] ℂ) :
    Prop :=
  ∀ l ∈ S, ∀ v ∈ U, v l = 0 → ∀ w : Fin p → 𝔼, (∀ i, w i l = 0) → ξ v w = 0

/-- The radial homotopy integral preserves vanishing along coordinate hyperplanes. -/
private theorem vanishesAlong_radial {r : ℝ} (S : Finset (Fin n)) {k : ℕ}
    {β : 𝔼 → 𝔼 [⋀^Fin (k + 1)]→L[ℂ] ℂ} (hβ : VanishesAlong S (ball 0 r) β) :
    VanishesAlong S (ball 0 r) (fun x => ∫ t in (0 : ℝ)..1,
      ((t : ℂ) ^ k) • (β ((t : ℂ) • x)).curryLeft x) := by
  intro l hl v hv hvl w hw
  set f : ℝ → 𝔼 [⋀^Fin k]→L[ℂ] ℂ := fun t => ((t : ℂ) ^ k) • (β ((t : ℂ) • v)).curryLeft v
  have hpt : ∀ t ∈ uIcc (0 : ℝ) 1, f t w = 0 := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hm : (t : ℂ) • v ∈ ball (0 : 𝔼) r := by
      rw [mem_ball_zero_iff] at hv ⊢
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖v‖ ≤ 1 * ‖v‖ := by gcongr; exact ht.2
        _ < r := by rwa [one_mul]
    simp only [f, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply]
    rw [hβ l hl _ hm (by simp [hvl]) _ ?_, smul_zero]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hvl
    · simpa using hw j
  by_cases hint : IntervalIntegrable f volume 0 1
  · have := (ContinuousAlternatingMap.apply ℂ 𝔼 ℂ w).intervalIntegral_comp_comm hint
    simp only [ContinuousAlternatingMap.apply_apply] at this
    change (∫ t in (0 : ℝ)..1, f t) w = 0
    rw [← this]
    exact (intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) hpt).trans (by simp)
  · change (∫ t in (0 : ℝ)..1, f t) w = 0
    rw [intervalIntegral.integral_undef hint]
    rfl

/-- The exterior derivative preserves vanishing along coordinate hyperplanes. -/
private theorem vanishesAlong_extDeriv {U : Set 𝔼} (hU : IsOpen U) (S : Finset (Fin n)) {k : ℕ}
    {ξ : 𝔼 → 𝔼 [⋀^Fin k]→L[ℂ] ℂ} (hξ : DifferentiableOn ℂ ξ U) (hv : VanishesAlong S U ξ) :
    VanishesAlong S U (extDeriv ξ) := by
  intro l hl x hx hxl w hw
  have hxd : DifferentiableAt ℂ ξ x := hξ.differentiableAt (hU.mem_nhds hx)
  rw [extDeriv_apply hxd]
  refine Finset.sum_eq_zero fun i _ => ?_
  set g : 𝔼 → ℂ := fun y => ξ y (i.removeNth w)
  have hgd : DifferentiableAt ℂ g x :=
    (ContinuousAlternatingMap.apply ℂ 𝔼 ℂ (i.removeNth w)).differentiableAt.comp x hxd
  -- `g` vanishes along the line through `x` in the direction `w i`
  have hline : ∀ᶠ s in 𝓝 (0 : ℂ), g (x + s • w i) = 0 := by
    have hc : Continuous (fun s : ℂ => x + s • w i) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have : (fun s : ℂ => x + s • w i) 0 ∈ U := by simpa using hx
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds this)] with s hs
    refine hv l hl _ hs (by simp [hxl, hw i]) _ fun j => ?_
    simpa only [Fin.removeNth] using hw _
  have hpath : HasDerivAt (fun s : ℂ => x + s • w i) (w i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (w i)).const_add x
  have hcomp : HasDerivAt (fun s : ℂ => g (x + s • w i)) (fderiv ℂ g x (w i)) 0 :=
    hgd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hpath (by simp)
  have h0 : HasDerivAt (fun s : ℂ => g (x + s • w i)) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hline
  rw [hcomp.unique h0, smul_zero]

/-- The standard basis vectors indexed by a sorted `p`-subset. -/
private noncomputable def basisTuple {p : ℕ} (I : Set.powersetCard (Fin n) p) : Fin p → 𝔼 :=
  fun a => EuclideanSpace.single (sortedIdx I a) (1 : ℂ)

private theorem sortedIdx_injective {p : ℕ} (I : Set.powersetCard (Fin n) p) :
    Function.Injective (sortedIdx I) :=
  (Set.powersetCard.ofFinEmbEquiv.symm I).injective

private theorem sortedIdx_mem {p : ℕ} (I : Set.powersetCard (Fin n) p) (a : Fin p) :
    sortedIdx I a ∈ I :=
  (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I (sortedIdx I a)).1 ⟨a, rfl⟩

private theorem exists_sortedIdx_eq {p : ℕ} (I : Set.powersetCard (Fin n) p) {j : Fin n}
    (hj : j ∈ I) : ∃ a, sortedIdx I a = j :=
  (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I j).2 hj

/-- **The determinant forms are dual to the basis tuples.** -/
private theorem detForm_basisTuple {p : ℕ} (I J : Set.powersetCard (Fin n) p) :
    detForm (sortedIdx I) (basisTuple J) = if I = J then 1 else 0 := by
  classical
  rw [detForm_apply]
  have hM : (Matrix.of fun a b => (basisTuple J a).ofLp (sortedIdx I b)) =
      Matrix.of fun a b => if sortedIdx I b = sortedIdx J a then (1 : ℂ) else 0 := by
    ext a b
    simp [basisTuple, PiLp.single_apply]
  rw [hM]
  split_ifs with hIJ
  · subst hIJ
    have h1 : (Matrix.of fun a b => if sortedIdx I b = sortedIdx I a then (1 : ℂ) else 0) = 1 := by
      ext a b
      simp only [Matrix.of_apply, Matrix.one_apply, (sortedIdx_injective I).eq_iff, eq_comm]
    rw [h1, Matrix.det_one]
  · have hex : ∃ a, sortedIdx J a ∉ I := by
      by_contra h
      push Not at h
      apply hIJ
      have hsub : J.1 ⊆ I.1 := by
        intro j hj
        obtain ⟨a, rfl⟩ := exists_sortedIdx_eq J hj
        exact h a
      have := Finset.eq_of_subset_of_card_le hsub (by rw [I.2, J.2])
      exact Subtype.ext this.symm
    obtain ⟨a, ha⟩ := hex
    refine Matrix.det_eq_zero_of_row_eq_zero a fun b => ?_
    have : sortedIdx I b ≠ sortedIdx J a := fun h => ha (h ▸ sortedIdx_mem I b)
    simp [this]

/-- **Coordinates in the determinant basis** are the values on the basis tuples. -/
private theorem detBasis_repr_apply {p : ℕ} (ω : 𝔼 [⋀^Fin p]→L[ℂ] ℂ) (I : Set.powersetCard (Fin n) p) :
    (detBasis p).repr ω I = ω (basisTuple I) := by
  classical
  have h := congrArg (ContinuousAlternatingMap.apply ℂ 𝔼 ℂ (basisTuple I))
    ((detBasis p).sum_repr ω)
  rw [_root_.map_sum] at h
  simp only [ContinuousAlternatingMap.apply_apply, ContinuousAlternatingMap.smul_apply,
    detBasis_apply, detForm_basisTuple, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

/-- Every alternating form is the combination of the determinant forms with its values on the
basis tuples as coefficients. -/
private theorem eq_sum_detForm {p : ℕ} (ω : 𝔼 [⋀^Fin p]→L[ℂ] ℂ) :
    ω = ∑ I, ω (basisTuple I) • detForm (sortedIdx I) := by
  conv_lhs => rw [← (detBasis p).sum_repr ω]
  simp only [detBasis_repr_apply, detBasis_apply]

/-- The holomorphic logarithmic product forms of `analytification_smooth_differentials`:
`e_I = ⋀_{a} s_a ⬝ dv_{I(a)}` with `s_a = (v_j + c_j)⁻¹` on the first `k` coordinates. -/
private noncomputable def logProd (k : ℕ) (c : Fin n → ℂ) (p : ℕ) (I : Set.powersetCard (Fin n) p)
    (v : 𝔼) : 𝔼 [⋀^Fin p]→L[ℂ] ℂ :=
  ContinuousMultilinearMap.alternatization
    ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin p) ℂ).compContinuousLinearMap
      fun a =>
        let j := Set.powersetCard.ofFinEmbEquiv.symm I a
        (if (j : ℕ) < k then (v j + c j)⁻¹ else 1) • EuclideanSpace.proj j)

/-- The scalar factor of `logProd`. -/
private noncomputable def logScalar (k : ℕ) (c : Fin n → ℂ) {p : ℕ} (I : Set.powersetCard (Fin n) p)
    (v : 𝔼) : ℂ :=
  ∏ a : Fin p, if ((sortedIdx I a : Fin n) : ℕ) < k then (v (sortedIdx I a) + c (sortedIdx I a))⁻¹
    else 1

private theorem logProd_eq_smul_detForm (k : ℕ) (c : Fin n → ℂ) {p : ℕ} (I : Set.powersetCard (Fin n) p)
    (v : 𝔼) : logProd k c p I v = logScalar k c I v • detForm (sortedIdx I) := by
  ext w
  rw [ContinuousAlternatingMap.smul_apply, detForm_apply, Matrix.det_apply, logProd,
    ContinuousMultilinearMap.alternatization_apply_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Matrix.of_apply, logScalar, sortedIdx]
  rw [Finset.prod_mul_distrib, mul_smul_comm]
  rfl

/-- Two functions continuous at `v` agreeing at `v + s • u` for all small `s ≠ 0` agree at `v`. -/
private theorem eq_of_eventually_eq_punctured {G : Type*} [TopologicalSpace G] [T2Space G]
    {f g : 𝔼 → G} {v : 𝔼} (hf : ContinuousAt f v) (hg : ContinuousAt g v) (u : 𝔼)
    (h : ∀ᶠ s in 𝓝[≠] (0 : ℂ), f (v + s • u) = g (v + s • u)) : f v = g v := by
  have hpath : Tendsto (fun s : ℂ => v + s • u) (𝓝[≠] (0 : ℂ)) (𝓝 v) := by
    have : Continuous (fun s : ℂ => v + s • u) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 := this.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h1 := hf.tendsto.comp hpath
  have h2 := hg.tendsto.comp hpath
  exact tendsto_nhds_unique h1 (h2.congr' (h.mono fun s hs => hs.symm))

/-- The complement of the divisor in the chart: the first `k` translated coordinates are
nonzero. -/
private def chartDc (k : ℕ) (c : Fin n → ℂ) : Set 𝔼 := {v | ∀ j : Fin n, (j : ℕ) < k → v j + c j ≠ 0}

open Classical in
/-- The twisting factor `∏_{j < k, j ∉ I} (v_j + c_j)` of the forms of `Ω^p(log E)(-E)`. -/
private noncomputable def twistFactor (k : ℕ) (c : Fin n → ℂ) {p : ℕ} (I : Set.powersetCard (Fin n) p)
    (v : 𝔼) : ℂ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k ∧ j ∉ I), (v j + c j)

/-- The vector with `1` in the first `k` coordinates. -/
private noncomputable def firstOnes (k : ℕ) : 𝔼 := ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
  EuclideanSpace.single j (1 : ℂ)

private theorem firstOnes_apply (k : ℕ) (j : Fin n) : (firstOnes k : 𝔼) j = if (j : ℕ) < k then 1 else 0 := by
  classical
  simp [firstOnes, PiLp.single_apply, Finset.sum_apply]

/-- Near any point, the points `v + s • 𝟙_{<k}` with `s ≠ 0` small lie off the divisor. -/
private theorem eventually_mem_chartDc (k : ℕ) (c : Fin n → ℂ) (v : 𝔼) :
    ∀ᶠ s in 𝓝[≠] (0 : ℂ), v + s • (firstOnes k : 𝔼) ∈ chartDc k c := by
  have h : ∀ j : Fin n, ∀ᶠ s in 𝓝[≠] (0 : ℂ), (j : ℕ) < k → v j + s + c j ≠ 0 := by
    intro j
    by_cases hj : v j + c j = 0
    · filter_upwards [self_mem_nhdsWithin] with s hs _
      have : v j + s + c j = s := by linear_combination hj
      rw [this]; exact hs
    · have hne : ∀ᶠ s in 𝓝 (0 : ℂ), v j + s + c j ≠ 0 := by
        have hc : Continuous (fun s : ℂ => v j + s + c j) := by fun_prop
        have : (fun s : ℂ => v j + s + c j) 0 ≠ 0 := by simpa [add_comm, add_left_comm] using hj
        exact hc.continuousAt.eventually_ne this
      filter_upwards [nhdsWithin_le_nhds hne] with s hs _ using hs
  filter_upwards [Filter.eventually_all.2 h] with s hs
  intro j hj
  have := hs j hj
  simpa [firstOnes_apply, hj] using this

open Classical in
/-- **The algebra of the twisting factor**: off the divisor,
`(∏_{j<k} (v_j + c_j)) · (∏_{a} s_a) = ∏_{j<k, j ∉ I} (v_j + c_j)`. -/
private theorem prod_mul_logScalar (k : ℕ) (hk : k ≤ n) (c : Fin n → ℂ) {p : ℕ}
    (I : Set.powersetCard (Fin n) p) {v : 𝔼} (hv : v ∈ chartDc k c) :
    (∏ j : Fin k, (v (Fin.castLE hk j) + c (Fin.castLE hk j))) * logScalar k c I v =
      twistFactor k c I v := by
  set f : Fin n → ℂ := fun j => v j + c j with hf
  have hf0 : ∀ j : Fin n, (j : ℕ) < k → f j ≠ 0 := hv
  -- the product over `Fin k`
  have h1 : (∏ j : Fin k, (v (Fin.castLE hk j) + c (Fin.castLE hk j))) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), f j := by
    change ∏ j : Fin k, f (Fin.castLEEmb hk j) = _
    rw [← Finset.prod_map Finset.univ (Fin.castLEEmb hk) f]
    congr 1
    ext j
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply]
    constructor
    · rintro ⟨i, rfl⟩; exact i.2
    · intro h; exact ⟨⟨j, h⟩, rfl⟩
  -- the scalar as a product over `I`
  have h2 : logScalar k c I v = ∏ j ∈ (I.1 : Finset (Fin n)), (if (j : ℕ) < k then (f j)⁻¹ else 1) := by
    unfold logScalar
    have hmap : (I.1 : Finset (Fin n)) = Finset.univ.map ⟨sortedIdx I, sortedIdx_injective I⟩ := by
      ext j
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
      constructor
      · intro hj; exact exists_sortedIdx_eq I hj
      · rintro ⟨a, rfl⟩; exact sortedIdx_mem I a
    rw [hmap, Finset.prod_map]
    rfl
  rw [h1, h2, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_inv_distrib,
    ← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter fun j : Fin n => (j : ℕ) < k)
      (fun j => j ∈ I)]
  have hset : (Finset.univ.filter fun j : Fin n => (j : ℕ) < k).filter (fun j => j ∈ I) =
      (I.1 : Finset (Fin n)).filter fun j : Fin n => (j : ℕ) < k := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hset' : (Finset.univ.filter fun j : Fin n => (j : ℕ) < k).filter (fun j => j ∉ I) =
      Finset.univ.filter fun j : Fin n => (j : ℕ) < k ∧ j ∉ I := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset, hset', mul_comm (∏ j ∈ (I.1 : Finset (Fin n)).filter fun j : Fin n => (j : ℕ) < k, f j), mul_assoc,
    mul_inv_cancel₀, mul_one]
  · rfl
  · exact Finset.prod_ne_zero_iff.2 fun j hj => hf0 j (Finset.mem_filter.1 hj).2

/-- Off the divisor, a combination of the twisted log forms, written in the determinant basis. -/
private theorem smul_sum_logProd (k : ℕ) (hk : k ≤ n) (c : Fin n → ℂ) {p : ℕ}
    (g : Set.powersetCard (Fin n) p → 𝔼 → ℂ) {v : 𝔼} (hv : v ∈ chartDc k c) :
    (∏ j : Fin k, (v (Fin.castLE hk j) + c (Fin.castLE hk j))) • ∑ I, g I v • logProd k c p I v =
      ∑ I, (g I v * twistFactor k c I v) • detForm (sortedIdx I) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [logProd_eq_smul_detForm, smul_smul, smul_smul, ← prod_mul_logScalar k hk c I hv]
  ring_nf

/-- The holomorphic forms of the analytified `Ω^p(log E)(-E)` in a chart, as in
`analytification_smooth_differentials`: holomorphic combinations of the twisted log forms. -/
private def HolSubOn (k : ℕ) (hk : k ≤ n) (c : Fin n → ℂ) {p : ℕ} (A : Set 𝔼)
    (ξ : 𝔼 → 𝔼 [⋀^Fin p]→L[ℂ] ℂ) : Prop :=
  ∃ g : Set.powersetCard (Fin n) p → 𝔼 → ℂ, (∀ I, DifferentiableOn ℂ (g I) A) ∧
    ∀ v ∈ A ∩ chartDc k c, ξ v =
      (∏ j : Fin k, (v (Fin.castLE hk j) + c (Fin.castLE hk j))) • ∑ I, g I v • logProd k c p I v

private theorem continuous_twistFactor (k : ℕ) (c : Fin n → ℂ) {p : ℕ} (I : Set.powersetCard (Fin n) p) :
    Continuous (twistFactor k c I : 𝔼 → ℂ) := by
  unfold twistFactor
  refine continuous_finset_prod _ fun j _ => ?_
  exact ((EuclideanSpace.proj j : 𝔼 →L[ℂ] ℂ).continuous).add continuous_const

/-- A form of `HolSubOn` is, on all of `A`, the combination
`∑_I (g_I ∏_{j<k, j ∉ I} (v_j + c_j)) dv_I`. -/
private theorem eq_sum_twistFactor_of_holSubOn (k : ℕ) (hk : k ≤ n) (c : Fin n → ℂ) {p : ℕ} {A : Set 𝔼}
    (hA : IsOpen A) {ξ : 𝔼 → 𝔼 [⋀^Fin p]→L[ℂ] ℂ} (hξ : ContinuousOn ξ A)
    {g : Set.powersetCard (Fin n) p → 𝔼 → ℂ} (hg : ∀ I, DifferentiableOn ℂ (g I) A)
    (hgξ : ∀ v ∈ A ∩ chartDc k c, ξ v =
      (∏ j : Fin k, (v (Fin.castLE hk j) + c (Fin.castLE hk j))) • ∑ I, g I v • logProd k c p I v)
    {v : 𝔼} (hv : v ∈ A) :
    ξ v = ∑ I, (g I v * twistFactor k c I v) • detForm (sortedIdx I) := by
  refine eq_of_eventually_eq_punctured
    (g := fun w => ∑ I, (g I w * twistFactor k c I w) • detForm (sortedIdx I))
    (hξ.continuousAt (hA.mem_nhds hv)) ?_ (firstOnes k) ?_
  · have hc : ∀ I, ContinuousAt (fun w => (g I w * twistFactor k c I w) • detForm (sortedIdx I))
        v := fun I =>
      (((hg I).differentiableAt (hA.mem_nhds hv)).continuousAt.mul
        (continuous_twistFactor k c I).continuousAt).smul continuousAt_const
    exact tendsto_finset_sum _ fun I _ => hc I
  · have hpathA : ∀ᶠ s in 𝓝 (0 : ℂ), v + s • (firstOnes k : 𝔼) ∈ A := by
      have hc : Continuous (fun s : ℂ => v + s • (firstOnes k : 𝔼)) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have : (fun s : ℂ => v + s • (firstOnes k : 𝔼)) 0 ∈ A := by simpa using hv
      exact hc.continuousAt.preimage_mem_nhds (hA.mem_nhds this)
    filter_upwards [eventually_mem_chartDc k c v, nhdsWithin_le_nhds hpathA] with s hDc hsA
    rw [hgξ _ ⟨hsA, hDc⟩, smul_sum_logProd k hk c g hDc]

open Classical in
/-- The coordinates `l < k` vanishing at the chart centre: the components of the divisor through
it. -/
private noncomputable def boundaryCoords (k : ℕ) (c : Fin n → ℂ) : Finset (Fin n) :=
  Finset.univ.filter fun l : Fin n => (l : ℕ) < k ∧ c l = 0

/-- **Forms of `Ω^p(log E)(-E)` vanish along the divisor.** -/
private theorem vanishesAlong_of_holSubOn (k : ℕ) (hk : k ≤ n) (c : Fin n → ℂ) {p : ℕ} {A : Set 𝔼}
    (hA : IsOpen A) {ξ : 𝔼 → 𝔼 [⋀^Fin p]→L[ℂ] ℂ} (hξ : ContinuousOn ξ A)
    (h : HolSubOn k hk c A ξ) : VanishesAlong (boundaryCoords k c) A ξ := by
  classical
  obtain ⟨g, hg, hgξ⟩ := h
  intro l hl v hv hvl w hw
  have hsum := eq_sum_twistFactor_of_holSubOn k hk c hA hξ hg hgξ hv
  have hval : ξ v w = ∑ I, (g I v * twistFactor k c I v) * detForm (sortedIdx I) w := by
    rw [hsum]
    exact (_root_.map_sum (ContinuousAlternatingMap.apply ℂ 𝔼 ℂ w) _ _).trans (by simp)
  rw [hval]
  simp only [boundaryCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  refine Finset.sum_eq_zero fun I _ => ?_
  by_cases hlI : l ∈ I
  · obtain ⟨b, hb⟩ := exists_sortedIdx_eq I hlI
    rw [detForm_apply, Matrix.det_eq_zero_of_column_eq_zero b (fun a => by simp [hb, hw a]),
      mul_zero]
  · have h0 : twistFactor k c I v = 0 :=
      Finset.prod_eq_zero (i := l) (by simp [hl.1, hlI]) (by simp [hvl, hl.2])
    rw [h0, mul_zero, zero_mul]

/-- A product of affine coordinate functions is holomorphic. -/
private theorem differentiable_prod_affine (s : Finset (Fin n)) (c : Fin n → ℂ) :
    Differentiable ℂ (fun v : 𝔼 => ∏ j ∈ s, (v j + c j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact ((EuclideanSpace.proj a : 𝔼 →L[ℂ] ℂ).differentiable.add_const _).mul ih

open Classical in
/-- **Forms vanishing along the divisor are forms of `Ω^p(log E)(-E)`**, on a ball about the chart
centre small enough that the coordinates not vanishing at the centre stay invertible. -/
private theorem holSubOn_of_vanishesAlong (k : ℕ) (hk : k ≤ n) (c : Fin n → ℂ) {p : ℕ} {r : ℝ}
    (hr : ∀ j : Fin n, (j : ℕ) < k → c j ≠ 0 → r ≤ ‖c j‖)
    {ξ : 𝔼 → 𝔼 [⋀^Fin p]→L[ℂ] ℂ} (hξ : DifferentiableOn ℂ ξ (ball 0 r))
    (hv : VanishesAlong (boundaryCoords k c) (ball 0 r) ξ) : HolSubOn k hk c (ball 0 r) ξ := by
  -- the coefficients in the determinant basis
  have hcoef : ∀ I : Set.powersetCard (Fin n) p, ∃ b : 𝔼 → ℂ, DifferentiableOn ℂ b (ball 0 r) ∧
      ∀ v ∈ ball (0 : 𝔼) r, ξ v (basisTuple I) =
        (∏ l ∈ (boundaryCoords k c).filter (· ∉ I), v l) * b v := by
    intro I
    refine exists_eq_prod_mul _ ?_ fun l hl v hvr hvl => ?_
    · exact (ContinuousAlternatingMap.apply ℂ 𝔼 ℂ (basisTuple I)).differentiable.comp_differentiableOn hξ
    · rw [Finset.mem_filter] at hl
      refine hv l hl.1 v hvr hvl _ fun a => ?_
      have : l ≠ sortedIdx I a := fun h => hl.2 (h ▸ sortedIdx_mem I a)
      simp [basisTuple, PiLp.single_apply, this]
  choose b hb hbξ using hcoef
  set den : Set.powersetCard (Fin n) p → 𝔼 → ℂ := fun I v =>
    ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k ∧ j ∉ I ∧ c j ≠ 0), (v j + c j)
  have hden : ∀ I, ∀ v ∈ ball (0 : 𝔼) r, den I v ≠ 0 := by
    intro I v hvr
    refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    intro h0
    have hvj : ‖v j‖ < r := (PiLp.norm_apply_le v j).trans_lt (mem_ball_zero_iff.1 hvr)
    have hcj : c j = -v j := by linear_combination h0
    have := hr j hj.1 hj.2.2
    rw [hcj, norm_neg] at this
    linarith
  have hdend : ∀ I, DifferentiableOn ℂ (den I) (ball 0 r) := fun I => by
    show DifferentiableOn ℂ (fun v : 𝔼 => ∏ j ∈ Finset.univ.filter
      (fun j : Fin n => (j : ℕ) < k ∧ j ∉ I ∧ c j ≠ 0), (v j + c j)) (ball 0 r)
    exact (differentiable_prod_affine _ c).differentiableOn
  refine ⟨fun I v => b I v * (den I v)⁻¹, fun I => (hb I).mul ((hdend I).inv (hden I)),
    fun v hv' => ?_⟩
  obtain ⟨hvr, hvD⟩ := hv'
  rw [smul_sum_logProd k hk c (fun I v => b I v * (den I v)⁻¹) hvD]
  conv_lhs => rw [eq_sum_detForm (ξ v)]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  have htw : twistFactor k c I v =
      (∏ l ∈ (boundaryCoords k c).filter (· ∉ I), v l) * den I v := by
    unfold twistFactor
    rw [← Finset.prod_filter_mul_prod_filter_not
      (Finset.univ.filter fun j : Fin n => (j : ℕ) < k ∧ j ∉ I) (fun j => c j = 0)]
    congr 1
    · refine Finset.prod_congr ?_ fun j hj => ?_
      · ext j
        simp only [boundaryCoords, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      · rw [(Finset.mem_filter.1 (Finset.mem_filter.1 hj).1).2.2, add_zero]
    · refine Finset.prod_congr ?_ fun _ _ => rfl
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
  rw [htw, hbξ I v hvr]
  field_simp [hden I v hvr]

/-- **The twisted logarithmic Poincaré lemma** on a ball about `0`: a closed form vanishing along
coordinate hyperplanes through `0` is the exterior derivative of a form vanishing along them,
namely its radial homotopy. -/
private theorem exists_vanishing_primitive {r : ℝ} (S : Finset (Fin n)) {k : ℕ}
    {β : 𝔼 → 𝔼 [⋀^Fin (k + 1)]→L[ℂ] ℂ} (hcd : ContDiffOn ℂ 1 β (ball 0 r))
    (hd : ∀ y ∈ ball (0 : 𝔼) r, extDeriv β y = 0) (hv : VanishesAlong S (ball 0 r) β) :
    ∃ η : 𝔼 → 𝔼 [⋀^Fin k]→L[ℂ] ℂ, DifferentiableOn ℂ η (ball 0 r) ∧
      VanishesAlong S (ball 0 r) η ∧ ∀ y ∈ ball (0 : 𝔼) r, extDeriv η y = β y := by
  refine ⟨radialHomotopy k β, fun y hy ↦ (hasFDerivAt_radialHomotopy hcd hy).differentiableAt
    |>.differentiableWithinAt, vanishesAlong_radial S hv, fun y hy ↦ ?_⟩
  have h := extDeriv_radialHomotopy_add hcd hy
  have h0 : radialHomotopy (k + 1) (extDeriv β) y = 0 := by
    unfold radialHomotopy
    rw [intervalIntegral.integral_congr (g := fun _ ↦ 0)]
    · simp
    · intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hts : (t : ℂ) • y ∈ ball (0 : 𝔼) r := by
        rw [mem_ball_zero_iff] at hy ⊢
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
        calc t * ‖y‖ ≤ 1 * ‖y‖ := by gcongr; exact ht.2
          _ < r := by rwa [one_mul]
      show (t : ℂ) ^ (k + 1) • (extDeriv β ((t : ℂ) • y)).curryLeft y = 0
      rw [hd _ hts]
      simp
  rwa [h0, add_zero] at h

/-- A ball about `0` inside an open neighbourhood of `0`, of radius at most the norms of the
nonzero first `k` coordinates of `c`. -/
private theorem exists_ball_subset_le_norm {A : Set 𝔼} (hA : IsOpen A) (h0 : (0 : 𝔼) ∈ A)
    (k : ℕ) (c : Fin n → ℂ) :
    ∃ r > 0, ball (0 : 𝔼) r ⊆ A ∧ ∀ j : Fin n, (j : ℕ) < k → c j ≠ 0 → r ≤ ‖c j‖ := by
  classical
  obtain ⟨r0, hr0, hb⟩ := Metric.isOpen_iff.1 hA 0 h0
  let S := Finset.univ.filter (fun j : Fin n => c j ≠ 0)
  by_cases hS : S.Nonempty
  · refine ⟨min r0 (S.inf' hS fun j => ‖c j‖), lt_min hr0 ((Finset.lt_inf'_iff hS).2 fun j hj =>
      norm_pos_iff.2 (Finset.mem_filter.1 hj).2), (ball_subset_ball (min_le_left _ _)).trans hb,
      fun j _ hj => (min_le_right _ _).trans (Finset.inf'_le (fun j => ‖c j‖)
        (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩))⟩
  · refine ⟨r0, hr0, hb, fun j _ hj => absurd ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩⟩ hS⟩

open scoped ContDiff in
/-- **The twisted Poincaré lemma for the restriction complex** on a small ball about the chart
centre: a holomorphic form whose exterior derivative is a combination of the twisted logarithmic
forms is, up to such a combination, an exterior derivative. -/
private theorem exists_eq_extDeriv_add_of_holSubOn_extDeriv (k : ℕ) (hk : k ≤ n) (c : Fin n → ℂ)
    {r : ℝ} (hr : ∀ j : Fin n, (j : ℕ) < k → c j ≠ 0 → r ≤ ‖c j‖) {p : ℕ}
    {ξ : 𝔼 → 𝔼 [⋀^Fin (p + 1)]→L[ℂ] ℂ} (hξ : DifferentiableOn ℂ ξ (ball 0 r))
    (hd : HolSubOn k hk c (ball 0 r) (extDeriv ξ)) :
    ∃ η : 𝔼 → 𝔼 [⋀^Fin p]→L[ℂ] ℂ, DifferentiableOn ℂ η (ball 0 r) ∧
      ∃ σ : 𝔼 → 𝔼 [⋀^Fin (p + 1)]→L[ℂ] ℂ, DifferentiableOn ℂ σ (ball 0 r) ∧
        HolSubOn k hk c (ball 0 r) σ ∧ ∀ v ∈ ball (0 : 𝔼) r, ξ v = extDeriv η v + σ v := by
  haveI := finiteDimensional_alt (n := n) (p + 1)
  haveI := finiteDimensional_alt (n := n) (p + 1 + 1)
  have hξc : ContDiffOn ℂ ∞ ξ (ball 0 r) := contDiffOn_of_differentiableOn_vec isOpen_ball hξ
  have hdξ : DifferentiableOn ℂ (extDeriv ξ) (ball 0 r) := differentiableOn_extDeriv isOpen_ball hξ
  have hv := vanishesAlong_of_holSubOn k hk c isOpen_ball hdξ.continuousOn hd
  have hcd : ContDiffOn ℂ 1 (extDeriv ξ) (ball 0 r) :=
    contDiffOn_of_differentiableOn_vec isOpen_ball hdξ
  have hdd : ∀ y ∈ ball (0 : 𝔼) r, extDeriv (extDeriv ξ) y = 0 := fun y hy =>
    extDeriv_extDeriv_apply (hξc.contDiffAt (isOpen_ball.mem_nhds hy)) (by simp)
  obtain ⟨η₁, hη₁d, hη₁v, hη₁⟩ := exists_vanishing_primitive _ hcd hdd hv
  have hcl : ∀ y ∈ ball (0 : 𝔼) r, extDeriv (ξ - η₁) y = 0 := by
    intro y hy
    have h1 : DifferentiableAt ℂ ξ y := hξ.differentiableAt (isOpen_ball.mem_nhds hy)
    have h2 : DifferentiableAt ℂ η₁ y := hη₁d.differentiableAt (isOpen_ball.mem_nhds hy)
    have e : ξ - η₁ = ξ + (-1 : ℂ) • η₁ := by rw [neg_one_smul, sub_eq_add_neg]
    rw [e, extDeriv_add h1 (h2.const_smul _), extDeriv_smul, hη₁ y hy, neg_one_smul,
      add_neg_cancel]
  have hcd2 : ContDiffOn ℂ 1 (ξ - η₁) (ball 0 r) :=
    contDiffOn_of_differentiableOn_vec isOpen_ball (hξ.sub hη₁d)
  obtain ⟨η₂, hη₂d, hη₂⟩ := exists_primitive_ball hcd2 hcl
  refine ⟨η₂, hη₂d, η₁, hη₁d, holSubOn_of_vanishesAlong k hk c hr hη₁d hη₁v, fun v hv => ?_⟩
  rw [hη₂ v hv, Pi.sub_apply, sub_add_cancel]

open scoped ContDiff in
/-- **The twisted Poincaré lemma in degree zero**: a holomorphic function whose differential is a
combination of the twisted logarithmic forms is a constant up to a twisted function. -/
private theorem exists_eq_const_add_of_holSubOn_extDeriv (k : ℕ) (hk : k ≤ n) (c : Fin n → ℂ)
    {r : ℝ} (hr : ∀ j : Fin n, (j : ℕ) < k → c j ≠ 0 → r ≤ ‖c j‖)
    {f : 𝔼 → 𝔼 [⋀^Fin 0]→L[ℂ] ℂ} (hf : DifferentiableOn ℂ f (ball 0 r))
    (hd : HolSubOn k hk c (ball 0 r) (extDeriv f)) :
    ∃ a : 𝔼 [⋀^Fin 0]→L[ℂ] ℂ, ∃ σ : 𝔼 → 𝔼 [⋀^Fin 0]→L[ℂ] ℂ,
      DifferentiableOn ℂ σ (ball 0 r) ∧ HolSubOn k hk c (ball 0 r) σ ∧
        ∀ v ∈ ball (0 : 𝔼) r, f v = a + σ v := by
  haveI := finiteDimensional_alt (n := n) 0
  haveI := finiteDimensional_alt (n := n) (0 + 1)
  have hfc : ContDiffOn ℂ ∞ f (ball 0 r) := contDiffOn_of_differentiableOn_vec isOpen_ball hf
  have hdf : DifferentiableOn ℂ (extDeriv f) (ball 0 r) := differentiableOn_extDeriv isOpen_ball hf
  have hv := vanishesAlong_of_holSubOn k hk c isOpen_ball hdf.continuousOn hd
  have hcd : ContDiffOn ℂ 1 (extDeriv f) (ball 0 r) :=
    contDiffOn_of_differentiableOn_vec isOpen_ball hdf
  have hdd : ∀ y ∈ ball (0 : 𝔼) r, extDeriv (extDeriv f) y = 0 := fun y hy =>
    extDeriv_extDeriv_apply (hfc.contDiffAt (isOpen_ball.mem_nhds hy)) (by simp)
  obtain ⟨η₁, hη₁d, hη₁v, hη₁⟩ := exists_vanishing_primitive _ hcd hdd hv
  have hcl : ∀ y ∈ ball (0 : 𝔼) r, fderiv ℂ (f - η₁) y = 0 := by
    intro y hy
    have h1 : DifferentiableAt ℂ f y := hf.differentiableAt (isOpen_ball.mem_nhds hy)
    have h2 : DifferentiableAt ℂ η₁ y := hη₁d.differentiableAt (isOpen_ball.mem_nhds hy)
    refine fderiv_eq_zero_of_extDeriv_eq_zero ?_
    have e : f - η₁ = f + (-1 : ℂ) • η₁ := by rw [neg_one_smul, sub_eq_add_neg]
    rw [e, extDeriv_add h1 (h2.const_smul _), extDeriv_smul, hη₁ y hy, neg_one_smul,
      add_neg_cancel]
  have hconst : ∀ v ∈ ball (0 : 𝔼) r, (f - η₁) v = (f - η₁) 0 := fun v hv =>
    (convex_ball (0 : 𝔼) r).is_const_of_fderivWithin_eq_zero (hf.sub hη₁d)
      (fun x hx => by rw [fderivWithin_of_isOpen isOpen_ball hx]; exact hcl x hx) hv
      (mem_ball_self (pos_of_mem_ball hv))
  refine ⟨(f - η₁) 0, η₁, hη₁d, holSubOn_of_vanishesAlong k hk c hr hη₁d hη₁v, fun v hv => ?_⟩
  rw [← hconst v hv, Pi.sub_apply, sub_add_cancel]

private theorem holSubOn_congr (k : ℕ) (hk : k ≤ n) (c : Fin n → ℂ) {p : ℕ} {A : Set 𝔼}
    {ξ ξ' : 𝔼 → 𝔼 [⋀^Fin p]→L[ℂ] ℂ} (h : ∀ v ∈ A, ξ v = ξ' v) (h' : HolSubOn k hk c A ξ') :
    HolSubOn k hk c A ξ :=
  let ⟨g, hg, hf⟩ := h'
  ⟨g, hg, fun v hv => (h v hv.1).trans (hf v hv)⟩

end HolomorphicTwisted

/-! ### Stalks of epimorphisms of abelian sheaves -/

section StalkEpi

open scoped ZeroObject

/-- An epimorphism of sheaves of abelian groups is surjective on stalks. -/
private theorem stalkFunctor_map_surjective_of_epi {T : TopCat.{0}}
    {F G : TopCat.Sheaf AddCommGrpCat.{0} T} (f : F ⟶ G) [Epi f] (x : T) :
    Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map f.hom) := by
  have : Epi ((TopCat.Sheaf.forget AddCommGrpCat.{0} T ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map f) := Functor.map_epi _ f
  exact (AddCommGrpCat.epi_iff_surjective _).1 this

end StalkEpi

/-! ### The twisted forms in holomorphic charts -/

section ChartForms

open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints MMP.DeRhamBetti
open scoped Manifold ContDiff

variable (n : ℕ) {Z : Scheme.{0}} (sZ : Z ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n sZ]
  [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sZ)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sZ)]
  {Θ : structureSheaf sZ ≅ 𝒪[n, ComplexPoints sZ]}

/-- The span, over the holomorphic functions on a chart patch, of the analytifications of the
twisted generators `τ_I` of `Ω^p(log E)(-E)`. -/
private noncomputable def chartSpan {y : ComplexPoints sZ} (C : ChartData sZ n Θ y) (k p : ℕ)
    (O : Opens (EuclideanSpace ℂ (Fin n))) :
    Submodule ((ringCatSheaf sZ).obj.obj (op (patch sZ C.φ O)))
      ((Ωan sZ p).val.obj (op (patch sZ C.φ O))) :=
  Submodule.span _ (Set.range fun I : Set.powersetCard (Fin n) p =>
    an sZ p C.W (patch sZ C.φ O) (patch_le_W sZ C O)
      ((MMP.DeRham.formsAlgEquiv sZ p ⟨C.W, C.hW⟩).symm
        (twistedGen n sZ ⟨C.W, C.hW⟩ k C.z p I)))

/-- The span of the twisted generators is stable under restriction to smaller patches. -/
private theorem map_mem_chartSpan {y : ComplexPoints sZ} (C : ChartData sZ n Θ y) (k p : ℕ)
    {O₁ O₂ : Opens (EuclideanSpace ℂ (Fin n))} (h : patch sZ C.φ O₁ ≤ patch sZ C.φ O₂)
    {s : (Ωan sZ p).val.obj (op (patch sZ C.φ O₂))} (hs : s ∈ chartSpan n sZ C k p O₂) :
    (Ωan sZ p).val.presheaf.map (homOfLE h).op s ∈ chartSpan n sZ C k p O₁ := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, rfl⟩ := hx
    rw [an_res]
    exact Submodule.subset_span ⟨I, rfl⟩
  | zero => erw [map_zero]; exact Submodule.zero_mem _
  | add x x' _ _ hx hx' => erw [map_add]; exact Submodule.add_mem _ hx hx'
  | smul a x _ hx =>
    erw [(Ωan sZ p).val.map_smul (homOfLE h).op a x]
    exact Submodule.smul_mem _ _ hx

/-- Restriction to a smaller chart patch. -/
private theorem patch_mono {φ : OpenPartialHomeomorph (ComplexPoints sZ) (EuclideanSpace ℂ (Fin n))}
    {O₁ O₂ : Opens (EuclideanSpace ℂ (Fin n))} (h : O₁ ≤ O₂) : patch sZ φ O₁ ≤ patch sZ φ O₂ :=
  fun _ hy => ⟨hy.1, h hy.2⟩

/-- The germs at `y` of combinations of the twisted generators on chart patches around `y`. -/
private def chartGerms {y : ComplexPoints sZ} (C : ChartData sZ n Θ y) (k p : ℕ) :
    Set (TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ)
      (Ωan sZ p).val.presheaf y) :=
  {g | ∃ (O : Opens (EuclideanSpace ℂ (Fin n))) (hO : y ∈ patch sZ C.φ O)
    (s : (Ωan sZ p).val.obj (op (patch sZ C.φ O))), s ∈ chartSpan n sZ C k p O ∧
      TopCat.Presheaf.germ (Ωan sZ p).val.presheaf (patch sZ C.φ O) y hO s = g}

private theorem zero_mem_chartGerms {y : ComplexPoints sZ} (C : ChartData sZ n Θ y) (k p : ℕ) :
    0 ∈ chartGerms n sZ C k p :=
  ⟨⊤, ⟨C.hy, Set.mem_univ _⟩, 0, Submodule.zero_mem _, map_zero _⟩

private theorem add_mem_chartGerms {y : ComplexPoints sZ} (C : ChartData sZ n Θ y) (k p : ℕ)
    {g₁ g₂} (h₁ : g₁ ∈ chartGerms n sZ C k p) (h₂ : g₂ ∈ chartGerms n sZ C k p) :
    g₁ + g₂ ∈ chartGerms n sZ C k p := by
  obtain ⟨O₁, hO₁, s₁, hs₁, rfl⟩ := h₁
  obtain ⟨O₂, hO₂, s₂, hs₂, rfl⟩ := h₂
  have i₁ : patch sZ C.φ (O₁ ⊓ O₂) ≤ patch sZ C.φ O₁ := patch_mono n sZ inf_le_left
  have i₂ : patch sZ C.φ (O₁ ⊓ O₂) ≤ patch sZ C.φ O₂ := patch_mono n sZ inf_le_right
  refine ⟨O₁ ⊓ O₂, ⟨hO₁.1, hO₁.2, hO₂.2⟩,
    (Ωan sZ p).val.presheaf.map (homOfLE i₁).op s₁ + (Ωan sZ p).val.presheaf.map (homOfLE i₂).op s₂,
    Submodule.add_mem _ (map_mem_chartSpan n sZ C k p i₁ hs₁) (map_mem_chartSpan n sZ C k p i₂ hs₂),
    ?_⟩
  rw [map_add]
  congr 1 <;> exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem smul_mem_chartGerms {y : ComplexPoints sZ} (C : ChartData sZ n Θ y) (k p : ℕ) :
    letI : Module ((analytification sZ).presheaf.stalk y)
        ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ)
          (Ωan sZ p).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (Ωan sZ p).val y
    ∀ (r : (analytification sZ).presheaf.stalk y) {g}, g ∈ chartGerms n sZ C k p →
      r • g ∈ chartGerms n sZ C k p := by
  letI : Module ((analytification sZ).presheaf.stalk y)
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ)
        (Ωan sZ p).val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (Ωan sZ p).val y
  rintro r _ ⟨O, hO, s, hs, rfl⟩
  obtain ⟨V, hyV, a, rfl⟩ := TopCat.Presheaf.germ_exist (analytification sZ).presheaf r
  let O' : Opens (EuclideanSpace ℂ (Fin n)) :=
    O ⊓ ⟨C.φ '' (C.φ.source ∩ V), C.φ.isOpen_image_source_inter V.2⟩
  have hO'O : patch sZ C.φ O' ≤ patch sZ C.φ O := patch_mono n sZ inf_le_left
  have hO'V : patch sZ C.φ O' ≤ V := by
    rintro y' ⟨hy's, -, y'', ⟨hy''s, hy''V⟩, hφ⟩
    rwa [← C.φ.injOn hy''s hy's hφ]
  have hyO' : y ∈ patch sZ C.φ O' := ⟨C.hy, hO.2, y, ⟨C.hy, hyV⟩, rfl⟩
  refine ⟨O', hyO',
    (show (ringCatSheaf sZ).obj.obj (op (patch sZ C.φ O')) from
      (analytification sZ).presheaf.map (homOfLE hO'V).op a) •
      (Ωan sZ p).val.presheaf.map (homOfLE hO'O).op s,
    Submodule.smul_mem _ _ (map_mem_chartSpan n sZ C k p hO'O hs), ?_⟩
  erw [PresheafOfModules.germ_smul, TopCat.Presheaf.germ_res_apply]
  congr 1
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- The stalk map of a morphism of analytic modules is linear over the analytic local ring. -/
private theorem stalkFunctor_map_smul {F G : SheafOfModules.{0} (ringCatSheaf sZ)} (φ : F ⟶ G)
    (y : ComplexPoints sZ) :
    letI : Module ((analytification sZ).presheaf.stalk y)
        ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ) F.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val y
    letI : Module ((analytification sZ).presheaf.stalk y)
        ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ) G.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val y
    ∀ (r : (analytification sZ).presheaf.stalk y)
      (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ) F.val.presheaf y),
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
          ((PresheafOfModules.toPresheaf _).map φ.val) (r • m) =
        r • (show TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ)
          G.val.presheaf y from (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
          ((PresheafOfModules.toPresheaf _).map φ.val) m) := by
  letI : Module ((analytification sZ).presheaf.stalk y)
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ) F.val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val y
  letI : Module ((analytification sZ).presheaf.stalk y)
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ) G.val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val y
  intro r m
  obtain ⟨V, hyV, a, rfl⟩ := TopCat.Presheaf.germ_exist (analytification sZ).presheaf r
  obtain ⟨V', hyV', t, rfl⟩ := TopCat.Presheaf.germ_exist F.val.presheaf m
  have i₁ : V ⊓ V' ≤ V := inf_le_left
  have i₂ : V ⊓ V' ≤ V' := inf_le_right
  have hy : y ∈ V ⊓ V' := ⟨hyV, hyV'⟩
  have e1 : TopCat.Presheaf.germ (analytification sZ).presheaf V y hyV a =
      TopCat.Presheaf.germ (analytification sZ).presheaf (V ⊓ V') y hy
        ((analytification sZ).presheaf.map (homOfLE i₁).op a) :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  have e2 : TopCat.Presheaf.germ F.val.presheaf V' y hyV' t =
      TopCat.Presheaf.germ F.val.presheaf (V ⊓ V') y hy (F.val.presheaf.map (homOfLE i₂).op t) :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  rw [e1, e2]
  erw [← PresheafOfModules.germ_smul, TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [(φ.val.app (op (V ⊓ V'))).hom.map_smul, PresheafOfModules.germ_smul]
  rfl

/-- The values at the chart centre of the coordinates of a chart. -/
private noncomputable def chartCentre {y : ComplexPoints sZ} (C : ChartData sZ n Θ y) :
    Fin n → ℂ :=
  fun j => evalHom C.W ⟨y, C.hφ C.hy⟩ (C.z j)

/-- A form on a chart patch is a holomorphic combination of the twisted logarithmic forms of the
chart. -/
private def chartHolSub {y : ComplexPoints sZ} (C : ChartData sZ n Θ y) (k : ℕ) (hk : k ≤ n)
    (p : ℕ) (O : Opens (EuclideanSpace ℂ (Fin n)))
    (η : patch sZ C.φ O → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ) : Prop :=
  ∃ ξ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ,
    DifferentiableOn ℂ ξ (C.φ.target ∩ O) ∧ (∀ y' : patch sZ C.φ O, ξ (C.φ y') = η y') ∧
      HolSubOn k hk (chartCentre n sZ C) (C.φ.target ∩ O) ξ

/-- The chart centre is sent to `0`. -/
private theorem chart_apply_self {y : ComplexPoints sZ} (C : ChartData sZ n Θ y) : C.φ y = 0 := by
  ext i
  rw [C.coord y C.hy i, sub_self]
  rfl

/-- **The holomorphic differential preserves the twisted forms**: the germ of `δan` of a germ of a
combination of twisted generators is again one. -/
private theorem stalk_δan_mem_chartGerms {hΘ : ∀ (V : Z.Opens) (g : Γ(Z, V))
      (y : (Opens.map (toSchemeHom sZ)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sZ).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g}
    (Cf : ∀ y, ChartData sZ n Θ y) {y : ComplexPoints sZ} {k : ℕ} (hk : k ≤ n)
    (hS : ∀ p O (η : patch sZ (Cf y).φ O → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ),
      η ∈ (Cf y).Ψ p O '' (chartSpan n sZ (Cf y) k p O : Set _) ↔
        chartHolSub n sZ (Cf y) k hk p O η)
    (p : ℕ) {g} (hg : g ∈ chartGerms n sZ (Cf y) k p) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map (δan sZ hΘ Cf p).hom g ∈
      chartGerms n sZ (Cf y) k (p + 1) := by
  obtain ⟨O, hO, s, hs, rfl⟩ := hg
  obtain ⟨ξ, hξd, hξ, hhol⟩ := (hS p O _).1 ⟨s, hs, rfl⟩
  have h0 := chart_apply_self n sZ (Cf y)
  have hA : IsOpen ((Cf y).φ.target ∩ (O : Set (EuclideanSpace ℂ (Fin n)))) :=
    (Cf y).φ.open_target.inter O.2
  obtain ⟨r, hr0, hball, hrc⟩ := exists_ball_subset_le_norm hA
    (h0 ▸ ⟨(Cf y).φ.map_source (Cf y).hy, hO.2⟩) k (chartCentre n sZ (Cf y))
  let O' : Opens (EuclideanSpace ℂ (Fin n)) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  have hO'O : patch sZ (Cf y).φ O' ≤ patch sZ (Cf y).φ O :=
    patch_mono n sZ fun v hv => (hball hv).2
  have hyO' : y ∈ patch sZ (Cf y).φ O' := ⟨(Cf y).hy, by
    change (Cf y).φ y ∈ Metric.ball 0 r
    rw [h0]; exact Metric.mem_ball_self hr0⟩
  have hv := vanishesAlong_of_holSubOn k hk _ hA hξd.continuousOn hhol
  have hvb : VanishesAlong (boundaryCoords k (chartCentre n sZ (Cf y))) (Metric.ball 0 r) ξ :=
    fun l hl v hv' => hv l hl v (hball hv')
  have hξb : DifferentiableOn ℂ ξ (Metric.ball 0 r) := hξd.mono hball
  have hdv := vanishesAlong_extDeriv Metric.isOpen_ball _ hξb hvb
  have hdξ : DifferentiableOn ℂ (extDeriv ξ) (Metric.ball 0 r) :=
    differentiableOn_extDeriv Metric.isOpen_ball hξb
  have hhol' := holSubOn_of_vanishesAlong k hk _ hrc hdξ hdv
  let t := (Ωan sZ p).val.presheaf.map (homOfLE hO'O).op s
  have hΨt : ∀ y' : patch sZ (Cf y).φ O', ξ ((Cf y).φ y') = (Cf y).Ψ p O' t y' := fun y' =>
    (hξ ⟨y'.1, hO'O y'.2⟩).trans ((Cf y).restr p O' O hO'O s y').symm
  have hδ : ∀ y' : patch sZ (Cf y).φ O',
      (Cf y).Ψ (p + 1) O' (δP sZ (Cf y) O' t) y' = extDeriv ξ ((Cf y).φ y') :=
    Ψ_δP_of_ext sZ (Cf y) O' t ξ hΨt
  have htgt : (Cf y).φ.target ∩ (O' : Set (EuclideanSpace ℂ (Fin n))) = Metric.ball 0 r :=
    Set.inter_eq_right.2 fun v hv => (hball hv).1
  have hmem : chartHolSub n sZ (Cf y) k hk (p + 1) O' ((Cf y).Ψ (p + 1) O' (δP sZ (Cf y) O' t)) :=
    ⟨extDeriv ξ, htgt ▸ hdξ, fun y' => (hδ y').symm, htgt ▸ hhol'⟩
  obtain ⟨s', hs', hs'eq⟩ := (hS (p + 1) O' _).2 hmem
  have hs'' : s' = δP sZ (Cf y) O' t := (Cf y).inj _ _ hs'eq
  refine ⟨O', hyO', δP sZ (Cf y) O' t, hs'' ▸ hs', ?_⟩
  have e1 : TopCat.Presheaf.germ (Ωan sZ p).val.presheaf (patch sZ (Cf y).φ O) y hO s =
      TopCat.Presheaf.germ (Ωan sZ p).val.presheaf (patch sZ (Cf y).φ O') y hyO' t :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  rw [e1]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  congr 1
  exact (δan_app_patch sZ hΘ Cf p ⟨y, O'⟩ t).symm

end ChartForms

/-! ### Twisted log forms in holomorphic charts -/

section ChartLog

open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints MMP.DeRhamBetti
open MMP.Mori.Divisor.LogSpreadingProof.G1
open scoped Manifold ContDiff

variable (n : ℕ) {Z : Scheme.{0}} (sZ : Z ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n sZ] (E : MMP.Mori.Divisor Z) (hE : E.IsRelativeSNC n sZ)
  [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sZ)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sZ)]
  {Θ : structureSheaf sZ ≅ 𝒪[n, ComplexPoints sZ]}

/-- The analytification of the regular extension `Ω^p(log E)(-E) ⟶ Ω^p`. -/
private noncomputable abbrev ιan (p : ℕ) :=
  (analytifyModule sZ).map (logToForms sZ ((isLocalSectionRel_twisted sZ hE
    (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p))

/-- The analytification of the regular extension on the image of an algebraic section. -/
private theorem ιan_unit (p : ℕ) (V : Z.Opens)
    (ℓ : (logModule n sZ E hE E.suppIdeal p).val.obj (op V)) :
    (ιan n sZ E hE p).val.app (op ((Opens.map (toSchemeHom sZ)).obj V))
        ((analytifyModuleUnit sZ _).val.app (op V) ℓ) =
      (analytifyModuleUnit sZ (sZ.relativeDifferentialForms (p : ℤ))).val.app (op V)
        ((logToForms sZ ((isLocalSectionRel_twisted sZ hE
          (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p)).val.app (op V) ℓ) := by
  have h := (SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sZ)).unit.naturality
    (logToForms sZ ((isLocalSectionRel_twisted sZ hE
      (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p))
  exact (ConcreteCategory.congr_hom (congrArg (fun f => f.val.app (op V)) h) ℓ).symm

/-- `an` is additive. -/
private theorem an_sum (p : ℕ) (V : Z.Opens) (U : Opens (space sZ))
    (h : U ≤ (Opens.map (toSchemeHom sZ)).obj V) {ι : Type*} (S : Finset ι)
    (f : ι → Γ(sZ.relativeDifferentialForms (p : ℤ), V)) :
    an sZ p V U h (∑ i ∈ S, f i) = ∑ i ∈ S, an sZ p V U h (f i) := by
  unfold an
  erw [map_sum, map_sum]
  rfl

set_option maxRecDepth 40000 in
include hE in
/-- **The analytified twisted log forms are, near each point, combinations of the twisted
generators** of an adapted chart. -/
private theorem germ_ιan_mem_chartGerms [QuasiCompact sZ] {y : ComplexPoints sZ}
    (C : ChartData sZ n Θ y) {k : ℕ} (hk : k ≤ n)
    (hb : letI := MMP.Mori.sectionAlgebra sZ C.W
      ∃ b : Module.Basis (Fin n) Γ(Z, C.W) Ω[Γ(Z, C.W)⁄ℂ],
        ∀ i, b i = KaehlerDifferential.D ℂ Γ(Z, C.W) (C.z i))
    (hzero : ∀ w ∈ C.W, (∃ D ∈ E.support, w ∈ D.support) ↔
      w ∉ Z.basicOpen (∏ i : Fin k, C.z (Fin.castLE hk i)))
    (p : ℕ) (V : Opens (space sZ)) (hy : y ∈ V)
    (t : ((analytifyModule sZ).obj (logModule n sZ E hE E.suppIdeal p)).val.obj (op V)) :
    TopCat.Presheaf.germ (Ωan sZ p).val.presheaf V y hy
        ((ιan n sZ E hE p).val.app (op V) t) ∈ chartGerms n sZ C k p := by
  letI := MMP.Mori.sectionAlgebra sZ C.W
  haveI : Smooth sZ := SmoothOfRelativeDimension.smooth n sZ
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : (logModule n sZ E hE E.suppIdeal p).IsCoherent := G1.logModule_isCoherent hE true p
  haveI := _root_.isQuasicoherent_of_isCoherent (logModule n sZ E hE E.suppIdeal p)
  have hyW : y.toScheme ∈ C.W := mem_chart_iff.1 (C.hφ C.hy)
  have hg : TopCat.Presheaf.germ (Ωan sZ p).val.presheaf V y hy
      ((ιan n sZ E hE p).val.app (op V) t) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
        ((PresheafOfModules.toPresheaf _).map (ιan n sZ E hE p).val)
        (TopCat.Presheaf.germ ((analytifyModule sZ).obj
          (logModule n sZ E hE E.suppIdeal p)).val.presheaf V y hy t) := by
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl
  rw [hg]
  have hspan := mem_span_germ_analytifyModuleUnit_of_isAffineOpen sZ
    (logModule n sZ E hE E.suppIdeal p) C.hW y hyW
    (TopCat.Presheaf.germ ((analytifyModule sZ).obj (logModule n sZ E hE E.suppIdeal p)).val.presheaf
      V y hy t)
  generalize TopCat.Presheaf.germ ((analytifyModule sZ).obj
    (logModule n sZ E hE E.suppIdeal p)).val.presheaf V y hy t = m at hspan ⊢
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ℓ, rfl⟩ := hx
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    erw [ιan_unit n sZ E hE p C.W ℓ]
    obtain ⟨a, ha⟩ := exists_formsAlgEquiv_logToForms_eq_sum n sZ E hE ⟨C.W, C.hW⟩ hk C.z hb
      hzero p ℓ
    have hℓ : (logToForms sZ ((isLocalSectionRel_twisted sZ hE
        (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p)).val.app (op C.W) ℓ =
        ∑ I, a I • (MMP.DeRham.formsAlgEquiv sZ p ⟨C.W, C.hW⟩).symm
          (twistedGen n sZ ⟨C.W, C.hW⟩ k C.z p I) := by
      apply (MMP.DeRham.formsAlgEquiv sZ p ⟨C.W, C.hW⟩).injective
      erw [ha, map_sum]
      simp only [map_smul, LinearEquiv.apply_symm_apply]
    refine ⟨⊤, ⟨C.hy, Set.mem_univ _⟩, an sZ p C.W (patch sZ C.φ ⊤) (patch_le_W sZ C ⊤)
      ((logToForms sZ ((isLocalSectionRel_twisted sZ hE
        (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p)).val.app (op C.W) ℓ), ?_, ?_⟩
    · rw [hℓ, an_sum]
      refine Submodule.sum_mem _ fun I _ => ?_
      rw [an_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨I, rfl⟩)
    · exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  | zero => erw [map_zero]; exact zero_mem_chartGerms n sZ C k p
  | add x x' _ _ hx hx' => erw [map_add]; exact add_mem_chartGerms n sZ C k p hx hx'
  | smul r x _ hx =>
    erw [stalkFunctor_map_smul sZ (ιan n sZ E hE p) y r x]
    exact smul_mem_chartGerms n sZ C k p r hx

/-- The analytification of the quotient map `Ω^p ⟶ 𝒟_E^p`. -/
private noncomputable abbrev πan (p : ℕ) :=
  (analytifyModule sZ).map (cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
    (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p)))

private theorem ιan_comp_πan (p : ℕ) : ιan n sZ E hE p ≫ πan n sZ E hE p = 0 := by
  haveI : (analytifyModule sZ).IsLeftAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sZ)).isLeftAdjoint
  haveI := Functor.preservesZeroMorphisms_of_isLeftAdjoint (analytifyModule sZ)
  rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]

include hE in
/-- **The analytified quotient map kills the twisted generators.** -/
private theorem πan_eq_zero_of_mem_chartSpan {y : ComplexPoints sZ} (C : ChartData sZ n Θ y)
    {k : ℕ} (hk : k ≤ n)
    (hb : letI := MMP.Mori.sectionAlgebra sZ C.W
      ∃ b : Module.Basis (Fin n) Γ(Z, C.W) Ω[Γ(Z, C.W)⁄ℂ],
        ∀ i, b i = KaehlerDifferential.D ℂ Γ(Z, C.W) (C.z i))
    (hzero : ∀ w ∈ C.W, (∃ D ∈ E.support, w ∈ D.support) ↔
      w ∉ Z.basicOpen (∏ i : Fin k, C.z (Fin.castLE hk i)))
    (p : ℕ) (O : Opens (EuclideanSpace ℂ (Fin n))) {s} (hs : s ∈ chartSpan n sZ C k p O) :
    (πan n sZ E hE p).val.app (op (patch sZ C.φ O)) s = 0 := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, rfl⟩ := hx
    obtain ⟨ℓ, hℓ⟩ := exists_formsAlgEquiv_logToForms_eq_twistedGen n sZ E hE ⟨C.W, C.hW⟩ hk C.z
      hb hzero p I
    have h1 : (MMP.DeRham.formsAlgEquiv sZ p ⟨C.W, C.hW⟩).symm
        (twistedGen n sZ ⟨C.W, C.hW⟩ k C.z p I) =
        (logToForms sZ ((isLocalSectionRel_twisted sZ hE
          (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p)).val.app (op C.W) ℓ := by
      rw [← hℓ]
      exact LinearEquiv.symm_apply_apply _ _
    beta_reduce
    erw [h1]
    unfold an
    rw [← ιan_unit n sZ E hE p C.W ℓ]
    have h3 := ConcreteCategory.congr_hom (congrArg (fun f => f.val.app
      (op ((Opens.map (toSchemeHom sZ)).obj C.W))) (ιan_comp_πan n sZ E hE p))
      ((analytifyModuleUnit sZ _).val.app (op C.W) ℓ)
    refine (ConcreteCategory.congr_hom ((πan n sZ E hE p).val.naturality
      (homOfLE (patch_le_W sZ C O)).op) _).trans ?_
    erw [ConcreteCategory.comp_apply, h3, map_zero]
    rfl
  | zero => exact map_zero _
  | add x x' _ _ hx hx' => rw [map_add, hx, hx', add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

include hE in
/-- **The holomorphic differential preserves the analytified twisted log forms**: their image in
`Ω^{p+1}_an` maps to zero in the analytified quotient. -/
private theorem ιan_comp_δan_comp_πan [QuasiCompact sZ] {hΘ : ∀ (V : Z.Opens) (g : Γ(Z, V))
      (y : (Opens.map (toSchemeHom sZ)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sZ).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g}
    (Cf : ∀ y, ChartData sZ n Θ y) (kf : ComplexPoints sZ → ℕ) (hkf : ∀ y, kf y ≤ n)
    (hbf : ∀ y, letI := MMP.Mori.sectionAlgebra sZ (Cf y).W
      ∃ b : Module.Basis (Fin n) Γ(Z, (Cf y).W) Ω[Γ(Z, (Cf y).W)⁄ℂ],
        ∀ i, b i = KaehlerDifferential.D ℂ Γ(Z, (Cf y).W) ((Cf y).z i))
    (hzf : ∀ y, ∀ w ∈ (Cf y).W, (∃ D ∈ E.support, w ∈ D.support) ↔
      w ∉ Z.basicOpen (∏ i : Fin (kf y), (Cf y).z (Fin.castLE (hkf y) i)))
    (hSf : ∀ y p O (η : patch sZ (Cf y).φ O → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ),
      η ∈ (Cf y).Ψ p O '' (chartSpan n sZ (Cf y) (kf y) p O : Set _) ↔
        chartHolSub n sZ (Cf y) (kf y) (hkf y) p O η)
    (p : ℕ) :
    (SheafOfModules.toSheaf _).map (ιan n sZ E hE p) ≫ δan sZ hΘ Cf p ≫
      (SheafOfModules.toSheaf _).map (πan n sZ E hE (p + 1)) = 0 := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
  ext t
  refine TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf _).obj ((analytifyModule sZ).obj
    (cokernel (logToForms sZ ((isLocalSectionRel_twisted sZ hE
      (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) (p + 1)))))) U.unop _ _ fun x hx => ?_
  have h1 := germ_ιan_mem_chartGerms n sZ E hE (Cf x) (hkf x) (hbf x) (hzf x) p U.unop hx t
  obtain ⟨O, hO, s, hs, hg⟩ := stalk_δan_mem_chartGerms n sZ (hΘ := hΘ) Cf (hkf x) (hSf x) p h1
  have hz := πan_eq_zero_of_mem_chartSpan n sZ E hE (Cf x) (hkf x) (hbf x) (hzf x) (p + 1) O hs
  have e1 := congrArg ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
    ((PresheafOfModules.toPresheaf _).map (πan n sZ E hE (p + 1)).val)) hg
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hz, map_zero] at e1
  erw [map_zero]
  refine Eq.trans ?_ e1.symm
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

/-- **Charts adapted to `E` at every point**, with the holomorphic description of the twisted forms
supplied by `MMP.Analytic.analytification_smooth_differentials_of_smoothOfRelativeDimension`. -/
private structure AdaptedCharts where
  /-- The identification of the analytic structure sheaf with the holomorphic functions. -/
  Θ : structureSheaf sZ ≅ 𝒪[n, ComplexPoints sZ]
  hΘ : ∀ (V : Z.Opens) (g : Γ(Z, V)) (y : (Opens.map (toSchemeHom sZ)).obj V),
    Θ.hom.hom.app (op _) ((analytificationHom sZ).hom.c.app (op V) g) y =
      evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g
  /-- The chart at a point. -/
  C : ∀ y, ChartData sZ n Θ y
  /-- The number of components of `E` through the chart centre. -/
  k : ComplexPoints sZ → ℕ
  hk : ∀ y, k y ≤ n
  hb : ∀ y, letI := MMP.Mori.sectionAlgebra sZ (C y).W
    ∃ b : Module.Basis (Fin n) Γ(Z, (C y).W) Ω[Γ(Z, (C y).W)⁄ℂ],
      ∀ i, b i = KaehlerDifferential.D ℂ Γ(Z, (C y).W) ((C y).z i)
  hzero : ∀ y, ∀ w ∈ (C y).W, (∃ D ∈ E.support, w ∈ D.support) ↔
    w ∉ Z.basicOpen (∏ i : Fin (k y), (C y).z (Fin.castLE (hk y) i))
  hS : ∀ y p O (η : patch sZ (C y).φ O → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ),
    η ∈ (C y).Ψ p O '' (chartSpan n sZ (C y) (k y) p O : Set _) ↔
      chartHolSub n sZ (C y) (k y) (hk y) p O η

variable {n sZ E}

/-- The analytification of modules followed by the underlying abelian sheaves. -/
private noncomputable abbrev anToSheaf : Z.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{0} (space sZ) :=
  analytifyModule sZ ⋙ SheafOfModules.toSheaf _

private theorem preservesFiniteColimits_anToSheaf [LocallyOfFiniteType sZ] [QuasiCompact sZ] :
    PreservesFiniteColimits (anToSheaf (sZ := sZ)) := by
  haveI := (MMP.Analytic.analytification_stalks sZ).2.2.2.2.1
  haveI : PreservesFiniteColimits (SheafOfModules.toSheaf (MMP.Analytic.ringCatSheaf sZ)) :=
    Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits _ _
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ (analytifyModule sZ)
    (SheafOfModules.toSheaf (MMP.Analytic.ringCatSheaf sZ)) ‹_› this

/-- The analytified quotient, as a cokernel of abelian sheaves. -/
private noncomputable def anCokernelIso [LocallyOfFiniteType sZ] [QuasiCompact sZ] (p : ℕ) :
    (SheafOfModules.toSheaf _).obj ((analytifyModule sZ).obj (cokernel (logToForms sZ
      ((isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p)))) ≅
      cokernel ((SheafOfModules.toSheaf _).map (ιan n sZ E hE p)) :=
  haveI := preservesFiniteColimits_anToSheaf (sZ := sZ)
  PreservesCokernel.iso (anToSheaf (sZ := sZ)) _

private theorem πan_comp_anCokernelIso_hom [LocallyOfFiniteType sZ] [QuasiCompact sZ] (p : ℕ) :
    (SheafOfModules.toSheaf _).map (πan n sZ E hE p) ≫ (anCokernelIso hE p).hom =
      cokernel.π ((SheafOfModules.toSheaf _).map (ιan n sZ E hE p)) :=
  haveI := preservesFiniteColimits_anToSheaf (sZ := sZ)
  PreservesCokernel.π_iso_hom (anToSheaf (sZ := sZ)) _

/-- **The holomorphic differential of the analytic restriction complex.** -/
private noncomputable def δanD [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (A : AdaptedCharts n sZ E) (p : ℕ) :
    (SheafOfModules.toSheaf _).obj ((analytifyModule sZ).obj (cokernel (logToForms sZ
      ((isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) p)))) ⟶
    (SheafOfModules.toSheaf _).obj ((analytifyModule sZ).obj (cokernel (logToForms sZ
      ((isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE))
        (p + 1))))) :=
  (anCokernelIso hE p).hom ≫ cokernel.desc _ (δan sZ A.hΘ A.C p ≫
    (SheafOfModules.toSheaf _).map (πan n sZ E hE (p + 1)))
    (ιan_comp_δan_comp_πan n sZ E hE (hΘ := A.hΘ) A.C A.k A.hk A.hb A.hzero A.hS p)

private theorem πan_comp_δanD [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (A : AdaptedCharts n sZ E) (p : ℕ) :
    (SheafOfModules.toSheaf _).map (πan n sZ E hE p) ≫ δanD hE A p =
      δan sZ A.hΘ A.C p ≫ (SheafOfModules.toSheaf _).map (πan n sZ E hE (p + 1)) := by
  rw [δanD, ← Category.assoc, πan_comp_anCokernelIso_hom, cokernel.π_desc]

private theorem epi_toSheaf_πan [LocallyOfFiniteType sZ] [QuasiCompact sZ] (p : ℕ) :
    Epi ((SheafOfModules.toSheaf _).map (πan n sZ E hE p)) := by
  have h := πan_comp_anCokernelIso_hom hE p
  rw [show (SheafOfModules.toSheaf _).map (πan n sZ E hE p) =
      cokernel.π ((SheafOfModules.toSheaf _).map (ιan n sZ E hE p)) ≫ (anCokernelIso hE p).inv by
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]]
  infer_instance

private theorem δanD_comp [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (A : AdaptedCharts n sZ E) (p : ℕ) : δanD hE A p ≫ δanD hE A (p + 1) = 0 := by
  haveI := epi_toSheaf_πan hE p
  rw [← cancel_epi ((SheafOfModules.toSheaf _).map (πan n sZ E hE p)), comp_zero,
    ← Category.assoc, πan_comp_δanD, Category.assoc, πan_comp_δanD, ← Category.assoc,
    δan_comp_δan, zero_comp]

/-- The analytified sequence `Ω^p(log E)(-E)^an ⟶ (Ω^p)^an ⟶ (𝒟_E^p)^an`, as a short complex of
abelian sheaves. -/
private noncomputable abbrev anSC [LocallyOfFiniteType sZ] [QuasiCompact sZ] (p : ℕ) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (space sZ)) :=
  ShortComplex.mk ((SheafOfModules.toSheaf _).map (ιan n sZ E hE p))
    ((SheafOfModules.toSheaf _).map (πan n sZ E hE p))
    ((Functor.map_comp _ _ _).symm.trans ((congrArg (SheafOfModules.toSheaf _).map
      (ιan_comp_πan n sZ E hE p)).trans (Functor.map_zero _ _ _)))

private theorem exact_anSC [LocallyOfFiniteType sZ] [QuasiCompact sZ] (p : ℕ) :
    (anSC hE p).Exact := by
  have h := ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk ((SheafOfModules.toSheaf _).map (ιan n sZ E hE p)) (cokernel.π _)
      (cokernel.condition _)) (cokernelIsCokernel _)
  refine (ShortComplex.exact_iff_of_iso ?_).2 h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (anCokernelIso hE p)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (πan_comp_anCokernelIso_hom hE p).symm)

/-- **A germ of an analytic form maps to zero in the analytified quotient exactly when it is a
germ of a combination of twisted generators.** -/
private theorem stalk_πan_eq_zero_iff [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (A : AdaptedCharts n sZ E) (y : ComplexPoints sZ) (p : ℕ)
    (g : TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ)
      (Ωan sZ p).val.presheaf y) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
        ((SheafOfModules.toSheaf _).map (πan n sZ E hE p)).hom g = 0 ↔
      g ∈ chartGerms n sZ (A.C y) (A.k y) p := by
  constructor
  · intro hg
    have hS := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).1 (exact_anSC hE p) y
    rw [ShortComplex.ab_exact_iff] at hS
    obtain ⟨l, hl⟩ := hS g hg
    obtain ⟨U, hyU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ l
    have h1 := germ_ιan_mem_chartGerms n sZ E hE (A.C y) (A.hk y) (A.hb y) (A.hzero y) p U hyU t
    rw [← hl]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact h1
  · rintro ⟨O, hO, s, hs, rfl⟩
    have hz := πan_eq_zero_of_mem_chartSpan n sZ E hE (A.C y) (A.hk y) (A.hb y) (A.hzero y) p O hs
    refine (TopCat.Presheaf.stalkFunctor_map_germ_apply _ y hO
      ((SheafOfModules.toSheaf _).map (πan n sZ E hE p)).hom s).trans ?_
    erw [hz]
    exact map_zero _

/-- **The twisted Poincaré lemma on a chart ball**: on a small ball about the chart centre, an
analytic form whose holomorphic differential is a combination of twisted generators is, up to such
a combination, a holomorphic differential. -/
private theorem exists_eq_δP_add_of_mem_chartSpan (A : AdaptedCharts n sZ E) (y : ComplexPoints sZ)
    (p : ℕ) {r : ℝ} (O : Opens (EuclideanSpace ℂ (Fin n)))
    (hOb : (O : Set (EuclideanSpace ℂ (Fin n))) = Metric.ball 0 r) (hball : Metric.ball (0 : EuclideanSpace ℂ (Fin n)) r ⊆ (A.C y).φ.target)
    (hrc : ∀ j : Fin n, (j : ℕ) < A.k y → chartCentre n sZ (A.C y) j ≠ 0 →
      r ≤ ‖chartCentre n sZ (A.C y) j‖)
    (om : (Ωan sZ (p + 1)).val.obj (op (patch sZ (A.C y).φ O)))
    (hom0 : δP sZ (A.C y) O om ∈
      chartSpan n sZ (A.C y) (A.k y) (p + 1 + 1) O) :
    ∃ (η : (Ωan sZ p).val.obj (op (patch sZ (A.C y).φ O)))
      (σ : (Ωan sZ (p + 1)).val.obj
        (op (patch sZ (A.C y).φ O))),
      σ ∈ chartSpan n sZ (A.C y) (A.k y) (p + 1) O ∧
        om = δP sZ (A.C y) O η + σ := by
  have htgt : (A.C y).φ.target ∩ (O : Set (EuclideanSpace ℂ (Fin n))) = Metric.ball 0 r := by
    rw [hOb]; exact Set.inter_eq_right.2 hball
  have hpatch : ∀ v ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin n)) r,
      (A.C y).φ.symm v ∈ patch sZ (A.C y).φ O := fun v hv =>
    ⟨(A.C y).φ.map_target (hball hv), by
      change (A.C y).φ ((A.C y).φ.symm v) ∈ (O : Set (EuclideanSpace ℂ (Fin n)))
      rw [(A.C y).φ.right_inv (hball hv), hOb]; exact hv⟩
  obtain ⟨hξd, hξ⟩ := holExt_spec sZ (A.C y) O om
  have hδ := Ψ_δP sZ (A.C y) O om
  obtain ⟨ξ', hξ'd, hξ'eq, hhol⟩ := (A.hS y (p + 1 + 1) O _).1 ⟨_, hom0, rfl⟩
  have heq : ∀ v ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin n)) r,
      extDeriv (holExt sZ (A.C y) O om) v = ξ' v := by
    intro v hv
    have h1 := (hξ'eq ⟨_, hpatch v hv⟩).trans (hδ ⟨_, hpatch v hv⟩)
    simp only [(A.C y).φ.right_inv (hball hv)] at h1
    exact h1.symm
  have hholξ : HolSubOn (A.k y) (A.hk y) (chartCentre n sZ (A.C y)) (Metric.ball 0 r)
      (extDeriv (holExt sZ (A.C y) O om)) :=
    holSubOn_congr _ _ _ heq (htgt ▸ hhol)
  obtain ⟨η, hηd, σ, hσd, hσhol, hdec⟩ := exists_eq_extDeriv_add_of_holSubOn_extDeriv _ (A.hk y)
    _ hrc (htgt ▸ hξd) hholξ
  obtain ⟨η', hη'⟩ := ((A.C y).range p O (fun y' => η ((A.C y).φ y'))).2 ⟨η, htgt ▸ hηd, fun _ => rfl⟩
  obtain ⟨σ', hσ'⟩ := ((A.C y).range (p + 1) O (fun y' => σ ((A.C y).φ y'))).2 ⟨σ, htgt ▸ hσd, fun _ => rfl⟩
  obtain ⟨σ'', hσ''mem, hσ''⟩ := (A.hS y (p + 1) O _).2
    ⟨σ, htgt ▸ hσd, fun y' => (congrFun hσ' y').symm, htgt ▸ hσhol⟩
  have hσeq : σ'' = σ' := (A.C y).inj _ _ hσ''
  refine ⟨η', σ', hσeq ▸ hσ''mem, (A.C y).inj (p + 1) O ?_⟩
  funext y'
  have hy'b : (A.C y).φ y' ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin n)) r := hOb ▸ y'.2.2
  rw [map_add, Pi.add_apply, Ψ_δP_of_ext sZ (A.C y) O η' η (fun y'' => (congrFun hη' y'').symm) y',
    congrFun hσ' y', ← hξ y', hdec _ hy'b]

/-- A chart ball about a point, inside an open set, of radius at most the norms of the nonzero
coordinates of the chart centre. -/
private theorem exists_ball_patch_le (A : AdaptedCharts n sZ E) (y : ComplexPoints sZ)
    (W : Opens (space sZ)) (hyW : y ∈ W) :
    ∃ r > 0, Metric.ball (0 : EuclideanSpace ℂ (Fin n)) r ⊆ (A.C y).φ.target ∧
      patch sZ (A.C y).φ ⟨Metric.ball 0 r, Metric.isOpen_ball⟩ ≤ W ∧
      ∀ j : Fin n, (j : ℕ) < A.k y → chartCentre n sZ (A.C y) j ≠ 0 →
        r ≤ ‖chartCentre n sZ (A.C y) j‖ := by
  obtain ⟨r₁, hr₁, hb₁, hp₁⟩ := exists_ball_patch sZ (A.C y) W hyW
  rw [chart_apply_self n sZ (A.C y)] at hb₁ hp₁
  obtain ⟨r, hr, hb, hrc⟩ := exists_ball_subset_le_norm Metric.isOpen_ball
    (Metric.mem_ball_self hr₁) (A.k y) (chartCentre n sZ (A.C y))
  exact ⟨r, hr, hb.trans hb₁, fun y' hy' => hp₁ ⟨hy'.1, hb hy'.2⟩, hrc⟩

/-- **The analytic restriction complex is exact in positive degrees.** -/
private theorem exact_δanD [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (A : AdaptedCharts n sZ E) (p : ℕ) :
    (ShortComplex.mk (δanD hE A p) (δanD hE A (p + 1)) (δanD_comp hE A p)).Exact := by
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (C := AddCommGrpCat.{0})
    (X := space sZ) _).2 fun y => ?_
  rw [ShortComplex.ab_exact_iff]
  intro e he
  obtain ⟨γ, rfl⟩ := @stalkFunctor_map_surjective_of_epi _ _ _
    ((SheafOfModules.toSheaf _).map (πan n sZ E hE (p + 1))) (epi_toSheaf_πan hE (p + 1)) y e
  obtain ⟨U, hyU, om, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ γ
  -- the differential of the lift is twisted at `y`
  have hsec := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op U))
    (πan_comp_δanD hE A (p + 1))) om
  have key : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
      ((SheafOfModules.toSheaf _).map (πan n sZ E hE (p + 1 + 1))).hom
        (TopCat.Presheaf.germ (Ωan sZ (p + 1 + 1)).val.presheaf U y hyU
          ((δan sZ A.hΘ A.C (p + 1)).hom.app (op U) om)) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map (δanD hE A (p + 1)).hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
          ((SheafOfModules.toSheaf _).map (πan n sZ E hE (p + 1))).hom
          (TopCat.Presheaf.germ (Ωan sZ (p + 1)).val.presheaf U y hyU om)) := by
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact congrArg _ hsec.symm
  have hm := (stalk_πan_eq_zero_iff hE A y (p + 1 + 1) _).1 (key.trans he)
  obtain ⟨O', hO', s', hs', hg'⟩ := hm
  obtain ⟨W, hyW, iW, iW', hW⟩ := TopCat.Presheaf.germ_eq _ y hO' hyU _ _ hg'
  obtain ⟨r, hr, hball, hpW, hrc⟩ := exists_ball_patch_le A y W hyW
  set O : Opens (EuclideanSpace ℂ (Fin n)) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩ with hOdef
  have hyO : y ∈ patch sZ (A.C y).φ O := ⟨(A.C y).hy, by
    change (A.C y).φ y ∈ Metric.ball 0 r
    rw [chart_apply_self n sZ (A.C y)]; exact Metric.mem_ball_self hr⟩
  have hOU : patch sZ (A.C y).φ O ≤ U := hpW.trans iW'.le
  have hOO' : patch sZ (A.C y).φ O ≤ patch sZ (A.C y).φ O' := hpW.trans iW.le
  set omB := (Ωan sZ (p + 1)).val.presheaf.map (homOfLE hOU).op om with homB
  -- `δP` of the restriction is the restriction of the twisted section `s'`
  have hδB : δP sZ (A.C y) O omB ∈ chartSpan n sZ (A.C y) (A.k y) (p + 1 + 1) O := by
    have h1 := δan_app_patch sZ A.hΘ A.C (p + 1) ⟨y, O⟩ omB
    have h2 := ConcreteCategory.congr_hom ((δan sZ A.hΘ A.C (p + 1)).hom.naturality
      (homOfLE hOU).op) om
    have h3 : (Ωan sZ (p + 1 + 1)).val.presheaf.map (homOfLE hOU).op
        ((δan sZ A.hΘ A.C (p + 1)).hom.app (op U) om) =
        (Ωan sZ (p + 1 + 1)).val.presheaf.map (homOfLE hOO').op s' := by
      have hOU' : homOfLE hOU = homOfLE hpW ≫ iW' := Subsingleton.elim _ _
      have hOO'' : homOfLE hOO' = homOfLE hpW ≫ iW := Subsingleton.elim _ _
      rw [hOU', hOO'', op_comp, op_comp, Functor.map_comp, Functor.map_comp]
      exact congrArg ((Ωan sZ (p + 1 + 1)).val.presheaf.map (homOfLE hpW).op) hW.symm
    have : δP sZ (A.C y) O omB = (Ωan sZ (p + 1 + 1)).val.presheaf.map (homOfLE hOO').op s' :=
      h1.symm.trans (h2.trans h3)
    rw [this]
    exact map_mem_chartSpan n sZ (A.C y) (A.k y) (p + 1 + 1) hOO' hs'
  obtain ⟨η, σ, hσ, hdec⟩ := exists_eq_δP_add_of_mem_chartSpan A y p O rfl hball hrc omB hδB
  refine ⟨(TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
    ((SheafOfModules.toSheaf _).map (πan n sZ E hE p)).hom
    (TopCat.Presheaf.germ (Ωan sZ p).val.presheaf (patch sZ (A.C y).φ O) y hyO η), ?_⟩
  have hsecp := (fun (x : ((SheafOfModules.toSheaf (MMP.Analytic.ringCatSheaf sZ)).obj
      (Ωan sZ p)).obj.obj (op (patch sZ (A.C y).φ O))) => ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op (patch sZ (A.C y).φ O))) (πan_comp_δanD hE A p)) x) η
  have hδη := δan_app_patch sZ A.hΘ A.C p ⟨y, O⟩ η
  have hσ0 := πan_eq_zero_of_mem_chartSpan n sZ E hE (A.C y) (A.hk y) (A.hb y) (A.hzero y)
    (p + 1) O hσ
  have e1 : TopCat.Presheaf.germ (Ωan sZ (p + 1)).val.presheaf U y hyU om =
      TopCat.Presheaf.germ (Ωan sZ (p + 1)).val.presheaf (patch sZ (A.C y).φ O) y hyO omB :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  erw [e1]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [hdec]
  erw [map_add, hσ0, add_zero]
  exact congrArg _ (hsecp.trans (congrArg _ hδη))

/-- **Off the divisor every germ of an analytic form is twisted**: if the first `k` coordinates of
the chart do not vanish at its centre, every germ there is a combination of twisted generators. -/
private theorem mem_chartGerms_of_forall_ne (A : AdaptedCharts n sZ E) (y : ComplexPoints sZ)
    (hc : ∀ j : Fin n, (j : ℕ) < A.k y → chartCentre n sZ (A.C y) j ≠ 0) (p : ℕ)
    (g : TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ)
      (Ωan sZ p).val.presheaf y) :
    g ∈ chartGerms n sZ (A.C y) (A.k y) p := by
  obtain ⟨U, hyU, om, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ g
  obtain ⟨r, hr, hball, hpU, hrc⟩ := exists_ball_patch_le A y U hyU
  set O : Opens (EuclideanSpace ℂ (Fin n)) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩ with hOdef
  have hyO : y ∈ patch sZ (A.C y).φ O := ⟨(A.C y).hy, by
    change (A.C y).φ y ∈ Metric.ball 0 r
    rw [chart_apply_self n sZ (A.C y)]; exact Metric.mem_ball_self hr⟩
  have htgt : (A.C y).φ.target ∩ (O : Set (EuclideanSpace ℂ (Fin n))) = Metric.ball 0 r :=
    Set.inter_eq_right.2 hball
  have hS0 : boundaryCoords (A.k y) (chartCentre n sZ (A.C y)) = ∅ := by
    ext l
    simp only [boundaryCoords, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and]
    exact hc l
  let omB := (Ωan sZ p).val.presheaf.map (homOfLE hpU).op om
  obtain ⟨hξd, hξ⟩ := holExt_spec sZ (A.C y) O omB
  have hv : VanishesAlong (boundaryCoords (A.k y) (chartCentre n sZ (A.C y))) (Metric.ball 0 r)
      (holExt sZ (A.C y) O omB) := by
    rw [hS0]; intro l hl; simp at hl
  have hhol := holSubOn_of_vanishesAlong _ (A.hk y) _ hrc (htgt ▸ hξd) hv
  obtain ⟨s, hs, hseq⟩ := (A.hS y p O _).2 ⟨_, hξd, hξ, htgt ▸ hhol⟩
  have : s = omB := (A.C y).inj _ _ hseq
  refine ⟨O, hyO, omB, this ▸ hs, ?_⟩
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

omit hmfd in
/-- The structure map of the sections of a complex scheme is the base ring map. -/
private theorem algebraMap_eq_baseRingHom (V : Z.Opens) (a : ℂ) :
    letI := MMP.Mori.sectionAlgebra sZ V
    algebraMap ℂ Γ(Z, V) a = ComplexPoints.baseRingHom sZ V a := by
  letI := MMP.Mori.sectionAlgebra sZ V
  change ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sZ.appLE ⊤ V (by simp)).hom a =
    (Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (sZ.appTop.hom
      ((Scheme.ΓSpecIso (.of ℂ)).inv.hom a))
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  rfl

set_option maxRecDepth 40000 in
/-- **The kernel of the analytic restriction complex in degree zero is the constants.** -/
private theorem exists_eq_germ_unit_of_stalk_δanD_eq_zero [LocallyOfFiniteType sZ]
    [QuasiCompact sZ] (A : AdaptedCharts n sZ E) (y : ComplexPoints sZ)
    (g : TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := space sZ)
      ((analytifyModule sZ).obj (cokernel (logToForms sZ ((isLocalSectionRel_twisted sZ hE
        (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0)))).val.presheaf y)
    (hg : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map (δanD hE A 0).hom g = 0) :
    letI := MMP.Mori.sectionAlgebra sZ (A.C y).W
    ∃ a : ℂ, g = TopCat.Presheaf.germ ((analytifyModule sZ).obj (cokernel (logToForms sZ
        ((isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE))
          0)))).val.presheaf ((Opens.map (toSchemeHom sZ)).obj (A.C y).W) y
        (mem_chart_iff.1 ((A.C y).hφ (A.C y).hy))
        ((analytifyModuleUnit sZ (cokernel (logToForms sZ ((isLocalSectionRel_twisted sZ hE
          (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0)))).val.app (op (A.C y).W)
          ((cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
            (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0))).val.app (op (A.C y).W)
            ((Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.app (op (A.C y).W)
              (algebraMap ℂ Γ(Z, (A.C y).W) a)))) := by
  letI := MMP.Mori.sectionAlgebra sZ (A.C y).W
  obtain ⟨γ, rfl⟩ := @stalkFunctor_map_surjective_of_epi _ _ _
    ((SheafOfModules.toSheaf _).map (πan n sZ E hE 0)) (epi_toSheaf_πan hE 0) y g
  obtain ⟨U, hyU, om, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ γ
  have hsec := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op U))
    (πan_comp_δanD hE A 0)) om
  have key : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
      ((SheafOfModules.toSheaf _).map (πan n sZ E hE (0 + 1))).hom
        (TopCat.Presheaf.germ (Ωan sZ (0 + 1)).val.presheaf U y hyU
          ((δan sZ A.hΘ A.C 0).hom.app (op U) om)) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map (δanD hE A 0).hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
          ((SheafOfModules.toSheaf _).map (πan n sZ E hE 0)).hom
          (TopCat.Presheaf.germ (Ωan sZ 0).val.presheaf U y hyU om)) := by
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact congrArg _ hsec.symm
  obtain ⟨O', hO', s', hs', hg'⟩ := (stalk_πan_eq_zero_iff hE A y (0 + 1) _).1 (key.trans hg)
  obtain ⟨W', hyW', iW, iW', hW⟩ := TopCat.Presheaf.germ_eq (Ωan sZ (0 + 1)).val.presheaf y hO'
    hyU _ _ hg'
  obtain ⟨r, hr, hball, hpW, hrc⟩ := exists_ball_patch_le A y W' hyW'
  set O : Opens (EuclideanSpace ℂ (Fin n)) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩ with hOdef
  have hyO : y ∈ patch sZ (A.C y).φ O := ⟨(A.C y).hy, by
    change (A.C y).φ y ∈ Metric.ball 0 r
    rw [chart_apply_self n sZ (A.C y)]; exact Metric.mem_ball_self hr⟩
  have hOU : patch sZ (A.C y).φ O ≤ U := hpW.trans iW'.le
  have hOO' : patch sZ (A.C y).φ O ≤ patch sZ (A.C y).φ O' := hpW.trans iW.le
  set omB := (Ωan sZ 0).val.presheaf.map (homOfLE hOU).op om with homB
  have hδB : δP sZ (A.C y) O omB ∈ chartSpan n sZ (A.C y) (A.k y) (0 + 1) O := by
    have h1 := δan_app_patch sZ A.hΘ A.C 0 ⟨y, O⟩ omB
    have h2 := ConcreteCategory.congr_hom ((δan sZ A.hΘ A.C 0).hom.naturality
      (homOfLE hOU).op) om
    have h3 : (Ωan sZ (0 + 1)).val.presheaf.map (homOfLE hOU).op
        ((δan sZ A.hΘ A.C 0).hom.app (op U) om) =
        (Ωan sZ (0 + 1)).val.presheaf.map (homOfLE hOO').op s' := by
      have hOU' : homOfLE hOU = homOfLE hpW ≫ iW' := Subsingleton.elim _ _
      have hOO'' : homOfLE hOO' = homOfLE hpW ≫ iW := Subsingleton.elim _ _
      rw [hOU', hOO'', op_comp, op_comp, Functor.map_comp, Functor.map_comp]
      exact congrArg ((Ωan sZ (0 + 1)).val.presheaf.map (homOfLE hpW).op) hW.symm
    have : δP sZ (A.C y) O omB = (Ωan sZ (0 + 1)).val.presheaf.map (homOfLE hOO').op s' :=
      h1.symm.trans (h2.trans h3)
    rw [this]
    exact map_mem_chartSpan n sZ (A.C y) (A.k y) (0 + 1) hOO' hs'
  have htgt : (A.C y).φ.target ∩ (O : Set (EuclideanSpace ℂ (Fin n))) = Metric.ball 0 r :=
    Set.inter_eq_right.2 hball
  have hpatch : ∀ v ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin n)) r,
      (A.C y).φ.symm v ∈ patch sZ (A.C y).φ O := fun v hv =>
    ⟨(A.C y).φ.map_target (hball hv), by
      change (A.C y).φ ((A.C y).φ.symm v) ∈ Metric.ball 0 r
      rw [(A.C y).φ.right_inv (hball hv)]; exact hv⟩
  obtain ⟨hξd, hξ⟩ := holExt_spec sZ (A.C y) O omB
  have hδ := Ψ_δP sZ (A.C y) O omB
  obtain ⟨ξ', hξ'd, hξ'eq, hhol⟩ := (A.hS y (0 + 1) O _).1 ⟨_, hδB, rfl⟩
  have heq : ∀ v ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin n)) r,
      extDeriv (holExt sZ (A.C y) O omB) v = ξ' v := by
    intro v hv
    have h1 := (hξ'eq ⟨_, hpatch v hv⟩).trans (hδ ⟨_, hpatch v hv⟩)
    simp only [(A.C y).φ.right_inv (hball hv)] at h1
    exact h1.symm
  have hholξ : HolSubOn (A.k y) (A.hk y) (chartCentre n sZ (A.C y)) (Metric.ball 0 r)
      (extDeriv (holExt sZ (A.C y) O omB)) :=
    holSubOn_congr _ _ _ heq (htgt ▸ hhol)
  obtain ⟨b, σ, hσd, hσhol, hdec⟩ := exists_eq_const_add_of_holSubOn_extDeriv _ (A.hk y) _ hrc
    (htgt ▸ hξd) hholξ
  obtain ⟨σ', hσ'⟩ := ((A.C y).range 0 O (fun y' => σ ((A.C y).φ y'))).2
    ⟨σ, htgt ▸ hσd, fun _ => rfl⟩
  obtain ⟨σ'', hσ''mem, hσ''⟩ := (A.hS y 0 O _).2
    ⟨σ, htgt ▸ hσd, fun y' => (congrFun hσ' y').symm, htgt ▸ hσhol⟩
  have hσeq : σ'' = σ' := (A.C y).inj _ _ hσ''
  refine ⟨b Fin.elim0, ?_⟩
  set x := (Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.app (op (A.C y).W)
    (algebraMap ℂ Γ(Z, (A.C y).W) (b Fin.elim0)) with hx
  have hL : (MMP.DeRham.formsAlgEquiv sZ 0 ⟨(A.C y).W, (A.C y).hW⟩).symm
      ((exteriorPower.zeroEquiv Γ(Z, (A.C y).W) Ω[Γ(Z, (A.C y).W)⁄ℂ]).symm
        (algebraMap ℂ Γ(Z, (A.C y).W) (b Fin.elim0))) = x :=
    (LinearEquiv.symm_apply_eq _).2
      (formsAlgEquiv_zeroIso_inv sZ ⟨(A.C y).W, (A.C y).hW⟩ _).symm
  set cst := an sZ 0 (A.C y).W (patch sZ (A.C y).φ O) (patch_le_W sZ (A.C y) O) x with hcst
  have hΨcst : ∀ y', (A.C y).Ψ 0 O cst y' = b := by
    intro y'
    have h0 := (A.C y).deg0 (A.C y).W (A.C y).hW O (patch_le_W sZ (A.C y) O)
      (algebraMap ℂ Γ(Z, (A.C y).W) (b Fin.elim0)) y'
    rw [hL] at h0
    rw [h0, algebraMap_eq_baseRingHom, evalHom_baseRingHom]
    ext v
    rw [ContinuousAlternatingMap.constOfIsEmpty_apply]
    exact congrArg b (Subsingleton.elim _ _)
  have hdecS : omB = cst + σ' := by
    apply (A.C y).inj 0 O
    funext y'
    have hy'b : (A.C y).φ y' ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin n)) r := y'.2.2
    rw [map_add, Pi.add_apply, hΨcst, congrFun hσ' y', ← hξ y', hdec _ hy'b]
  have hσ0 := πan_eq_zero_of_mem_chartSpan n sZ E hE (A.C y) (A.hk y) (A.hb y) (A.hzero y)
    0 O (hσeq ▸ hσ''mem)
  have e1 : TopCat.Presheaf.germ (Ωan sZ 0).val.presheaf U y hyU om =
      TopCat.Presheaf.germ (Ωan sZ 0).val.presheaf (patch sZ (A.C y).φ O) y hyO omB :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  erw [e1, TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [hdecS, map_add, hσ0, add_zero]
  have h1 := ConcreteCategory.congr_hom (congrArg (fun f => f.val.app (op (A.C y).W))
    ((SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sZ)).unit.naturality
      (cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
        (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0))))) x
  have h2 := ConcreteCategory.congr_hom ((πan n sZ E hE 0).val.naturality
    (homOfLE (patch_le_W sZ (A.C y) O)).op)
    ((analytifyModuleUnit sZ (sZ.relativeDifferentialForms ((0 : ℕ) : ℤ))).val.app
      (op (A.C y).W) x)
  erw [h1]
  refine (congrArg _ h2).trans ?_
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- **On the divisor the constants survive in the analytic restriction complex**: at a point where
a boundary coordinate vanishes, a constant function whose class vanishes is zero. -/
private theorem eq_zero_of_stalk_πan_germ_eq_zero [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (A : AdaptedCharts n sZ E) (y : ComplexPoints sZ)
    (hj : ∃ j : Fin n, (j : ℕ) < A.k y ∧ chartCentre n sZ (A.C y) j = 0)
    (O : Opens (EuclideanSpace ℂ (Fin n))) (hyO : y ∈ patch sZ (A.C y).φ O)
    (cst : (Ωan sZ 0).val.obj (op (patch sZ (A.C y).φ O))) (a : ℂ)
    (hcst : ∀ y', (A.C y).Ψ 0 O cst y' =
      ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin n)) (Fin 0) a)
    (h0 : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
        ((SheafOfModules.toSheaf _).map (πan n sZ E hE 0)).hom
        (TopCat.Presheaf.germ (Ωan sZ 0).val.presheaf (patch sZ (A.C y).φ O) y hyO cst) = 0) :
    a = 0 := by
  obtain ⟨O', hO', s', hs', hg'⟩ := (stalk_πan_eq_zero_iff hE A y 0 _).1 h0
  obtain ⟨W', hyW', iW, iW', hW⟩ := TopCat.Presheaf.germ_eq (Ωan sZ 0).val.presheaf y hO'
    hyO _ _ hg'
  obtain ⟨r, hr, hball, hpW, hrc⟩ := exists_ball_patch_le A y W' hyW'
  set O'' : Opens (EuclideanSpace ℂ (Fin n)) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩ with hOdef
  have hOO' : patch sZ (A.C y).φ O'' ≤ patch sZ (A.C y).φ O' := hpW.trans iW.le
  have hOO : patch sZ (A.C y).φ O'' ≤ patch sZ (A.C y).φ O := hpW.trans iW'.le
  have heqt : (Ωan sZ 0).val.presheaf.map (homOfLE hOO).op cst =
      (Ωan sZ 0).val.presheaf.map (homOfLE hOO').op s' := by
    have h1 : homOfLE hOO = homOfLE hpW ≫ iW' := Subsingleton.elim _ _
    have h2 : homOfLE hOO' = homOfLE hpW ≫ iW := Subsingleton.elim _ _
    rw [h1, h2, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
    exact congrArg ((Ωan sZ 0).val.presheaf.map (homOfLE hpW).op) hW.symm
  have hmem : (Ωan sZ 0).val.presheaf.map (homOfLE hOO).op cst ∈
      chartSpan n sZ (A.C y) (A.k y) 0 O'' :=
    heqt ▸ map_mem_chartSpan n sZ (A.C y) (A.k y) 0 hOO' hs'
  obtain ⟨ξ', hξ'd, hξ'eq, hhol⟩ := (A.hS y 0 O'' _).1 ⟨_, hmem, rfl⟩
  have htgt : (A.C y).φ.target ∩ (O'' : Set (EuclideanSpace ℂ (Fin n))) = Metric.ball 0 r :=
    Set.inter_eq_right.2 hball
  have hv := vanishesAlong_of_holSubOn _ (A.hk y) _ (htgt ▸ Metric.isOpen_ball)
    hξ'd.continuousOn hhol
  obtain ⟨j, hjk, hj0⟩ := hj
  have h0mem : (0 : EuclideanSpace ℂ (Fin n)) ∈ (A.C y).φ.target ∩ (O'' : Set _) :=
    htgt ▸ Metric.mem_ball_self hr
  have hjS : j ∈ boundaryCoords (A.k y) (chartCentre n sZ (A.C y)) := by
    simp only [boundaryCoords, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hjk, hj0⟩
  have hval := hv j hjS 0 h0mem (by simp) Fin.elim0 (fun i => i.elim0)
  -- `ξ'` is the constant `a` at the centre
  have hy0 : (A.C y).φ.symm 0 ∈ patch sZ (A.C y).φ O'' := by
    refine ⟨(A.C y).φ.map_target (hball (Metric.mem_ball_self hr)), ?_⟩
    change (A.C y).φ ((A.C y).φ.symm 0) ∈ Metric.ball 0 r
    rw [(A.C y).φ.right_inv (hball (Metric.mem_ball_self hr))]
    exact Metric.mem_ball_self hr
  have hc := hξ'eq ⟨_, hy0⟩
  rw [(A.C y).restr 0 O'' O hOO cst ⟨_, hy0⟩, hcst] at hc
  simp only [(A.C y).φ.right_inv (hball (Metric.mem_ball_self hr))] at hc
  rw [hc] at hval
  simpa using hval

end ChartLog

/-! ### Adapted charts from the analytification of differential forms -/

section AdaptedChartsExist

open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints MMP.DeRhamBetti
open scoped Manifold ContDiff

variable (n : ℕ) {Z : Scheme.{0}} (sZ : Z ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n sZ] (E : MMP.Mori.Divisor Z)

set_option maxRecDepth 10000 in
/-- **A relative snc divisor of a separated quasi-compact smooth complex scheme admits adapted
charts at every point**, by
`MMP.Analytic.analytification_smooth_differentials_of_smoothOfRelativeDimension`. -/
private theorem exists_adaptedCharts [IsSeparated sZ] [QuasiCompact sZ]
    (hE : E.IsRelativeSNC n sZ) :
    ∃ (cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sZ))
      (_ : letI := cs; IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sZ)),
      Nonempty (letI := cs; AdaptedCharts n sZ E) := by
  refine (MMP.Analytic.analytification_smooth_differentials_of_smoothOfRelativeDimension sZ (n := n)
    E
    (MMP.FourfoldProofs.FractionalLogComplexProof.isSNC_of_isRelativeSNC sZ E hE)).elim fun cs h => ?_
  letI := cs
  obtain ⟨hmfd, -, -, -, Θ, hΘ, hloc⟩ := h
  have key : ∀ y : ComplexPoints sZ, ∃ (C : ChartData sZ n Θ y) (k : ℕ) (hk : k ≤ n),
      (letI := MMP.Mori.sectionAlgebra sZ C.W
        ∃ b : Module.Basis (Fin n) Γ(Z, C.W) Ω[Γ(Z, C.W)⁄ℂ],
          ∀ i, b i = KaehlerDifferential.D ℂ Γ(Z, C.W) (C.z i)) ∧
      (∀ w ∈ C.W, (∃ D ∈ E.support, w ∈ D.support) ↔
        w ∉ Z.basicOpen (∏ i : Fin k, C.z (Fin.castLE hk i))) ∧
      ∀ p O (η : patch sZ C.φ O → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ),
        η ∈ C.Ψ p O '' (chartSpan n sZ C k p O : Set _) ↔ chartHolSub n sZ C k hk p O η := by
    intro y
    obtain ⟨W, hW, hxW, k, hk, z, -, hzero, hb, hy⟩ :=
      hloc y.toScheme (isClosed_singleton_toScheme' sZ y)
    obtain ⟨φ, hφm, hφ, hyφ, hcoord, Ψ, i1, i2, i3, i4, i5, i6, h4⟩ := hy y (mem_chart_iff.2 hxW)
    refine ⟨⟨W, hW, z, φ, hφm, hφ, hyφ, hcoord, Ψ, i1, i2, i3, i4, i5, i6⟩, k, hk, hb, hzero,
      fun p O η => ?_⟩
    obtain ⟨-, -, -, -, -, -, -, hSS, -, -⟩ := h4 p
    exact (hSS O (fun y' hy' => mem_chart_iff.1 (hφ hy'.1)) η).trans
      ⟨fun ⟨g, hg, ξ, h1, h2, h3⟩ => ⟨ξ, h1, h2, g, hg, h3⟩,
        fun ⟨ξ, h1, h2, g, hg, h3⟩ => ⟨g, hg, ξ, h1, h2, h3⟩⟩
  choose C k hk hb hzero hS using key
  exact ⟨cs, hmfd, ⟨⟨Θ, hΘ, C, k, hk, hb, hzero, hS⟩⟩⟩

end AdaptedChartsExist

/-! ### Naturality of the comparison with analytification -/

section AnalytifyNaturality

open MMP.Analytic MMP.Analytic.Analytification

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- `ι_F : α_X⁻¹ F ⟶ F^an` is natural in the `𝒪_X`-module `F`. -/
private theorem analytifyModuleι_naturality {F G : X.Modules} (a : F ⟶ G) :
    analytifyModuleι sX F ≫ (SheafOfModules.toSheaf _).map ((analytifyModule sX).map a) =
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX)).map
        ((SheafOfModules.toSheaf _).map a) ≫ analytifyModuleι sX G := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (toSchemeHom sX)
  have h1 := adj.homEquiv_naturality_right_symm
    ((SheafOfModules.toSheaf _).map (analytifyModuleUnit sX F))
    ((SheafOfModules.toSheaf _).map ((analytifyModule sX).map a))
  have h2 := adj.homEquiv_naturality_left_symm
    (Y := (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj G))
    ((SheafOfModules.toSheaf X.ringCatSheaf).map a)
    ((SheafOfModules.toSheaf _).map (analytifyModuleUnit sX G))
  have key : (SheafOfModules.toSheaf _).map (analytifyModuleUnit sX F) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).map
        ((SheafOfModules.toSheaf _).map ((analytifyModule sX).map a)) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map a ≫
        (SheafOfModules.toSheaf _).map (analytifyModuleUnit sX G) := by
    have := congrArg (SheafOfModules.toSheaf X.ringCatSheaf).map
      ((SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sX)).unit.naturality a)
    simp only [Functor.map_comp] at this
    exact this.symm
  exact h1.symm.trans ((congrArg _ key).trans h2)

end AnalytifyNaturality

/-! ### The comparison with analytification commutes with the de Rham differential -/

section DeRhamComparison

open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints MMP.DeRhamBetti
open scoped Manifold ContDiff

attribute [local implicit_reducible] TopCat.Sheaf

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}
  (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
  (C : ∀ y, ChartData sX n Θ y)

set_option maxRecDepth 10000 in
include hΘ in
private theorem dZ_unit_comm (k : ℕ) :
    DRCmp.dZ sX k ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map
        (analytifyModuleUnit sX (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ))) =
      ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (analytifyModuleUnit sX (sX.relativeDifferentialForms (k : ℤ))) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).map (δan sX hΘ C k) :) := by
  refine ObjectProperty.hom_ext _ (TopCat.Sheaf.hom_ext _ _
    (B := fun V : X.affineOpens => (V : X.Opens)) (by simpa using X.isBasis_affineOpens)
    fun V => ?_)
  ext s
  change (analytifyModuleUnit sX (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ))).val.app (op V)
      ((DRCmp.dZ sX k).hom.app (op V) s) =
    (δan sX hΘ C k).hom.app (op ((Opens.map (toSchemeHom sX)).obj V))
      ((analytifyModuleUnit sX (sX.relativeDifferentialForms (k : ℤ))).val.app (op V) s)
  rw [δan_unit sX hΘ C k V V.2 s, DRCmp.dZ_app]

private theorem dZ_ι_comm (k : ℕ) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX)).map (DRCmp.dZ sX k) ≫
        analytifyModuleι sX (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ)) =
      analytifyModuleι sX (sX.relativeDifferentialForms (k : ℤ)) ≫ δan sX hΘ C k := by
  have h1 := Adjunction.homEquiv_naturality_left_symm
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (toSchemeHom sX))
    (Y := (SheafOfModules.toSheaf _).obj
      ((analytifyModule sX).obj (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ)))) (DRCmp.dZ sX k)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (analytifyModuleUnit sX (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ))))
  have h2 := Adjunction.homEquiv_naturality_right_symm
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (toSchemeHom sX))
    (Y := (SheafOfModules.toSheaf _).obj
      ((analytifyModule sX).obj (sX.relativeDifferentialForms (k : ℤ))))
    ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (analytifyModuleUnit sX (sX.relativeDifferentialForms (k : ℤ)))) (δan sX hΘ C k)
  erw [dZ_unit_comm sX hΘ C k] at h1
  exact h1.symm.trans h2

end DeRhamComparison

/-! ### The analytic restriction complex -/

section AnalyticComplex

open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints MMP.DeRhamBetti
open scoped Manifold ContDiff

variable (n : ℕ) {Z : Scheme.{0}} (sZ : Z ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n sZ]
  (E : MMP.Mori.Divisor Z) (hE : E.IsRelativeSNC n sZ)
  (i : relativeLogDeRhamComplex n sZ E hE E.suppIdeal ⟶ Scheme.Hom.deRhamComplex sZ)
  (hi : ∀ (p : ℕ) (W : Z.Opensᵒᵖ)
    (w : ((relativeLogDeRhamComplex n sZ E hE E.suppIdeal).X p).val.obj W),
    ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι E.supp.compl) sZ).f p).val.app
      W ((i.f p).val.app W w) = w.1)
  (D : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
  (q : Scheme.Hom.deRhamComplex sZ ⟶ D) (hiq : i ≫ q = 0)
  (hq : IsColimit (CokernelCofork.ofπ q hiq))
  [IsLocallyNoetherian Z] [LocallyOfFiniteType sZ] [QuasiCompact sZ]
  [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sZ)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sZ)]
  (A : AdaptedCharts n sZ E)

/-- The differentials of the analytic restriction complex, indexed by `ℤ`. -/
private noncomputable def δanZ : ∀ p : ℤ,
    (SheafOfModules.toSheaf _).obj ((analytifyModule sZ).obj (cokZF n sZ E hE p)) ⟶
      (SheafOfModules.toSheaf _).obj ((analytifyModule sZ).obj (cokZF n sZ E hE (p + 1)))
  | Int.ofNat k => δanD hE A k
  | Int.negSucc _ => 0

private theorem δanZ_comp : ∀ p : ℤ,
    δanZ n sZ E hE A p ≫ δanZ n sZ E hE A (p + 1) = 0
  | Int.ofNat k => δanD_comp hE A k
  | Int.negSucc _ => zero_comp

/-- **The analytic restriction complex** `𝒟_E^{an,•}`, as a complex of abelian sheaves on
`Z^an`. -/
private noncomputable abbrev KDan :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} (space sZ)) ℤ :=
  CochainComplex.of (fun p => (SheafOfModules.toSheaf _).obj
    ((analytifyModule sZ).obj (cokZF n sZ E hE p))) (δanZ n sZ E hE A) (δanZ_comp n sZ E hE A)

private theorem epi_pullback_toSheaf_π (k : ℕ) :
    Epi ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)).map
      ((SheafOfModules.toSheaf _).map (cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
        (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) k))))) := by
  haveI : (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)).IsLeftAdjoint :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (toSchemeHom sZ)).isLeftAdjoint
  have he : Epi (cokernel.π (logToForms sZ
      ((isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) k))) :=
    inferInstance
  have hp : (SheafOfModules.toSheaf Z.ringCatSheaf).PreservesEpimorphisms := by
    haveI := Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits _ Z.ringCatSheaf
    infer_instance
  exact @Functor.map_epi _ _ _ _ _ inferInstance _ _ _ (@Functor.map_epi _ _ _ _ _ hp _ _ _ he)

private theorem KDan_d (k : ℕ) :
    (KDan n sZ E hE A).d (Int.ofNat k) (Int.ofNat k + 1) = δanD hE A k :=
  CochainComplex.of_d _ (δanZ n sZ E hE A) (Int.ofNat k)

private theorem cokZK_d (k : ℕ) :
    (cokZK n sZ E hE i hi D q hiq hq).d (Int.ofNat k) (Int.ofNat k + 1) =
      cokZd n sZ E hE i hi D q hiq hq k :=
  CochainComplex.of_d _ (cokZδ n sZ E hE i hi D q hiq hq) (Int.ofNat k)

/-- The comparison maps commute with the differentials of the algebraic and analytic restriction
complexes. -/
private theorem analytifyModuleι_comp_δanD (k : ℕ) :
    analytifyModuleι sZ (cokernel (logToForms sZ ((isLocalSectionRel_twisted sZ hE
        (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) k))) ≫ δanD hE A k =
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)).map
          (cokZd n sZ E hE i hi D q hiq hq k) ≫
        analytifyModuleι sZ (cokernel (logToForms sZ ((isLocalSectionRel_twisted sZ hE
          (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) (k + 1)))) := by
  haveI := epi_pullback_toSheaf_π n sZ E hE k
  have n1 := analytifyModuleι_naturality sZ (cokernel.π (logToForms sZ
    ((isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) k)))
  have n2 := analytifyModuleι_naturality sZ (cokernel.π (logToForms sZ
    ((isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) (k + 1))))
  have c1 := πan_comp_δanD hE A k
  have c2 := dZ_ι_comm sZ A.hΘ A.C k
  have c3 := toSheaf_π_comp_cokZd n sZ E hE i hi D q hiq hq k
  refine (cancel_epi ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)).map
    ((SheafOfModules.toSheaf _).map (cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
      (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) k)))))).1 ?_
  have key : ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)).map
      ((SheafOfModules.toSheaf _).map (cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
        (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) k)))) ≫
      analytifyModuleι sZ (cokernel (logToForms sZ ((isLocalSectionRel_twisted sZ hE
        (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) k)))) ≫ δanD hE A k =
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)).map
        ((SheafOfModules.toSheaf _).map (cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ
          hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) k))) ≫
          cokZd n sZ E hE i hi D q hiq hq k) ≫
        analytifyModuleι sZ (cokernel (logToForms sZ ((isLocalSectionRel_twisted sZ hE
          (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) (k + 1)))) := by
    erw [← n1, Category.assoc, c1, ← Category.assoc, ← c2, Category.assoc, n2, ← Category.assoc,
      ← Functor.map_comp, c3]
    rfl
  refine (Category.assoc _ _ _).symm.trans (key.trans ?_)
  exact (congrArg (fun φ => φ ≫ analytifyModuleι sZ (cokernel (logToForms sZ
    ((isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) (k + 1)))))
    (Functor.map_comp _ _ _)).trans (Category.assoc _ _ _)

/-- **The comparison `α⁻¹ 𝒟_E^• ⟶ 𝒟_E^{an,•}`**, `s ↦ s ⊗ 1` in every degree. -/
private noncomputable def ιD :
    (complexPullback (toSchemeHom sZ)).obj (cokZK n sZ E hE i hi D q hiq hq) ⟶
      KDan n sZ E hE A where
  f p := analytifyModuleι sZ (cokZF n sZ E hE p)
  comm' := by
    rintro j _ rfl
    cases j with
    | ofNat k =>
      rw [KDan_d, show ((complexPullback (toSchemeHom sZ)).obj
          (cokZK n sZ E hE i hi D q hiq hq)).d (Int.ofNat k) (Int.ofNat k + 1) =
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)).map
          ((cokZK n sZ E hE i hi D q hiq hq).d (Int.ofNat k) (Int.ofNat k + 1)) from rfl, cokZK_d]
      change analytifyModuleι sZ (cokZF n sZ E hE (Int.ofNat k)) ≫ δanD hE A k =
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)).map
          (cokZd n sZ E hE i hi D q hiq hq k) ≫ analytifyModuleι sZ (cokZF n sZ E hE (Int.ofNat k + 1))
      exact analytifyModuleι_comp_δanD n sZ E hE i hi D q hiq hq A k
    | negSucc m =>
      exact ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)).map_isZero
        (by haveI := Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits _
              Z.ringCatSheaf
            exact (SheafOfModules.toSheaf _).map_isZero (isZero_zero _))).eq_of_src _ _

/-- **GAGA for the restriction complex**: the comparison `ℍ^m(Z, 𝒟_E^•) ⟶ ℍ^m(Z^an, 𝒟_E^{an,•})`
is an isomorphism. -/
private theorem isIso_hypercohomologyPullback_comp_map_ιD (hZ : IsProjective sZ) (m : ℤ) :
    IsIso (hypercohomologyPullback (toSchemeHom sZ) (cokZK n sZ E hE i hi D q hiq hq) m ≫
      (hypercohomology (space sZ) m).map (ιD n sZ E hE i hi D q hiq hq A)) := by
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  obtain ⟨N, hN⟩ := exists_isZero_cokZF n sZ E hE
  exact (MMP.Analytic.isIso_hypercohomologyPullback_comp_map_of_isProjective sZ hZ
    (cokZF n sZ E hE) (isCoherent_cokZF n sZ E hE) 0 N hN (cokZδ n sZ E hE i hi D q hiq hq)
    (cokZδ_smul n sZ E hE i hi D q hiq hq) (cokZδ_comp n sZ E hE i hi D q hiq hq)
    (δanZ n sZ E hE A) (δanZ_comp n sZ E hE A) (ιD n sZ E hE i hi D q hiq hq A)
    (fun _ => rfl)).1 m

omit [IsLocallyNoetherian Z] [LocallyOfFiniteType sZ] [QuasiCompact sZ] in
/-- **A point lies on the divisor exactly when one of the boundary coordinates of its chart
vanishes at it.** -/
private theorem toScheme_mem_supp_iff (y : ComplexPoints sZ) :
    y.toScheme ∈ E.supp ↔ ∃ j : Fin n, (j : ℕ) < A.k y ∧ chartCentre n sZ (A.C y) j = 0 := by
  have hW : y.toScheme ∈ (A.C y).W := mem_chart_iff.1 ((A.C y).hφ (A.C y).hy)
  have h1 := A.hzero y y.toScheme hW
  have hb := toScheme_mem_basicOpen_iff (sX := sZ) (⟨y, (A.C y).hφ (A.C y).hy⟩ :
    chart (sX := sZ) (A.C y).W) (∏ i : Fin (A.k y), (A.C y).z (Fin.castLE (A.hk y) i))
  rw [map_prod] at hb
  constructor
  · intro h
    obtain ⟨D, hD, hwD⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.1 h
    have h2 := h1.1 ⟨D, Finsupp.mem_support_iff.2 hD, hwD⟩
    rw [hb, not_not, Finset.prod_eq_zero_iff] at h2
    obtain ⟨i, -, hi⟩ := h2
    exact ⟨Fin.castLE (A.hk y) i, i.2, hi⟩
  · rintro ⟨j, hj, hj0⟩
    by_contra h
    have hD : ¬ ∃ D ∈ E.support, y.toScheme ∈ D.support := fun ⟨D, hD, hwD⟩ =>
      h (MMP.Mori.DivisorWithCoeffs.mem_supp_iff.2 ⟨D, Finsupp.mem_support_iff.1 hD, hwD⟩)
    have h2 : y.toScheme ∈ Z.basicOpen (∏ i : Fin (A.k y), (A.C y).z (Fin.castLE (A.hk y) i)) := by
      by_contra h3; exact hD (h1.2 h3)
    rw [hb] at h2
    exact Finset.prod_ne_zero_iff.1 h2 ⟨j, hj⟩ (Finset.mem_univ _) hj0

/-- **The analytic restriction complex is supported on `E^an`**: its stalks vanish off it. -/
private theorem subsingleton_stalk_KDan (y : ComplexPoints sZ) (hy : y.toScheme ∉ E.supp)
    (q : ℤ) : Subsingleton (((KDan n sZ E hE A).X q).presheaf.stalk y) := by
  have hc : ∀ j : Fin n, (j : ℕ) < A.k y → chartCentre n sZ (A.C y) j ≠ 0 := fun j hj h0 =>
    hy ((toScheme_mem_supp_iff n sZ E A y).2 ⟨j, hj, h0⟩)
  cases q with
  | ofNat k =>
    have h0 : ∀ g : ((KDan n sZ E hE A).X (Int.ofNat k)).presheaf.stalk y, g = 0 := by
      intro g
      obtain ⟨γ, rfl⟩ := @stalkFunctor_map_surjective_of_epi _ _ _
        ((SheafOfModules.toSheaf _).map (πan n sZ E hE k)) (epi_toSheaf_πan hE k) y g
      exact (stalk_πan_eq_zero_iff hE A y k γ).2 (mem_chartGerms_of_forall_ne A y hc k γ)
    exact ⟨fun a b => (h0 a).trans (h0 b).symm⟩
  | negSucc j =>
    haveI : (analytifyModule sZ).IsLeftAdjoint :=
      (SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sZ)).isLeftAdjoint
    haveI := Functor.preservesZeroMorphisms_of_isLeftAdjoint (analytifyModule sZ)
    exact MMP.Analytic.CoherentAnalytic.subsingleton_stalk_of_isZero
      ((SheafOfModules.toSheaf _).map_isZero ((analytifyModule sZ).map_isZero (isZero_zero _))) y

/-- **The constants of the analytic restriction complex**, `ℂ_{Z^an} ⟶ 𝒟_E^{0,an}`: the
holomorphic constants followed by the quotient map. -/
private noncomputable abbrev εZ :
    (constantSheaf (Opens.grothendieckTopology (space sZ)) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of ℂ) ⟶ (KDan n sZ E hE A).X 0 :=
  εan sZ A.hΘ A.C ≫ (SheafOfModules.toSheaf _).map (πan n sZ E hE 0)

private theorem εZ_comp_δanD : εZ n sZ E hE A ≫ δanD hE A 0 = 0 := by
  rw [Category.assoc]
  erw [πan_comp_δanD hE A 0]
  rw [← Category.assoc, εan_comp_δan, zero_comp]

omit [IsLocallyNoetherian Z] [LocallyOfFiniteType sZ] [QuasiCompact sZ] in
/-- The germ of the holomorphic constant `c` on a chart patch. -/
private theorem stalk_εan_toSheafify_germ (y : ComplexPoints sZ)
    (O : Opens (EuclideanSpace ℂ (Fin n))) (hyO : y ∈ patch sZ (A.C y).φ O) (c : ℂ) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map (εan sZ A.hΘ A.C).hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
          (toSheafify (Opens.grothendieckTopology (space sZ)) (constPre sZ))
          ((constPre sZ).germ (patch sZ (A.C y).φ O) y hyO c)) =
      TopCat.Presheaf.germ (Ωan sZ 0).val.presheaf (patch sZ (A.C y).φ O) y hyO (εP sZ (A.C y) O c) := by
  have h1 := ConcreteCategory.congr_hom (stalk_εan sZ A.hΘ A.C y)
    ((constPre sZ).germ (patch sZ (A.C y).φ O) y hyO c)
  refine ((ConcreteCategory.comp_apply _ _ _).symm.trans h1).trans ?_
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact congrArg _ (εPre_app_patch sZ A.hΘ A.C ⟨y, O⟩ c)

set_option maxRecDepth 40000 in
/-- The analytification of the class of an algebraic constant is the class of the holomorphic
constant. -/
private theorem germ_unit_π_zeroIso_inv_eq (y : ComplexPoints sZ)
    (O : Opens (EuclideanSpace ℂ (Fin n))) (hyO : y ∈ patch sZ (A.C y).φ O) (a : ℂ) :
    letI := MMP.Mori.sectionAlgebra sZ (A.C y).W
    TopCat.Presheaf.germ ((analytifyModule sZ).obj (cokernel (logToForms sZ
        ((isLocalSectionRel_twisted sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE))
          0)))).val.presheaf ((Opens.map (toSchemeHom sZ)).obj (A.C y).W) y
        (mem_chart_iff.1 ((A.C y).hφ (A.C y).hy))
        ((analytifyModuleUnit sZ (cokernel (logToForms sZ ((isLocalSectionRel_twisted sZ hE
          (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0)))).val.app (op (A.C y).W)
          ((cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
            (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0))).val.app (op (A.C y).W)
            ((Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.app (op (A.C y).W)
              (algebraMap ℂ Γ(Z, (A.C y).W) a)))) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
        ((SheafOfModules.toSheaf _).map (πan n sZ E hE 0)).hom
        (TopCat.Presheaf.germ (Ωan sZ 0).val.presheaf (patch sZ (A.C y).φ O) y hyO (εP sZ (A.C y) O a)) := by
  letI := MMP.Mori.sectionAlgebra sZ (A.C y).W
  set x := (Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.app (op (A.C y).W)
    (algebraMap ℂ Γ(Z, (A.C y).W) a) with hx
  have hL : (MMP.DeRham.formsAlgEquiv sZ 0 ⟨(A.C y).W, (A.C y).hW⟩).symm
      ((exteriorPower.zeroEquiv Γ(Z, (A.C y).W) Ω[Γ(Z, (A.C y).W)⁄ℂ]).symm
        (algebraMap ℂ Γ(Z, (A.C y).W) a)) = x :=
    (LinearEquiv.symm_apply_eq _).2
      (formsAlgEquiv_zeroIso_inv sZ ⟨(A.C y).W, (A.C y).hW⟩ _).symm
  have hcst : an sZ 0 (A.C y).W (patch sZ (A.C y).φ O) (patch_le_W sZ (A.C y) O) x =
      εP sZ (A.C y) O a := by
    apply (A.C y).inj 0 O
    rw [Ψ_εP]
    funext y'
    have h0 := (A.C y).deg0 (A.C y).W (A.C y).hW O (patch_le_W sZ (A.C y) O)
      (algebraMap ℂ Γ(Z, (A.C y).W) a) y'
    rw [hL] at h0
    rw [h0, algebraMap_eq_baseRingHom, evalHom_baseRingHom]
  rw [← hcst]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have h1 := ConcreteCategory.congr_hom (congrArg (fun f => f.val.app (op (A.C y).W))
    ((SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sZ)).unit.naturality
      (cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
        (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0))))) x
  have h2 := ConcreteCategory.congr_hom ((πan n sZ E hE 0).val.naturality
    (homOfLE (patch_le_W sZ (A.C y) O)).op)
    ((analytifyModuleUnit sZ (sZ.relativeDifferentialForms ((0 : ℕ) : ℤ))).val.app
      (op (A.C y).W) x)
  erw [h1]
  unfold an
  refine Eq.trans ?_ (congrArg _ h2).symm
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

set_option maxRecDepth 40000 in
/-- **The constant `a` of `ℂ_{Z^an}` goes to the analytification of the class of the algebraic
constant `a`**, on global sections. -/
private theorem εZ_app_top_toSheafify (a : ℂ) :
    (εZ n sZ E hE A).hom.app (op ⊤)
        ((toSheafify (Opens.grothendieckTopology (space sZ)) (constPre sZ)).app (op ⊤) a) =
      (analytifyModuleUnit sZ (cokernel (logToForms sZ ((isLocalSectionRel_twisted sZ hE
          (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0)))).val.app (op ⊤)
        ((cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
          (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0))).val.app (op ⊤)
          ((Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.app (op ⊤)
            (ComplexPoints.baseRingHom sZ ⊤ a))) := by
  refine TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf _).obj ((analytifyModule sZ).obj
    (cokernel (logToForms sZ ((isLocalSectionRel_twisted sZ hE
      (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0))))) ⊤ _ _ fun y _ => ?_
  have hyT : y ∈ patch sZ (A.C y).φ ⊤ := ⟨(A.C y).hy, Set.mem_univ _⟩
  have hyW : y.toScheme ∈ (A.C y).W := mem_chart_iff.1 ((A.C y).hφ (A.C y).hy)
  letI := MMP.Mori.sectionAlgebra sZ (A.C y).W
  have hL := stalk_εan_toSheafify_germ n sZ E A y ⊤ hyT a
  have hgc : (constPre sZ).germ (patch sZ (A.C y).φ ⊤) y hyT a = (constPre sZ).germ ⊤ y trivial a :=
    TopCat.Presheaf.germ_res_apply (constPre sZ) (homOfLE le_top) y hyT a
  rw [hgc] at hL
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply]
    at hL
  have hL' := congrArg ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
    ((SheafOfModules.toSheaf _).map (πan n sZ E hE 0)).hom) hL
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hL'
  refine hL'.trans ((germ_unit_π_zeroIso_inv_eq n sZ E hE A y ⊤ hyT a).symm.trans ?_)
  have hb := ComplexPoints.baseRingHom_res (sX := sZ) (le_top : (A.C y).W ≤ ⊤) a
  rw [algebraMap_eq_baseRingHom, ← hb]
  have h2 := ConcreteCategory.congr_hom
    ((Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.naturality
      (homOfLE (le_top : (A.C y).W ≤ ⊤)).op) (ComplexPoints.baseRingHom sZ ⊤ a)
  have h1 := ConcreteCategory.congr_hom
    ((cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
      (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0))).val.naturality
      (homOfLE (le_top : (A.C y).W ≤ ⊤)).op)
    ((Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.app (op ⊤)
      (ComplexPoints.baseRingHom sZ ⊤ a))
  erw [h2, h1]
  exact germ_analytifyModuleUnit_res sZ _ (le_top : (A.C y).W ≤ ⊤) y hyW _

/-- **The kernel of the analytic restriction complex in degree zero is the image of the
constants.** -/
private theorem exact_εZ_δanD :
    (ShortComplex.mk (εZ n sZ E hE A) (δanD hE A 0) (εZ_comp_δanD n sZ E hE A)).Exact := by
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (C := AddCommGrpCat.{0})
    (X := space sZ) _).2 fun y => ?_
  rw [ShortComplex.ab_exact_iff]
  intro e he
  obtain ⟨a, rfl⟩ := exists_eq_germ_unit_of_stalk_δanD_eq_zero hE A y e he
  have hyT : y ∈ patch sZ (A.C y).φ ⊤ := ⟨(A.C y).hy, Set.mem_univ _⟩
  refine ⟨(TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
    (toSheafify (Opens.grothendieckTopology (space sZ)) (constPre sZ))
    ((constPre sZ).germ (patch sZ (A.C y).φ ⊤) y hyT a), ?_⟩
  refine Eq.trans ?_ (germ_unit_π_zeroIso_inv_eq n sZ E hE A y ⊤ hyT a).symm
  rw [← stalk_εan_toSheafify_germ n sZ E A y ⊤ hyT a]
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
      ((εan sZ A.hΘ A.C).hom ≫ ((SheafOfModules.toSheaf _).map (πan n sZ E hE 0)).hom) _ = _
  rw [Functor.map_comp]
  rfl

/-- **On the divisor the constants inject into the analytic restriction complex.** -/
private theorem stalk_εZ_injective (y : ComplexPoints sZ)
    (hj : ∃ j : Fin n, (j : ℕ) < A.k y ∧ chartCentre n sZ (A.C y) j = 0) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
      (εZ n sZ E hE A).hom) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y AddCommGrpCat.{0}
    (constPre sZ)
  have hsurj := ((ConcreteCategory.isIso_iff_bijective
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
      (toSheafify (Opens.grothendieckTopology (space sZ)) (constPre sZ)))).1 inferInstance).2
  obtain ⟨w', rfl⟩ := hsurj w
  obtain ⟨U, hyU, c, rfl⟩ := TopCat.Presheaf.exists_germ_eq (constPre sZ) w'
  obtain ⟨r, hr, -, hpU, -⟩ := exists_ball_patch_le A y U hyU
  set O : Opens (EuclideanSpace ℂ (Fin n)) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩ with hOdef
  have hyO : y ∈ patch sZ (A.C y).φ O := ⟨(A.C y).hy, by
    change (A.C y).φ y ∈ Metric.ball 0 r
    rw [chart_apply_self n sZ (A.C y)]; exact Metric.mem_ball_self hr⟩
  have hgerm : (constPre sZ).germ U y hyU c = (constPre sZ).germ (patch sZ (A.C y).φ O) y hyO c :=
    (TopCat.Presheaf.germ_res_apply (constPre sZ) (homOfLE hpU) y hyO c).symm
  rw [hgerm] at hw ⊢
  have hw' : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
      ((SheafOfModules.toSheaf _).map (πan n sZ E hE 0)).hom
      (TopCat.Presheaf.germ (Ωan sZ 0).val.presheaf (patch sZ (A.C y).φ O) y hyO
        (εP sZ (A.C y) O c)) = 0 := by
    rw [← stalk_εan_toSheafify_germ n sZ E A y O hyO c]
    refine Eq.trans ?_ hw
    change _ = (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} y).map
      ((εan sZ A.hΘ A.C).hom ≫ ((SheafOfModules.toSheaf _).map (πan n sZ E hE 0)).hom) _
    rw [Functor.map_comp]
    rfl
  have hc := eq_zero_of_stalk_πan_germ_eq_zero hE A y hj O hyO (εP sZ (A.C y) O c) c
    (fun y' => congrFun (Ψ_εP sZ (A.C y) O c) y') hw'
  subst hc
  erw [map_zero]
  exact map_zero _

omit [IsLocallyNoetherian Z] [LocallyOfFiniteType sZ] [QuasiCompact sZ] cs hmfd in
/-- The points of `E^an` lie over the divisor. -/
private theorem toScheme_κE_mem_supp (x : space (E.suppIdeal.subschemeι ≫ sZ)) :
    (κE sZ E x).toScheme ∈ E.supp := by
  have h : (κE sZ E x).toScheme ∈ Set.range E.suppIdeal.subschemeι := ⟨x.toScheme, rfl⟩
  rw [E.suppIdeal.range_subschemeι] at h
  rw [← SetLike.mem_coe, ← MMP.Mori.DivisorWithCoeffs.coe_support_suppIdeal]
  exact h

/-- The inverse image along `κ : E^an ⟶ Z^an` of abelian sheaves is exact. -/
private theorem exact_map_pullback_κE {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (space sZ))}
    (hS : S.Exact) :
    (S.map (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E))).Exact := by
  haveI : (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).IsLeftAdjoint :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (κE sZ E)).isLeftAdjoint
  haveI := Functor.preservesZeroMorphisms_of_isLeftAdjoint
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E))
  exact hS.map _

/-- **The constants of `E^an` inject into the restricted analytic restriction complex.** -/
private theorem mono_pullback_εZ :
    Mono ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map (εZ n sZ E hE A)) := by
  haveI : (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).IsLeftAdjoint :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (κE sZ E)).isLeftAdjoint
  haveI := Functor.preservesZeroMorphisms_of_isLeftAdjoint
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E))
  rw [Preadditive.mono_iff_isZero_kernel]
  refine IsZero.of_iso ?_ (PreservesKernel.iso (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E))
    (εZ n sZ E hE A)).symm
  refine (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).2 fun x => ?_
  refine IsZero.of_iso ?_ (Stacks.SheafifyStalk.stalkSheafPullbackIso AddCommGrpCat.{0} (κE sZ E)
    (kernel (εZ n sZ E hE A)) x)
  have hinj := stalk_εZ_injective n sZ E hE A (κE sZ E x)
    ((toScheme_mem_supp_iff n sZ E A (κE sZ E x)).1 (toScheme_κE_mem_supp sZ E x))
  have hmono : Mono ((TopCat.Sheaf.forget AddCommGrpCat.{0} (space sZ) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} (κE sZ E x)).map (εZ n sZ E hE A)) :=
    (AddCommGrpCat.mono_iff_injective _).2 hinj
  refine IsZero.of_iso ?_ (PreservesKernel.iso (TopCat.Sheaf.forget AddCommGrpCat.{0} (space sZ) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} (κE sZ E x)) (εZ n sZ E hE A))
  exact isZero_kernel_of_mono _

/-- The analytic restriction complex restricted to `E^an`. -/
private noncomputable abbrev KE : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0}
    (space (E.suppIdeal.subschemeι ≫ sZ))) ℤ :=
  (complexPullback (κE sZ E)).obj (KDan n sZ E hE A)

/-- The constant sheaf `ℂ` on `Z^an`. -/
private noncomputable abbrev constZ :
    TopCat.Sheaf AddCommGrpCat.{0} (space sZ) :=
  (constantSheaf (Opens.grothendieckTopology (space sZ)) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℂ)

private theorem KE_d (k : ℕ) : (KE n sZ E hE A).d (Int.ofNat k) (Int.ofNat k + 1) =
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map (δanD hE A k) := by
  change (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map
    ((KDan n sZ E hE A).d (Int.ofNat k) (Int.ofNat k + 1)) = _
  rw [KDan_d]

/-- **The inclusion of the constants into the restricted analytic restriction complex.** -/
private noncomputable def εE : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).obj (constZ sZ)) ⟶ KE n sZ E hE A :=
  HomologicalComplex.mkHomFromSingle
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map (εZ n sZ E hE A)) (by
      intro k hk
      change (0 : ℤ) + 1 = k at hk
      subst hk
      erw [KE_d n sZ E hE A 0]
      haveI : (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).IsLeftAdjoint :=
        (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (κE sZ E)).isLeftAdjoint
      haveI := Functor.preservesZeroMorphisms_of_isLeftAdjoint
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E))
      exact ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map_comp _ _).symm.trans
        ((congrArg (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map
          (εZ_comp_δanD n sZ E hE A)).trans (Functor.map_zero _ _ _)))

private theorem εE_f_zero : (εE n sZ E hE A).f 0 =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).hom ≫
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map (εZ n sZ E hE A) := by
  unfold εE
  exact HomologicalComplex.mkHomFromSingle_f _ _

private theorem isZero_KE_negSucc (j : ℕ) : IsZero ((KE n sZ E hE A).X (Int.negSucc j)) := by
  haveI : (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).IsLeftAdjoint :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (κE sZ E)).isLeftAdjoint
  haveI := Functor.preservesZeroMorphisms_of_isLeftAdjoint
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E))
  haveI : (analytifyModule sZ).IsLeftAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sZ)).isLeftAdjoint
  haveI := Functor.preservesZeroMorphisms_of_isLeftAdjoint (analytifyModule sZ)
  exact (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map_isZero
    ((SheafOfModules.toSheaf _).map_isZero ((analytifyModule sZ).map_isZero (isZero_zero _)))

/-- **The holomorphic Poincaré lemma for the restriction complex**: on `E^an` the constants resolve
the restricted analytic restriction complex. -/
private theorem quasiIso_εE : QuasiIso (εE n sZ E hE A) := ⟨fun q => by
  rcases q with (_ | k) | j
  · change QuasiIsoAt (εE n sZ E hE A) 0
    rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp), ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨exact_map_pullback_κE sZ E (exact_εZ_δanD n sZ E hE A), mono_pullback_εZ n sZ E hE A⟩
      refine ShortComplex.isoMk (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _)
        (Iso.refl _) (Iso.refl _) ?_ ?_
      · change (HomologicalComplex.singleObjXSelf _ 0 _).hom ≫
          (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map (εZ n sZ E hE A) =
          (εE n sZ E hE A).f 0 ≫ 𝟙 _
        rw [Category.comp_id, εE_f_zero]
      · change 𝟙 _ ≫ (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map (δanD hE A 0) =
          (KE n sZ E hE A).d (Int.ofNat 0) (Int.ofNat 0 + 1) ≫ 𝟙 _
        rw [KE_d, Category.id_comp, Category.comp_id]
    · exact (HomologicalComplex.isZero_single_obj_X (V := TopCat.Sheaf AddCommGrpCat.{0}
        (space (E.suppIdeal.subschemeι ≫ sZ))) (ComplexShape.up ℤ) 0
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).obj (constZ sZ)) (-1)
        (by norm_num)).eq_of_src _ _
    · exact (HomologicalComplex.isZero_single_obj_X (V := TopCat.Sheaf AddCommGrpCat.{0}
        (space (E.suppIdeal.subschemeι ≫ sZ))) (ComplexShape.up ℤ) 0
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).obj (constZ sZ)) 1
        (by norm_num)).eq_of_tgt _ _
    · exact (isZero_KE_negSucc n sZ E hE A 0).eq_of_src _ _
  · rw [quasiIsoAt_iff_exactAt]
    · change (KE n sZ E hE A).ExactAt (Int.ofNat k + 1)
      rw [HomologicalComplex.exactAt_iff' _ (Int.ofNat k) (Int.ofNat k + 1) (Int.ofNat k + 1 + 1)
        (by simp) (by simp)]
      refine (ShortComplex.exact_iff_of_iso ?_).2
        (exact_map_pullback_κE sZ E (exact_δanD hE A k))
      refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
      · change 𝟙 _ ≫ (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map (δanD hE A k) =
          (KE n sZ E hE A).d (Int.ofNat k) (Int.ofNat k + 1) ≫ 𝟙 _
        rw [KE_d, Category.id_comp, Category.comp_id]
      · change 𝟙 _ ≫ (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map
            (δanD hE A (k + 1)) =
          (KE n sZ E hE A).d (Int.ofNat (k + 1)) (Int.ofNat (k + 1) + 1) ≫ 𝟙 _
        rw [KE_d, Category.id_comp, Category.comp_id]
    · exact HomologicalComplex.exactAt_single_obj _ _ _ _ (by change ((k : ℤ) + 1) ≠ 0; omega)
  · rw [quasiIsoAt_iff_exactAt]
    · exact ShortComplex.exact_of_isZero_X₂ _ (isZero_KE_negSucc n sZ E hE A j)
    · exact HomologicalComplex.exactAt_single_obj _ _ _ _ (by simp)⟩

end AnalyticComplex

/-! ### Surjectivity onto the cohomology of `𝒪_{E^an}` -/

section FinalSurjectivity

open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints MMP.DeRhamBetti
open scoped Manifold ContDiff

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (n : ℕ) {Z : Scheme.{0}} (sZ : Z ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n sZ] (hZ : IsProjective sZ)
  (E : MMP.Mori.Divisor Z) (hE : E.IsRelativeSNC n sZ)
  (i : relativeLogDeRhamComplex n sZ E hE E.suppIdeal ⟶ Scheme.Hom.deRhamComplex sZ)
  (hi : ∀ (p : ℕ) (W : Z.Opensᵒᵖ)
    (w : ((relativeLogDeRhamComplex n sZ E hE E.suppIdeal).X p).val.obj W),
    ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι E.supp.compl) sZ).f p).val.app
      W ((i.f p).val.app W w) = w.1)
  (D : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
  (q : Scheme.Hom.deRhamComplex sZ ⟶ D) (hiq : i ≫ q = 0)
  (hq : IsColimit (CokernelCofork.ofπ q hiq))
  [IsLocallyNoetherian Z] [LocallyOfFiniteType sZ] [QuasiCompact sZ]
  [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sZ)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sZ)]
  (A : AdaptedCharts n sZ E)

private theorem KDan_d_neg_one : (KDan n sZ E hE A).d (-1) 0 = 0 :=
  (CochainComplex.of_d _ (δanZ n sZ E hE A) (-1)).trans rfl

/-- **The inclusion of constants factors through the analytic restriction complex**:
`ℂ_{E^an} ⟶ 𝒪_{E^an}` is `ℂ_{E^an} ≅ κ⁻¹ ℂ_{Z^an} ⟶ κ⁻¹ 𝒟_E^{0,an} ≅ 𝒪_{E^an}`. -/
private theorem homEquiv_symm_const_eq
    (θ : (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).obj ((KDan n sZ E hE A).X 0) ≅
      (sheafCompose (Opens.grothendieckTopology (space (E.suppIdeal.subschemeι ≫ sZ)))
          (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf (E.suppIdeal.subschemeι ≫ sZ)))
    (hθ : ∀ (V : Z.Opens) (g : Γ(Z, V)),
        (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (κE sZ E)).unit.app _ ≫
            (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (κE sZ E)).map θ.hom).hom.app
          (op ((Opens.map (toSchemeHom sZ)).obj V)))
          (((analytifyModuleUnit sZ (cokernelLogToForms sZ (isLocalSectionRel_twisted
            sZ hE (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0)).val.app (op V)).hom
            (((cokernel.π (logToForms sZ ((isLocalSectionRel_twisted sZ hE
              (forall_mem_weakChart_of_isRelativeSNC n sZ E hE)) 0))).val.app (op V)).hom
              (((Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.app (op V)).hom g))) =
        ((ringCatSheafHom (E.suppIdeal.subschemeι ≫ sZ)).hom.app
          (op (E.suppIdeal.subschemeι ⁻¹ᵁ V))).hom ((E.suppIdeal.subschemeι.app V).hom g)) :
    ((constantSheafAdj (Opens.grothendieckTopology (space (E.suppIdeal.subschemeι ≫ sZ)))
        AddCommGrpCat.{0} isTerminalTop).homEquiv (AddCommGrpCat.of ℂ)
          ((sheafCompose (Opens.grothendieckTopology (space (E.suppIdeal.subschemeι ≫ sZ)))
            (forget₂ RingCat AddCommGrpCat)).obj
              (ringCatSheaf (E.suppIdeal.subschemeι ≫ sZ)))).symm
        (AddCommGrpCat.ofHom ((sharpHom (sX := E.suppIdeal.subschemeι ≫ sZ) ⊤).comp
          (ComplexPoints.baseRingHom (E.suppIdeal.subschemeι ≫ sZ) ⊤)).toAddMonoidHom) =
      (constantSheafPullbackIso (κE sZ E)).hom.app (AddCommGrpCat.of ℂ) ≫
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map (εZ n sZ E hE A) ≫ θ.hom := by
  refine (Equiv.symm_apply_eq _).2 ?_
  erw [homEquiv_constantSheafPullbackIso_hom_app_comp]
  have hnat : (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (κE sZ E)).unit.app
        (constZ sZ) ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (κE sZ E)).map
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map (εZ n sZ E hE A) ≫ θ.hom) =
      εZ n sZ E hE A ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (κE sZ E)).unit.app _ ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (κE sZ E)).map θ.hom) := by
    erw [Functor.map_comp, ← Category.assoc, Adjunction.unit_naturality, Category.assoc]
  erw [hnat]
  ext a
  change (sharpHom (sX := E.suppIdeal.subschemeι ≫ sZ) ⊤)
      (ComplexPoints.baseRingHom (E.suppIdeal.subschemeι ≫ sZ) ⊤ a) =
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (κE sZ E)).unit.app _ ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (κE sZ E)).map θ.hom).hom.app (op ⊤)
      ((εZ n sZ E hE A).hom.app (op ⊤)
        (((constantSheafAdj (Opens.grothendieckTopology (space sZ)) AddCommGrpCat.{0}
          isTerminalTop).unit.app (AddCommGrpCat.of ℂ)) a))
  rw [constantSheafAdj_unit_app]
  erw [εZ_app_top_toSheafify n sZ E hE A a]
  refine Eq.trans ?_ (hθ ⊤ (ComplexPoints.baseRingHom sZ ⊤ a)).symm
  change (sharpHom (sX := E.suppIdeal.subschemeι ≫ sZ) ⊤) _ =
    (sharpHom (sX := E.suppIdeal.subschemeι ≫ sZ) (E.suppIdeal.subschemeι ⁻¹ᵁ ⊤)) _
  rw [app_top_baseRingHom E.suppIdeal.subschemeι sZ a]
  rfl

/-- The projection of `𝒟_E^•` onto its degree-zero term, pulled back to `Z^an` and followed by
the analytification of `𝒟_E^0`, is the comparison `ιD` followed by the projection of
`𝒟_E^{an,•}` onto its degree-zero term. -/
private theorem kdanSurj_complexPullback_map_toSingleZero_comp_eq :
    (complexPullback (toSchemeHom sZ)).map
        (toSingleZero _ (cokZK_d_neg_one n sZ E hE i hi D q hiq hq)) ≫
        ((HomologicalComplex.singleMapHomologicalComplex
            (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)) (ComplexShape.up ℤ)
            0).hom.app ((SheafOfModules.toSheaf _).obj (cokZF n sZ E hE 0)) ≫
          (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
            (analytifyModuleι sZ (cokZF n sZ E hE 0))) =
      ιD n sZ E hE i hi D q hiq hq A ≫ toSingleZero _ (KDan_d_neg_one n sZ E hE A) := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    show ((complexPullback (toSchemeHom sZ)).map
        (toSingleZero _ (cokZK_d_neg_one n sZ E hE i hi D q hiq hq))).f 0 =
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)).map
        ((toSingleZero _ (cokZK_d_neg_one n sZ E hE i hi D q hiq hq)).f 0) from rfl,
    toSingleZero_f, toSingleZero_f]
  have e2 : ((HomologicalComplex.singleMapHomologicalComplex
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)) (ComplexShape.up ℤ)
        0).hom.app ((SheafOfModules.toSheaf _).obj (cokZF n sZ E hE 0))).f 0 =
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            ((SheafOfModules.toSheaf _).obj (cokZF n sZ E hE 0))).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)).obj
            ((SheafOfModules.toSheaf _).obj (cokZF n sZ E hE 0)))).inv :=
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self _ _ _ _
  have e3 : ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        (analytifyModuleι sZ (cokZF n sZ E hE 0))).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).hom ≫
        analytifyModuleι sZ (cokZF n sZ E hE 0) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv :=
    HomologicalComplex.single_map_f_self _ _ _
  rw [e2, e3]
  exact map_iso_chain_comp_eq (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ))
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _)
    (analytifyModuleι sZ (cokZF n sZ E hE 0))
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _)

include hZ hi hq A in
/-- **GAGA for `𝒟_E^0`**: the comparison `H^m(Z, 𝒟_E^0) ⟶ H^m(Z^an, 𝒟_E^{0,an})`, read on
hypercohomology of complexes concentrated in degree `0`, is an isomorphism. -/
private theorem kdanSurj_isIso_hypercohomologyPullback_comp_map_single_analytifyModuleι (m : ℕ) :
    IsIso (hypercohomologyPullback (toSchemeHom sZ) _ m ≫
      (hypercohomology (space sZ) m).map
        ((HomologicalComplex.singleMapHomologicalComplex
            (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)) (ComplexShape.up ℤ)
            0).hom.app ((SheafOfModules.toSheaf _).obj (cokZF n sZ E hE 0)) ≫
          (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
            (analytifyModuleι sZ (cokZF n sZ E hE 0)))) := by
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have he := MMP.Analytic.hypercohomologyComparison_single sZ (cokZF n sZ E hE 0) 0 m
  haveI := MMP.Analytic.isIso_comparisonMap_of_isProjective sZ hZ (cokZF n sZ E hE 0)
    (isCoherent_cokZF n sZ E hE 0) ((m : ℤ) - 0)
  have : IsIso (MMP.Analytic.hypercohomologyComparison sZ
      (MMP.Analytic.singleAnalytifyModuleι sZ (cokZF n sZ E hE 0) 0) m ≫
      (MMP.Analytic.hypercohomologySingleIso (space sZ) 0 m).hom.app ((SheafOfModules.toSheaf _).obj
          ((analytifyModule sZ).obj (cokZF n sZ E hE 0)))) := by
    rw [he]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom
      ((MMP.Analytic.hypercohomologySingleIso Z.carrier 0 m).app _)) inferInstance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom
    ((MMP.Analytic.hypercohomologySingleIso (space sZ) 0 m).app _)) this

/-- The square comparing the degree-zero projections of `𝒟_E^•` and of `𝒟_E^{an,•}` on
hypercohomology commutes. -/
private theorem kdanSurj_hypercohomology_map_toSingleZero_comp_eq (m : ℕ) :
    (hypercohomology Z.carrier m).map
        (toSingleZero _ (cokZK_d_neg_one n sZ E hE i hi D q hiq hq)) ≫
        (hypercohomologyPullback (toSchemeHom sZ) _ m ≫
          (hypercohomology (space sZ) m).map
            ((HomologicalComplex.singleMapHomologicalComplex
                (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)) (ComplexShape.up ℤ)
                0).hom.app ((SheafOfModules.toSheaf _).obj (cokZF n sZ E hE 0)) ≫
              (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
                (analytifyModuleι sZ (cokZF n sZ E hE 0)))) =
      (hypercohomologyPullback (toSchemeHom sZ) (cokZK n sZ E hE i hi D q hiq hq) m ≫
        (hypercohomology (space sZ) m).map (ιD n sZ E hE i hi D q hiq hq A)) ≫
        (hypercohomology (space sZ) m).map (toSingleZero _ (KDan_d_neg_one n sZ E hE A)) := by
  rw [hypercohomology_map_comp_hypercohomologyPullback_assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp,
    kdanSurj_complexPullback_map_toSingleZero_comp_eq n sZ E hE i hi D q hiq hq A]

include hZ hi hq in
/-- **The edge map of the analytic restriction complex is onto**: by GAGA, the projection of
`𝒟_E^{an,•}` onto its degree-zero term is surjective on hypercohomology over `Z^an`. -/
private theorem surjective_hypercohomology_map_toSingleZero_KDan (m : ℕ) :
    Function.Surjective ((hypercohomology (space sZ) m).map
      (toSingleZero _ (KDan_d_neg_one n sZ E hE A))) := by
  haveI := isIso_hypercohomologyPullback_comp_map_ιD n sZ E hE i hi D q hiq hq A hZ m
  haveI := kdanSurj_isIso_hypercohomologyPullback_comp_map_single_analytifyModuleι n sZ hZ E hE i hi D q
    hiq hq A m
  exact surjective_of_comm _ _
    (asIso (hypercohomologyPullback (toSchemeHom sZ) (cokZK n sZ E hE i hi D q hiq hq) m ≫
        (hypercohomology (space sZ) m).map (ιD n sZ E hE i hi D q hiq hq A)))
    (asIso (hypercohomologyPullback (toSchemeHom sZ) _ m ≫
      (hypercohomology (space sZ) m).map
        ((HomologicalComplex.singleMapHomologicalComplex
            (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sZ)) (ComplexShape.up ℤ)
            0).hom.app ((SheafOfModules.toSheaf _).obj (cokZF n sZ E hE 0)) ≫
          (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
            (analytifyModuleι sZ (cokZF n sZ E hE 0)))))
    (kdanSurj_hypercohomology_map_toSingleZero_comp_eq n sZ E hE i hi D q hiq hq A m)
    (surjective_hypercohomology_map_toSingleZero_cokZK n sZ hZ E hE i hi D q hiq hq m)

include hZ hi hq in
/-- **The edge map of the restricted analytic restriction complex is onto**: the projection of
`κ⁻¹ 𝒟_E^{an,•}` onto its degree-zero term is surjective on hypercohomology over `E^an`, the
terms of `𝒟_E^{an,•}` being supported on `E^an`. -/
private theorem surjective_hypercohomology_map_complexPullback_toSingleZero_KDan
    (hrange : ∀ y : ComplexPoints sZ, y.toScheme ∈ E.supp → y ∈ Set.range (κE sZ E)) (m : ℕ) :
    Function.Surjective ((hypercohomology (space (E.suppIdeal.subschemeι ≫ sZ)) m).map
      ((complexPullback (κE sZ E)).map (toSingleZero _ (KDan_d_neg_one n sZ E hE A)))) := by
  have hemb : Topology.IsClosedEmbedding (κE sZ E) :=
    ((MMP.Analytic.analytification_stalks (E.suppIdeal.subschemeι ≫ sZ)).2.2.2.2.2.2.2.2.2.2
      sZ E.suppIdeal.subschemeι rfl).1
  have hK1 : ∀ q, ∀ x ∉ Set.range (κE sZ E),
      Subsingleton (((KDan n sZ E hE A).X q).presheaf.stalk x) := fun q x hx =>
    subsingleton_stalk_KDan n sZ E hE A x (fun h => hx (hrange x h)) q
  have hK2 : ∀ q, ∀ x ∉ Set.range (κE sZ E),
      Subsingleton ((((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((KDan n sZ E hE A).X 0)).X q).presheaf.stalk x) := fun q x hx =>
    subsingleton_stalk_single_obj_X _ x (hK1 0 x hx) q
  haveI := isIso_hypercohomologyPullback_of_isClosedEmbedding (κE sZ E) hemb _ hK1 m
  haveI := isIso_hypercohomologyPullback_of_isClosedEmbedding (κE sZ E) hemb _ hK2 m
  exact surjective_of_comm _ _
    (asIso (hypercohomologyPullback (κE sZ E) (KDan n sZ E hE A) m))
    (asIso (hypercohomologyPullback (κE sZ E) ((HomologicalComplex.single _ (ComplexShape.up ℤ)
      0).obj ((KDan n sZ E hE A).X 0)) m))
    (hypercohomology_map_comp_hypercohomologyPullback (κE sZ E)
      (toSingleZero _ (KDan_d_neg_one n sZ E hE A)) m)
    (surjective_hypercohomology_map_toSingleZero_KDan n sZ hZ E hE i hi D q hiq hq A m)

include hZ hi hq A in
/-- **`H^j(E^an, ℂ) ⟶ H^j(E^an, 𝒪_{E^an})` is onto.** -/
private theorem surjective_sheafCohomology_map_homEquiv_symm
    (hrange : ∀ y : ComplexPoints sZ, y.toScheme ∈ E.supp → y ∈ Set.range (κE sZ E)) (j : ℕ) :
    Function.Surjective ((sheafCohomology (space (E.suppIdeal.subschemeι ≫ sZ)) j).map
      (((constantSheafAdj (Opens.grothendieckTopology (space (E.suppIdeal.subschemeι ≫ sZ)))
        AddCommGrpCat.{0} isTerminalTop).homEquiv (AddCommGrpCat.of ℂ)
          ((sheafCompose (Opens.grothendieckTopology (space (E.suppIdeal.subschemeι ≫ sZ)))
            (forget₂ RingCat AddCommGrpCat)).obj
              (ringCatSheaf (E.suppIdeal.subschemeι ≫ sZ)))).symm
        (AddCommGrpCat.ofHom ((sharpHom (sX := E.suppIdeal.subschemeι ≫ sZ) ⊤).comp
          (ComplexPoints.baseRingHom (E.suppIdeal.subschemeι ≫ sZ) ⊤)).toAddMonoidHom))) := by
  obtain ⟨θ, hθ⟩ := exists_pullback_toSheaf_analytify_cokernel_zero_iso n sZ hZ E hE i hi
  rw [homEquiv_symm_const_eq n sZ E hE A θ hθ]
  have e : (sheafCohomology (space (E.suppIdeal.subschemeι ≫ sZ)) j).map
      ((constantSheafPullbackIso (κE sZ E)).hom.app (AddCommGrpCat.of ℂ) ≫
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map (εZ n sZ E hE A) ≫ θ.hom) =
      (sheafCohomology (space (E.suppIdeal.subschemeι ≫ sZ)) j).map
          ((constantSheafPullbackIso (κE sZ E)).hom.app (AddCommGrpCat.of ℂ)) ≫
        (sheafCohomology (space (E.suppIdeal.subschemeι ≫ sZ)) j).map
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map (εZ n sZ E hE A)) ≫
        (sheafCohomology (space (E.suppIdeal.subschemeι ≫ sZ)) j).map θ.hom :=
    ((sheafCohomology _ j).map_comp _ _).trans
      (congrArg (fun t => (sheafCohomology (space (E.suppIdeal.subschemeι ≫ sZ)) j).map
          ((constantSheafPullbackIso (κE sZ E)).hom.app (AddCommGrpCat.of ℂ)) ≫ t)
        ((sheafCohomology _ j).map_comp _ _))
  refine (congrArg (fun φ => Function.Surjective (ConcreteCategory.hom φ)) e).mpr ?_
  haveI : IsIso ((sheafCohomology (space (E.suppIdeal.subschemeι ≫ sZ)) j).map
      ((constantSheafPullbackIso (κE sZ E)).hom.app (AddCommGrpCat.of ℂ))) :=
    @Functor.map_isIso _ _ _ _ _ _ (sheafCohomology _ j) _
      ((constantSheafPullbackIso (κE sZ E)).app (AddCommGrpCat.of ℂ)).isIso_hom
  haveI : IsIso ((sheafCohomology (space (E.suppIdeal.subschemeι ≫ sZ)) j).map θ.hom) :=
    @Functor.map_isIso _ _ _ _ _ _ (sheafCohomology _ j) _ θ.isIso_hom
  refine surjective_comp_of_surjective _ _
    (ConcreteCategory.bijective_of_isIso ((sheafCohomology (space (E.suppIdeal.subschemeι ≫ sZ))
      j).map ((constantSheafPullbackIso (κE sZ E)).hom.app (AddCommGrpCat.of ℂ)))).2
    (surjective_comp_of_surjective _ _ ?_
      (ConcreteCategory.bijective_of_isIso ((sheafCohomology (space (E.suppIdeal.subschemeι ≫ sZ))
        j).map θ.hom)).2)
  change Function.Surjective ((hypercohomology _ j).map ((HomologicalComplex.single _
    (ComplexShape.up ℤ) 0).map ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map
      (εZ n sZ E hE A))))
  have hfac : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).map (εZ n sZ E hE A)) =
      εE n sZ E hE A ≫ (complexPullback (κE sZ E)).map
        (toSingleZero _ (KDan_d_neg_one n sZ E hE A)) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)) (ComplexShape.up ℤ) 0).hom.app
          ((KDan n sZ E hE A).X 0) := by
    apply HomologicalComplex.to_single_hom_ext
    simp only [HomologicalComplex.comp_f, εE_f_zero, Functor.mapHomologicalComplex_map_f,
      toSingleZero_f, HomologicalComplex.single_map_f_self, Category.assoc]
    erw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    exact comp_map_iso_chain_eq (TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)) _ _
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _) _
  haveI : QuasiIso (εE n sZ E hE A) := quasiIso_εE n sZ E hE A
  let K : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{0}
      (space (E.suppIdeal.subschemeι ≫ sZ))) :=
    ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (κE sZ E)).obj (constZ sZ)), 0,
      (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
        HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩
  let L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{0}
      (space (E.suppIdeal.subschemeι ≫ sZ))) :=
    ⟨KE n sZ E hE A, 0, (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi => by
      rcases i with k | k
      · exact absurd hi (not_lt.2 (Int.natCast_nonneg k))
      · exact isZero_KE_negSucc n sZ E hE A k⟩
  haveI : QuasiIso (ObjectProperty.homMk (P := _) (X := K) (Y := L) (εE n sZ E hE A)).hom :=
    quasiIso_εE n sZ E hE A
  haveI : IsIso ((hypercohomology (space (E.suppIdeal.subschemeι ≫ sZ)) j).map
      (εE n sZ E hE A)) :=
    MMP.DeRhamBetti.DRCmp.isIso_hypercohomology_map_of_quasiIso (space (E.suppIdeal.subschemeι ≫ sZ))
      (ObjectProperty.homMk (P := _) (X := K) (Y := L) (εE n sZ E hE A)) j
  rw [hfac, Functor.map_comp, Functor.map_comp]
  exact surjective_comp_of_surjective _ _ (ConcreteCategory.bijective_of_isIso _).2
    (surjective_comp_of_surjective _ _
      (surjective_hypercohomology_map_complexPullback_toSingleZero_KDan n sZ hZ E hE i hi D q hiq
        hq A hrange j) (ConcreteCategory.bijective_of_isIso _).2)

end FinalSurjectivity

private theorem solution : ∀ (n : ℕ) {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n sZ] (hZ : IsProjective sZ)
    (E : MMP.Mori.Divisor Z) (hE : E.IsRelativeSNC n sZ)
    -- the inclusion `Ω^•_Z(log E)(-E) ⟶ Ω^•_Z`, pinned by its restriction to `U = Z ∖ E`
    (i : relativeLogDeRhamComplex n sZ E hE E.suppIdeal ⟶ Scheme.Hom.deRhamComplex sZ)
    (hi : ∀ (p : ℕ) (W : Z.Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n sZ E hE E.suppIdeal).X p).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι E.supp.compl) sZ).f p).val.app
        W ((i.f p).val.app W ω) = ω.1)
    -- the quotient `𝒟_E^• = Ω^•_Z / Ω^•_Z(log E)(-E)`
    (D : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
    (q : Scheme.Hom.deRhamComplex sZ ⟶ D) (hiq : i ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hiq)),
    -- `ℍ^j(Z, L)` over `Γ(Spec ℂ, ⊤) = ℂ`, for a bounded below complex of `sZ⁻¹𝒪`-modules
    let H : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) →
        ℤ → ModuleCat.{0} Γ(Spec (CommRingCat.of ℂ), ⊤) := fun L j =>
      let Γd := (SheafOfModules.evaluation.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (CommRingCat.of ℂ)).sheaf))
          (op ⊤)).rightDerivedFunctorPlus
      let Mj := (DerivedCategory.homologyFunctor _ j).obj
        (DerivedCategory.Plus.ι.obj (Γd.obj (DerivedCategory.Plus.Q.obj L)))
      (ModuleCat.restrictScalars.{0} (show Γ(Spec (CommRingCat.of ℂ), ⊤) →+*
          ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj
            (Spec (CommRingCat.of ℂ)).sheaf).obj.obj (op ⊤) from
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} sZ.base).unit.app
          (Spec (CommRingCat.of ℂ)).sheaf).hom.app (op ⊤)).hom)).obj Mj
    -- `E` as a complex scheme, and its analytification
    let sE : E.suppIdeal.subscheme ⟶ Spec (CommRingCat.of ℂ) := E.suppIdeal.subschemeι ≫ sZ
    let J := Opens.grothendieckTopology (MMP.Analytic.Analytification.space sE)
    let 𝒪an := (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj
      (MMP.Analytic.ringCatSheaf sE)
    -- the inclusion of constants `ℂ_E ⟶ 𝒪_E^an`
    let c : (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℂ) ⟶ 𝒪an :=
      ((constantSheafAdj J AddCommGrpCat.{0} isTerminalTop).homEquiv _ _).symm
        (AddCommGrpCat.ofHom
          ((MMP.Analytic.Analytification.sharpHom (sX := sE) ⊤).comp
            (MMP.Analytic.ComplexPoints.baseRingHom sE ⊤)).toAddMonoidHom)
    (∀ k : ℕ, Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (H ⟨D.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
      ∑ p ∈ Finset.range (k + 1), Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (H ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (D.X p), 0,
          (CochainComplex.isStrictlyGE_iff _ 0).2 fun m hm =>
            HomologicalComplex.isZero_single_obj_X _ 0 _ m (by omega)⟩ ((k - p : ℕ) : ℤ))) ∧
    (∀ (W : Z.affineOpens) (g : Γ(Z, W)),
      (q.f 0).val.app (op (W : Z.Opens))
          ((Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.app (op (W : Z.Opens)) g) =
        0 ↔ g ∈ E.suppIdeal.ideal W) ∧
    ∀ j : ℕ, Function.Surjective
      ((MMP.Analytic.sheafCohomology (MMP.Analytic.Analytification.space sE) j).map c).hom  := by
  intro n Z sZ _ hZ E hE i hi D q hiq hq H sE J 𝒪an c
  refine ⟨?degen, ?zero, ?surj⟩
  case degen =>
    intro k
    exact finrank_hc_cokernel_eq_sum n sZ hZ E hE i hi D q hiq hq k
  case zero =>
    intro W g
    have hi0 : ∀ (W : Z.Opens) (ω : ((relativeLogDeRhamComplex n sZ E hE E.suppIdeal).X 0).val.obj
        (op W)), ρ0 sZ E W ((i.f 0).val.app (op W) ω) = ω.1 := fun W ω => hi 0 (op W) ω
    have hzero := comp_toSubschemeFunctions_eq_zero sZ hE (i.f 0) hi0
    have hcomp : i.f 0 ≫ toSubschemeFunctions sZ E.suppIdeal = 0 := by
      ext W x
      exact hzero W.unop x
    have hq0 : IsColimit (CokernelCofork.ofπ (q.f 0)
        (by rw [← HomologicalComplex.comp_f, hiq, HomologicalComplex.zero_f]) :
          Cofork (i.f 0) 0) :=
      isColimitCoforkMapOfIsColimit' (HomologicalComplex.eval _ _ 0) _ hq
    have hψ := hq0.fac (CokernelCofork.ofπ _ hcomp) WalkingParallelPair.one
    constructor
    · intro h
      have e := congrArg (fun φ => φ.val.app (op (W : Z.Opens)) (z0 sZ g)) hψ
      have e' : (toSubschemeFunctions sZ E.suppIdeal).val.app (op (W : Z.Opens)) (z0 sZ g) = 0 :=
        e.symm.trans ((congrArg ((hq0.desc (CokernelCofork.ofπ _ hcomp)).val.app
          (op (W : Z.Opens))) h).trans (map_zero _))
      rw [← E.suppIdeal.ker_subschemeι_app W]
      rwa [toSubschemeFunctions_z0] at e'
    · intro hg
      obtain ⟨x, hx⟩ := exists_relativeLogDeRhamComplex_X_zero sZ hE E.suppIdeal W hg
      have hx' : (i.f 0).val.app (op (W : Z.Opens)) x = z0 sZ g :=
        ρ0_injective sZ hE W (by rw [hi0, hx])
      refine (congrArg ((q.f 0).val.app (op (W : Z.Opens))) hx'.symm).trans ?_
      exact congrArg (fun φ => φ.val.app (op (W : Z.Opens)) x)
        (congrArg (fun φ => φ.f 0) hiq)
  case surj =>
    intro j
    haveI : IsProper sZ := hZ.isProper
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    obtain ⟨cs, hmfd, ⟨A⟩⟩ := exists_adaptedCharts n sZ E hE
    letI := cs
    haveI := hmfd
    have hrange : ∀ y : MMP.Analytic.ComplexPoints sZ, y.toScheme ∈ E.supp →
        y ∈ Set.range (κE sZ E) := fun y hy => by
      rw [MMP.Analytic.range_analyticMap_subschemeι sZ E.suppIdeal]
      change y.toScheme ∈ E.suppIdeal.support
      rw [← SetLike.mem_coe, MMP.Mori.DivisorWithCoeffs.coe_support_suppIdeal]
      exact hy
    exact surjective_sheafCohomology_map_homEquiv_symm n sZ hZ E hE i hi D q hiq hq A hrange j

end Proof_thm_mmp_conductor_snc_restriction_degeneration

end

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

namespace MMP.Mori.Divisor.IsRelativeSNC

/-- **The restriction complex of a simple normal crossing divisor.** Let `sZ : Z ⟶ Spec ℂ` be
smooth of relative dimension `n` and projective, and `E` a (reduced) simple normal crossing
divisor on `Z`. Let `q : Ω^•_Z ⟶ D` be a cokernel of the inclusion
`i : Ω^•_Z(log E)(-E) ⟶ Ω^•_Z`, so that `D = 𝒟_E^• = Ω^•_Z / Ω^•_Z(log E)(-E)`. Then
1. the Hodge-to-de Rham spectral sequence of `D` degenerates at `E₁`:
   `dim_ℂ ℍ^k(Z, D) = ∑_{p ≤ k} dim_ℂ H^{k-p}(Z, D^p)` for every `k`;
2. `D^0 = 𝒪_E`: a function `g` on an affine open is killed by `Ω^0_Z = 𝒪_Z ⟶ D^0` if and only if
   it lies in the ideal of `E`;
3. the inclusion of constants `ℂ_E ⟶ 𝒪_E^an` induces surjections
   `H^i(E^an, ℂ) ⟶ H^i(E^an, 𝒪_E^an)` for every `i`. -/
@[mmp "thm_mmp_conductor_snc_restriction_degeneration"]
public theorem restrictionComplex_degenerates_and_surjective (n : ℕ) {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n sZ] (hZ : IsProjective sZ)
    (E : Divisor Z) (hE : E.IsRelativeSNC n sZ)
    -- the inclusion `Ω^•_Z(log E)(-E) ⟶ Ω^•_Z`, pinned by its restriction to `U = Z ∖ E`
    (i : relativeLogDeRhamComplex n sZ E hE E.suppIdeal ⟶ Scheme.Hom.deRhamComplex sZ)
    (hi : ∀ (p : ℕ) (W : Z.Opensᵒᵖ)
      (ω : ((relativeLogDeRhamComplex n sZ E hE E.suppIdeal).X p).val.obj W),
      ((Stacks.DeRhamPullback.deRhamPushforwardChain (Scheme.Opens.ι E.supp.compl) sZ).f p).val.app
        W ((i.f p).val.app W ω) = ω.1)
    -- the quotient `𝒟_E^• = Ω^•_Z / Ω^•_Z(log E)(-E)`
    (D : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
    (q : Scheme.Hom.deRhamComplex sZ ⟶ D) (hiq : i ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hiq)) :
    -- `ℍ^j(Z, L)` over `Γ(Spec ℂ, ⊤) = ℂ`, for a bounded below complex of `sZ⁻¹𝒪`-modules
    let H : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) →
        ℤ → ModuleCat.{0} Γ(Spec (CommRingCat.of ℂ), ⊤) := fun L j =>
      let Γd := (SheafOfModules.evaluation.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj (Spec (CommRingCat.of ℂ)).sheaf))
          (op ⊤)).rightDerivedFunctorPlus
      let Mj := (DerivedCategory.homologyFunctor _ j).obj
        (DerivedCategory.Plus.ι.obj (Γd.obj (DerivedCategory.Plus.Q.obj L)))
      (ModuleCat.restrictScalars.{0} (show Γ(Spec (CommRingCat.of ℂ), ⊤) →+*
          ((TopCat.Sheaf.pullback CommRingCat.{0} sZ.base).obj
            (Spec (CommRingCat.of ℂ)).sheaf).obj.obj (op ⊤) from
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} sZ.base).unit.app
          (Spec (CommRingCat.of ℂ)).sheaf).hom.app (op ⊤)).hom)).obj Mj
    -- `E` as a complex scheme, and its analytification
    let sE : E.suppIdeal.subscheme ⟶ Spec (CommRingCat.of ℂ) := E.suppIdeal.subschemeι ≫ sZ
    let J := Opens.grothendieckTopology (MMP.Analytic.Analytification.space sE)
    let 𝒪an := (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj
      (MMP.Analytic.ringCatSheaf sE)
    -- the inclusion of constants `ℂ_E ⟶ 𝒪_E^an`
    let c : (constantSheaf J AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℂ) ⟶ 𝒪an :=
      ((constantSheafAdj J AddCommGrpCat.{0} isTerminalTop).homEquiv _ _).symm
        (AddCommGrpCat.ofHom
          ((MMP.Analytic.Analytification.sharpHom (sX := sE) ⊤).comp
            (MMP.Analytic.ComplexPoints.baseRingHom sE ⊤)).toAddMonoidHom)
    (∀ k : ℕ, Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (H ⟨D.extend ComplexShape.embeddingUpNat, 0,
          CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ k) =
      ∑ p ∈ Finset.range (k + 1), Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
        (H ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (D.X p), 0,
          (CochainComplex.isStrictlyGE_iff _ 0).2 fun m hm =>
            HomologicalComplex.isZero_single_obj_X _ 0 _ m (by omega)⟩ ((k - p : ℕ) : ℤ))) ∧
    (∀ (W : Z.affineOpens) (g : Γ(Z, W)),
      (q.f 0).val.app (op (W : Z.Opens))
          ((Scheme.Hom.relativeDifferentialFormsZeroIso sZ).inv.val.app (op (W : Z.Opens)) g) =
        0 ↔ g ∈ E.suppIdeal.ideal W) ∧
    ∀ j : ℕ, Function.Surjective
      ((MMP.Analytic.sheafCohomology (MMP.Analytic.Analytification.space sE) j).map c).hom := by
  revert n Z sZ hZ E hE; exact Proof_thm_mmp_conductor_snc_restriction_degeneration.solution

end MMP.Mori.Divisor.IsRelativeSNC
