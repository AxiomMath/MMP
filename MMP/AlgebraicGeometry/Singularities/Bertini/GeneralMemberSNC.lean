module
public import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent

/-!
# A general member of a free linear system stays snc on a log resolution

Let `X` be a normal variety over an algebraically closed field `k` of characteristic zero, `(X, Δ)`
a pair with `Δ` a `ℚ`-divisor, `|V|` a free linear system on `X` spanned by sections `s_i` of
`𝒪_X(H)`, and `f : Y ⟶ X` a log resolution of `(X, Δ)` with `f`-exceptional prime divisors
`E_1, …, E_r`, such that `∑_j f⁻¹_* D_j` is smooth. For a general member `H_g = (σ)₀` of `|V|`, the
divisor `f^*H_g + ∑_j f⁻¹_* D_j + ∑_i E_i`, all of whose coefficients are `1`, is a reduced snc
divisor on `Y`, and `f^*H_g` is smooth: its components are pairwise disjoint. In particular `f`
is also a log resolution of `(X, Δ + H_g)`.

## Main results

* `MMP.Mori.exists_polynomial_zeroDivisor_eq_sum_isSNC`: Bertini for a free system on a smooth
  variety, in Weil-divisor form, with an arbitrary reduced snc boundary.
* `MMP.Mori.exists_polynomial_dualPoint_mem`: a dense open of `ℙᴺ_k` contains the points `[c]`
  off the zero locus of a nonzero polynomial.
* `MMP.Mori.exists_affine_zeroScheme_ideal_eq_span`,
  `MMP.Mori.exists_isLocalEquation_stalk_zeroScheme_eq_span`: near every point, the zero scheme
  of a section of `𝒪_Y(D)` is cut out by a local equation of its divisor of zeros.
* `MMP.Mori.coeff_zeroDivisor_eq_one_of_isReduced`, `MMP.Mori.coeff_zeroDivisor_eq_zero_of_notMem`,
  `MMP.Mori.mem_nonvanishingOpen_of_notMem_supp`: the divisor of zeros against the zero scheme.
* `MMP.Mori.disjoint_support_of_mem_componentsOf`: the components of a smooth divisor are
  pairwise disjoint.
* `MMP.Mori.exists_polynomial_pullback_zeroDivisor_eq_sum_isSNC_of_isDominant`: Bertini for a
  system pulled back along a dominant morphism from a smooth variety, free on its image, with an
  arbitrary reduced snc boundary; `MMP.Mori.exists_polynomial_pullback_zeroDivisor_eq_sum_isSNC`
  is the case of a smooth resolution and a free system.
* `MMP.Mori.pullSec`: the pull-back `H⁰(X, 𝒪_X(H)) → H⁰(Y, 𝒪_Y(f^*H))` along a dominant
  morphism, with `MMP.Mori.isPullback_zeroDivisor_pullSec`: `f^*(s)₀ = (f^*s)₀`.
* `MMP.Mori.IsLogResolution.exists_polynomial_isSNC_pullback_zeroDivisor_add`: Kollár–Mori,
  Lemma 5.17: for a general member `H_g` of a free system and a log resolution `f` of `(X, Δ)`,
  `f^*H_g + ∑ F` is a reduced snc divisor and `f^*H_g` is smooth.
* `MMP.Mori.IsLogResolution.exists_polynomial_isSNC_pullback_zeroDivisor_add'`: the same
  without the smoothness of `∑_j f⁻¹_* D_j`, which the proof does not need.

## Implementation notes

A member of `|V|` is the divisor of zeros `(σ)₀` of a nonzero section `σ = ∑_i c_i s_i`, and
*general* means: for every coefficient vector `c` off the zero locus of a nonzero polynomial
`Q` in the coefficients. As `c ↦ σ` is a linear surjection onto `V`, this is the same as `σ`
ranging over a dense Zariski open subset of `V`, or `[σ]` over a dense open subset of `ℙ(V)`.

The reduced divisor `∑_j f⁻¹_* D_j + ∑_i E_i` is written as the sum, with coefficient `1`, of
the prime divisors which are components of `f⁻¹_* Δ` or `f`-exceptional; "reduced" for the total
sum says that `f^*H_g` is reduced and shares no component with it.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Lemma 5.17
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Mori

private theorem support_sum_single {Y : Scheme.{u}} (S : Finset (PrimeDivisor Y)) :
    (∑ F ∈ S, Finsupp.single F (1 : ℤ)).support = S := by
  classical
  ext F; simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

private theorem exists_of_mem_support_mapPrimeDivisors {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R]
    (φ : PrimeDivisor X → Option (PrimeDivisor Y))
    (D : DivisorWithCoeffs R X) (F : PrimeDivisor Y)
    (hF : F ∈ (DivisorWithCoeffs.mapPrimeDivisors φ D).support) :
    ∃ D' ∈ D.support, φ D' = some F := by
  classical
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum] at hF
  obtain ⟨D', hD', hF'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hF)
  refine ⟨D', hD', ?_⟩
  cases h : φ D' with
  | none => simp [h] at hF'
  | some G =>
    simp only [h, Option.elim_some, Finsupp.singleAddHom_apply] at hF'
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hF')]

open Classical in
/-- The reduced boundary `∑_j f⁻¹_* D_j + ∑_i E_i` of a log resolution is snc: its components
lie in the snc subset `Ex(f) ∪ f⁻¹(Supp Δ)`, hence are among the components of that subset. -/
private theorem isSNC_boundary {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian Y] [IsNormal Y] {Δ : QDivisor X} (hΔ : IsPair sX Δ) {f : Y ⟶ X}
    (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f) (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ F : PrimeDivisor Y, F ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap F) :
    DivisorWithCoeffs.IsSNC (f ≫ sX)
      (∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex, Finsupp.single F (1 : ℤ)) := by
  set S := exceptionalSet f ⊔ (QDivisor.toRDivisor Δ).supp.preimage f.continuous with hS
  have key : ∀ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex, F.support ⊆ (S : Set Y) := by
    intro F hF
    rcases Finset.mem_union.mp hF with hF | hF
    · obtain ⟨D, hD, hφ⟩ := exists_of_mem_support_mapPrimeDivisors _ Δ F hF
      rw [support_inverseTransformPrimeDivisor hφ]
      intro y hy
      refine Or.inr ?_
      change f y ∈ (QDivisor.toRDivisor Δ).supp
      rw [QDivisor.supp_toRDivisor]
      have hcl : IsClosed (f ⁻¹' ((Δ.supp : Closeds X) : Set X)) :=
        (Δ.supp.isClosed).preimage f.continuous
      refine (hcl.closure_subset_iff.mpr ?_) hy
      rintro z ⟨hz, -⟩
      exact DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hD) hz
    · exact fun y hy => Or.inl (MMP.Positivity.support_subset_exceptionalSet F ((hEx F).1 hF) hy)
  rcases hf.isSNCSubset with h0 | ⟨s, hs, hsnc⟩
  · -- the boundary is empty
    have hempty : (inverseTransformDivisor f Δ).support ∪ Ex = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun F hF => ?_
      have := key F hF (MMP.Flips.primeDivisor_genericPoint_mem_support F)
      rwa [hS, h0] at this
    rw [hempty, Finset.sum_empty]
    have := hΔ.isNormalVariety.1
    have : LocallyOfFiniteType (f ≫ sX) := by
      have := hf.isProper; infer_instance
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hf.isSmoothScheme
  · refine hsnc.of_support_subset ?_
    rw [support_sum_single, support_sum_single]
    intro F hF
    have hsub := key F hF
    rw [hS, ← hs] at hsub
    obtain ⟨E, hE, hgen⟩ :=
      Set.mem_iUnion₂.mp (hsub (MMP.Flips.primeDivisor_genericPoint_mem_support F))
    rwa [(MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E F
      (by simpa using hgen)).symm]

open Classical in
/-- The coefficient of the reduced divisor `∑_{E ∈ S} E` at `F` is `1` or `0`. -/
private theorem coeff_sum_single {Y : Scheme.{u}} (S : Finset (PrimeDivisor Y))
    (F : PrimeDivisor Y) :
    DivisorWithCoeffs.coeff (∑ E ∈ S, Finsupp.single E (1 : ℤ) : Divisor Y) F =
      if F ∈ S then 1 else 0 := by
  change (∑ E ∈ S, Finsupp.single E (1 : ℤ)) F = _
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- A general linear combination of finitely many sections, one of them nonzero, is nonzero:
the coefficient vectors `c` with `∑ cᵢ sᵢ = 0` form a proper subspace of `kⁱ`, contained in the
kernel of a linear form `ℓ` with `ℓ(e_j) ≠ 0`. -/
private theorem exists_polynomial_sum_smul_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X]
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤) (j : ι)
    (hj : s j ≠ 0) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0 := by
  classical
  let p : Submodule k (ι → k) :=
    { carrier := {c | ∑ i, scalarsToGlobalSections k sX (c i) • s i = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add, add_smul,
          Finset.sum_add_distrib] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at *
        rw [← Finset.smul_sum, hc, smul_zero] }
  have hjp : (Pi.single j 1 : ι → k) ∉ p := by
    intro h
    apply hj
    have : ∑ i, scalarsToGlobalSections k sX ((Pi.single j 1 : ι → k) i) • s i = 0 := h
    rwa [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp),
      Pi.single_eq_same, map_one, one_smul] at this
  obtain ⟨ℓ, hℓ, hp⟩ := Submodule.exists_le_ker_of_notMem hjp
  let Q : MvPolynomial ι k :=
    ∑ i, MvPolynomial.C (ℓ (fun j => if i = j then 1 else 0)) * MvPolynomial.X i
  have heval : ∀ c, MvPolynomial.eval c Q = ℓ c := by
    intro c
    rw [LinearMap.pi_apply_eq_sum_univ ℓ c]
    simp [Q, mul_comm]
  exact ⟨Q, fun h => hℓ (by rw [← heval, h, map_zero]),
    fun c hc h0 => hc ((heval c).trans (LinearMap.mem_ker.mp (hp h0)))⟩

/-- A divisor `H` admitting finitely many sections of `𝒪_X(H)` without common zero is Cartier:
off `Supp (sᵢ)₀ = Supp (div uᵢ + H)` the divisor `H` has the local equation `uᵢ⁻¹`. -/
private theorem isCartier_of_forall_exists_notMem_supp {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {H : Divisor X} {ι : Type*}
    (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp) :
    H.IsCartier := by
  intro x
  obtain ⟨i, hi, hx⟩ := hs x
  refine ⟨(H.zeroDivisor (s i) hi).supp.compl, hx, ?_⟩
  set u := (Divisor.isUnit_sectionToRationalFunctions hi).unit
  refine ⟨u⁻¹, fun E ⟨y, hyE, hyU⟩ => ?_⟩
  have h0 : (H.zeroDivisor (s i) hi).coeff E = 0 := by
    by_contra hne
    exact hyU (DivisorWithCoeffs.support_subset_supp hne hyE)
  rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor] at h0
  rw [PrimeDivisor.ord_inv]
  exact eq_neg_of_add_eq_zero_right h0

/-! ### The zero scheme of a section of a divisorial sheaf -/

/-- The invertibility of `L` in the spelling the zero scheme takes. It is a local instance here;
to state the zero-scheme lemmas below elsewhere, localise it there in the same way. -/
public local instance isInvertible_of_isInvertibleModule {Y : Scheme.{u}} (L : Y.Modules)
    [h : Stacks.Ample.IsInvertibleModule Y L] :
    SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L := h

section ZeroScheme

/-- A frame `b` of `𝒪_Y(D)` over `V`, on which `D` has the local equation `φ`, has order
`-d_E` along every prime divisor `E` with generic point in `V`. -/
public theorem valuation_frame_eq {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    {D : Divisor Y} {V : Y.Opens} {φ : (RationalFunctions Y)ˣ} (hφ : D.IsLocalEquation V φ)
    (b : D.divisorialSubmodule V) (r : Γ(Y, V)) (E : PrimeDivisor Y)
    (hE : E.genericPoint ∈ V) (hZ : componentGenericPoint Y E.component ∈ V)
    (hr : ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) E.component =
      (Y.presheaf.germ V _ hZ).hom r * b.1 ⟨E.component, hZ⟩) :
    E.valuation (b.1 ⟨E.component, hZ⟩) = WithZero.exp (-D.coeff E) := by
  have hEV : (E.support ∩ V).Nonempty :=
    ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, hE⟩
  have hv := congrArg E.valuation hr
  rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv, ← hφ E hEV, map_mul] at hv
  have hne : (Y.presheaf.germ V _ hZ).hom r ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hv
    exact WithZero.coe_ne_zero hv
  have hgerm : (Y.presheaf.germ V _ hZ).hom r =
      E.toComponent.hom ((Y.presheaf.germ V _ hE).hom r) := by
    rw [← TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hE E.specializes_genericPoint]
    rfl
  have hne' : (Y.presheaf.germ V _ hE).hom r ≠ 0 := fun h0 => hne (by rw [hgerm, h0, map_zero])
  have h1 : 1 ≤ E.valuation ((Y.presheaf.germ V _ hZ).hom r) := by
    rw [hgerm]; exact E.one_le_valuation_toComponent hne'
  have hb0 : b.1 ⟨E.component, hZ⟩ ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero] at hv
    exact WithZero.coe_ne_zero hv
  refine le_antisymm ?_ ?_
  · rw [hv]
    exact le_mul_of_one_le_left' h1
  · exact (b.2 E hEV).resolve_left hb0

/-- **The zero scheme of a section of `𝒪_Y(D)` near a point.** Around every point there is an
affine open `V` on which the ideal of `Z(t)` is generated by a function `a`, and the coefficient
of every prime divisor `E` with generic point in `V` in the divisor of zeros `(t)₀` is the order
of `a` along `E`. -/
public theorem exists_affine_zeroScheme_ideal_eq_span {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (x : Y) :
    ∃ (V : Y.affineOpens) (_ : x ∈ (V : Y.Opens)) (a : Γ(Y, V))
      (ha : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
        (Y.presheaf.germ V _ hZ).hom a ≠ 0),
      (zeroScheme Y D.divisorialSheaf t).ideal V = Ideal.span {a} ∧
      ∀ E : PrimeDivisor Y, E.genericPoint ∈ (V : Y.Opens) →
        (D.zeroDivisor t ht).coeff E =
          E.ord (MMP.Threefold.Resolution.sectionUnit a ha) := by
  obtain ⟨W, hxW, φ, hφ⟩ := hD x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  obtain ⟨g, hxg, hgU, ⟨e⟩⟩ := exists_basicOpen_linearEquiv D.divisorialSheaf ⟨U, hU⟩ x hxU
  let V : Y.affineOpens := ⟨Y.basicOpen g, hU.basicOpen g⟩
  have hVW : (V : Y.Opens) ≤ W := hgU.trans hUW
  set tV := D.divisorialSheaf.presheaf.map (homOfLE (le_top : (V : Y.Opens) ≤ ⊤)).op t
  set a : Γ(Y, V) := e tV with ha_def
  set b : D.divisorialSubmodule V := e.symm 1
  have htV : (tV : D.divisorialSubmodule V) = a • b := by
    change tV = a • e.symm 1
    rw [← map_smul e.symm a 1, smul_eq_mul, mul_one, ha_def, e.symm_apply_apply]
  set u := (Divisor.isUnit_sectionToRationalFunctions ht).unit
  -- the value of `t` at a component through `V`
  have hval : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
      (u : RationalFunctions Y) Z = (Y.presheaf.germ V _ hZ).hom a * b.1 ⟨Z, hZ⟩ := by
    intro Z hZ
    have := congrArg (fun m : D.divisorialSubmodule V => m.1 ⟨Z, hZ⟩) htV
    simp only [Submodule.coe_smul, rationalFunctions_smul_apply] at this
    exact this
  have ha : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
      (Y.presheaf.germ V _ hZ).hom a ≠ 0 := by
    intro Z hZ h0
    have hu := (Pi.isUnit_iff.mp u.isUnit) Z
    rw [hval Z hZ, h0, zero_mul] at hu
    exact not_isUnit_zero hu
  refine ⟨V, hxg, a, ha, zeroScheme_ideal_of_trivialization Y D.divisorialSheaf t V e a rfl,
    fun E hE => ?_⟩
  set hZ := E.specializes_genericPoint.mem_open (V : Y.Opens).isOpen hE
  -- the frame `b` has order `-d_E`
  have hr : (hφ.mono hVW).invSection = e (hφ.mono hVW).invSection • e.symm 1 := by
    rw [← map_smul e.symm _ 1, smul_eq_mul, mul_one, e.symm_apply_apply]
  have hr' := congrArg (fun m : D.divisorialSubmodule V => m.1 ⟨E.component, hZ⟩) hr
  simp only [Divisor.IsLocalEquation.invSection_apply, Submodule.coe_smul] at hr'
  have hb := valuation_frame_eq (hφ.mono hVW) b _ E hE hZ hr'
  have hv := congrArg E.valuation (hval E.component hZ)
  rw [PrimeDivisor.valuation_component, map_mul, hb,
    ← MMP.Threefold.Resolution.sectionUnit_apply a ha E.component hZ,
    PrimeDivisor.valuation_component, ← WithZero.exp_add] at hv
  have hv' := WithZero.exp_injective hv
  rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  change E.ord u + _ = _
  omega

/-- **A local equation of `(t)₀` generating the stalk of `Z(t)`.** Around every point `x` there
is an affine open `V` and a function `a` on `V` which is a local equation of the divisor of zeros
`(t)₀` on `V` and whose germ at `x` generates the stalk at `x` of the ideal of `Z(t)`. -/
public theorem exists_isLocalEquation_stalk_zeroScheme_eq_span {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (x : Y) :
    ∃ (V : Y.affineOpens) (hxV : x ∈ (V : Y.Opens)) (a : Γ(Y, V))
      (ha : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
        (Y.presheaf.germ V _ hZ).hom a ≠ 0),
      (D.zeroDivisor t ht).IsLocalEquation V (MMP.Threefold.Resolution.sectionUnit a ha) ∧
      IdealSheafData.stalk (zeroScheme Y D.divisorialSheaf t) x =
        Ideal.span {(Y.presheaf.germ V x hxV).hom a} := by
  obtain ⟨V, hxV, a, ha, hI, hc⟩ := exists_affine_zeroScheme_ideal_eq_span D hD t ht x
  refine ⟨V, hxV, a, ha, fun E ⟨y, hyE, hyV⟩ => hc E ?_, ?_⟩
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
    exact (specializes_iff_mem_closure.mpr hyE).mem_open (V : Y.Opens).isOpen hyV
  · rw [IdealSheafData.stalk_eq_map_germ _ _ V hxV, hI, Ideal.map_span, Set.image_singleton]

/-- In a discrete valuation ring, a nonzero nonunit generating a radical ideal is a
uniformizer. -/
private theorem irreducible_of_isRadical_span {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {x : R} (hx0 : x ≠ 0) (hxu : ¬ IsUnit x)
    (hrad : (Ideal.span {x}).IsRadical) : Irreducible x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    exact hxu (by simp)
  have hmem : ϖ ^ n ∈ Ideal.span {(u : R) * ϖ ^ n} :=
    Ideal.mem_span_singleton.mpr ⟨(u⁻¹ : Rˣ), by
      rw [mul_comm (u : R), mul_assoc, Units.mul_inv, mul_one]⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hrad ⟨n, hmem⟩)
  have hdvd : ϖ ^ n ∣ ϖ ^ 1 := ⟨(u : R) * c, by linear_combination hc⟩
  have hle := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp hdvd
  obtain rfl : n = 1 := by omega
  rw [pow_one, irreducible_isUnit_mul u.isUnit]
  exact hϖ

/-- Off the zero scheme of `t`, a prime divisor has coefficient `0` in `(t)₀`. -/
public theorem coeff_zeroDivisor_eq_zero_of_notMem {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (E : PrimeDivisor Y)
    (hE : E.genericPoint ∉ (zeroScheme Y D.divisorialSheaf t).supportSet) :
    (D.zeroDivisor t ht).coeff E = 0 := by
  obtain ⟨V, hxV, a, ha, hI, hc⟩ :=
    exists_affine_zeroScheme_ideal_eq_span D hD t ht E.genericPoint
  rw [hc E hxV]
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem hxV, hI, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not] at hE
  exact MMP.Threefold.Resolution.ord_sectionUnit_eq_zero a ha E hxV
    ((Y.mem_basicOpen a _ hxV).mp hE)

/-- On a reduced zero scheme of `t`, a prime divisor through it has coefficient `1` in `(t)₀`. -/
public theorem coeff_zeroDivisor_eq_one_of_isReduced {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0)
    [IsReduced (zeroScheme Y D.divisorialSheaf t).subscheme] (E : PrimeDivisor Y)
    (hE : E.genericPoint ∈ (zeroScheme Y D.divisorialSheaf t).supportSet) :
    (D.zeroDivisor t ht).coeff E = 1 := by
  obtain ⟨V, hxV, a, ha, hI, hc⟩ :=
    exists_affine_zeroScheme_ideal_eq_span D hD t ht E.genericPoint
  rw [hc E hxV]
  have hrad :
      (IdealSheafData.stalk (zeroScheme Y D.divisorialSheaf t) E.genericPoint).IsRadical := by
    rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
      (zeroScheme Y D.divisorialSheaf t) _ rfl]
    exact MMP.Resolution.isRadical_stalk_vanishingIdeal _ _
  have hst : IdealSheafData.stalk (zeroScheme Y D.divisorialSheaf t) E.genericPoint =
      Ideal.span {(Y.presheaf.germ V _ hxV).hom a} := by
    rw [IdealSheafData.stalk_eq_map_germ _ _ V hxV, hI, Ideal.map_span, Set.image_singleton]
  rw [hst] at hrad
  have hnu : ¬ IsUnit ((Y.presheaf.germ V _ hxV).hom a) := by
    rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem hxV, hI, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton, Set.mem_compl_iff] at hE
    exact fun h => hE ((Y.mem_basicOpen a _ hxV).mpr h)
  have hne := MMP.Threefold.Resolution.germ_genericPoint_ne_zero a ha E hxV
  have := E.isDiscreteValuationRing_localRing
  exact E.ord_eq_one_of_irreducible (irreducible_of_isRadical_span hne hnu hrad)
    (MMP.Threefold.Resolution.toComponent_germ_eq_sectionUnit a ha E hxV)

/-- A point off the support of `(t)₀` lies in the nonvanishing open of `t`. -/
public theorem mem_nonvanishingOpen_of_notMem_supp {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (y : Y)
    (hy : y ∉ (D.zeroDivisor t ht).supp) :
    y ∈ Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf t := by
  have hyZ : y ∉ (zeroScheme Y D.divisorialSheaf t).supportSet := by
    obtain ⟨V, hyV, a, ha, hI, hc⟩ := exists_affine_zeroScheme_ideal_eq_span D hD t ht y
    rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem hyV, hI, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not, SetLike.mem_coe,
      Y.mem_basicOpen a y hyV]
    obtain ⟨c, hc'⟩ := exists_unit_stalk_of_forall_ord_eq_zero (mem_pointComponent y)
      (MMP.Threefold.Resolution.sectionUnit a ha) fun E hE => by
        have hEV : E.genericPoint ∈ (V : Y.Opens) := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
          exact (specializes_iff_mem_closure.mpr hE).mem_open (V : Y.Opens).isOpen hyV
        rw [← hc E hEV]
        by_contra hne
        exact hy (DivisorWithCoeffs.support_subset_supp hne hE)
    have hZ : componentGenericPoint Y (pointComponent y) ∈ (V : Y.Opens) :=
      ((isGenericPoint_componentGenericPoint Y _).specializes
        (mem_pointComponent y)).mem_open (V : Y.Opens).isOpen hyV
    have heq : (Y.presheaf.germ V y hyV).hom a = c := by
      apply stalkToRationalFunctions_injective (mem_pointComponent y)
      rw [hc', MMP.Threefold.Resolution.sectionUnit_apply a ha _ hZ]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [heq]
    exact c.isUnit
  set s' := (Stacks.NonvanishingSpelling.sectionsEquiv Y D.divisorialSheaf).symm t
  have hev : PresheafOfModules.sections.eval s' (Opposite.op ⊤) = t :=
    (Stacks.NonvanishingSpelling.sectionsEquiv Y D.divisorialSheaf).apply_symm_apply t
  have h := AlgebraicGeometry.nonvanishingLocus_eq_compl_supportSet_zeroScheme
    D.divisorialSheaf s' (fun h0 => ht (hev.symm.trans h0))
  have h3 : y ∈ Stacks.SheafOfModules.nonvanishingLocus D.divisorialSheaf s' := by
    rw [h]
    exact fun hm => hyZ (hev ▸ hm)
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq Y D.divisorialSheaf s'] at h3
  change y ∈ Stacks.Ample.nonvanishingLocus D.divisorialSheaf t
  exact hev ▸ h3

end ZeroScheme

/-! ### Pulling back rational functions and sections along a dominant morphism -/

section PullbackSections

private theorem bijective_stalkSpecializes_of_eq {X : Scheme.{u}} {x y : X} (h : x ⤳ y)
    (hxy : y = x) : Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

private theorem map_componentGenericPoint_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (Z : irreducibleComponents Y) :
    componentGenericPoint X (pointComponent (f (componentGenericPoint Y Z))) =
      f (componentGenericPoint Y Z) := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint,
    MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]

/-- `𝒪_{X,f(η_Z)} ≅ 𝒪_{X,η}`: `f` maps the generic point of `Y` to that of `X`. -/
private noncomputable def stalkEquiv {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (Z : irreducibleComponents Y) :
    X.presheaf.stalk (f (componentGenericPoint Y Z)) ≃+*
      X.presheaf.stalk (componentGenericPoint X (pointComponent (f (componentGenericPoint Y Z)))) :=
  RingEquiv.ofBijective (stalkToRationalFunctions X (mem_pointComponent _)).hom
    (bijective_stalkSpecializes_of_eq _ (map_componentGenericPoint_eq f Z).symm)

/-- The pull-back `f^* : K(X) → K(Y)` of rational functions along a dominant morphism of
integral schemes. -/
public noncomputable def pullbackRat {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] : RationalFunctions X →+* RationalFunctions Y :=
  RingHom.pi fun Z => (f.stalkMap (componentGenericPoint Y Z)).hom.comp
    ((stalkEquiv f Z).symm.toRingHom.comp
      (RationalFunctions.component X (pointComponent (f (componentGenericPoint Y Z)))))

/-- On units, `f^*` is `MMP.Mori.pullbackRationalFunction`. -/
public theorem coe_pullbackRationalFunction {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : Y ⟶ X) [IsDominant f]
    (u : (RationalFunctions X)ˣ)
    (hu : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (principalDivisor u).supp) :
    ((pullbackRationalFunction f u hu : (RationalFunctions Y)ˣ) : RationalFunctions Y) =
      pullbackRat f u := by
  funext Z
  have key := pullbackComponent_eq hu (Divisor.isLocalEquation_principalDivisor u ⊤)
    (Z := Z) trivial (mem_pointComponent _)
    (Units.map (stalkEquiv f Z).symm.toMonoidHom
      ((RationalFunctions.unitsEquiv X u) (pointComponent (f (componentGenericPoint Y Z)))))
    ((stalkEquiv f Z).apply_symm_apply _)
  change ((pullbackComponent f hu (Divisor.isLocalEquation_principalDivisor u ⊤) Z trivial :
    (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ) :
      Y.presheaf.stalk (componentGenericPoint Y Z)) = _
  rw [key]
  rfl

/-- `f^*` maps the germ of a global function to the germ of its pull-back. -/
public theorem pullbackRat_germ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (r : Γ(X, ⊤)) :
    pullbackRat f (fun Z => (X.presheaf.germ ⊤ (componentGenericPoint X Z) trivial).hom r) =
      fun Z => (Y.presheaf.germ ⊤ (componentGenericPoint Y Z) trivial).hom (f.appTop r) := by
  funext Z
  have h1 : (stalkEquiv f Z).symm
      ((X.presheaf.germ ⊤ (componentGenericPoint X (pointComponent _)) trivial).hom r) =
      (X.presheaf.germ ⊤ (f (componentGenericPoint Y Z)) trivial).hom r := by
    rw [RingEquiv.symm_apply_eq]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
  change (f.stalkMap (componentGenericPoint Y Z)).hom ((stalkEquiv f Z).symm
      ((X.presheaf.germ ⊤ (componentGenericPoint X (pointComponent _)) trivial).hom r)) = _
  rw [h1]
  exact Scheme.Hom.germ_stalkMap_apply f ⊤ _ trivial r

/-- `f^*` of a section of `𝒪_X(H)` is a section of `𝒪_Y(f^*H)`: for `s ≠ 0`,
`div(f^*s) + f^*H = f^*(s)₀ ≥ 0`. -/
private theorem isDivisorialSection_pullbackRat {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) [IsDominant f] {H : Divisor X} (hHc : H.IsCartier)
    {hBH : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp}
    {D' : Divisor Y} (hD' : H.IsPullback f hBH D') (s : H.divisorialSubmodule ⊤) :
    D'.IsDivisorialSection ⊤ ((rationalFunctionsPresheafTopEquiv Y).symm
      (pullbackRat f (Divisor.sectionToRationalFunctions s))) := by
  intro E hE
  by_cases hs : s = 0
  · subst hs
    have h0 : Divisor.sectionToRationalFunctions (0 : H.divisorialSubmodule ⊤) = 0 :=
      map_zero (rationalFunctionsPresheafTopEquiv X)
    rw [h0, map_zero, map_zero]
    exact Or.inl rfl
  · set u := (Divisor.isUnit_sectionToRationalFunctions hs).unit
    have hu : ∀ Z : irreducibleComponents Y,
        f (componentGenericPoint Y Z) ∉ (principalDivisor u).supp :=
      fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _ Z
    have hBs : ∀ Z : irreducibleComponents Y,
        f (componentGenericPoint Y Z) ∉ (H.zeroDivisor s hs).supp :=
      fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _ Z
    have hpb : (H.zeroDivisor s hs).IsPullback f hBs
        (principalDivisor (pullbackRationalFunction f u hu) + D') :=
      Divisor.IsPullback.add (Divisor.isCartier_principalDivisor u) hHc hBs
        (Divisor.isPullback_principalDivisor u hu) hD'
    have hnn := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn
      ((Divisor.isCartier_principalDivisor u).add hHc) (V := ⊤)
      (fun P _ => Divisor.zeroDivisor_nonneg H s hs P) hpb E
      ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, trivial⟩
    rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor] at hnn
    have hval : ((rationalFunctionsPresheafTopEquiv Y).symm
        (pullbackRat f (Divisor.sectionToRationalFunctions s)))
          ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ =
        ((pullbackRationalFunction f u hu : (RationalFunctions Y)ˣ) : RationalFunctions Y)
          E.component := by
      rw [coe_pullbackRationalFunction f u hu]
      rfl
    rw [hval]
    refine Or.inr ?_
    rw [PrimeDivisor.valuation_component]
    exact WithZero.exp_le_exp.mpr (by omega)

/-- The pull-back `s ↦ f^*s : H⁰(X, 𝒪_X(H)) → H⁰(Y, 𝒪_Y(f^*H))`. -/
public noncomputable def pullSec {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) [IsDominant f] {H : Divisor X} (hHc : H.IsCartier)
    {hBH : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp}
    {D' : Divisor Y} (hD' : H.IsPullback f hBH D') :
    H.divisorialSubmodule ⊤ →+ D'.divisorialSubmodule ⊤ where
  toFun s := ⟨_, isDivisorialSection_pullbackRat f hHc hD' s⟩
  map_zero' := Subtype.ext (by
    change (rationalFunctionsPresheafTopEquiv Y).symm
      (pullbackRat f (rationalFunctionsPresheafTopEquiv X 0)) = 0
    rw [map_zero, map_zero, map_zero])
  map_add' a b := Subtype.ext (by
    change (rationalFunctionsPresheafTopEquiv Y).symm
      (pullbackRat f (rationalFunctionsPresheafTopEquiv X (a.1 + b.1))) = _
    rw [map_add, map_add, map_add]
    rfl)

/-- `f^*s`, as a rational function, is the pull-back of `s`. -/
public theorem sectionToRationalFunctions_pullSec {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) [IsDominant f] {H : Divisor X} (hHc : H.IsCartier)
    {hBH : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp}
    {D' : Divisor Y} (hD' : H.IsPullback f hBH D') (s : H.divisorialSubmodule ⊤) :
    Divisor.sectionToRationalFunctions (pullSec f hHc hD' s) =
      pullbackRat f (Divisor.sectionToRationalFunctions s) :=
  (rationalFunctionsPresheafTopEquiv Y).apply_symm_apply _

/-- `f^*` is semilinear along `f^* : Γ(X, 𝒪_X) → Γ(Y, 𝒪_Y)`. -/
public theorem pullSec_smul {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) [IsDominant f] {H : Divisor X} (hHc : H.IsCartier)
    {hBH : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp}
    {D' : Divisor Y} (hD' : H.IsPullback f hBH D') (r : Γ(X, ⊤)) (s : H.divisorialSubmodule ⊤) :
    pullSec f hHc hD' (r • s) = f.appTop r • pullSec f hHc hD' s := by
  apply Divisor.sectionToRationalFunctions_injective
  rw [sectionToRationalFunctions_pullSec]
  have h1 : ∀ {Z : Scheme.{u}} [IsLocallyNoetherian Z] [IsNormal Z] {M : Divisor Z}
      (r : Γ(Z, ⊤)) (σ : M.divisorialSubmodule ⊤),
      Divisor.sectionToRationalFunctions (r • σ) =
        (fun W => (Z.presheaf.germ ⊤ (componentGenericPoint Z W) trivial).hom r) *
          Divisor.sectionToRationalFunctions σ := fun _ _ => rfl
  rw [h1, h1, map_mul, pullbackRat_germ, sectionToRationalFunctions_pullSec]

/-- `f^*(s)₀ = (f^*s)₀` for `s ≠ 0`, and `f^*s ≠ 0`. -/
public theorem isPullback_zeroDivisor_pullSec {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) [IsDominant f] {H : Divisor X} (hHc : H.IsCartier)
    {hBH : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp}
    {D' : Divisor Y} (hD' : H.IsPullback f hBH D') (s : H.divisorialSubmodule ⊤) (hs : s ≠ 0)
    (hBs : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (H.zeroDivisor s hs).supp) :
    ∃ h : pullSec f hHc hD' s ≠ 0,
      (H.zeroDivisor s hs).IsPullback f hBs (D'.zeroDivisor (pullSec f hHc hD' s) h) := by
  set u := (Divisor.isUnit_sectionToRationalFunctions hs).unit
  have hu : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (principalDivisor u).supp :=
    fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _ Z
  have hval : Divisor.sectionToRationalFunctions (pullSec f hHc hD' s) =
      ((pullbackRationalFunction f u hu : (RationalFunctions Y)ˣ) : RationalFunctions Y) := by
    rw [sectionToRationalFunctions_pullSec, coe_pullbackRationalFunction f u hu]
    rfl
  have h : pullSec f hHc hD' s ≠ 0 := by
    intro h0
    obtain ⟨y⟩ : Nonempty Y := inferInstance
    have hu' := (Pi.isUnit_iff.mp (pullbackRationalFunction f u hu).isUnit) (pointComponent y)
    rw [← hval, h0] at hu'
    have h00 : Divisor.sectionToRationalFunctions (0 : D'.divisorialSubmodule ⊤) = 0 :=
      map_zero (rationalFunctionsPresheafTopEquiv Y)
    rw [h00] at hu'
    exact not_isUnit_zero hu'
  refine ⟨h, ?_⟩
  have heq : (Divisor.isUnit_sectionToRationalFunctions h).unit =
      pullbackRationalFunction f u hu := Units.ext hval
  rw [Divisor.zeroDivisor_eq D', heq]
  exact Divisor.IsPullback.add (Divisor.isCartier_principalDivisor u) hHc hBs
    (Divisor.isPullback_principalDivisor u hu) hD'

end PullbackSections

/-! ### General points of the projective space of a system -/

section Projective

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **A dense open of `ℙᴺ_k` contains the general points.** For a dense open `U ⊆ ℙᴺ_k` there is
a nonzero polynomial `Q` with `[c] ∈ U` whenever `Q(c) ≠ 0`. -/
public theorem exists_polynomial_dualPoint_mem {k : Type u} [Field k] {N : ℕ}
    (U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens)
    (hU : Dense (U : Set
      (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0),
      MvPolynomial.eval c Q ≠ 0 → MMP.Threefold.Bridges.dualPoint c hc ∈ U := by
  classical
  obtain ⟨p, hp⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).exists_subset_of_mem_open hp U.isOpen
  have hpf' : f ∉ (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      from p).asHomogeneousIdeal :=
    (ProjectiveSpectrum.mem_basicOpen _ f _).mp hpf
  obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.homogeneousComponent d f ∉
      (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
        from p).asHomogeneousIdeal := by
    by_contra h
    push Not at h
    apply hpf'
    rw [← MvPolynomial.sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun i _ => h i
  have hQ0 : MvPolynomial.homogeneousComponent d f ≠ 0 := fun h0 => hd (h0 ▸ zero_mem _)
  refine ⟨_, hQ0, fun c hc hcQ => hfU ?_⟩
  refine (ProjectiveSpectrum.mem_basicOpen _ f
    (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) from
      MMP.Threefold.Bridges.dualPoint c hc)).mpr fun hf => hcQ ?_
  change f ∈ ((RingHom.ker (MvPolynomial.eval c)).homogeneousCore
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).toIdeal at hf
  have hcore := (HomogeneousIdeal.isHomogeneous ((RingHom.ker (MvPolynomial.eval c)).homogeneousCore
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))).mem_iff.mp hf d
  have hdec : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) f d :
      MvPolynomial (Fin (N + 1)) k)) = MvPolynomial.homogeneousComponent d f :=
    MvPolynomial.decomposition.decompose'_apply f d
  rw [hdec] at hcore
  exact RingHom.mem_ker.mp (Ideal.toIdeal_homogeneousCore_le _ _ hcore)

end Projective

/-! ### Bertini on `Y`, in Weil-divisor form -/

section WeilBertini

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)

attribute [local instance] globalSectionsModule

/-- Two distinct prime divisors whose supports are irreducible components of a closed subscheme
`Z` are disjoint if at every point `Z` is cut out by one member of a regular system of
parameters. -/
public theorem disjoint_support_of_mem_componentsOf {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {Z : Y.IdealSheafData}
    (hZ : ∀ x ∈ Z.support, ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk x) (m : Fin n),
      IsRegularSystemOfParameters z ∧ IdealSheafData.stalk Z x = Ideal.span {z m})
    {E E' : PrimeDivisor Y} (hE : E.support ∈ MMP.Resolution.componentsOf (Z.support : Set Y))
    (hE' : E'.support ∈ MMP.Resolution.componentsOf (Z.support : Set Y)) (hne : E ≠ E') :
    Disjoint E.support E'.support := by
  refine Set.disjoint_left.2 fun x hx hx' => hne ?_
  obtain ⟨n, z, m, hz, hZx⟩ := hZ x (hE.1.2 hx)
  have hTy : Y.fromSpecStalk x ⁻¹' (Z.support : Set Y) =
      ⋃ t ∈ ({m} : Finset (Fin n)), PrimeSpectrum.zeroLocus {z t} := by
    have h := MMP.Resolution.preimage_fromSpecStalk_iUnion_support (fun _ : Unit => Z) x z
      (fun _ => m) (fun _ => hZx)
    have : Nonempty {i : Unit // x ∈ Z.support} := ⟨⟨(), hE.1.2 hx⟩⟩
    rw [Set.iUnion_const, Set.iUnion_const] at h
    simpa using h
  -- a component through `x` is cut out at `x` by `z m`
  have key : ∀ F : PrimeDivisor Y, F.support ∈ MMP.Resolution.componentsOf (Z.support : Set Y) →
      x ∈ F.support → IdealSheafData.stalk F.idealSheaf x = Ideal.span {z m} := by
    intro F hF hxF
    obtain ⟨c₀, hc₀, hst, -⟩ :=
      MMP.Resolution.exists_stalk_componentsFamily_eq_span Z.support.isClosed hz hTy ⟨_, hF⟩ hxF
    have hFideal : F.idealSheaf = MMP.Resolution.componentsFamily (Z.support : Set Y) ⟨_, hF⟩ := by
      have := F.integral
      refine (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl).trans
        (congrArg _ ?_)
      ext1
      rw [Closeds.coe_closure]
      exact F.idealSheaf.support.isClosed.closure_eq.symm
    rw [hFideal, hst, Finset.mem_singleton.1 hc₀]
  exact MMP.Intersection.eq_of_stalk_idealSheaf_eq hx hx' (by rw [key E hE hx, key E' hE' hx'])

open Classical in
/-- **Bertini's theorem for snc divisors, in Weil-divisor form.** On a smooth variety `Y` over an
algebraically closed field of characteristic zero, let `D` be a Cartier divisor and
`t : ι → H⁰(Y, 𝒪_Y(D))` finitely many sections without common zero, and let `∑_{E ∈ S} E` be
snc. For a general coefficient vector `c`, the divisor of zeros of `τ = ∑ cᵢ tᵢ` is the reduced
divisor `∑_{E ∈ T} E` on a finite set `T` of prime divisors disjoint from `S`, the members of `T`
are pairwise disjoint (the zero scheme of `τ` is smooth), and `∑_{E ∈ T ∪ S} E` is snc.
The set `T` consists of the prime divisors whose generic point lies on the zero scheme of `τ`. -/
public theorem exists_polynomial_zeroDivisor_eq_sum_isSNC {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [IsSmoothVariety k (Y ↘ Spec (.of k))] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (D : Divisor Y) (hD : D.IsCartier) {ι : Type*} [Fintype ι]
    (t : ι → D.divisorialSubmodule ⊤)
    (ht : ∀ y : Y, ∃ (i : ι) (hi : t i ≠ 0), y ∉ (D.zeroDivisor (t i) hi).supp)
    (S : Finset (PrimeDivisor Y))
    (hS : DivisorWithCoeffs.IsSNC (Y ↘ Spec (.of k)) (∑ E ∈ S, Finsupp.single E (1 : ℤ))) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      ∀ hτ : (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i) ≠ 0,
        ∃ T : Finset (PrimeDivisor Y),
          D.zeroDivisor _ hτ = ∑ E ∈ T, Finsupp.single E (1 : ℤ) ∧ Disjoint T S ∧
          DivisorWithCoeffs.IsSNC (Y ↘ Spec (.of k)) (∑ E ∈ T ∪ S, Finsupp.single E (1 : ℤ)) ∧
          ∀ E ∈ T, ∀ E' ∈ T, E ≠ E' → Disjoint E.support E'.support := by
  classical
  have hL := hD.isInvertibleModule_divisorialSheaf
  have : TopologicalSpace.NoetherianSpace Y :=
    MMP.Resolution.Aux.noetherianSpace_of_finiteType (Y ↘ Spec (.of k))
  obtain ⟨i₀, -, -⟩ := ht (Nonempty.some inferInstance)
  set N := Fintype.card ι - 1
  have hcard : Fintype.card ι = N + 1 := by
    have := Fintype.card_pos_iff.mpr ⟨i₀⟩
    omega
  let e : ι ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  let s : Fin (N + 1) → Γ(D.divisorialSheaf, ⊤) := fun j => t (e.symm j)
  have hsys : ∀ c : ι → k, MMP.Threefold.Bridges.systemSection (k := k) s (c ∘ e.symm) =
      ∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i := by
    intro c
    rw [MMP.Threefold.Bridges.systemSection_apply]
    exact Fintype.sum_equiv e.symm _ _ (fun j => rfl)
  have hs : ⨆ c : Fin (N + 1) → k, Stacks.NonvanishingOpen.nonvanishingOpen Y D.divisorialSheaf
      (MMP.Threefold.Bridges.systemSection s c) = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨i, hi, hy⟩ := ht y
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Pi.single (e i) 1, ?_⟩
    have h1 : MMP.Threefold.Bridges.systemSection (k := k) s (Pi.single (e i) 1) = t i := by
      rw [MMP.Threefold.Bridges.systemSection_apply,
        Finset.sum_eq_single (e i) (fun j _ hj => by simp [hj]) (by simp)]
      simp only [s, Equiv.symm_apply_apply, Pi.single_eq_same]
      exact one_smul k _
    rw [h1]
    exact mem_nonvanishingOpen_of_notMem_supp D hD (t i) hi y hy
  obtain ⟨U, hU, hUc⟩ := MMP.Threefold.Bridges.exists_dense_open_isSNC_zeroScheme_add s hs _ hS
  obtain ⟨Q', hQ'0, hQ'⟩ := exists_polynomial_dualPoint_mem U hU
  -- the general member alone is an snc family, i.e. a smooth divisor
  have : Smooth (𝟙 Y ≫ Y ↘ Spec (.of k)) := by
    rw [Category.id_comp]
    infer_instance
  have hG : MMP.Resolution.IsSNCFamily (𝟙 Y ≫ Y ↘ Spec (.of k))
      (PEmpty.elim : PEmpty.{u + 1} → _) := by
    refine ⟨fun i => i.elim, fun x => ?_⟩
    obtain ⟨n, z, -, hz, -⟩ := hS.2 x
    exact ⟨n, z, fun i => i.1.elim, hz, fun i => i.1.elim, fun i => i.1.elim⟩
  obtain ⟨-, U₂, hU₂, hU₂c⟩ :=
    MMP.Threefold.Bridges.exists_dense_open_isSNCFamily_zeroScheme s hs (𝟙 Y) _ hG
  obtain ⟨Q₂, hQ₂0, hQ₂⟩ := exists_polynomial_dualPoint_mem U₂ hU₂
  refine ⟨MvPolynomial.rename e.symm (Q' * Q₂), fun h => mul_ne_zero hQ'0 hQ₂0
    (MvPolynomial.rename_injective _ e.symm.injective (h.trans (map_zero _).symm)),
    fun c hc hτ => ?_⟩
  rw [MvPolynomial.eval_rename, map_mul] at hc
  have hc' : MvPolynomial.eval (c ∘ e.symm) Q' ≠ 0 := left_ne_zero_of_mul hc
  have hc₂ : MvPolynomial.eval (c ∘ e.symm) Q₂ ≠ 0 := right_ne_zero_of_mul hc
  have hc0 : c ∘ e.symm ≠ 0 := by
    intro h0
    apply hτ
    rw [← hsys, h0, map_zero]
    rfl
  obtain ⟨hred, T, hTcomp, hTS, hsnc⟩ := hUc (c ∘ e.symm) hc0 (hQ' _ hc0 hc')
  obtain ⟨-, -, hsncZ⟩ := hU₂c (c ∘ e.symm) hc0 (hQ₂ _ hc0 hc₂)
  simp only [Scheme.IdealSheafData.comap_id] at hsncZ
  rw [support_sum_single] at hTS hsnc
  rw [hsys] at hred hTcomp hsncZ
  have hZ : ∀ x ∈ (zeroScheme Y D.divisorialSheaf
      (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i)).support,
      ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk x) (m : Fin n), IsRegularSystemOfParameters z ∧
        IdealSheafData.stalk (zeroScheme Y D.divisorialSheaf
          (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i)) x =
          Ideal.span {z m} := fun x hx => by
    obtain ⟨n, z, j, hz, hI, -⟩ := hsncZ.2 x
    exact ⟨n, z, j ⟨none, hx⟩, hz, hI ⟨none, hx⟩⟩
  refine ⟨T, ?_, hTS, hsnc, fun E hE E' hE' => disjoint_support_of_mem_componentsOf hZ
    ((hTcomp E.support).mpr ⟨E, hE, rfl⟩) ((hTcomp E'.support).mpr ⟨E', hE', rfl⟩)⟩
  ext E
  change (D.zeroDivisor _ hτ).coeff E =
    DivisorWithCoeffs.coeff (∑ E ∈ T, Finsupp.single E (1 : ℤ) : Divisor Y) E
  rw [coeff_sum_single]
  split_ifs with hET
  · exact coeff_zeroDivisor_eq_one_of_isReduced D hD _ hτ E
      (((hTcomp E.support).mpr ⟨E, hET, rfl⟩).1.2
        (MMP.Flips.primeDivisor_genericPoint_mem_support E))
  · by_cases hEZ : E.genericPoint ∈
        (zeroScheme Y D.divisorialSheaf
          (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i)).supportSet
    · exfalso
      obtain ⟨-, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf
        (zeroScheme Y D.divisorialSheaf
          (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i)).support.isClosed
      obtain ⟨W, hW, hEW⟩ := Set.mem_sUnion.mp (hcov hEZ)
      obtain ⟨E', hE'T, hE'W⟩ := (hTcomp W).mp hW
      exact hET (by
        rwa [(MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E
          (hE'W ▸ hEW)).symm])
    · exact coeff_zeroDivisor_eq_zero_of_notMem D hD _ hτ E hEZ

end WeilBertini

open Classical in
/-- **Bertini for a system pulled back along a dominant morphism from a smooth variety, in
Weil-divisor form.** Let `X` be a normal integral scheme over an algebraically closed field `k` of
characteristic zero, `H` a Cartier divisor on `X`, `s : ι → H⁰(X, 𝒪_X(H))` finitely many
sections, `f : Y ⟶ X` a dominant morphism from a smooth variety `Y` such that the sections have
no common zero on the image of `f`, and `∑_{E ∈ S} E` a reduced snc divisor on `Y`. For a general
coefficient vector `c`, the pull-back `f^*(σ)₀` of the member `σ = ∑ cᵢ sᵢ` is the reduced
divisor `∑_{E ∈ T} E` on a finite set `T` of pairwise disjoint prime divisors disjoint from `S`,
and `∑_{E ∈ T ∪ S} E` is snc.

Here `f` need not be proper, so this covers a resolution of an open subscheme of `X` off the
base locus of the system. -/
public theorem exists_polynomial_pullback_zeroDivisor_eq_sum_isSNC_of_isDominant {k : Type u}
    [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} [IsDominant f]
    [IsSmoothVariety k (f ≫ sX)] {H : Divisor X} (hHc : H.IsCartier) {ι : Type*} [Fintype ι]
    (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ y : Y, ∃ (i : ι) (hi : s i ≠ 0), f y ∉ (H.zeroDivisor (s i) hi).supp)
    (S : Finset (PrimeDivisor Y))
    (hS : DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ S, Finsupp.single E (1 : ℤ))) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      ∀ (hσ : (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0)
        (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
          (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).supp)
        (H' : Divisor Y),
        (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).IsPullback f hB H' →
        ∃ T : Finset (PrimeDivisor Y), H' = ∑ E ∈ T, Finsupp.single E (1 : ℤ) ∧
          Disjoint T S ∧
          DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ T ∪ S, Finsupp.single E (1 : ℤ)) ∧
          ∀ E ∈ T, ∀ E' ∈ T, E ≠ E' → Disjoint E.support E'.support := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  let : Y.Over (Spec (.of k)) := ⟨f ≫ sX⟩
  have : IsSmoothVariety k (Y ↘ Spec (.of k)) := ‹IsSmoothVariety k (f ≫ sX)›
  have hBH : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp :=
    fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _ Z
  have hD' := Divisor.isPullback_pullback hHc hBH
  set t : ι → (H.pullback hHc hBH).divisorialSubmodule ⊤ := fun i => pullSec f hHc hD' (s i)
  have ht : ∀ y : Y, ∃ (i : ι) (hi : t i ≠ 0),
      y ∉ ((H.pullback hHc hBH).zeroDivisor (t i) hi).supp := by
    intro y
    obtain ⟨i, hi, hy⟩ := hs y
    obtain ⟨h, hpb⟩ := isPullback_zeroDivisor_pullSec f hHc hD' (s i) hi
      (fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _ Z)
    refine ⟨i, h, fun hmem => hy ?_⟩
    have := MMP.Flips.supp_eq_preimage_supp_of_isPullback
      ((Divisor.isCartier_principalDivisor _).add hHc) (Divisor.zeroDivisor_nonneg _ _ hi) hpb
    have hmem' : y ∈ (((H.pullback hHc hBH).zeroDivisor (t i) h).supp : Set Y) := hmem
    rwa [this] at hmem'
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_zeroDivisor_eq_sum_isSNC (k := k) (Y := Y)
    (H.pullback hHc hBH) (MMP.Fourfold.isCartier_of_isPullback f hHc hD') t ht S hS
  refine ⟨Q, hQ0, fun c hc hσ hB H' hH' => ?_⟩
  have hτeq : (∑ i, scalarsToGlobalSections k (Y ↘ Spec (.of k)) (c i) • t i) =
      pullSec f hHc hD' (∑ i, scalarsToGlobalSections k sX (c i) • s i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pullSec_smul]
    congr 1
  obtain ⟨hτ0, hpbτ⟩ := isPullback_zeroDivisor_pullSec f hHc hD' _ hσ hB
  obtain ⟨T, hT, hTS, hsnc, hdisj⟩ := hQ c hc (hτeq ▸ hτ0)
  refine ⟨T, ?_, hTS, hsnc, hdisj⟩
  rw [hH'.eq ((Divisor.isCartier_principalDivisor _).add hHc) hpbτ, ← hT]
  congr 1
  exact hτeq.symm

open Classical in
/-- **Bertini for a free system pulled back to a smooth resolution, in Weil-divisor form.** Let
`X` be a normal variety over an algebraically closed field `k` of characteristic zero,
`s : ι → H⁰(X, 𝒪_X(H))` finitely many sections without common zero, `f : Y ⟶ X` a resolution
with `Y` smooth, and `∑_{E ∈ S} E` a reduced snc divisor on `Y`. For a general coefficient vector
`c`, the pull-back `f^*(σ)₀` of the member `σ = ∑ cᵢ sᵢ` is the reduced divisor `∑_{E ∈ T} E` on
a finite set `T` of pairwise disjoint prime divisors disjoint from `S`, and `∑_{E ∈ T ∪ S} E` is
snc. -/
public theorem exists_polynomial_pullback_zeroDivisor_eq_sum_isSNC {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : AlgebraicGeometry.IsVariety k sX) {f : Y ⟶ X} (hf : IsSmoothResolution sX f)
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp)
    (S : Finset (PrimeDivisor Y))
    (hS : DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ S, Finsupp.single E (1 : ℤ))) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      ∀ (hσ : (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0)
        (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
          (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).supp)
        (H' : Divisor Y),
        (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).IsPullback f hB H' →
        ∃ T : Finset (PrimeDivisor Y), H' = ∑ E ∈ T, Finsupp.single E (1 : ℤ) ∧
          Disjoint T S ∧
          DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ E ∈ T ∪ S, Finsupp.single E (1 : ℤ)) ∧
          ∀ E ∈ T, ∀ E' ∈ T, E ≠ E' → Disjoint E.support E'.support := by
  have : IsIntegral Y := hf.isIntegral
  have : IsDominant f := hf.isBirationalMorphism.isDominant
  have : IsProper f := hf.isProper
  have := hX
  have : IsSmoothVariety k (f ≫ sX) :=
    { toIsVariety := by constructor <;> infer_instance
      toSmooth := Scheme.Hom.smoothLocus_eq_top_iff.mp (by
        rw [← smoothLocus_eq_smoothLocus]
        exact hf.isSmoothScheme) }
  exact exists_polynomial_pullback_zeroDivisor_eq_sum_isSNC_of_isDominant
    (isCartier_of_forall_exists_notMem_supp s hs) s (fun y => hs (f y)) S hS

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Y] [IsNormal Y]

open Classical in
/-- **A general member of a free linear system meets a log resolution transversally**, without
assuming that `∑_j f⁻¹_* D_j` is smooth. Let `(X, Δ)` be a pair over an algebraically closed
field `k` of characteristic zero, `s : ι → H⁰(X, 𝒪_X(H))` finitely many sections without common
zero, and `f : Y ⟶ X` a log resolution of `(X, Δ)` whose `f`-exceptional prime divisors form
the finite set `Ex`. Then for a general coefficient vector `c` the section `σ = ∑_i c_i s_i` is
nonzero, `f` maps no generic point of `Y` into `Supp (σ)₀`, and with `H' = f^*(σ)₀` the divisor
`H' + ∑ F` (`F` ranging over the components of `f⁻¹_* Δ` and the `f`-exceptional prime
divisors) is reduced and snc, and the components of `H'` are pairwise disjoint. -/
public theorem IsLogResolution.exists_polynomial_isSNC_pullback_zeroDivisor_add'
    [IsAlgClosed k] [CharZero k] {Δ : QDivisor X} (hΔ : IsPair sX Δ) {f : Y ⟶ X}
    (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f) (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ F : PrimeDivisor Y, F ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap F)
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      ∃ hσ : (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0,
        ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
            (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).supp)
          (H' : Divisor Y),
          (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).IsPullback f hB H' ∧
          (∀ F : PrimeDivisor Y,
            (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
              Finsupp.single F (1 : ℤ)).coeff F = 0 ∨
            (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
              Finsupp.single F (1 : ℤ)).coeff F = 1) ∧
          DivisorWithCoeffs.IsSNC (f ≫ sX)
            (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex, Finsupp.single F (1 : ℤ)) ∧
          ∀ E ∈ H'.support, ∀ E' ∈ H'.support, E ≠ E' → Disjoint E.support E'.support := by
  have hB := isSNC_boundary hΔ hf Ex hEx
  set S := (inverseTransformDivisor f Δ).support ∪ Ex
  have : IsIntegral Y := hf.toIsSmoothResolution.isIntegral
  have : IsDominant f := hf.toIsSmoothResolution.isBirationalMorphism.isDominant
  have : CompactSpace Y := by
    have := hf.toIsSmoothResolution.isProper
    exact QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨j, hj, -⟩ := hs (Nonempty.some inferInstance)
  obtain ⟨Q₁, hQ₁, hσ⟩ := exists_polynomial_sum_smul_ne_zero sX s j hj
  obtain ⟨Q₂, hQ₂, hT⟩ := exists_polynomial_pullback_zeroDivisor_eq_sum_isSNC hΔ.1.1
    hf.toIsSmoothResolution s hs S hB
  have hHc : H.IsCartier := isCartier_of_forall_exists_notMem_supp s hs
  refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, fun c hc => ?_⟩
  rw [map_mul] at hc
  have hσc := hσ c (left_ne_zero_of_mul hc)
  have hBc : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
      (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσc).supp :=
    fun Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _ Z
  have hZc : (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσc).IsCartier := by
    rw [Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add hHc
  obtain ⟨H', hH'⟩ := hZc.exists_isPullback hBc
  obtain ⟨T, rfl, hTS, hsnc, hdisj⟩ := hT c (right_ne_zero_of_mul hc) hσc hBc H' hH'
  have hsum : (∑ E ∈ T, Finsupp.single E (1 : ℤ)) + ∑ E ∈ S, Finsupp.single E (1 : ℤ) =
      ∑ E ∈ T ∪ S, Finsupp.single E (1 : ℤ) := (Finset.sum_union hTS).symm
  refine ⟨hσc, hBc, _, hH', fun F => ?_, hsum ▸ hsnc, by rwa [support_sum_single]⟩
  rw [hsum, coeff_sum_single]
  split_ifs <;> simp

open Classical in
/-- **A general member of a free linear system meets a log resolution transversally** (Kollár–Mori,
proof of Lemma 5.17). Let `X` be a normal integral scheme over an algebraically closed field `k` of
characteristic zero, `(X, Δ)` a pair with `Δ` a `ℚ`-divisor, `s : ι → H⁰(X, 𝒪_X(H))` finitely many
sections without common zero, and `f : Y ⟶ X` a log resolution of `(X, Δ)` whose `f`-exceptional
prime divisors form the finite set `Ex` and such that the reduced divisor `∑_j f⁻¹_* D_j` on the
components of `f⁻¹_* Δ` is smooth. Then there is a nonzero polynomial `Q` in the coefficients such
that for every `c` with `Q(c) ≠ 0` the section `σ = ∑_i c_i s_i` is nonzero, `f` maps no generic
point of `Y` into `Supp (σ)₀`, and with `H' = f^*(σ)₀` the divisor `H' + ∑ F` (`F` ranging over the
components of `f⁻¹_* Δ` and the `f`-exceptional prime divisors) has all coefficients `0` or `1` and
is an snc divisor, and the components of `H'` are pairwise disjoint (`H'` is smooth). -/
@[mmp "lem_km5d_general_member_log_resolution"]
public theorem IsLogResolution.exists_polynomial_isSNC_pullback_zeroDivisor_add
    [IsAlgClosed k] [CharZero k] {Δ : QDivisor X} (hΔ : IsPair sX Δ) {f : Y ⟶ X}
    (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f) (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ F : PrimeDivisor Y, F ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap F)
    (hsm : IsSmoothScheme
      ((⨅ F ∈ (inverseTransformDivisor f Δ).support, F.idealSheaf).subschemeι ≫ f ≫ sX))
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      ∃ hσ : (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0,
        ∃ (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
            (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).supp)
          (H' : Divisor Y),
          (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).IsPullback f hB H' ∧
          (∀ F : PrimeDivisor Y,
            (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
              Finsupp.single F (1 : ℤ)).coeff F = 0 ∨
            (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
              Finsupp.single F (1 : ℤ)).coeff F = 1) ∧
          DivisorWithCoeffs.IsSNC (f ≫ sX)
            (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex, Finsupp.single F (1 : ℤ)) ∧
          ∀ E ∈ H'.support, ∀ E' ∈ H'.support, E ≠ E' → Disjoint E.support E'.support :=
  IsLogResolution.exists_polynomial_isSNC_pullback_zeroDivisor_add' hΔ hf Ex hEx s hs

end MMP.Mori
