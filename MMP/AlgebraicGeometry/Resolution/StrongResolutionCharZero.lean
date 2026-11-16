module
public import MMP.AlgebraicGeometry.Resolution.StrongResolution.Functorial
public import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre

/-!
# Strong resolutions exist in characteristic zero

Every variety `X` over a field `k` of characteristic zero admits a strong resolution: a
projective birational morphism `g : Y ⟶ X` from a smooth variety `Y` which is an isomorphism
over the smooth locus of `X` and such that the reduced inverse image of the singular locus of
`X` is a simple normal crossing divisor (empty when `X` is smooth).

Kollár's blow-up sequence functor `MMP.Resolution.exists_strongResolution_blowupSequenceFunctor`,
applied to `X` (a disjoint union of varieties with one component), gives a blow-up sequence
`Π : X_r ⟶ ⋯ ⟶ X` with `X_r` smooth, `Π` an isomorphism over the smooth locus `X^ns`, and
`Π⁻¹(Sing X)` a divisor with simple normal crossings. The composite `Π` of blow-ups of the
Noetherian scheme `X` is projective. The smooth locus is dense, since `k` is perfect, so `X_r` is
nonempty; each blow-up of a variety along a nonzero ideal is a variety, so `X_r` is a variety, and
`Π`, an isomorphism over the dense open `X^ns`, is birational. Finally, at every point the closed
set `Π⁻¹(Sing X)` is, on the local scheme, the union of the hyperplanes of some coordinates `w_c`,
`c ∈ C`; as its ideal sheaf is radical and the `(w_c)` are distinct primes, the stalk of that
ideal is `(∏_{c ∈ C} w_c)`, which is the simple normal crossing condition of
`MMP.Resolution.IsSNCSubscheme`.

## Main results

* `MMP.Resolution.exists_isStrongResolution`: existence of a strong resolution in
  characteristic zero.

## Implementation notes

"Projective" is projectivity in the sense of EGA II 5.5 / Stacks 01W8,
`AlgebraicGeometry.IsProjective`: proper, together with a relatively ample invertible sheaf.
A blow-up sequence over an arbitrary variety is projective in this sense, but need not be
a closed subscheme of some `ℙⁿ_X`, which requires an ample sheaf on `X`. The
projectivity field of `MMP.Resolution.IsResolutionOfVariety` is this EGA projectivity
(`isProjective : AlgebraicGeometry.IsProjective f`); the conclusion lists the clauses of
`MMP.Resolution.IsStrongResolution` explicitly.

The remaining clauses are: `Y` is a variety with structure morphism `g ≫ sX`, `g` is
birational, `Y` is smooth, `IsIso (g ∣_ smoothLocus sX)`, and `MMP.Resolution.IsSNCSubscheme`
of the vanishing ideal of `g⁻¹(Sing X)`. When `X` is smooth that ideal is the unit ideal
(`MMP.Resolution.vanishingIdeal_preimage_singularLocus_eq_top_of_isSmoothScheme`), the empty
divisor, which covers the "empty or SNC" alternative. The source `Y` lives in the universe of
`X`. The auxiliary lemmas of the proof live in the namespace
`Proof_lem_mmp_characteristic_zero_strong_resolution_dictionary`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.3, 3.36]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, 0.4]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_lem_mmp_characteristic_zero_strong_resolution_dictionary

open TopologicalSpace MMP.Resolution

/-! ### Varieties and blow-up sequences -/

/-- A variety is a disjoint union of varieties, with one component. -/
private theorem isDisjointUnionOfVarieties_of_isVariety {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX) :
    IsDisjointUnionOfVarieties sX := by
  haveI : IsIntegral X := hX.toIsIntegral
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro C hC C' hC' hne
  rw [irreducibleComponents_eq_singleton] at hC hC'
  exact absurd (hC.trans hC'.symm) hne

/-- If the end result of a blow-up sequence of a variety is nonempty, it is a variety. -/
private theorem isVariety_toBase {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k)),
      AlgebraicGeometry.IsVariety k sX → Nonempty B.target →
        AlgebraicGeometry.IsVariety k (B.toBase ≫ sX)
  | X, .nil _, sX, hX, _ => by
    change AlgebraicGeometry.IsVariety k (𝟙 X ≫ sX)
    rwa [Category.id_comp]
  | X, .cons Z B, sX, hX, hne => by
    have hZ : Z ≠ ⊥ := by
      rintro rfl
      haveI := isEmpty_blowUp_bot X
      obtain ⟨y⟩ := hne
      exact isEmptyElim (B.toBase y)
    have := isVariety_toBase B _
      (MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational sX Z hZ).1 hne
    change AlgebraicGeometry.IsVariety k ((B.toBase ≫ blowUpToBase Z) ≫ sX)
    rwa [Category.assoc]

/-- A morphism which is an isomorphism over a nonempty open has points over it. -/
private theorem nonempty_preimage_of_isIso_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty := by
  obtain ⟨x, hx⟩ := hV
  obtain ⟨y, -⟩ := (g ∣_ V).surjective ⟨x, hx⟩
  exact ⟨y.1, y.2⟩

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)]
    (hV : (V : Set X).Nonempty) : IsBirationalMorphism g := by
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _
    (nonempty_preimage_of_isIso_restrict g V hV) hV le_rfl ?_
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-! ### From a divisor with simple normal crossings to its reduced ideal -/

/-- If each `w i`, `i ∈ s`, generates a prime ideal and no `w j` is a multiple of another `w i`,
then every common multiple of the `w i` is a multiple of their product. -/
private theorem prod_dvd_of_forall_dvd {R ι : Type*} [CommRing R] [DecidableEq ι] (w : ι → R)
    (s : Finset ι) (hp : ∀ i ∈ s, (Ideal.span {w i}).IsPrime)
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → w j ∉ Ideal.span {w i}) {r : R}
    (hr : ∀ i ∈ s, w i ∣ r) : (∏ i ∈ s, w i) ∣ r := by
  induction s using Finset.induction_on generalizing r with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨t, rfl⟩ := ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hne i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      (fun i hi => hr i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha]
    have hpa := hp a (Finset.mem_insert_self _ _)
    rcases hpa.mem_or_mem (Ideal.mem_span_singleton.2 (hr a (Finset.mem_insert_self _ _))) with
      h | h
    · obtain ⟨i, hi, hi'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hpa)).1 h
      exact (hne a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (fun e => ha (e ▸ hi)) hi').elim
    · obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton.1 h
      exact ⟨t', by ring⟩

/-- In the setting of `prod_dvd_of_forall_dvd`, the product of the `w i` generates a radical
ideal. -/
private theorem isRadical_span_prod {R ι : Type*} [CommRing R] [DecidableEq ι] (w : ι → R)
    (s : Finset ι) (hp : ∀ i ∈ s, (Ideal.span {w i}).IsPrime)
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → w j ∉ Ideal.span {w i}) :
    (Ideal.span {∏ i ∈ s, w i}).IsRadical := by
  rintro r ⟨n, hn⟩
  rw [Ideal.mem_span_singleton] at hn ⊢
  exact prod_dvd_of_forall_dvd w s hp hne fun i hi => Ideal.mem_span_singleton.1
    ((hp i hi).mem_of_pow_mem n
      (Ideal.mem_span_singleton.2 ((Finset.dvd_prod_of_mem w hi).trans hn)))

/-- If on `Spec 𝒪_{Y,y}` a closed set `T` is the union of the hyperplanes `(w_c = 0)`, `c ∈ s`,
for a regular system of parameters `w`, the stalk at `y` of the reduced ideal of `T` is
`(∏_{c ∈ s} w_c)`. -/
private theorem stalk_vanishingIdeal_eq_span_prod {Y : Scheme.{u}} (T : Closeds Y) (y : Y)
    [IsNoetherianRing (Y.presheaf.stalk y)] {N : ℕ} {w : Fin N → Y.presheaf.stalk y}
    (hw : MMP.Mori.IsRegularSystemOfParameters w) (s : Finset (Fin N))
    (hT : ∀ P : PrimeSpectrum (Y.presheaf.stalk y),
      Y.fromSpecStalk y P ∈ (T : Set Y) ↔ ∃ c ∈ s, w c ∈ P.asIdeal) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) y =
      Ideal.span {∏ c ∈ s, w c} := by
  classical
  set K := IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) y
  have hzl : PrimeSpectrum.zeroLocus (K : Set (Y.presheaf.stalk y)) =
      PrimeSpectrum.zeroLocus ((Ideal.span {∏ c ∈ s, w c} : Ideal _) : Set _) := by
    rw [← preimage_fromSpecStalk_support, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      PrimeSpectrum.zeroLocus_span]
    ext (P : PrimeSpectrum (Y.presheaf.stalk y))
    change Y.fromSpecStalk y P ∈ (T : Set Y) ↔ {∏ c ∈ s, w c} ⊆ (P.asIdeal : Set _)
    rw [Set.singleton_subset_iff, SetLike.mem_coe]
    exact (hT P).trans (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).symm
  calc K = K.radical := (isRadical_stalk_vanishingIdeal T y).radical.symm
    _ = (Ideal.span {∏ c ∈ s, w c}).radical := by
      rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
        ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hzl]
    _ = Ideal.span {∏ c ∈ s, w c} :=
      (isRadical_span_prod w s (fun c _ => span_singleton_isPrime_of_isRegularSystemOfParameters
        hw c) fun i _ j _ hij => notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw
          hij).radical

/-- Simple normal crossings at `x` follow from the stalk: if `I_x = (∏_{c ∈ s} w_c)` for a regular
system of parameters `w` of `𝒪_{X,x}`, then `I` has simple normal crossings at `x`. -/
private theorem hasSNCAt_of_stalk_eq_span_prod {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (x : X) {N : ℕ} {w : Fin N → X.presheaf.stalk x}
    (hw : MMP.Mori.IsRegularSystemOfParameters w) (s : Finset (Fin N))
    (h : IdealSheafData.stalk D x = Ideal.span {∏ c ∈ s, w c}) : HasSNCAt D x := by
  classical
  choose V hV t ht using fun c => X.presheaf.germ_exist (x := x) (w c)
  let W : X.Opens := Finset.univ.inf V
  have hxW : x ∈ W := by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
    exact Set.mem_iInter₂.2 fun c _ => hV c
  have hWV : ∀ c, W ≤ V c := fun c => Finset.inf_le (Finset.mem_univ c)
  let t' : Fin N → Γ(X, W) := fun c => (X.presheaf.map (homOfLE (hWV c)).op).hom (t c)
  have ht' : ∀ c (y : X) (hy : y ∈ W), (X.presheaf.germ W y hy).hom (t' c) =
      (X.presheaf.germ (V c) y (hWV c hy)).hom (t c) := fun c y hy =>
    X.presheaf.germ_res_apply (homOfLE (hWV c)) y hy (t c)
  let g : Γ(X, W) := ∏ c ∈ s, t' c
  have hg : (X.presheaf.germ W x hxW).hom g = ∏ c ∈ s, w c := by
    simp only [g, map_prod, ht', ht]
  obtain ⟨U, hUW, hxU, hU⟩ := MMP.Flips.ResolutionInputs.exists_ideal_eq_span_of_stalk_eq D hxW
    (fun _ : Unit => g) (by rw [Set.range_const, hg, h])
  let r : Fin N → Γ(X, U) := fun c => (X.presheaf.map (homOfLE hUW).op).hom (t' c)
  have hr : ∀ c (y : X) (hy : y ∈ U), (X.presheaf.germ U y hy).hom (r c) =
      (X.presheaf.germ W y (hUW hy)).hom (t' c) := fun c y hy =>
    X.presheaf.germ_res_apply (homOfLE hUW) y hy (t' c)
  refine ⟨N, U, hxU, r, fun c => if c ∈ s then 1 else 0, ?_, fun y hy => ?_⟩
  · convert hw using 1
    funext c
    rw [hr, ht', ht]
  · obtain ⟨W', hW', hyW', hW'U⟩ := exists_isAffineOpen_mem_and_subset hy
    rw [IdealSheafData.stalk_eq_map_germ D y ⟨W', hW'⟩ hyW', hU ⟨W', hW'⟩ hW'U, Ideal.map_span,
      Set.range_const, Set.image_singleton]
    congr 2
    have h1 : (X.presheaf.germ W' y hyW').hom (restrictSection ⟨W', hW'⟩ (hW'U.trans hUW) g) =
        (X.presheaf.germ W y (hUW hy)).hom g :=
      X.presheaf.germ_res_apply (homOfLE (hW'U.trans hUW)) y hyW' g
    rw [h1]
    simp only [pow_ite, pow_one, pow_zero]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
    simp only [g, map_prod, hr]

/-- On a locally Noetherian scheme, the reduced ideal of a closed set which is snc at every point
is a simple normal crossing divisor. -/
private theorem isSNCSubscheme_vanishingIdeal_of_forall_isSNCAt {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (T : Closeds Y) (hT : ∀ y, IsSNCAt (T : Set Y) y) :
    IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal T) := by
  intro y _
  obtain ⟨n, w, C, hw, hC⟩ := hT y
  refine hasSNCAt_of_stalk_eq_span_prod _ y hw C
    (stalk_vanishingIdeal_eq_span_prod T y hw C fun P => ?_)
  refine ((Set.ext_iff.1 hC) P).trans ?_
  change P ∈ (⋃ c ∈ C, PrimeSpectrum.zeroLocus {w c} : Set (PrimeSpectrum _)) ↔ _
  simp only [Set.mem_iUnion, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff,
    SetLike.mem_coe, exists_prop]

/-- A divisor with simple normal crossings on a smooth Noetherian scheme over a field is snc at
every point. -/
private theorem isSNCAt_of_isSNCClosedSubset {k : Type u} [Field k] {Y : Scheme.{u}}
    {f : Y ⟶ Spec (.of k)} [Smooth f] [NoetherianSpace Y] {D : Set Y}
    (hD : IsSNCClosedSubset f D) (y : Y) : IsSNCAt D y := by
  obtain ⟨hD, hD0 | ⟨-, -, hfam⟩⟩ := hD
  · subst hD0
    have := isRegularLocalRing_stalk_of_smooth_over_field f y
    obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk y)
    exact ⟨n, z, ∅, hz, by simp <;> rfl⟩
  · exact IsSNCClosedSubset.isSNCAt_of_nonempty hD hfam y

end Proof_lem_mmp_characteristic_zero_strong_resolution_dictionary

namespace MMP.Resolution

open Proof_lem_mmp_characteristic_zero_strong_resolution_dictionary

/-- Every variety over a field of characteristic zero has a strong resolution: a projective
birational morphism `g : Y ⟶ X` from a smooth variety, an isomorphism over the smooth locus of
`X`, with `g⁻¹(Sing X)_red` a simple normal crossing divisor. -/
@[mmp "lem_mmp_characteristic_zero_strong_resolution_dictionary"]
public theorem exists_isStrongResolution {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X),
      AlgebraicGeometry.IsVariety k (g ≫ sX) ∧ AlgebraicGeometry.IsProjective g ∧
      IsBirationalMorphism g ∧ IsSmoothScheme (g ≫ sX) ∧ IsIso (g ∣_ smoothLocus sX) ∧
      IsSNCSubscheme
        (Scheme.IdealSheafData.vanishingIdeal ((singularLocus sX).preimage g.continuous)) := by
  haveI : IsIntegral X := hX.toIsIntegral
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsNoetherian X := {}
  obtain ⟨BR, hBR, -⟩ := MMP.Resolution.exists_strongResolution_blowupSequenceFunctor.{u}
  have hDU := isDisjointUnionOfVarieties_of_isVariety sX hX
  obtain ⟨hsm, hiso, hsnc⟩ := hBR sX hDU
  set B := BR sX hDU
  set g := B.toBase
  have hsmne : ((smoothLocus sX : X.Opens) : Set X).Nonempty := by
    rw [smoothLocus_eq_smoothLocus]
    exact (Scheme.Hom.dense_smoothLocus_of_perfectField sX).nonempty
  have hY : AlgebraicGeometry.IsVariety k (g ≫ sX) := isVariety_toBase B sX hX
    ⟨(nonempty_preimage_of_isIso_restrict g (smoothLocus sX) hsmne).some⟩
  haveI : IsIntegral B.target := hY.toIsIntegral
  haveI : IsLocallyNoetherian B.target := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : CompactSpace B.target := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian B.target := {}
  haveI : Smooth (g ≫ sX) := (isSmoothScheme_iff _).1 hsm
  exact ⟨B.target, g, hY, ClosedBlowupSequence.isProjective_toBase B,
    isBirationalMorphism_of_isIso_restrict g (smoothLocus sX) hsmne, hsm, hiso,
    isSNCSubscheme_vanishingIdeal_of_forall_isSNCAt _
      fun y => isSNCAt_of_isSNCClosedSubset hsnc y⟩

end MMP.Resolution
