module

public import MMP.AlgebraicGeometry.Divisor.CartierDivisorFamiliesHilbert
public import MMP.AlgebraicGeometry.Intersection.Surface.RiemannRochHodgeIndex
public import MMP.AlgebraicGeometry.Positivity.AmpleNumerical
public import MMP.AlgebraicGeometry.Vanishing.KodairaSerreDual

section

/-!
# Numerically trivial line bundles on a surface have rationally zero Chern class

Let `S` be a smooth projective complex surface and `L` a numerically trivial invertible sheaf.
Then `c₁(L) = 0` in `H²(S^an; ℚ)`.

Write `L ≅ 𝒪_S(D)`. For a sufficiently ample `H` the divisors `H + nD - K_S` are ample, so by
Kodaira vanishing and Riemann–Roch `h⁰(𝒪_S(H + nD)) = χ(𝒪_S(H)) > 0` for every `n ≥ 0`. The zero
schemes `D_n` of nonzero sections are effective Cartier divisors with one and the same Hilbert
polynomial, so they are fibres of finitely many families of effective Cartier divisors over
schemes of finite type. Two of them, `D_n` and `D_m` with `n ≠ m`, lie over points of one
irreducible component of one parameter scheme `T`, whose complex points form a path connected
space. Along a path the two fibre inclusions `S^an ⟶ (S × T)^an` are homotopic, so the first
Chern classes of the restrictions of `𝒪(𝒟)` agree: `c₁(𝒪(H + nD)) = c₁(𝒪(H + mD))`, that is
`(n - m) c₁(L) = 0`.

## Main results

* `MMP.Analytic.mapCoeff_algebraicFirstChernClass_eq_zero_of_degreeOn_eq_zero`.

## Implementation notes

* `H` is `K_S + M G` for an ample and very ample `G`; positive multiples of `G` and their sums
  with `n D` are ample by the numerical criterion of ampleness, `D` having degree zero on every
  curve. `χ(𝒪_S(H)) > 0` for `M` large, by Riemann–Roch and `(G · G) > 0`.
* The Hilbert polynomial of `D_n` with respect to `𝒪_S(G)` is computed from the ideal sequence:
  `χ(D_n, 𝒪_S(t G)|_{D_n}) = χ(𝒪_S(t G)) - χ(𝒪_S(t G - H - n D))`, which by Riemann–Roch is the
  affine function `t ↦ t (G · H) + χ(𝒪_S) - χ(𝒪_S(-H))` of `t`.
* Path connectedness of the complex points of an irreducible component `T₀` of a parameter scheme
  is that of an integral scheme of finite type over `ℂ`: its regular part is connected and dense,
  and it is locally contractible.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

open CategoryTheory AlgebraicGeometry Limits

open scoped Stacks.SmallDerivedModel

namespace MMP.FourfoldProofs.MmpConductorSurfaceNumericChernZeroProof

open MMP.Analytic MMP.Analytic.ComplexPoints MMP

/-! ### Homotopic fibre inclusions -/

section Fibre

variable {S T : Scheme.{0}} [S.Over (Spec (.of ℂ))] (sT : T ⟶ Spec (.of ℂ))

/-- The fibre inclusion `S ⟶ S × T`, `s ↦ (s, t)`, at a `ℂ`-point `t` of `T`. -/
private noncomputable def fibreι (t : ComplexPoints sT) : S ⟶ pullback (S ↘ Spec (.of ℂ)) sT :=
  pullback.lift (𝟙 S) (S ↘ Spec (.of ℂ) ≫ t.hom) (by
    rw [Category.id_comp, Category.assoc, t.hom_comp_structure, Category.comp_id])

/-- The product scheme `S × T` over `ℂ`, through its first projection. -/
private noncomputable abbrev prodOver : (pullback (S ↘ Spec (.of ℂ)) sT).Over (Spec (.of ℂ)) :=
  ⟨pullback.fst _ _ ≫ S ↘ Spec (.of ℂ)⟩

/-- **Fibres over a path have the same first Chern class.** For an invertible module `M` on
`S × T` and a path `γ` in `T(ℂ)` from `a` to `b`, the restrictions of `M` to the fibres
`S × {a}` and `S × {b}` have the same first Chern class. -/
private theorem algebraicFirstChernClass_pullback_fibreι_eq
    (M : (pullback (S ↘ Spec (.of ℂ)) sT).Modules)
    [SheafOfModules.IsInvertible (pullback (S ↘ Spec (.of ℂ)) sT).presheaf
      (pullback (S ↘ Spec (.of ℂ)) sT).ringCatSheaf.2 M]
    {a b : ComplexPoints sT} (γ : Path a b)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((Scheme.Modules.pullback (fibreι sT a)).obj M)]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((Scheme.Modules.pullback (fibreι sT b)).obj M)] :
    letI := prodOver (S := S) sT
    algebraicFirstChernClass ((Scheme.Modules.pullback (fibreι sT a)).obj M) =
      algebraicFirstChernClass ((Scheme.Modules.pullback (fibreι sT b)).obj M) := by
  letI := prodOver (S := S) sT
  letI : T.Over (Spec (.of ℂ)) := ⟨sT⟩
  haveI : (pullback.fst (S ↘ Spec (.of ℂ)) sT).IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : (pullback.snd (S ↘ Spec (.of ℂ)) sT).IsOver (Spec (.of ℂ)) := ⟨pullback.condition.symm⟩
  -- the homotopy `(τ, s) ↦ (s, γ τ)`
  let pt : unitInterval × ComplexPoints (S ↘ Spec (.of ℂ)) →
      ComplexPoints (pullback (S ↘ Spec (.of ℂ)) sT ↘ Spec (.of ℂ)) := fun p =>
    ⟨pullback.lift p.2.hom (γ p.1).hom (by
        rw [p.2.hom_comp_structure, (γ p.1).hom_comp_structure]), by
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _ = _
      rw [pullback.lift_fst_assoc, p.2.hom_comp_structure]⟩
  have hemb := UnderlyingSpace.isEmbedding_prodMap_of_isPullback (K := ℂ)
    (IsPullback.of_hasPullback (S ↘ Spec (.of ℂ)) sT)
  have hcont : Continuous pt := by
    have h1 : Continuous fun p => homeomorphUnderlyingSpace (pt p) := by
      rw [hemb.continuous_iff]
      have : (UnderlyingSpace.prodMap (K := ℂ) (pullback.fst (S ↘ Spec (.of ℂ)) sT)
            (pullback.snd (S ↘ Spec (.of ℂ)) sT) ∘ fun p => homeomorphUnderlyingSpace (pt p)) =
          fun p => (homeomorphUnderlyingSpace p.2,
            homeomorphUnderlyingSpace (X := T) (γ p.1)) := by
        funext p
        refine Prod.ext (UnderlyingSpace.ext ?_) (UnderlyingSpace.ext ?_)
        · exact pullback.lift_fst _ _ _
        · exact pullback.lift_snd _ _ _
      rw [this]
      exact (homeomorphUnderlyingSpace.continuous.comp continuous_snd).prodMk
        ((homeomorphUnderlyingSpace (X := T)).continuous.comp (γ.continuous.comp continuous_fst))
    exact homeomorphUnderlyingSpace.symm.continuous.comp h1 |>.congr fun p => by simp
  let g : unitInterval → (Analytification.space (S ↘ Spec (.of ℂ)) ⟶
      Analytification.space (pullback (S ↘ Spec (.of ℂ)) sT ↘ Spec (.of ℂ))) := fun τ =>
    TopCat.ofHom ⟨fun x => pt (τ, x), hcont.comp (Continuous.prodMk_right τ)⟩
  let Hm : TopCat.Homotopy (g 0) (g 1) :=
    { toFun := pt
      continuous_toFun := hcont
      map_zero_left := fun _ => rfl
      map_one_left := fun _ => rfl }
  have hg : ∀ (t : ComplexPoints sT) (τ : unitInterval), γ τ = t →
      ∀ x, (g τ x).hom = x.hom ≫ fibreι sT t := by
    intro t τ hτ x
    refine pullback.hom_ext ?_ ?_
    · change pullback.lift _ _ _ ≫ _ = _
      rw [pullback.lift_fst, Category.assoc, fibreι, pullback.lift_fst, Category.comp_id]
    · change pullback.lift _ _ _ ≫ _ = _
      rw [pullback.lift_snd, Category.assoc, fibreι, pullback.lift_snd, ← Category.assoc,
        x.hom_comp_structure, Category.id_comp, hτ]
  rw [algebraicFirstChernClass_pullback (fibreι sT a) (g 0) (hg a 0 γ.source) M,
    algebraicFirstChernClass_pullback (fibreι sT b) (g 1) (hg b 1 γ.target) M]
  exact congrArg (fun φ => ModuleCat.Hom.hom φ (algebraicFirstChernClass M))
    (relativeSingularCohomology.map_eq_of_homotopy ℤ Hm (fun _ h => (h (Set.mem_univ _)).elim)
      _ _ 2)

end Fibre

/-! ### Path connectedness of an irreducible component -/

/-- **Two `ℂ`-points of an irreducible component are joined by a path.** For a scheme `T` locally
of finite type and quasi-compact over `ℂ`, two `ℂ`-points lying on one irreducible component
of `T` are joined by a path in `T(ℂ)`: the component, with its reduced structure, is an
integral scheme of finite type over `ℂ`, whose complex points form a connected and locally path
connected space. -/
private theorem nonempty_path_of_mem_irreducibleComponents {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sT] [QuasiCompact sT] {C : Set T}
    (hC : C ∈ irreducibleComponents T) {a b : ComplexPoints sT} (ha : a.toScheme ∈ C)
    (hb : b.toScheme ∈ C) : Nonempty (Path a b) := by
  let I := Scheme.IdealSheafData.vanishingIdeal ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩
  haveI : IsIntegral I.subscheme :=
    MMP.Fourfold.isIntegral_subscheme_vanishingIdeal _ hC.1
  have hker : ∀ c : ComplexPoints sT, c.toScheme ∈ C → I.subschemeι.ker ≤ c.hom.ker := by
    intro c hc
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
    rw [TopologicalSpace.Closeds.closure_le]
    rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim y default]
  let sC := I.subschemeι ≫ sT
  let lift : ∀ c : ComplexPoints sT, c.toScheme ∈ C → ComplexPoints sC := fun c hc =>
    ⟨IsClosedImmersion.lift I.subschemeι c.hom (hker c hc), by
      rw [IsClosedImmersion.lift_fac_assoc, c.hom_comp_structure]⟩
  have hlift : ∀ c hc, realize I.subschemeι rfl (lift c hc) = c := fun c hc =>
    ComplexPoints.ext (IsClosedImmersion.lift_fac _ _ _)
  -- `C(ℂ)` is connected and locally path connected, hence path connected
  letI : I.subscheme.Over (Spec (.of ℂ)) := ⟨sC⟩
  haveI : LocallyOfFiniteType (I.subscheme ↘ Spec (.of ℂ)) :=
    (inferInstance : LocallyOfFiniteType sC)
  haveI : QuasiCompact (I.subscheme ↘ Spec (.of ℂ)) := (inferInstance : QuasiCompact sC)
  have hconn : IsConnected (UnderlyingSpace.regularPart ℂ I.subscheme) := by
    simpa using UnderlyingSpace.isConnected_regularPart_diff (X := I.subscheme)
      isClosed_empty (Set.empty_ne_univ (α := I.subscheme))
  haveI : ConnectedSpace (UnderlyingSpace ℂ I.subscheme) := by
    rw [connectedSpace_iff_univ, ← UnderlyingSpace.dense_regularPart.closure_eq]
    exact hconn.closure
  have hb' := UnderlyingSpace.hasOpenContractibleBasis I.subscheme
  haveI : LocallyPathConnectedSpace (UnderlyingSpace ℂ I.subscheme) :=
    LocallyPathConnectedSpace.of_bases hb' fun x V hV => by
      show IsPathConnected V
      haveI : ContractibleSpace V := hV.2.2
      exact isPathConnected_iff_pathConnectedSpace.2 inferInstance
  haveI : ConnectedSpace (ComplexPoints sC) :=
    (homeomorphUnderlyingSpace (X := I.subscheme)).symm.surjective.connectedSpace
      (homeomorphUnderlyingSpace (X := I.subscheme)).symm.continuous
  haveI : LocallyPathConnectedSpace (ComplexPoints sC) :=
    (homeomorphUnderlyingSpace (X := I.subscheme)).isOpenEmbedding.locallyPathConnectedSpace
  haveI : PathConnectedSpace (ComplexPoints sC) :=
    pathConnectedSpace_iff_connectedSpace.2 inferInstance
  exact ⟨((PathConnectedSpace.somePath (lift a ha) (lift b hb)).map
    (continuous_realize I.subschemeι rfl)).cast (hlift a ha).symm (hlift b hb).symm⟩

/-- **Fibre divisors over one irreducible component have the same first Chern class.** For an
effective Cartier divisor `𝒟` on `S × T` and two `ℂ`-points `a, b` of one irreducible component
of `T`, the fibre divisors of `𝒟` over `a` and `b` have the same first Chern class. -/
private theorem algebraicFirstChernClass_comap_fibreι_eq {S T : Scheme.{0}}
    [S.Over (Spec (.of ℂ))] (sT : T ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sT] [QuasiCompact sT]
    (𝒟 : (pullback (S ↘ Spec (.of ℂ)) sT).IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor 𝒟] {C : Set T} (hC : C ∈ irreducibleComponents T)
    {a b : ComplexPoints sT} (ha : a.toScheme ∈ C) (hb : b.toScheme ∈ C)
    [Stacks.Divisors.IsEffectiveCartierDivisor (𝒟.comap (fibreι sT a))]
    [Stacks.Divisors.IsEffectiveCartierDivisor (𝒟.comap (fibreι sT b))] :
    algebraicFirstChernClass
        (Stacks.Divisors.invertibleSheaf' (𝒟.comap (fibreι sT a)) : S.Modules) =
      algebraicFirstChernClass
        (Stacks.Divisors.invertibleSheaf' (𝒟.comap (fibreι sT b)) : S.Modules) := by
  obtain ⟨γ⟩ := nonempty_path_of_mem_irreducibleComponents sT hC ha hb
  haveI : Stacks.Divisors.IsPullbackDefined (fibreι sT a) 𝒟 := ‹_›
  haveI : Stacks.Divisors.IsPullbackDefined (fibreι sT b) 𝒟 := ‹_›
  rw [← algebraicFirstChernClass_eq_of_iso
      (Stacks.Divisors.invertibleSheafPullbackIso (fibreι sT a) 𝒟),
    ← algebraicFirstChernClass_eq_of_iso
      (Stacks.Divisors.invertibleSheafPullbackIso (fibreι sT b) 𝒟)]
  exact algebraicFirstChernClass_pullback_fibreι_eq sT _ γ

/-! ### The intersection pairing of a proper surface -/

section Pairing

variable {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ)) [IsProper f] [IsLocallyNoetherian S]
  [IsNormal S] [CompactSpace S] (hd : topologicalKrullDim S ≤ (2 : ℕ))
  (hC : ∀ D : MMP.Mori.Divisor S, D.IsCartier)

/-- The intersection number `(D · E)` of two divisors on a proper surface on which every divisor
is Cartier. -/
private noncomputable def ip (D E : MMP.Mori.Divisor S) : ℤ :=
  MMP.Mori.Divisor.intersectionNumberOn ℂ f (𝟙 S) 2 hd ![D, E] fun _ => hC _

private theorem isInvertible_pair (N₁ N₂ : S.Modules)
    [h₁ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₁]
    [h₂ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N₂] :
    ∀ j : Fin 2, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (![N₁, N₂] j) := by
  intro j
  fin_cases j
  exacts [h₁, h₂]

/-- `(D · E)` is the intersection number of the pair `𝒪_S(D), 𝒪_S(E)`. -/
private theorem ip_eq (D E : MMP.Mori.Divisor S) :
    haveI := (hC D).isInvertibleModule_divisorialSheaf
    haveI := (hC E).isInvertibleModule_divisorialSheaf
    haveI := isInvertible_pair D.divisorialSheaf E.divisorialSheaf
    ip f hd hC D E = AlgebraicGeometry.intersectionNumber ℂ f (𝟙 S) 2 hd
      ![D.divisorialSheaf, E.divisorialSheaf] := by
  haveI := fun D : MMP.Mori.Divisor S => (hC D).isInvertibleModule_divisorialSheaf
  haveI := isInvertible_pair D.divisorialSheaf E.divisorialSheaf
  unfold ip MMP.Mori.Divisor.intersectionNumberOn
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact AlgebraicGeometry.intersectionNumber_congr_family ℂ f (𝟙 S) 2 hd
    (funext fun j => by fin_cases j <;> rfl)

private theorem ip_comm (D E : MMP.Mori.Divisor S) : ip f hd hC D E = ip f hd hC E D := by
  haveI := fun D : MMP.Mori.Divisor S => (hC D).isInvertibleModule_divisorialSheaf
  haveI := isInvertible_pair D.divisorialSheaf E.divisorialSheaf
  haveI := isInvertible_pair E.divisorialSheaf D.divisorialSheaf
  rw [ip_eq, ip_eq, ← AlgebraicGeometry.intersectionNumber_comp_perm ℂ f (𝟙 S) 2 hd
    ![E.divisorialSheaf, D.divisorialSheaf] (Equiv.swap 0 1)]
  exact AlgebraicGeometry.intersectionNumber_congr_family ℂ f (𝟙 S) 2 hd
    (funext fun j => by fin_cases j <;> rfl)

private theorem ip_add_left (D D' E : MMP.Mori.Divisor S) :
    ip f hd hC (D + D') E = ip f hd hC D E + ip f hd hC D' E := by
  haveI := fun D : MMP.Mori.Divisor S => (hC D).isInvertibleModule_divisorialSheaf
  haveI := isInvertible_pair (D + D').divisorialSheaf E.divisorialSheaf
  haveI := isInvertible_pair D.divisorialSheaf E.divisorialSheaf
  haveI := isInvertible_pair D'.divisorialSheaf E.divisorialSheaf
  rw [ip_eq, ip_eq, ip_eq]
  exact AlgebraicGeometry.intersectionNumber_tensor ℂ f (𝟙 S) 2 hd 0 _ _ _
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl)
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl)
    ((hC D).divisorialSheafTensorIso (hC D')).symm

/-- `(· · E)` as an additive map. -/
private noncomputable def ipLeft (E : MMP.Mori.Divisor S) : MMP.Mori.Divisor S →+ ℤ :=
  AddMonoidHom.mk' (fun D => ip f hd hC D E) fun D D' => ip_add_left f hd hC D D' E

private theorem ip_add_right (D E E' : MMP.Mori.Divisor S) :
    ip f hd hC D (E + E') = ip f hd hC D E + ip f hd hC D E' := by
  rw [ip_comm, ip_add_left, ip_comm, ip_comm f hd hC E']

private theorem ip_zsmul_left (n : ℤ) (D E : MMP.Mori.Divisor S) :
    ip f hd hC (n • D) E = n * ip f hd hC D E :=
  (map_zsmul (ipLeft f hd hC E) n D).trans (smul_eq_mul _ _)

private theorem ip_zsmul_right (n : ℤ) (D E : MMP.Mori.Divisor S) :
    ip f hd hC D (n • E) = n * ip f hd hC D E := by
  rw [ip_comm, ip_zsmul_left, ip_comm]

private theorem ip_neg_left (D E : MMP.Mori.Divisor S) :
    ip f hd hC (-D) E = -ip f hd hC D E :=
  map_neg (ipLeft f hd hC E) D

private theorem ip_neg_right (D E : MMP.Mori.Divisor S) :
    ip f hd hC D (-E) = -ip f hd hC D E := by
  rw [ip_comm, ip_neg_left, ip_comm]

/-- **Cutting down by a prime divisor.** On a smooth proper surface, `(P · E)` is the degree of
`𝒪_S(E)` along the prime divisor `P`. -/
private theorem ip_single_left (hsm : MMP.Mori.IsSmoothScheme f) (P : MMP.Mori.PrimeDivisor S)
    (hP : topologicalKrullDim P.idealSheaf.subscheme ≤ 1) (E : MMP.Mori.Divisor S) :
    haveI := (hC E).isInvertibleModule_divisorialSheaf
    ip f hd hC (Finsupp.single P 1) E =
      MMP.Mori.degreeOn ℂ f P.idealSheaf.subschemeι hP E.divisorialSheaf := by
  haveI := fun D : MMP.Mori.Divisor S => (hC D).isInvertibleModule_divisorialSheaf
  haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P
  haveI := isInvertible_pair
    (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor S)) E.divisorialSheaf
  obtain ⟨e⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' P
    inferInstance (hC _)
  have hL : (Scheme.Modules.pullback (𝟙 S)).obj
      (![MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor S),
        E.divisorialSheaf] 0) ≅
      (Stacks.Divisors.invertibleSheaf P.idealSheaf : S.Modules) :=
    (Scheme.Modules.pullbackId S).app _ ≪≫ e
  rw [ip_eq, AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor' ℂ f (𝟙 S) 1 hd
    _ P.idealSheaf hL]
  rw [AlgebraicGeometry.intersectionNumber_congr_family ℂ f _ 1 _
    (show (fun t : Fin 1 => ![MMP.Mori.Divisor.divisorialSheaf
      (Finsupp.single P 1 : MMP.Mori.Divisor S),
      E.divisorialSheaf] t.succ) = fun _ => E.divisorialSheaf from
        funext fun t => by fin_cases t; rfl)]
  have key : ∀ (j : P.idealSheaf.subscheme ⟶ S) [IsClosedImmersion j]
      (hj : j = P.idealSheaf.subschemeι) (hdj : topologicalKrullDim P.idealSheaf.subscheme ≤ 1),
      AlgebraicGeometry.intersectionNumber ℂ f j 1 hdj (fun _ => E.divisorialSheaf) =
        MMP.Mori.degreeOn ℂ f P.idealSheaf.subschemeι hP E.divisorialSheaf := by
    intro j _ hj hdj
    subst hj
    rw [AlgebraicGeometry.intersectionNumber_one_eq_invertibleCurveDegree,
      MMP.Mori.degreeOn_eq_invertibleCurveDegree]
  exact key _ (Category.comp_id _) _

end Pairing

/-! ### Twists of the structure sheaf and Euler characteristics -/

section Twists

open Stacks.SheafOfModules.Invertible

/-- The tensor product of `𝒪_X`-modules. -/
private noncomputable abbrev tens (X : Scheme.{0}) : X.Modules ⥤ X.Modules ⥤ X.Modules :=
  Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
    (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩

private theorem nonempty_iso_of_tensor_iso {X : Scheme.{0}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {A B : X.Modules}
    (h : ((tens X).obj A).obj L ≅ ((tens X).obj B).obj L) : Nonempty (A ≅ B) := by
  haveI : ((tens X).flip.obj L).IsEquivalence :=
    (isInvertible_iff_tensorRightFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 L).1
      inferInstance
  exact ⟨((tens X).flip.obj L).preimageIso h⟩

/-- `𝒪_X(n D) ≅ 𝒪_X(D)^{⊗ n}` for a Cartier divisor `D` and an integer `n`. -/
private theorem nonempty_divisorialSheaf_zsmul_iso {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {D : MMP.Mori.Divisor X} (hD : D.IsCartier) (n : ℤ) :
    haveI := hD.isInvertibleModule_divisorialSheaf
    Nonempty ((n • D).divisorialSheaf ≅
      tensorPower X.presheaf X.ringCatSheaf.2 D.divisorialSheaf n) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  set L := D.divisorialSheaf
  induction n using Int.induction_on with
  | zero => exact ⟨eqToIso (by rw [zero_smul]) ≪≫ MMP.Mori.Divisor.divisorialSheafZeroIso⟩
  | succ i ih =>
    obtain ⟨e⟩ := ih
    have h : (((i : ℤ) + 1) • D).divisorialSheaf ≅
        ((tens X).obj ((i : ℤ) • D).divisorialSheaf).obj L :=
      eqToIso (by rw [add_smul, one_smul]) ≪≫ (((hD.zsmul i).divisorialSheafTensorIso hD)).symm
    exact ⟨h ≪≫ ((tens X).mapIso e).app L ≪≫ tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L i⟩
  | pred i ih =>
    obtain ⟨e⟩ := ih
    have h : ((tens X).obj ((-(i : ℤ) - 1) • D).divisorialSheaf).obj L ≅
        ((-(i : ℤ)) • D).divisorialSheaf :=
      (hD.zsmul _).divisorialSheafTensorIso hD ≪≫
        eqToIso (by rw [sub_smul, one_smul, sub_add_cancel])
    have h2 : ((tens X).obj (tensorPower X.presheaf X.ringCatSheaf.2 L (-(i : ℤ) - 1))).obj L ≅
        ((-(i : ℤ)) • D).divisorialSheaf :=
      tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 L _ ≪≫
        tensorPowerReindex X.presheaf X.ringCatSheaf.2 L (n := -(i : ℤ) - 1 + 1) (m := -(i : ℤ))
          (by ring) ≪≫ e.symm
    exact nonempty_iso_of_tensor_iso L (h.trans h2.symm)

/-- The two-term family `𝒪_X(D), 𝒪_X(E)`. -/
private noncomputable abbrev pairFamily {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    (D E : MMP.Mori.Divisor X) : Fin 2 → X.Modules :=
  Fin.cons D.divisorialSheaf fun _ : Fin 1 => E.divisorialSheaf

private theorem isInvertible_pairFamily {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {D E : MMP.Mori.Divisor X} (hD : D.IsCartier) (hE : E.IsCartier) :
    ∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (pairFamily D E t) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := hE.isInvertibleModule_divisorialSheaf
  intro t
  refine Fin.cases ?_ (fun _ => ?_) t
  · show SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 D.divisorialSheaf
    infer_instance
  · show SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E.divisorialSheaf
    infer_instance

/-- `𝒪_X ⊗ 𝒪_X(D)^{⊗ a} ⊗ 𝒪_X(E)^{⊗ b} ≅ 𝒪_X(a D + b E)`. -/
private theorem nonempty_twistedSheaf_pairFamily_iso {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {D E : MMP.Mori.Divisor X} (hD : D.IsCartier)
    (hE : E.IsCartier) (a b : ℤ) :
    haveI := isInvertible_pairFamily hD hE
    Nonempty (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (pairFamily D E)
      (Fin.cons a fun _ => b) ≅ (a • D + b • E).divisorialSheaf) := by
  haveI := isInvertible_pairFamily hD hE
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := hE.isInvertibleModule_divisorialSheaf
  obtain ⟨ea⟩ := nonempty_divisorialSheaf_zsmul_iso hD a
  obtain ⟨eb⟩ := nonempty_divisorialSheaf_zsmul_iso hE b
  have hfold : twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (pairFamily D E)
      (Fin.cons a fun _ => b) = ((tens X).obj (((tens X).obj
        (SheafOfModules.unit X.ringCatSheaf)).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 D.divisorialSheaf a))).obj
          (tensorPower X.presheaf X.ringCatSheaf.2 E.divisorialSheaf b) := by
    change List.foldl _ _ (List.finRange 2) = _
    rw [List.finRange_succ, List.finRange_succ, List.finRange_zero]
    rfl
  rw [hfold]
  exact ⟨tensorProductIso X.presheaf X.ringCatSheaf.2
    (tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫ ea.symm) eb.symm ≪≫
      (hD.zsmul a).divisorialSheafTensorIso (hE.zsmul b)⟩

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [IsProper f]

/-- The Euler characteristic `χ(𝒪_X(D))` of a Cartier divisor. -/
private noncomputable def chi [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (D : MMP.Mori.Divisor X) (hD : D.IsCartier) : ℤ :=
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X D.divisorialSheaf
  eulerCharacteristic ℂ f D.divisorialSheaf

private theorem eulerCharacteristic_eq_chi [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {D : MMP.Mori.Divisor X} (hD : D.IsCartier) {M : X.Modules} (hM : M.IsCoherent)
    (e : M ≅ D.divisorialSheaf) : @eulerCharacteristic ℂ _ X f _ M hM = chi f D hD := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X D.divisorialSheaf
  exact eulerCharacteristic_eq_of_iso ℂ f e

private theorem chi_congr [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {D D' : MMP.Mori.Divisor X} (h : D = D') (hD : D.IsCartier) (hD' : D'.IsCartier) :
    chi f D hD = chi f D' hD' := by
  subst h; rfl

/-- **The first difference along an effective Cartier divisor**, at an arbitrary exponent vector.
For an effective Cartier divisor `D ⊆ X` and invertible sheaves `𝓛_0 ≅ 𝒪_X(D), 𝓛_1, …, 𝓛_d`,
`χ(X, 𝓛^{e}) - χ(X, 𝓛_0^{-1} ⊗ 𝓛^{e}) = χ(D, 𝓛^{e}|_D)` for `𝓛^e = ⨂ 𝓛_j^{⊗ e_j}`: the ideal
sequence `0 ⟶ 𝒪_X(-D) ⟶ 𝒪_X ⟶ 𝒪_D ⟶ 0`, twisted by `𝓛^e`, and additivity of `χ`. -/
private theorem eulerCharacteristic_twistedSheaf_sub_eq {d : ℕ} (M₀ : X.Modules)
    (N : Fin d → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ((Fin.cons M₀ N :
      Fin (d + 1) → X.Modules) t)]
    (Dv : X.IdealSheafData) [hDv : Stacks.Divisors.IsEffectiveCartierDivisor Dv]
    (hL : M₀ ≅ (Stacks.Divisors.invertibleSheaf Dv : X.Modules)) (e : Fin d → ℤ) :
    (@eulerCharacteristic ℂ _ X f _
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (Fin.cons M₀ N) (Fin.cons 0 e))
        (@twistedSheaf_isCoherent X (d + 1) _ (Fin.cons M₀ N) _
          (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit ℂ f) _) : ℤ) -
      (@eulerCharacteristic ℂ _ X f _
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (Fin.cons M₀ N) (Fin.cons (-1) e))
        (@twistedSheaf_isCoherent X (d + 1) _ (Fin.cons M₀ N) _
          (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit ℂ f) _) : ℤ) =
    @eulerCharacteristic ℂ _ Dv.subscheme (Dv.subschemeι ≫ f) _
      (twistedSheaf (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
        (fun t : Fin d => (Scheme.Modules.pullback Dv.subschemeι).obj
          ((Fin.cons M₀ N : Fin (d + 1) → X.Modules) t.succ)) e)
      (isCoherent_twistedSheafUnitPullback ℂ f Dv.subschemeι
        (fun t : Fin d => (Fin.cons M₀ N : Fin (d + 1) → X.Modules) t.succ) e) := by
  classical
  set L : Fin (d + 1) → X.Modules := Fin.cons M₀ N with hLdef
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hinvW : ∀ t, SheafOfModules.IsInvertible Dv.subscheme.presheaf
      Dv.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback Dv.subschemeι).obj (L t)) :=
    fun t => SheafOfModules.isInvertible_pullback _ (L t)
  let Sq : ShortComplex X.Modules :=
    ShortComplex.mk (C := X.Modules) (Stacks.IdealSheafSequence.divisorIdealMap Dv)
      (Stacks.IdealSheafSequence.divisorQuotientMap Dv)
      (Stacks.IdealSheafSequence.divisorIdeal_shortExact Dv).choose
  have hSq : Sq.ShortExact := (Stacks.IdealSheafSequence.divisorIdeal_shortExact Dv).choose_spec
  have hfin : ∀ G : X.Modules, _root_.SheafOfModules.IsCoherent G →
      ∀ m : ℕ, FiniteDimensional ℂ (cohomologyOverField ℂ f G m) := fun G hG m =>
    @finiteDimensional_cohomologyOverField_of_isProper ℂ _ X f _ G hG m
  have cOX : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit ℂ f
  have cOW : _root_.SheafOfModules.IsCoherent
      (SheafOfModules.unit Dv.subscheme.ringCatSheaf : Dv.subscheme.Modules) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit ℂ (Dv.subschemeι ≫ f)
  have cN : _root_.SheafOfModules.IsCoherent (Stacks.Divisors.negativeTwist Dv : X.Modules) :=
    @SheafOfModules.isCoherent_of_isInvertible X ℂ _ f _ _ hDv
  have cT3 : _root_.SheafOfModules.IsCoherent Sq.X₃ :=
    @isCoherent_pushforward_of_isClosedImmersion Dv.subscheme X Dv.subschemeι _ _ _ cOW
  have hadd := eulerCharacteristic_twistedSheaf_add_of_shortExact ℂ f L hfin hSq cN cOX cT3
    (Fin.cons 0 e)
  have cXN : _root_.SheafOfModules.IsCoherent
      (twistedSheaf (Stacks.Divisors.negativeTwist Dv : X.Modules) L (Fin.cons 0 e)) :=
    @twistedSheaf_isCoherent X (d + 1) _ L _ cN _
  have cXm : _root_.SheafOfModules.IsCoherent
      (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) L (Fin.cons (-1) e)) :=
    @twistedSheaf_isCoherent X (d + 1) _ L _ cOX _
  have cW0 : _root_.SheafOfModules.IsCoherent
      (twistedSheaf (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
        (fun t => (Scheme.Modules.pullback Dv.subschemeι).obj (L t)) (Fin.cons 0 e)) :=
    isCoherent_twistedSheafUnitPullback ℂ f Dv.subschemeι L (Fin.cons 0 e)
  have cWf : _root_.SheafOfModules.IsCoherent
      (twistedSheaf (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
        (fun t : Fin d => (Scheme.Modules.pullback Dv.subschemeι).obj (L t.succ)) e) :=
    isCoherent_twistedSheafUnitPullback ℂ f Dv.subschemeι (fun t : Fin d => L t.succ) e
  have hfirst : (@eulerCharacteristic ℂ _ X f _
        (twistedSheaf Sq.X₁ L (Fin.cons 0 e)) cXN : ℤ) =
      @eulerCharacteristic ℂ _ X f _
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) L (Fin.cons (-1) e)) cXm :=
    @eulerCharacteristic_eq_of_iso ℂ _ X f _ _ _ cXN cXm
      (@twistedSheafNegativeTwistConsZeroIso X d Dv hDv L _ hL e)
  have hthird : (@eulerCharacteristic ℂ _ X f _ (twistedSheaf Sq.X₃ L (Fin.cons 0 e))
        (@twistedSheaf_isCoherent X (d + 1) Sq.X₃ L _ cT3 _) : ℤ) =
      @eulerCharacteristic ℂ _ Dv.subscheme (Dv.subschemeι ≫ f) _
        (twistedSheaf (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback Dv.subschemeι).obj (L t)) (Fin.cons 0 e)) cW0 :=
    @eulerCharacteristic_twistedSheaf_pushforward_of_isClosedImmersion ℂ _ Dv.subscheme X
      Dv.subschemeι f _ _ _ (d + 1) L _ hinvW
      (SheafOfModules.unit Dv.subscheme.ringCatSheaf) (Fin.cons 0 e)
      (@twistedSheaf_isCoherent X (d + 1) Sq.X₃ L _ cT3 _) cW0
  have hdrop : (@eulerCharacteristic ℂ _ Dv.subscheme (Dv.subschemeι ≫ f) _
        (twistedSheaf (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
          (fun t => (Scheme.Modules.pullback Dv.subschemeι).obj (L t)) (Fin.cons 0 e)) cW0 : ℤ) =
      @eulerCharacteristic ℂ _ Dv.subscheme (Dv.subschemeι ≫ f) _
        (twistedSheaf (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
          (fun t : Fin d => (Scheme.Modules.pullback Dv.subschemeι).obj (L t.succ)) e) cWf :=
    @eulerCharacteristic_eq_of_iso ℂ _ Dv.subscheme (Dv.subschemeι ≫ f) _ _ _ cW0 cWf
      (@twistedSheafConsZeroIso Dv.subscheme d (SheafOfModules.unit Dv.subscheme.ringCatSheaf)
        (fun t => (Scheme.Modules.pullback Dv.subschemeι).obj (L t)) hinvW e)
  have hmid : (@eulerCharacteristic ℂ _ X f _ (twistedSheaf Sq.X₂ L (Fin.cons 0 e))
        (@twistedSheaf_isCoherent X (d + 1) Sq.X₂ L _ cOX _) : ℤ) =
      @eulerCharacteristic ℂ _ X f _
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) L (Fin.cons 0 e))
        (@twistedSheaf_isCoherent X (d + 1) _ L _
          (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit ℂ f) _) := rfl
  rw [hmid, hfirst, hthird, hdrop] at hadd
  rw [hadd]
  ring

/-- **The Hilbert function of an effective Cartier divisor.** If `𝒪_X(B) ≅ 𝒪_X(D)` for an
effective Cartier divisor `D`, then `χ(D, 𝒪_X(A)^{⊗ t}|_D) = χ(𝒪_X(t A)) - χ(𝒪_X(t A - B))`. -/
private theorem subschemeHilbertFunction_eq_chi_sub [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {B A : MMP.Mori.Divisor X} (hB : B.IsCartier) (hA : A.IsCartier)
    (Dv : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor Dv]
    (eB : B.divisorialSheaf ≅ (Stacks.Divisors.invertibleSheaf Dv : X.Modules)) (t : ℤ) :
    haveI := hA.isInvertibleModule_divisorialSheaf
    MMP.Mori.subschemeHilbertFunction ℂ f Dv.subschemeι A.divisorialSheaf t =
      chi f (t • A) (hA.zsmul t) - chi f (-B + t • A) (hB.neg.add (hA.zsmul t)) := by
  haveI := isInvertible_pairFamily hB hA
  haveI := hA.isInvertibleModule_divisorialSheaf
  have key := eulerCharacteristic_twistedSheaf_sub_eq f (d := 1) B.divisorialSheaf
    (fun _ => A.divisorialSheaf) Dv eB fun _ => t
  obtain ⟨e₀⟩ := nonempty_twistedSheaf_pairFamily_iso hB hA 0 t
  obtain ⟨e₁⟩ := nonempty_twistedSheaf_pairFamily_iso hB hA (-1) t
  rw [eulerCharacteristic_eq_chi f ((hB.zsmul 0).add (hA.zsmul t)) _ e₀,
    eulerCharacteristic_eq_chi f ((hB.zsmul (-1)).add (hA.zsmul t)) _ e₁] at key
  rw [chi_congr f (show (0 : ℤ) • B + t • A = t • A by simp) _ (hA.zsmul t),
    chi_congr f (show (-1 : ℤ) • B + t • A = -B + t • A by simp) _
      (hB.neg.add (hA.zsmul t))] at key
  rw [key]
  rfl

end Twists

/-! ### A smooth projective surface -/

section Surface

variable {S : Scheme.{0}} [S.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (S ↘ Spec (.of ℂ))]
  [Smooth (S ↘ Spec (.of ℂ))] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]

private theorem isSmoothScheme_over : MMP.Mori.IsSmoothScheme (S ↘ Spec (.of ℂ)) :=
  (MMP.Mori.isSmoothScheme_iff _).2 inferInstance

private theorem isCartier_of_surface (D : MMP.Mori.Divisor S) : D.IsCartier :=
  MMP.Threefold.Resolution.isCartier_of_isSmoothScheme isSmoothScheme_over D

/-- **Riemann–Roch on the surface**, `2 χ(𝒪_S(D)) = (D · D) - (D · K) + 2 χ(𝒪_S)`. -/
private theorem exists_two_mul_chi (hS : topologicalKrullDim S = 2)
    (hd : topologicalKrullDim S ≤ (2 : ℕ)) {K : MMP.Mori.Divisor S}
    (hK : K.IsCanonicalDivisor (S ↘ Spec (.of ℂ)) 2) :
    ∃ c : ℤ, ∀ D : MMP.Mori.Divisor S,
      2 * chi (S ↘ Spec (.of ℂ)) D (isCartier_of_surface D) =
        ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface D D -
          ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface D K + c := by
  haveI : (SheafOfModules.unit S.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent S
  refine ⟨2 * eulerCharacteristic ℂ (S ↘ Spec (.of ℂ)) (SheafOfModules.unit S.ringCatSheaf),
    fun D => ?_⟩
  exact MMP.Mori.Divisor.two_mul_eulerCharacteristic_divisorialSheaf_eq ℂ (S ↘ Spec (.of ℂ))
    inferInstance hS K hK D

/-- **Numerically trivial divisors do not change `χ`.** If `(E · D₀) = 0` for every `E`, then
`χ(𝒪_S(E + n D₀)) = χ(𝒪_S(E))`. -/
private theorem chi_add_zsmul (hS : topologicalKrullDim S = 2)
    (hd : topologicalKrullDim S ≤ (2 : ℕ)) {K : MMP.Mori.Divisor S}
    (hK : K.IsCanonicalDivisor (S ↘ Spec (.of ℂ)) 2) {D₀ : MMP.Mori.Divisor S}
    (h₀ : ∀ E, ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface E D₀ = 0) (E : MMP.Mori.Divisor S)
    (n : ℤ) :
    chi (S ↘ Spec (.of ℂ)) (E + n • D₀) (isCartier_of_surface _) =
      chi (S ↘ Spec (.of ℂ)) E (isCartier_of_surface E) := by
  obtain ⟨c, hc⟩ := exists_two_mul_chi hS hd hK
  have h₀' : ∀ E, ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface D₀ E = 0 := fun E => by
    rw [ip_comm, h₀]
  have h1 := hc (E + n • D₀)
  have h2 := hc E
  simp only [ip_add_left, ip_add_right, ip_zsmul_left, ip_zsmul_right, h₀, h₀', mul_zero,
    add_zero, zero_add] at h1
  omega

/-- **The Hilbert polynomial of a divisor in `|H|`**: `χ(𝒪_S(t A)) - χ(𝒪_S(t A - H))` is an
affine function of `t`, by Riemann–Roch. -/
private theorem chi_sub_chi_eq (hS : topologicalKrullDim S = 2)
    (hd : topologicalKrullDim S ≤ (2 : ℕ)) {K : MMP.Mori.Divisor S}
    (hK : K.IsCanonicalDivisor (S ↘ Spec (.of ℂ)) 2) (A H : MMP.Mori.Divisor S) (t : ℤ) :
    chi (S ↘ Spec (.of ℂ)) (t • A) (isCartier_of_surface _) -
        chi (S ↘ Spec (.of ℂ)) (-H + t • A) (isCartier_of_surface _) =
      t * ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface A H +
        (chi (S ↘ Spec (.of ℂ)) ((0 : ℤ) • A) (isCartier_of_surface _) -
          chi (S ↘ Spec (.of ℂ)) (-H + (0 : ℤ) • A) (isCartier_of_surface _)) := by
  obtain ⟨c, hc⟩ := exists_two_mul_chi hS hd hK
  have h1 := hc (t • A)
  have h2 := hc (-H + t • A)
  have h3 := hc ((0 : ℤ) • A)
  have h4 := hc (-H + (0 : ℤ) • A)
  have hcomm := ip_comm (S ↘ Spec (.of ℂ)) hd isCartier_of_surface H A
  simp only [ip_add_left, ip_add_right, ip_zsmul_left, ip_zsmul_right, ip_neg_left,
    ip_neg_right] at h1 h2 h3 h4
  rw [hcomm] at h2 h4
  have key : 2 * (chi (S ↘ Spec (.of ℂ)) (t • A) (isCartier_of_surface _) -
        chi (S ↘ Spec (.of ℂ)) (-H + t • A) (isCartier_of_surface _)) =
      2 * (t * ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface A H +
        (chi (S ↘ Spec (.of ℂ)) ((0 : ℤ) • A) (isCartier_of_surface _) -
          chi (S ↘ Spec (.of ℂ)) (-H + (0 : ℤ) • A) (isCartier_of_surface _))) := by
    linear_combination h1 - h2 - h3 + h4
  linarith

variable (hd : topologicalKrullDim S ≤ (2 : ℕ))

/-- An ample divisor has positive degree on every curve, [Stacks, Tag 0BEV]. -/
private theorem degreeOn_pos_of_isAmple {G : MMP.Mori.Divisor S} (hGc : G.IsCartier)
    (hG : G.IsAmple hGc) (C : Scheme.{0}) (i : C ⟶ S) [IsClosedImmersion i]
    [IsProper (i ≫ (S ↘ Spec (.of ℂ)))] (hC : topologicalKrullDim C = 1) :
    0 < G.degreeOn ℂ (S ↘ Spec (.of ℂ)) i hC.le hGc := by
  haveI := hGc.isInvertibleModule_divisorialSheaf
  have hC' : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by rw [hC]; rfl
  have h := AlgebraicGeometry.intersectionNumber_pos ℂ (S ↘ Spec (.of ℂ)) i 1 hC'
    (fun _ => G.divisorialSheaf)
    (fun _ => Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _ hG)
  have e := AlgebraicGeometry.intersectionNumber_one_eq_invertibleCurveDegree ℂ
    (S ↘ Spec (.of ℂ)) i hC.le G.divisorialSheaf
  unfold MMP.Mori.Divisor.degreeOn
  rw [MMP.Mori.degreeOn_eq_invertibleCurveDegree, ← e]
  exact h

/-- **Adding a divisor of nonnegative degrees to an ample divisor**, by the numerical criterion
of ampleness. -/
private theorem isAmple_add_of_degreeOn_nonneg {A N : MMP.Mori.Divisor S} (hAc : A.IsCartier)
    (hA : A.IsAmple hAc) (hNc : N.IsCartier)
    (hN : ∀ (C : Scheme.{0}) (i : C ⟶ S) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ (S ↘ Spec (.of ℂ)))] (hC : topologicalKrullDim C = 1),
      0 ≤ N.degreeOn ℂ (S ↘ Spec (.of ℂ)) i hC.le hNc) :
    (A + N).IsAmple (hAc.add hNc) := by
  have hAq : (MMP.Mori.Divisor.toQDivisor A).IsAmple := ⟨1, one_pos, A, by simp, hAc, hA⟩
  have hNnef : (MMP.Mori.Divisor.toQDivisor N).IsNef ℂ (S ↘ Spec (.of ℂ)) := by
    refine ⟨MMP.Mori.QDivisor.isQCartier_toQDivisor hNc, fun C i _ _ _ hC => ?_⟩
    rw [MMP.Mori.QDivisor.intersectionNumber_toQDivisor ℂ _ i hC.le N hNc]
    exact_mod_cast hN C i hC
  have hB : (MMP.Mori.Divisor.toQDivisor (A + N)).NumericallyEquivalent ℂ (S ↘ Spec (.of ℂ))
      (MMP.Mori.Divisor.toQDivisor A + MMP.Mori.Divisor.toQDivisor N) := by
    rw [← map_add]
    exact ⟨MMP.Mori.QDivisor.isQCartier_toQDivisor (hAc.add hNc),
      MMP.Mori.QDivisor.isQCartier_toQDivisor (hAc.add hNc), fun _ _ _ _ _ _ => rfl⟩
  exact MMP.Mori.QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef
    (S ↘ Spec (.of ℂ)) hAq hNnef hB 1 one_pos (A + N) (by rw [Nat.cast_one, one_smul])
    (hAc.add hNc)

/-- **Numerically trivial divisors pair to zero.** If `𝒪_S(D₀)` has degree zero along every prime
divisor, then `(E · D₀) = 0` for every divisor `E`. -/
private theorem ip_eq_zero_of_degreeOn_eq_zero {D₀ : MMP.Mori.Divisor S}
    (h : ∀ (P : MMP.Mori.PrimeDivisor S) (hP : topologicalKrullDim P.idealSheaf.subscheme ≤ 1),
      haveI := (isCartier_of_surface D₀).isInvertibleModule_divisorialSheaf
      MMP.Mori.degreeOn ℂ (S ↘ Spec (.of ℂ)) P.idealSheaf.subschemeι hP D₀.divisorialSheaf = 0)
    (E : MMP.Mori.Divisor S) : ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface E D₀ = 0 := by
  induction E using Finsupp.induction_linear with
  | zero => exact map_zero (ipLeft (S ↘ Spec (.of ℂ)) hd isCartier_of_surface D₀)
  | add E E' h₁ h₂ => rw [ip_add_left, h₁, h₂, add_zero]
  | single P n =>
    haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme
      isSmoothScheme_over P
    have hP : topologicalKrullDim P.idealSheaf.subscheme ≤ 1 := by
      have := topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper ℂ
        (S ↘ Spec (.of ℂ)) (𝟙 S) 1 hd P.idealSheaf
      exact_mod_cast this
    rw [← Finsupp.smul_single_one, ip_zsmul_left,
      ip_single_left _ hd _ isSmoothScheme_over P hP, h P hP, mul_zero]

/-- **An ample and very ample divisor.** The pull-back of `𝒪(1)` along a projective embedding is
`𝒪_S(G)` for an ample divisor `G`. -/
private theorem exists_isAmple_isVeryAmple :
    ∃ (G : MMP.Mori.Divisor S) (hG : G.IsAmple (isCartier_of_surface G)),
      MMP.Intersection.IsVeryAmple ℂ G.divisorialSheaf := by
  obtain ⟨n, i, hi, hover⟩ :=
    (IsProjectiveVariety.isProjective : IsProjectiveMorphism (S ↘ Spec (.of ℂ)))
  haveI := hi
  let A₀ := (Scheme.Modules.pullback i).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of ℂ)))
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A₀ := inferInstance
  obtain ⟨G, ⟨eG⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible A₀
  haveI := (isCartier_of_surface G).isInvertibleModule_divisorialSheaf
  refine ⟨G, ?_, MMP.Resolution.Bridges.isVeryAmple_of_isClosedImmersion ℂ _ A₀ eG n i hover
    (Iso.refl _)⟩
  have htfae := Stacks.AmpleRelativeFiniteType.tfae_six (S ↘ Spec (.of ℂ)) G.divisorialSheaf
  have h5 : ∃ d : ℕ, 1 ≤ d ∧ Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver
      (S ↘ Spec (.of ℂ)) (Stacks.Ample.tensorPowModule S G.divisorialSheaf (d : ℤ)) :=
    ⟨1, le_rfl, n, i, inferInstance, hover, ⟨Stacks.Ample.tensorPowModuleOneIso _ _ ≪≫ eG⟩⟩
  exact (htfae.out 5 1).1 h5

/-- **The self-intersection of an ample divisor is positive**, [Stacks, Tag 0BEV]. -/
private theorem ip_self_pos_of_isAmple (hS : topologicalKrullDim S = 2) {G : MMP.Mori.Divisor S}
    (hG : G.IsAmple (isCartier_of_surface G)) :
    0 < ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface G G := by
  haveI := (isCartier_of_surface G).isInvertibleModule_divisorialSheaf
  haveI := isInvertible_pair G.divisorialSheaf G.divisorialSheaf
  have hS' : topologicalKrullDim S = ((2 : ℕ) : WithBot ℕ∞) := by rw [hS]; rfl
  rw [ip_eq]
  exact AlgebraicGeometry.intersectionNumber_pos ℂ (S ↘ Spec (.of ℂ)) (𝟙 S) 2 hS' _ fun j => by
    fin_cases j <;> exact Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _ hG

/-- Positive multiples of an ample divisor are ample. -/
private theorem isAmple_nsmul {G : MMP.Mori.Divisor S} (hG : G.IsAmple (isCartier_of_surface G))
    (m : ℕ) : ((m + 1 : ℕ) • G).IsAmple (isCartier_of_surface _) := by
  have h := isAmple_add_of_degreeOn_nonneg (isCartier_of_surface G) hG
    (isCartier_of_surface (m • G)) fun C i _ _ _ hC => by
      rw [MMP.Mori.Divisor.degreeOn_nsmul' ℂ _ i hC.le G (isCartier_of_surface G)]
      exact mul_nonneg (by positivity) (degreeOn_pos_of_isAmple _ hG C i hC).le
  rw [show (m + 1 : ℕ) • G = G + m • G by rw [add_smul, one_smul, add_comm]]
  exact h

end Surface

/-! ### Euler characteristics and global sections -/

section Sections

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [IsProper f]

/-- If the higher cohomology of a coherent module vanishes, `χ = h⁰`. -/
private theorem eulerCharacteristic_eq_finrank_zero (F : X.Modules) [F.IsCoherent]
    (h : ∀ i : ℤ, 0 < i → Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) i)) :
    eulerCharacteristic ℂ f F = Module.finrank ℂ (cohomologyOverField ℂ f F 0) := by
  rw [eulerCharacteristic_eq_finsum, finsum_eq_single _ 0]
  · simp
  · intro n hn
    have : Subsingleton (cohomologyOverField ℂ f F n) :=
      (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField ℂ f F
        n).toEquiv.subsingleton_congr.mpr (h n (by omega))
    simp [Module.finrank_zero_of_subsingleton]

/-- **A nonzero section gives an effective Cartier divisor.** On an integral scheme proper over
`ℂ`, an invertible module `M` with `h⁰(M) ≠ 0` is `𝒪_X(Z)` for an effective Cartier divisor
`Z`, the zero scheme of a nonzero section. -/
private theorem exists_isEffectiveCartierDivisor_iso [IsIntegral X] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (h : Module.finrank ℂ (cohomologyOverField ℂ f M 0) ≠ 0) :
    ∃ (Z : X.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor Z),
      Nonempty (M ≅ (Stacks.Divisors.invertibleSheaf' Z : X.Modules)) := by
  have e := cohomologyOverFieldZeroLinearEquivGlobalSectionsOver f M
  have : Nontrivial ((globalSectionsOver f).obj M) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (e.finrank_eq ▸ Nat.pos_of_ne_zero h)
  obtain ⟨σ, hσ⟩ := exists_ne (0 : (globalSectionsOver f).obj M)
  let t := Stacks.Divisors.sectionsOfTop M σ
  have ht : t.eval (Opposite.op ⊤) ≠ 0 :=
    ne_of_eq_of_ne (Stacks.Divisors.sectionsOfTop_eval_top M σ) hσ
  exact ⟨_, isEffectiveCartierDivisor_zeroScheme_of_ne_zero M _ ht,
    ⟨invertibleSheafIsoZeroSchemeOfIsRegularSection M t
      (isRegularSection_of_eval_top_ne_zero M t ht)⟩⟩

end Sections

/-- **Additivity of `c₁` along multiples of a divisor**:
`c₁(𝒪(E + n D)) = c₁(𝒪(E)) + n c₁(𝒪(D))`. -/
private theorem algebraicFirstChernClass_add_nsmul {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hC : ∀ D : MMP.Mori.Divisor X, D.IsCartier) (E D : MMP.Mori.Divisor X) (n : ℕ) :
    haveI := fun D : MMP.Mori.Divisor X => (hC D).isInvertibleModule_divisorialSheaf
    algebraicFirstChernClass (E + n • D).divisorialSheaf =
      algebraicFirstChernClass E.divisorialSheaf +
        n • algebraicFirstChernClass D.divisorialSheaf := by
  haveI := fun D : MMP.Mori.Divisor X => (hC D).isInvertibleModule_divisorialSheaf
  induction n with
  | zero => simp
  | succ n ih =>
    haveI := (hC (E + n • D)).isInvertibleModule_tensorSheaf (hC D)
    have e := (hC (E + n • D)).divisorialSheafTensorIso (hC D)
    rw [show E + (n + 1) • D = E + n • D + D by rw [add_smul, one_smul, add_assoc],
      ← algebraicFirstChernClass_eq_of_iso e, algebraicFirstChernClass_sheafTensor, ih,
      add_smul, one_smul, add_assoc]

/-- The quadratic `M b + M² g + c` is positive for `g > 0` and `M = |b| + |c| + 1`. -/
private theorem two_mul_pos_aux {b c g : ℤ} {M : ℕ} (hg : 0 < g)
    (hM : (M : ℤ) = |b| + |c| + 1) : 0 < (M : ℤ) * b + (M : ℤ) * ((M : ℤ) * g) + c := by
  have hM0 : (1 : ℤ) ≤ M := by rw [hM]; linarith [abs_nonneg b, abs_nonneg c]
  have h1 : (M : ℤ) * M ≤ (M : ℤ) * ((M : ℤ) * g) := by nlinarith
  have h2 : -((M : ℤ) * |b|) ≤ (M : ℤ) * b := by nlinarith [neg_abs_le b]
  nlinarith [neg_abs_le c, abs_nonneg b, abs_nonneg c]

/-! ### The divisors `D_n` -/

section Sequence

variable {S : Scheme.{0}} [S.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (S ↘ Spec (.of ℂ))]
  [Smooth (S ↘ Spec (.of ℂ))] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]

/-- A divisor of degree zero on every curve pairs to zero with every divisor. -/
private theorem ip_eq_zero_of_forall_degreeOn_eq_zero (hd : topologicalKrullDim S ≤ (2 : ℕ))
    {D₀ : MMP.Mori.Divisor S}
    (hdeg₀ : ∀ (C : Scheme.{0}) (i : C ⟶ S) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ (S ↘ Spec (.of ℂ)))] (hC : topologicalKrullDim C ≤ 1),
      haveI := (isCartier_of_surface D₀).isInvertibleModule_divisorialSheaf
      MMP.Mori.degreeOn ℂ (S ↘ Spec (.of ℂ)) i hC D₀.divisorialSheaf = 0)
    (E : MMP.Mori.Divisor S) : ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface E D₀ = 0 := by
  refine ip_eq_zero_of_degreeOn_eq_zero hd (fun P hP => ?_) E
  haveI : IsIntegral P.idealSheaf.subscheme := by
    rw [← MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf]
    exact MMP.Fourfold.isIntegral_subscheme_vanishingIdeal _ isIrreducible_singleton.closure
  exact hdeg₀ _ _ hP

/-- **`χ(𝒪_S(K + M G)) > 0`** for an ample `G` and `M = |(G · K)| + |c| + 1`, by Riemann–Roch. -/
private theorem chi_pos_of_eq_add_zsmul (hS : topologicalKrullDim S = 2)
    (hd : topologicalKrullDim S ≤ (2 : ℕ)) {K G H : MMP.Mori.Divisor S}
    (hG : G.IsAmple (isCartier_of_surface G)) {b c : ℤ} {M : ℕ}
    (hc : ∀ D : MMP.Mori.Divisor S,
      2 * chi (S ↘ Spec (.of ℂ)) D (isCartier_of_surface D) =
        ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface D D -
          ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface D K + c)
    (hb : ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface G K = b) (hM : (M : ℤ) = |b| + |c| + 1)
    (hHdef : H = K + (M : ℤ) • G) :
    0 < chi (S ↘ Spec (.of ℂ)) H (isCartier_of_surface H) := by
  have h := hc H
  have e₁ : ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface H H =
      ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface K K +
        M * ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface K G +
        M * ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface G K +
        M * (M * ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface G G) := by
    rw [hHdef, ip_add_left, ip_add_right, ip_add_right, ip_zsmul_left, ip_zsmul_left,
      ip_zsmul_right, ip_zsmul_right]
    ring
  have e₂ : ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface H K =
      ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface K K +
        M * ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface G K := by
    rw [hHdef, ip_add_left, ip_zsmul_left]
  rw [e₁, e₂, ip_comm _ _ _ K G, hb] at h
  have := two_mul_pos_aux (ip_self_pos_of_isAmple hd hS hG) hM
  linarith

/-- **`M G + n D₀` is ample** for an ample `G`, `M ≥ 1` and `D₀` of degree zero on every curve. -/
private theorem isAmple_zsmul_add_zsmul {G D₀ : MMP.Mori.Divisor S}
    (hG : G.IsAmple (isCartier_of_surface G)) {M : ℕ} (hM1 : 1 ≤ M)
    (hdeg₀ : ∀ (C : Scheme.{0}) (i : C ⟶ S) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ (S ↘ Spec (.of ℂ)))] (hC : topologicalKrullDim C ≤ 1),
      haveI := (isCartier_of_surface D₀).isInvertibleModule_divisorialSheaf
      MMP.Mori.degreeOn ℂ (S ↘ Spec (.of ℂ)) i hC D₀.divisorialSheaf = 0) (n : ℕ) :
    ((M : ℤ) • G + (n : ℤ) • D₀).IsAmple (isCartier_of_surface _) := by
  have hMG : ((M : ℤ) • G).IsAmple (isCartier_of_surface _) := by
    have := isAmple_nsmul hG (M - 1)
    have he : ((M - 1 + 1 : ℕ) • G) = (M : ℤ) • G := by
      rw [Nat.sub_add_cancel hM1, natCast_zsmul]
    rw [← he]
    exact this
  exact isAmple_add_of_degreeOn_nonneg (isCartier_of_surface _) hMG
    (isCartier_of_surface ((n : ℤ) • D₀)) fun C i _ _ _ hC => by
      rw [MMP.Mori.Divisor.degreeOn_congr (show ((n : ℤ) • D₀) = n • D₀ by
          rw [natCast_zsmul]) _ ((isCartier_of_surface D₀).nsmul n),
        MMP.Mori.Divisor.degreeOn_nsmul' ℂ _ i hC.le D₀ (isCartier_of_surface D₀)]
      have := hdeg₀ C i hC.le
      unfold MMP.Mori.Divisor.degreeOn
      rw [this, mul_zero]

/-- **A divisor `B` with `B - K` ample and `χ(𝒪_S(B)) > 0` is linearly equivalent to an
effective Cartier divisor**, by Kodaira vanishing. -/
private theorem exists_isEffectiveCartierDivisor_of_isAmple_sub {K : MMP.Mori.Divisor S}
    (hK : K.IsCanonicalDivisor (S ↘ Spec (.of ℂ)) 2) (B : MMP.Mori.Divisor S)
    (hB : ∃ h : (B - K).IsCartier, (B - K).IsAmple h)
    (hχB : 0 < chi (S ↘ Spec (.of ℂ)) B (isCartier_of_surface B)) :
    ∃ (Z : S.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor Z),
      Nonempty (B.divisorialSheaf ≅ (Stacks.Divisors.invertibleSheaf' Z : S.Modules)) := by
  haveI := (isCartier_of_surface B).isInvertibleModule_divisorialSheaf
  haveI : B.divisorialSheaf.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible S _
  have hχ := eulerCharacteristic_eq_finrank_zero (S ↘ Spec (.of ℂ)) B.divisorialSheaf
    fun i hi => MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_of_isAmple_sub
      (S ↘ Spec (.of ℂ)) isSmoothScheme_over K B hK hB i hi
  have hχ' : chi (S ↘ Spec (.of ℂ)) B (isCartier_of_surface _) =
      Module.finrank ℂ (cohomologyOverField ℂ (S ↘ Spec (.of ℂ)) B.divisorialSheaf 0) := hχ
  exact exists_isEffectiveCartierDivisor_iso (S ↘ Spec (.of ℂ)) _ (by omega)

/-- **The Hilbert polynomial of `D_n`** with respect to `𝒪_S(G)` is the affine function
`t ↦ t (G · H) + χ(𝒪_S) - χ(𝒪_S(-H))`. -/
private theorem subschemeHilbertFunction_eq_of_iso (hS : topologicalKrullDim S = 2)
    (hd : topologicalKrullDim S ≤ (2 : ℕ)) {K : MMP.Mori.Divisor S}
    (hK : K.IsCanonicalDivisor (S ↘ Spec (.of ℂ)) 2) {D₀ : MMP.Mori.Divisor S}
    (h₀ : ∀ E, ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface E D₀ = 0)
    (G H : MMP.Mori.Divisor S) (n : ℕ) (Z : S.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor Z]
    (e : (H + (n : ℤ) • D₀).divisorialSheaf ≅ (Stacks.Divisors.invertibleSheaf' Z : S.Modules))
    (t : ℤ) :
    haveI := (isCartier_of_surface G).isInvertibleModule_divisorialSheaf
    MMP.Mori.subschemeHilbertFunction ℂ (S ↘ Spec (.of ℂ)) Z.subschemeι G.divisorialSheaf t =
      t * ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface G H +
        (chi (S ↘ Spec (.of ℂ)) ((0 : ℤ) • G) (isCartier_of_surface _) -
          chi (S ↘ Spec (.of ℂ)) (-H + (0 : ℤ) • G) (isCartier_of_surface _)) := by
  rw [subschemeHilbertFunction_eq_chi_sub (S ↘ Spec (.of ℂ)) (isCartier_of_surface _)
    (isCartier_of_surface G) Z e t,
    chi_congr (S ↘ Spec (.of ℂ)) (show -(H + (n : ℤ) • D₀) + t • G =
      (-H + t • G) + (-(n : ℤ)) • D₀ by rw [neg_smul]; abel) _ (isCartier_of_surface _),
    chi_add_zsmul hS hd hK h₀, chi_sub_chi_eq hS hd hK G H t]

end Sequence

/-- **The divisors `D_n ∈ |H + nD|`.** On a smooth projective complex surface `S` with a
numerically trivial invertible sheaf `L`, there are a very ample invertible sheaf `A`, a class
`x ∈ H²(S^an; ℤ)`, effective Cartier divisors `Z_n` (`n ∈ ℕ`) with
`c₁(𝒪_S(Z_n)) = x + n c₁(L)`, and an integer-valued polynomial `P` which is the Hilbert
polynomial of every `Z_n` with respect to `A`. -/
private theorem exists_isEffectiveCartierDivisor_sequence {S : Scheme.{0}}
    [S.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (S ↘ Spec (.of ℂ))]
    [Smooth (S ↘ Spec (.of ℂ))] (hS : topologicalKrullDim S = 2) (L : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L]
    (hL : ∀ (C : Scheme.{0}) (i : C ⟶ S) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ (S ↘ Spec (.of ℂ)))] (hC : topologicalKrullDim C ≤ 1),
      MMP.Mori.degreeOn ℂ (S ↘ Spec (.of ℂ)) i hC L = 0) :
    ∃ (A : S.Modules) (_ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A)
      (_ : MMP.Intersection.IsVeryAmple ℂ A)
      (x : analyticSingularCohomology ℤ (S ↘ Spec (.of ℂ)) 2) (Z : ℕ → S.IdealSheafData)
      (hZ : ∀ n, Stacks.Divisors.IsEffectiveCartierDivisor (Z n)) (P : Polynomial ℚ),
      (∀ t : ℤ, ∃ m : ℤ, P.eval (t : ℚ) = m) ∧
      (∀ (n : ℕ) (t : ℤ), P.eval (t : ℚ) =
        MMP.Mori.subschemeHilbertFunction ℂ (S ↘ Spec (.of ℂ)) (Z n).subschemeι A t) ∧
      ∀ n : ℕ, haveI := hZ n
        algebraicFirstChernClass (Stacks.Divisors.invertibleSheaf' (Z n) : S.Modules) =
          x + (n : ℤ) • algebraicFirstChernClass L := by
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of ℂ))
  haveI : IsNormal S :=
    { stalk_isDomain := fun x =>
        have := isRegularLocalRing_stalk_of_smooth_over_field (S ↘ Spec (.of ℂ)) x
        (isNormalDomain_of_isRegularLocalRing _).1
      stalk_normal := fun x =>
        have := isRegularLocalRing_stalk_of_smooth_over_field (S ↘ Spec (.of ℂ)) x
        (isNormalDomain_of_isRegularLocalRing _).2 }
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of ℂ))
  have hd : topologicalKrullDim S ≤ (2 : ℕ) := by rw [hS]; rfl
  haveI := fun D : MMP.Mori.Divisor S =>
    (isCartier_of_surface D).isInvertibleModule_divisorialSheaf
  obtain ⟨D₀, ⟨e₀⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible L
  have hdeg₀ : ∀ (C : Scheme.{0}) (i : C ⟶ S) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ (S ↘ Spec (.of ℂ)))] (hC : topologicalKrullDim C ≤ 1),
      MMP.Mori.degreeOn ℂ (S ↘ Spec (.of ℂ)) i hC D₀.divisorialSheaf = 0 := by
    intro C i _ _ _ hC
    rw [MMP.Mori.degreeOn_eq_of_iso ℂ _ i hC e₀]
    exact hL C i hC
  have h₀ := ip_eq_zero_of_forall_degreeOn_eq_zero hd hdeg₀
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (S ↘ Spec (.of ℂ))
    isSmoothScheme_over (n := 2) (by rw [hS]; rfl)
  obtain ⟨G, hG, hGva⟩ := exists_isAmple_isVeryAmple (S := S)
  obtain ⟨c, hc⟩ := exists_two_mul_chi hS hd hK
  obtain ⟨b, hb⟩ : ∃ b : ℤ, ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface G K = b := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = |b| + |c| + 1 :=
    ⟨(|b| + |c| + 1).toNat, Int.toNat_of_nonneg (by positivity)⟩
  obtain ⟨H, hHdef⟩ : ∃ H : MMP.Mori.Divisor S, H = K + (M : ℤ) • G := ⟨_, rfl⟩
  have hχH := chi_pos_of_eq_add_zsmul hS hd hG hc hb hM hHdef
  have hM1 : 1 ≤ M := by
    have : (1 : ℤ) ≤ M := by linarith [abs_nonneg b, abs_nonneg c]
    exact_mod_cast this
  have hBamp : ∀ n : ℕ, ∃ h : (H + (n : ℤ) • D₀ - K).IsCartier,
      (H + (n : ℤ) • D₀ - K).IsAmple h := fun n => by
    refine ⟨isCartier_of_surface _, ?_⟩
    have he : (M : ℤ) • G + (n : ℤ) • D₀ = H + (n : ℤ) • D₀ - K := by
      rw [hHdef]
      abel
    rw [← he]
    exact isAmple_zsmul_add_zsmul hG hM1 hdeg₀ n
  have hsec : ∀ n : ℕ, ∃ (Z : S.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor Z),
      Nonempty ((H + (n : ℤ) • D₀).divisorialSheaf ≅ (Stacks.Divisors.invertibleSheaf' Z :
        S.Modules)) := fun n =>
    exists_isEffectiveCartierDivisor_of_isAmple_sub hK _ (hBamp n)
      (by rwa [chi_add_zsmul hS hd hK h₀])
  choose Z hZ eZ using hsec
  set Q₀ : ℤ := chi (S ↘ Spec (.of ℂ)) ((0 : ℤ) • G) (isCartier_of_surface _) -
    chi (S ↘ Spec (.of ℂ)) (-H + (0 : ℤ) • G) (isCartier_of_surface _)
  set a : ℤ := ip (S ↘ Spec (.of ℂ)) hd isCartier_of_surface G H
  have hQ : ∀ (n : ℕ) (t : ℤ), haveI := hZ n
      MMP.Mori.subschemeHilbertFunction ℂ (S ↘ Spec (.of ℂ)) (Z n).subschemeι G.divisorialSheaf t =
        t * a + Q₀ := by
    intro n t
    haveI := hZ n
    obtain ⟨e⟩ := eZ n
    exact subschemeHilbertFunction_eq_of_iso hS hd hK h₀ G H n (Z n) e t
  refine ⟨G.divisorialSheaf, inferInstance, hGva,
    algebraicFirstChernClass H.divisorialSheaf, Z, hZ,
    Polynomial.C (a : ℚ) * Polynomial.X + Polynomial.C (Q₀ : ℚ), fun t => ⟨t * a + Q₀, ?_⟩,
    fun n t => ?_, fun n => ?_⟩
  · simp
    ring
  · rw [hQ n t]
    simp
    ring
  · haveI := hZ n
    obtain ⟨e⟩ := eZ n
    rw [← algebraicFirstChernClass_eq_of_iso e,
      show H + (n : ℤ) • D₀ = H + n • D₀ by rw [natCast_zsmul],
      algebraicFirstChernClass_add_nsmul isCartier_of_surface,
      algebraicFirstChernClass_eq_of_iso e₀,
      natCast_zsmul]

theorem solution {S : Scheme.{0}} [S.Over (Spec (.of ℂ))]
    [IsProjectiveVariety ℂ (S ↘ Spec (.of ℂ))] [Smooth (S ↘ Spec (.of ℂ))]
    (hS : topologicalKrullDim S = 2) (L : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L]
    (hL : ∀ (C : Scheme.{0}) (i : C ⟶ S) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ (S ↘ Spec (.of ℂ)))] (hC : topologicalKrullDim C ≤ 1),
      MMP.Mori.degreeOn ℂ (S ↘ Spec (.of ℂ)) i hC L = 0) :
    singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L) = 0 := by
  obtain ⟨A, hAi, hA, x, Z, hZ, P, hPint, hPZ, hc₁⟩ :=
    exists_isEffectiveCartierDivisor_sequence hS L hL
  have hproj : IsProjectiveMorphism (S ↘ Spec (.of ℂ)) := IsProjectiveVariety.isProjective
  obtain ⟨ι, hι, T, p, hlft, hqc, -, 𝒟, h𝒟, -, -, hcov⟩ :=
    MMP.exists_finite_isEffectiveCartierDivisor_families ℂ S hproj A hA P hPint
  choose i t ht hZt using fun n => hcov (Z n) (hZ n) (hPZ n)
  -- the `ℂ`-points `t n` of the parameter schemes, and an irreducible component through each
  let pt : ℕ → Σ j, ComplexPoints (p j) := fun n => ⟨i n, ⟨t n, ht n⟩⟩
  have hcomp : ∀ j (y : T j), ∃ C ∈ irreducibleComponents (T j), y ∈ C := fun j y =>
    exists_mem_irreducibleComponents_subset_of_isIrreducible {y} isIrreducible_singleton
      |>.imp fun C hC => ⟨hC.1, hC.2 rfl⟩
  choose comp hcompC hcompm using hcomp
  have hfin : ∀ j, Finite (irreducibleComponents (T j)) := fun j => by
    haveI := hlft j; haveI := hqc j
    haveI : IsLocallyNoetherian (T j) := LocallyOfFiniteType.isLocallyNoetherian (p j)
    haveI : CompactSpace (T j) := QuasiCompact.compactSpace_of_compactSpace (p j)
    haveI : IsNoetherian (T j) := ⟨⟩
    exact (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  let G : (Σ j, ComplexPoints (p j)) → Σ j, irreducibleComponents (T j) := fun y =>
    ⟨y.1, ⟨comp y.1 y.2.toScheme, hcompC _ _⟩⟩
  obtain ⟨n, m, hnm, hG⟩ := Finite.exists_ne_map_eq_of_infinite (G ∘ pt)
  have key : ∀ y y' : Σ j, ComplexPoints (p j), G y = G y' → ∀ (E E' : S.IdealSheafData)
      [Stacks.Divisors.IsEffectiveCartierDivisor E]
      [Stacks.Divisors.IsEffectiveCartierDivisor E'],
      (𝒟 y.1).comap (fibreι (p y.1) y.2) = E → (𝒟 y'.1).comap (fibreι (p y'.1) y'.2) = E' →
      algebraicFirstChernClass (Stacks.Divisors.invertibleSheaf' E : S.Modules) =
        algebraicFirstChernClass (Stacks.Divisors.invertibleSheaf' E' : S.Modules) := by
    rintro ⟨j, a⟩ ⟨j', b⟩ hGy E E' _ _ hE hE'
    obtain ⟨rfl, hcc⟩ := Sigma.mk.inj_iff.mp hGy
    have hcc' : comp j a.toScheme = comp j b.toScheme := congrArg Subtype.val (eq_of_heq hcc)
    haveI := h𝒟 j
    haveI := hlft j
    haveI := hqc j
    subst hE hE'
    exact algebraicFirstChernClass_comap_fibreι_eq (p j) (𝒟 j) (hcompC j a.toScheme)
      (hcompm j a.toScheme) (by rw [hcc']; exact hcompm j b.toScheme)
  have hnm' := key (pt n) (pt m) hG (Z n) (Z m) (hZt n) (hZt m)
  rw [hc₁ n, hc₁ m, add_right_inj, ← sub_eq_zero] at hnm'
  have hq := congrArg (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2) hnm'
  rw [map_sub, map_zsmul, map_zsmul, map_zero, ← sub_smul, ← Int.cast_smul_eq_zsmul ℚ] at hq
  refine (smul_eq_zero.mp hq).resolve_left fun h => hnm ?_
  simp only [Int.cast_sub, Int.cast_natCast, sub_eq_zero] at h
  exact_mod_cast h

end MMP.FourfoldProofs.MmpConductorSurfaceNumericChernZeroProof

open CategoryTheory AlgebraicGeometry

namespace MMP.Analytic

/-- **A numerically trivial line bundle on a smooth projective complex surface has rationally
zero first Chern class.** Let `S` be a smooth projective variety of dimension two over `ℂ` and
`L` an invertible `𝒪_S`-module with `MMP.Mori.degreeOn ℂ _ i hC L = 0` for every closed
immersion `i : C ⟶ S` of an integral scheme of dimension at most one. Then the image of
`algebraicFirstChernClass L` in `H²(S^an; ℚ)` is zero. -/
@[mmp "lem_mmp_conductor_surface_numeric_chern_zero"]
public theorem mapCoeff_algebraicFirstChernClass_eq_zero_of_degreeOn_eq_zero
    {S : Scheme.{0}} [S.Over (Spec (.of ℂ))]
    [IsProjectiveVariety ℂ (S ↘ Spec (.of ℂ))] [Smooth (S ↘ Spec (.of ℂ))]
    (hS : topologicalKrullDim S = 2) (L : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L]
    (hL : ∀ (C : Scheme.{0}) (i : C ⟶ S) [IsClosedImmersion i] [IsIntegral C]
      [IsProper (i ≫ (S ↘ Spec (.of ℂ)))] (hC : topologicalKrullDim C ≤ 1),
      MMP.Mori.degreeOn ℂ (S ↘ Spec (.of ℂ)) i hC L = 0) :
    singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L) = 0 :=
  MMP.FourfoldProofs.MmpConductorSurfaceNumericChernZeroProof.solution hS L hL

end MMP.Analytic

end
