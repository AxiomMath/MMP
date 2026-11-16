module
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai

/-!
# Prime divisors persist along a terminal chain

Let `(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, be a terminal chain over a stabilized small klt
tail `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` of fourfolds. For every model `(M, Θ^M)` of the chain,
the map `P ↦ c_M(ord_P)` sending a prime divisor `P` of `Y_0` to the centre on `M` of its
valuation is a bijection from the prime divisors of `Y_0` onto the prime divisors of `M`: a
coefficient decrease does not change the variety, and each flip of a bridge is a step diagram
with both maps small, so strict transform identifies the prime divisors on either side.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.primeDivisorEquivModel`: for every model `M`
  of a terminal chain, the centre map `P ↦ c_M(ord_P)` as an equivalence from the prime divisors
  of `Y_0` onto those of `M`.
* `TerminalChain.isPrimeDivisorCentre_iff_primeDivisorEquivModel_eq`
  says that `Q` is the centre of `ord_P` on `M` if and only if `Q = primeDivisorEquivModel C x P`.

## Implementation notes

* The centre `c_M(ord_P)` is recorded, as in
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCentre`, by the condition that a prime
  divisor `Q` of `M` has `ord_Q = ord_P` under the identification of function fields. The
  valuation `ord_P` of `k(Y_0)` is regarded as a valuation of `k(X_0)` through `p_0` and carried
  to `k(X_i)` by `MMP.Fourfold.StepSequence.Corresponds`. For the junction `M = Y_i`, `ord_Q` is
  compared in `k(X_i)` through `p_i`; for the model `M = V_k` of the `i`-th bridge, in `k(Z_i)`
  through the morphism `π_k : V_k ⟶ Z_i` of the programme of the bridge.
* The statement says that this relation
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsPrimeDivisorCentre`) is the graph of the
  equivalence `primeDivisorEquivModel`: `Q` is the centre of `ord_P` on `M` if and only if
  `Q = primeDivisorEquivModel C x P`. In particular the centre of every `ord_P` on `M` is a
  prime divisor, and it determines `P`.
* The proof shows that every `P` has exactly one centre on `M` and that every `Q` is the centre
  of exactly one `P`. Uniqueness is formal: on a normal integral scheme separated over a field a
  prime divisor is determined by its valuation (`MMP.Flips.eq_of_isLocal_le_valuationSubring`),
  the correspondence of valuations along the step sequence is functional both ways because
  `f_i` and `f_i⁺` are birational, and every `π_k` induces a surjection of function fields.
  Existence goes by induction along the chain: a small morphism sends the generic point of a
  prime divisor to a point of coheight one, every prime divisor of its target is the image of its
  strict transform (`MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply`), and a
  dominant morphism surjective on function fields matching generic points of prime divisors
  matches their valuations, both being normalized and centred on the same discrete valuation
  ring.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StabilizedSmallKltTail.TerminalChain

/-- An element `x` with `v x < 1` lies in the maximal ideal of the valuation subring of `v`. -/
private theorem mem_nonunits_valuationSubring {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {x : K} (h : v x < 1) :
    x ∈ v.valuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]
  have := Valuation.isEquiv_valuation_valuationSubring v 1 x
  simp only [map_one] at this
  exact lt_of_not_ge fun h' => (not_le.2 h) (this.2 h')

/-- On a normal integral scheme separated over a field, a prime divisor is determined by its
divisorial valuation: its generic point is the unique centre of that valuation. -/
private theorem divisorialValuation_injective {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k))
    [IsSeparated sY] :
    Function.Injective (fun P : MMP.Mori.PrimeDivisor Y => P.divisorialValuation) := by
  intro P P' h
  simp only at h
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  refine MMP.Flips.eq_of_isLocal_le_valuationSubring sY P.divisorialValuation.valuationSubring
    (fun a => (P.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩)
    (fun a ha => mem_nonunits_valuationSubring _
      ((P.divisorialValuation_algebraMap_lt_one_iff a).2 ha)) (fun a => ?_) (fun a ha => ?_)
  · rw [Valuation.mem_valuationSubring_iff, h]
    exact (P'.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩
  · rw [h]
    exact mem_nonunits_valuationSubring _ ((P'.divisorialValuation_algebraMap_lt_one_iff a).2 ha)

/-- Restriction of valuations along a surjective ring map is injective. -/
private theorem comap_injective_of_surjective {A B Γ : Type*} [Ring A] [Ring B]
    [LinearOrderedCommMonoidWithZero Γ] {φ : A →+* B} (hφ : Function.Surjective φ) :
    Function.Injective (fun v : Valuation B Γ => v.comap φ) := by
  intro v v' h
  ext b
  obtain ⟨a, rfl⟩ := hφ b
  exact congrArg (fun w : Valuation A Γ => w a) h

/-- Through a birational morphism `f : Y ⟶ X`, a prime divisor of `Y` is determined by its
valuation `ord_P` regarded as a valuation of `k(X)`. -/
private theorem valuationOver_injective {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsIntegral Y] [IsIntegral X] [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k))
    [IsSeparated sY] {f : Y ⟶ X} (hf : MMP.Mori.IsBirationalMorphism f) [IsDominant f] :
    Function.Injective (fun P : MMP.Mori.PrimeDivisor Y => P.valuationOver f) :=
  fun _ _ h => divisorialValuation_injective sY
    (comap_injective_of_surjective hf.functionFieldMap_bijective.2 h)

/-- Functoriality of the pullback of rational functions along dominant morphisms of integral
schemes. -/
private theorem functionFieldMap_comp_apply {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] {c : A ⟶ C}
    [IsDominant c] (hc : a ≫ b = c) (t : C.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap c t := by
  subst hc
  obtain ⟨s, rfl⟩ := MMP.Positivity.DivisorOver.algebraMap_stalk_surjective_of_eq_genericPoint
    ((a ≫ b) (genericPoint A)) (map_genericPoint_of_isDominant (a ≫ b)) t
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk (a ≫ b) (genericPoint A) s]
  erw [MMP.Mori.functionFieldMap_algebraMap_stalk b (a (genericPoint A)) s,
    MMP.Mori.functionFieldMap_algebraMap_stalk a (genericPoint A)]
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- Restriction of `ord_Q` along a composite `f ≫ g` is restriction along `f`, then along `g`. -/
private theorem valuationOver_comp {A B C : Scheme.{u}} [IsIntegral A] [IsLocallyNoetherian A]
    [IsNormal A] [IsIntegral B] [IsIntegral C] (Q : MMP.Mori.PrimeDivisor A) (f : A ⟶ B)
    (g : B ⟶ C) [IsDominant f] [IsDominant g] {c : A ⟶ C} [IsDominant c] (hc : f ≫ g = c) :
    Q.valuationOver c = (Q.valuationOver f).comap (functionFieldMap g) := by
  ext t
  simp only [MMP.Mori.PrimeDivisor.valuationOver_apply, Valuation.comap_apply]
  rw [functionFieldMap_comp_apply f g hc]

/-- Two prime divisors with the same valuation of `k(B)` have the same valuation of `k(C)` through
composites `f ≫ g`, `f' ≫ g` with a common dominant `g : B ⟶ C`. -/
private theorem valuationOver_comp_eq {A A' B C : Scheme.{u}} [IsIntegral A]
    [IsLocallyNoetherian A] [IsNormal A] [IsIntegral A'] [IsLocallyNoetherian A'] [IsNormal A']
    [IsIntegral B] [IsIntegral C] {Q : MMP.Mori.PrimeDivisor A} {Q' : MMP.Mori.PrimeDivisor A'}
    {f : A ⟶ B} {f' : A' ⟶ B} {g : B ⟶ C} [IsDominant f] [IsDominant f'] [IsDominant g]
    {c : A ⟶ C} {c' : A' ⟶ C} [IsDominant c] [IsDominant c'] (hc : f ≫ g = c)
    (hc' : f' ≫ g = c') (h : Q.valuationOver f = Q'.valuationOver f') :
    Q.valuationOver c = Q'.valuationOver c' := by
  rw [valuationOver_comp Q f g hc, valuationOver_comp Q' f' g hc', h]

/-- If a dominant morphism `f : Y ⟶ X` of normal integral schemes inducing a surjection of
function fields maps the generic point of a prime divisor `E` of `Y` to that of a prime divisor
`P` of `X`, then `ord_E`, read in `k(X)`, is `ord_P`. -/
private theorem valuationOver_eq_of_map_genericPoint {X Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (f : Y ⟶ X) [IsDominant f] (hf : Function.Surjective (functionFieldMap f))
    (E : MMP.Mori.PrimeDivisor Y) (P : MMP.Mori.PrimeDivisor X)
    (h : f E.genericPoint = P.genericPoint) :
    E.valuationOver f = P.divisorialValuation := by
  have := P.isDiscreteValuationRing_localRing
  have h1 : ∀ z, f E.genericPoint = z → ∀ a : X.presheaf.stalk z,
      E.valuationOver f (algebraMap _ X.functionField a) ≤ 1 := by
    rintro z rfl a
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
      MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨_, rfl⟩
  have h2 : ∀ z, f E.genericPoint = z → ∀ a : X.presheaf.stalk z,
      a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) →
      E.valuationOver f (algebraMap _ X.functionField a) < 1 := by
    rintro z rfl a ha
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
      MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
  have h3 : ∃ g, E.valuationOver f g = WithZero.exp (-1) := by
    have := E.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
    obtain ⟨g, hg⟩ := hf (algebraMap E.localRing Y.functionField ϖ)
    exact ⟨g, by rw [MMP.Mori.PrimeDivisor.valuationOver_apply, hg,
      MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_of_irreducible _ hϖ]⟩
  have h3' : ∃ g, P.divisorialValuation g = WithZero.exp (-1) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
    exact ⟨_, P.divisorialValuation_algebraMap_of_irreducible hϖ⟩
  exact MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing (R := P.localRing)
    (h1 _ h) (h2 _ h) h3 (fun r => (P.divisorialValuation_le_one_iff _).2 ⟨r, rfl⟩)
    (fun r hr => (P.divisorialValuation_algebraMap_lt_one_iff r).2 hr) h3'

/-- If `f` maps the generic point of a prime divisor `E` to a point of coheight one, that point
is the generic point of a prime divisor `P` with `ord_P = ord_E`. -/
private theorem exists_valuationOver_eq_of_coheight {X Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (f : Y ⟶ X) [IsDominant f] (hf : Function.Surjective (functionFieldMap f))
    (E : MMP.Mori.PrimeDivisor Y) (hE : Order.coheight (f E.genericPoint) = 1) :
    ∃ P : MMP.Mori.PrimeDivisor X, E.valuationOver f = P.divisorialValuation :=
  ⟨_, valuationOver_eq_of_map_genericPoint f hf E
    (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hE)
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hE).symm⟩

open MMP.Mori in
/-- A small morphism maps the generic point of a prime divisor to a point of coheight one: the
generic point lies outside the exceptional set, over which the morphism is an isomorphism. -/
private theorem coheight_map_genericPoint_of_isSmallMorphism {k : Type u} [Field k]
    {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z}
    (hg : MMP.Fourfold.IsSmallMorphism sX sZ g) (Q : MMP.Mori.PrimeDivisor X) :
    Order.coheight (g Q.genericPoint) = 1 := by
  set η := Q.genericPoint
  set V := biregularLocus g
  have hη : η ∉ (exceptionalSet g : Set X) := fun h => by
    have := (MMP.Flips.le_closedsCodimension_iff_le_coheight.1 hg.two_le_codimension) _ h
    rw [Q.coheight_genericPoint] at this
    exact absurd this (by norm_num)
  have : IsIso (g ∣_ V) := isBiregular_biregularLocus g
  let q : (g ⁻¹ᵁ V).toScheme := ⟨η, not_not.mp hη⟩
  rw [show g η = ((g ∣_ V) ≫ V.ι) q by rw [morphismRestrict_ι]; rfl,
    Topology.IsOpenEmbedding.coheight_eq _ ((g ∣_ V) ≫ V.ι).isOpenEmbedding,
    ← Topology.IsOpenEmbedding.coheight_eq _ (g ⁻¹ᵁ V).ι.isOpenEmbedding]
  exact Q.coheight_genericPoint

/-- Through a small morphism `g : X ⟶ Z`, every prime divisor `Q` of `X` has `ord_Q = ord_P`
for a prime divisor `P` of `Z`. -/
private theorem exists_valuationOver_eq_of_isSmallMorphism {k : Type u} [Field k]
    {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsDominant g]
    (hg : MMP.Fourfold.IsSmallMorphism sX sZ g) (Q : MMP.Mori.PrimeDivisor X) :
    ∃ P : MMP.Mori.PrimeDivisor Z, Q.valuationOver g = P.divisorialValuation :=
  exists_valuationOver_eq_of_coheight g hg.isBirationalMorphism.functionFieldMap_bijective.2 Q
    (coheight_map_genericPoint_of_isSmallMorphism hg Q)

/-- Through a small morphism `g : X ⟶ Z`, every prime divisor `P` of `Z` is `ord_Q` for a prime
divisor `Q` of `X`, its strict transform. -/
private theorem exists_valuationOver_eq_of_isSmallMorphism_of_primeDivisor {k : Type u} [Field k]
    {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsDominant g]
    (hg : MMP.Fourfold.IsSmallMorphism sX sZ g) (P : MMP.Mori.PrimeDivisor Z) :
    ∃ Q : MMP.Mori.PrimeDivisor X, Q.valuationOver g = P.divisorialValuation := by
  have := hg.isProper
  have hX : MMP.Mori.IsNormalVariety k (g ≫ sZ) := hg.comp_eq ▸ hg.isNormalVariety_source
  obtain ⟨Q, hQ, -⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0}
    hg.isNormalVariety_target hX hg.isBirationalMorphism P
  exact ⟨Q, valuationOver_eq_of_map_genericPoint g
    hg.isBirationalMorphism.functionFieldMap_bijective.2 Q P hQ⟩

variable {T : StabilizedSmallKltTail}

/-- The valuation of `k(X_i)` corresponding to a valuation of `k(X_0)` is unique. -/
private theorem corresponds_unique : ∀ (i : ℕ)
    {ξ : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {η η' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
    T.Corresponds i ξ η → T.Corresponds i ξ η' → η = η'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨ζ, hζ, ht⟩, ⟨ζ', hζ', ht'⟩ => by
    obtain rfl := corresponds_unique i hζ hζ'
    have hd := T.isFourfoldStepDiagram i
    have := hd.isNormalVariety_target.1.toIsIntegral
    have hb := hd.isSmallMorphism_plus.isBirationalMorphism
    have := hb.isDominant
    exact comap_injective_of_surjective hb.functionFieldMap_bijective.2 (ht.trans ht'.symm)

/-- The valuation of `k(X_0)` corresponding to a valuation of `k(X_i)` is unique. -/
private theorem corresponds_injective : ∀ (i : ℕ)
    {ξ ξ' : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {η : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
    T.Corresponds i ξ η → T.Corresponds i ξ' η → ξ = ξ'
  | 0, _, _, _, h, h' => h.symm.trans h'
  | i + 1, _, _, _, ⟨ζ, hζ, ht⟩, ⟨ζ', hζ', ht'⟩ => by
    have hd := T.isFourfoldStepDiagram i
    have := hd.isNormalVariety_target.1.toIsIntegral
    have hb := hd.isBirationalMorphism_minus
    have := hb.isDominant
    obtain rfl := comap_injective_of_surjective hb.functionFieldMap_bijective.2 (ht.symm.trans ht')
    exact corresponds_injective i hζ hζ'

/-- `C.IsPrimeDivisorCentre P x Q`: the prime divisor `Q` of the model `M` of index `x` is the
centre `c_M(ord_P)` of the valuation of the prime divisor `P` of `Y_0`. The valuation `ord_P`,
regarded in `k(X_0)` through `p_0`, is carried to `k(X_i)` along the step sequence
(`MMP.Fourfold.StepSequence.Corresponds`); for a junction `M = Y_i` it must agree with `ord_Q`
regarded in `k(X_i)` through `p_i`, and for the model `M = V_k` of the `i`-th bridge, carried on
to `k(Z_i)` through `f_i`, with `ord_Q` regarded in `k(Z_i)` through `π_k : V_k ⟶ Z_i`. -/
def IsPrimeDivisorCentre (C : TerminalChain T) (P : MMP.Mori.PrimeDivisor (C.junction 0).Y)
    (x : C.ModelIndex) (Q : MMP.Mori.PrimeDivisor (C.model x)) : Prop :=
  haveI := (C.junction 0).isBirationalMorphism.isDominant
  match x, Q with
  | ⟨i, none⟩, (Q : MMP.Mori.PrimeDivisor (C.junction i).Y) =>
    haveI := (C.junction i).isBirationalMorphism.isDominant
    ∃ w, T.Corresponds i (P.valuationOver (C.junction 0).p) w ∧
      Q.valuationOver (C.junction i).p = w
  | ⟨i, some k⟩, (Q : MMP.Mori.PrimeDivisor ((C.bridge i).P.model k)) =>
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
    ∃ w, T.Corresponds i (P.valuationOver (C.junction 0).p) w ∧
      ∃ _ : IsDominant ((C.bridge i).P.toBase k),
        Q.valuationOver ((C.bridge i).P.toBase k) = w.comap (functionFieldMap (T.f i))

/-- Along the programme of a bridge, every `π_k : V_k ⟶ Z_i` induces a surjection
`k(Z_i) → k(V_k)` of function fields: `π_0 = f_i ∘ p_i` is birational, and
`π_{k+1} = h_k ∘ g_k⁺` with `π_k = h_k ∘ g_k` and `g_k`, `g_k⁺` birational. -/
private theorem surjective_functionFieldMap_toBase (C : TerminalChain T) (i : ℕ) :
    ∀ k ≤ (C.bridge i).P.m, ∀ [IsDominant ((C.bridge i).P.toBase k)],
      Function.Surjective (functionFieldMap ((C.bridge i).P.toBase k))
  | 0, _, _ => by
    have hd := T.isFourfoldStepDiagram i
    have := hd.isNormalVariety_target.1.toIsIntegral
    have hb := hd.isBirationalMorphism_minus
    have := hb.isDominant
    have hp := (C.junction i).isBirationalMorphism
    have := hp.isDominant
    intro z
    obtain ⟨y, rfl⟩ := hp.functionFieldMap_bijective.2 z
    obtain ⟨x, rfl⟩ := hb.functionFieldMap_bijective.2 y
    exact ⟨x, (functionFieldMap_comp_apply (C.junction i).p (T.f i) rfl x).symm⟩
  | k + 1, hk, hdom => by
    have : IsDominant ((C.bridge i).P.toBase (k + 1)) := hdom
    have hk' : k < (C.bridge i).P.m := hk
    have hd := (C.bridge i).P.isFourfoldStepDiagram k hk'
    have := hd.isNormalVariety_target.1.toIsIntegral
    have hg := hd.isBirationalMorphism_minus
    have := hg.isDominant
    have hgp := hd.isSmallMorphism_plus.isBirationalMorphism
    have := hgp.isDominant
    have hπ : (C.bridge i).P.toBase (k + 1) = (C.bridge i).P.gp k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.πY_eq k hk'
    have hπ' : (C.bridge i).P.toBase k = (C.bridge i).P.g k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.modelMap_eq k hk'
    have : IsDominant ((C.bridge i).P.h k) := by
      have : IsDominant ((C.bridge i).P.gp k ≫ (C.bridge i).P.h k) := hπ ▸ hdom
      exact IsDominant.of_comp ((C.bridge i).P.gp k) _
    have : IsDominant ((C.bridge i).P.toBase k) := hπ' ▸ inferInstance
    have IH := surjective_functionFieldMap_toBase C i k hk'.le
    have hh : Function.Surjective (functionFieldMap ((C.bridge i).P.h k)) := by
      intro t
      obtain ⟨z, hz⟩ := IH (functionFieldMap ((C.bridge i).P.g k) t)
      refine ⟨z, (functionFieldMap ((C.bridge i).P.g k)).injective ?_⟩
      rw [functionFieldMap_comp_apply _ _ hπ'.symm, hz]
    intro x
    obtain ⟨y, rfl⟩ := hgp.functionFieldMap_bijective.2 x
    obtain ⟨z, rfl⟩ := hh y
    exact ⟨z, (@functionFieldMap_comp_apply _ _ _ _ _ _ ((C.bridge i).P.gp k)
      ((C.bridge i).P.h k) _ _ _ hdom hπ.symm z).symm⟩

/-- The centre of `ord_P` on a model is unique. -/
theorem IsPrimeDivisorCentre.unique {C : TerminalChain T} {x : C.ModelIndex}
    {P : MMP.Mori.PrimeDivisor (C.junction 0).Y} {Q Q' : MMP.Mori.PrimeDivisor (C.model x)}
    (hQ : IsPrimeDivisorCentre C P x Q) (hQ' : IsPrimeDivisorCentre C P x Q') : Q = Q' := by
  rcases x with ⟨i, _ | k⟩
  · obtain ⟨w, hw, hQw⟩ := hQ
    obtain ⟨w', hw', hQw'⟩ := hQ'
    have : IsSeparated ((C.junction i).p ≫ T.sX i) :=
      (C.junction i).isProjectiveVariety.1.toIsSeparated
    have := (C.junction i).isBirationalMorphism.isDominant
    exact valuationOver_injective ((C.junction i).p ≫ T.sX i) (C.junction i).isBirationalMorphism
      (hQw.trans ((corresponds_unique i hw hw').trans hQw'.symm))
  · obtain ⟨w, hw, _, hQw⟩ := hQ
    obtain ⟨w', hw', _, hQw'⟩ := hQ'
    obtain rfl := corresponds_unique i hw hw'
    have : IsSeparated ((C.bridge i).P.modelStructure k) :=
      ((C.bridge i).P.isFourfoldStepDiagram k k.2).isProjectiveVariety_minus.1.toIsSeparated
    exact divisorialValuation_injective ((C.bridge i).P.modelStructure k)
      (comap_injective_of_surjective
        (surjective_functionFieldMap_toBase C i k k.2.le) (hQw.trans hQw'.symm))

/-- A prime divisor of a model is the centre of at most one `ord_P`. -/
theorem IsPrimeDivisorCentre.unique_left {C : TerminalChain T} {x : C.ModelIndex}
    {P P' : MMP.Mori.PrimeDivisor (C.junction 0).Y} {Q : MMP.Mori.PrimeDivisor (C.model x)}
    (hP : IsPrimeDivisorCentre C P x Q) (hP' : IsPrimeDivisorCentre C P' x Q) : P = P' := by
  have : IsSeparated ((C.junction 0).p ≫ T.sX 0) :=
    (C.junction 0).isProjectiveVariety.1.toIsSeparated
  have := (C.junction 0).isBirationalMorphism.isDominant
  refine valuationOver_injective ((C.junction 0).p ≫ T.sX 0) (C.junction 0).isBirationalMorphism ?_
  rcases x with ⟨i, _ | k⟩
  · obtain ⟨w, hw, hQw⟩ := hP
    obtain ⟨w', hw', hQw'⟩ := hP'
    exact corresponds_injective i hw (hQw'.symm.trans hQw ▸ hw')
  · obtain ⟨w, hw, _, hQw⟩ := hP
    obtain ⟨w', hw', _, hQw'⟩ := hP'
    have hd := T.isFourfoldStepDiagram i
    have := hd.isNormalVariety_target.1.toIsIntegral
    have hb := hd.isBirationalMorphism_minus
    have := hb.isDominant
    have hww : w = w' :=
      comap_injective_of_surjective hb.functionFieldMap_bijective.2 (hQw.symm.trans hQw')
    exact corresponds_injective i hw (hww ▸ hw')

/-- Every `π_k : V_k ⟶ Z_i`, `k ≤ m`, of the programme of a bridge is dominant. -/
private theorem isDominant_toBase (C : TerminalChain T) (i : ℕ) :
    ∀ k ≤ (C.bridge i).P.m, IsDominant ((C.bridge i).P.toBase k)
  | 0, _ => by
    have hd := T.isFourfoldStepDiagram i
    have := hd.isBirationalMorphism_minus.isDominant
    have := (C.junction i).isBirationalMorphism.isDominant
    exact (inferInstance : IsDominant ((C.junction i).p ≫ T.f i))
  | k + 1, hk => by
    have hk' : k < (C.bridge i).P.m := hk
    have hd := (C.bridge i).P.isFourfoldStepDiagram k hk'
    have := hd.isSmallMorphism_plus.isBirationalMorphism.isDominant
    have : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) :=
      (C.bridge i).P.modelMap_eq k hk' ▸ isDominant_toBase C i k hk'.le
    have : IsDominant ((C.bridge i).P.h k) := IsDominant.of_comp ((C.bridge i).P.g k) _
    change IsDominant ((C.bridge i).P.πY k)
    rw [(C.bridge i).P.πY_eq k hk']
    infer_instance

/-- On `V_0 = Y_i`, the valuation `ord_Q` read in `k(Z_i)` through `π_0 = f_i ∘ p_i` is `ord_Q`
read in `k(X_i)` and restricted along `f_i`. -/
private theorem valuationOver_toBase_zero (C : TerminalChain T) (i : ℕ)
    (Q : MMP.Mori.PrimeDivisor (C.junction i).Y) :
    haveI : IsDominant (X := (C.junction i).Y) ((C.bridge i).P.toBase 0) :=
      isDominant_toBase C i 0 (Nat.zero_le _)
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (C.junction i).isBirationalMorphism.isDominant
    Q.valuationOver ((C.bridge i).P.toBase 0) =
      (Q.valuationOver (C.junction i).p).comap (functionFieldMap (T.f i)) := by
  have : IsDominant (X := (C.junction i).Y) ((C.bridge i).P.toBase 0) :=
    isDominant_toBase C i 0 (Nat.zero_le _)
  have := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  have := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  have := (C.junction i).isBirationalMorphism.isDominant
  ext z
  simp only [MMP.Mori.PrimeDivisor.valuationOver_apply, Valuation.comap_apply]
  exact congrArg _ (functionFieldMap_comp_apply (C.junction i).p (T.f i) rfl z).symm

/-- A flip of a bridge matches the prime divisors of `V_k` and `V_{k+1}` with the same
valuation of `k(Z_i)`. -/
private theorem flip_step (C : TerminalChain T) (i k : ℕ) (hk : k < (C.bridge i).P.m) :
    haveI := isDominant_toBase C i k hk.le
    haveI := isDominant_toBase C i (k + 1) hk
    (∀ Q : MMP.Mori.PrimeDivisor ((C.bridge i).P.model k),
      ∃ Q' : MMP.Mori.PrimeDivisor ((C.bridge i).P.model (k + 1)),
        Q'.valuationOver ((C.bridge i).P.toBase (k + 1)) =
          Q.valuationOver ((C.bridge i).P.toBase k)) ∧
    (∀ Q' : MMP.Mori.PrimeDivisor ((C.bridge i).P.model (k + 1)),
      ∃ Q : MMP.Mori.PrimeDivisor ((C.bridge i).P.model k),
        Q'.valuationOver ((C.bridge i).P.toBase (k + 1)) =
          Q.valuationOver ((C.bridge i).P.toBase k)) := by
  have hd := (C.bridge i).P.isFourfoldStepDiagram k hk
  have hg := (C.bridge i).isSmallMorphism k hk
  have hgp := hd.isSmallMorphism_plus
  have := hg.isNormalVariety_source.1.toIsIntegral
  have := hg.isNormalVariety_source.2
  have := hg.isNormalVariety_source.isLocallyNoetherian
  have := hgp.isNormalVariety_source.1.toIsIntegral
  have := hgp.isNormalVariety_source.2
  have := hgp.isNormalVariety_source.isLocallyNoetherian
  have := hg.isNormalVariety_target.1.toIsIntegral
  have := hg.isNormalVariety_target.2
  have := hg.isNormalVariety_target.isLocallyNoetherian
  have := hg.isBirationalMorphism.isDominant
  have := hgp.isBirationalMorphism.isDominant
  have := isDominant_toBase C i k hk.le
  have hdom := isDominant_toBase C i (k + 1) hk
  have hπ : (C.bridge i).P.toBase (k + 1) = (C.bridge i).P.gp k ≫ (C.bridge i).P.h k :=
    (C.bridge i).P.πY_eq k hk
  have hπ' : (C.bridge i).P.toBase k = (C.bridge i).P.g k ≫ (C.bridge i).P.h k :=
    (C.bridge i).P.modelMap_eq k hk
  have : IsDominant ((C.bridge i).P.h k) := by
    have : IsDominant ((C.bridge i).P.gp k ≫ (C.bridge i).P.h k) := hπ ▸ hdom
    exact IsDominant.of_comp ((C.bridge i).P.gp k) _
  have : IsDominant (X := (C.bridge i).P.model (k + 1)) ((C.bridge i).P.gp k) :=
    hgp.isBirationalMorphism.isDominant
  have : IsDominant (X := (C.bridge i).P.Y k) ((C.bridge i).P.toBase (k + 1)) := hdom
  refine ⟨fun Q => ?_, fun Q' => ?_⟩
  · obtain ⟨P, hP⟩ := exists_valuationOver_eq_of_isSmallMorphism hg Q
    obtain ⟨Q', hQ'⟩ := exists_valuationOver_eq_of_isSmallMorphism_of_primeDivisor hgp P
    exact ⟨Q', valuationOver_comp_eq hπ.symm hπ'.symm (hQ'.trans hP.symm)⟩
  · obtain ⟨P, hP⟩ := exists_valuationOver_eq_of_isSmallMorphism hgp Q'
    obtain ⟨Q, hQ⟩ := exists_valuationOver_eq_of_isSmallMorphism_of_primeDivisor hg P
    exact ⟨Q, valuationOver_comp_eq hπ.symm hπ'.symm (hP.trans hQ.symm)⟩

/-- The end `V_m ≅ Y_{i+1}` of a bridge matches prime divisors with the same valuation of
`k(Z_i)`. -/
private theorem end_step (C : TerminalChain T) (i : ℕ) :
    haveI := isDominant_toBase C i _ le_rfl
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isFourfoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
    (∀ Q : MMP.Mori.PrimeDivisor ((C.bridge i).P.model (C.bridge i).P.m),
      ∃ Q' : MMP.Mori.PrimeDivisor (C.junction (i + 1)).Y,
        (Q'.valuationOver (C.junction (i + 1)).p).comap (functionFieldMap (T.fp i)) =
          Q.valuationOver ((C.bridge i).P.toBase (C.bridge i).P.m)) ∧
    (∀ Q' : MMP.Mori.PrimeDivisor (C.junction (i + 1)).Y,
      ∃ Q : MMP.Mori.PrimeDivisor ((C.bridge i).P.model (C.bridge i).P.m),
        (Q'.valuationOver (C.junction (i + 1)).p).comap (functionFieldMap (T.fp i)) =
          Q.valuationOver ((C.bridge i).P.toBase (C.bridge i).P.m)) := by
  have := isDominant_toBase C i _ le_rfl
  have hd := T.isFourfoldStepDiagram i
  have := hd.isNormalVariety_target.1.toIsIntegral
  have := hd.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have := (C.junction (i + 1)).isBirationalMorphism.isDominant
  have := (C.junction (i + 1)).isProjectiveVariety.1.toLocallyOfFiniteType
  have := LocallyOfFiniteType.isLocallyNoetherian ((C.junction (i + 1)).p ≫ T.sX (i + 1))
  set e := (C.bridge i).e
  have he : Function.Surjective (functionFieldMap e.hom) :=
    (MMP.Mori.isBirationalMorphism_of_isIso e.hom).functionFieldMap_bijective.2
  have hπ := ((C.bridge i).toBase_end_eq).symm
  have key : ∀ (Q : MMP.Mori.PrimeDivisor ((C.bridge i).P.model (C.bridge i).P.m))
      (Q' : MMP.Mori.PrimeDivisor (C.junction (i + 1)).Y),
      Q.valuationOver e.hom = Q'.divisorialValuation →
      (Q'.valuationOver (C.junction (i + 1)).p).comap (functionFieldMap (T.fp i)) =
        Q.valuationOver ((C.bridge i).P.toBase (C.bridge i).P.m) := fun Q Q' h =>
    ((valuationOver_comp Q' _ _ rfl).symm.trans
      (congrArg (fun w => w.comap (functionFieldMap ((C.junction (i + 1)).p ≫ T.fp i)))
        h.symm)).trans
      (valuationOver_comp Q _ _ hπ).symm
  refine ⟨fun Q => ?_, fun Q' => ?_⟩
  · have hQ : Order.coheight (e.hom Q.genericPoint) = 1 :=
      (Topology.IsOpenEmbedding.coheight_eq _ e.hom.isOpenEmbedding).trans Q.coheight_genericPoint
    obtain ⟨Q', hQ'⟩ := exists_valuationOver_eq_of_coheight e.hom he Q hQ
    exact ⟨Q', key Q Q' hQ'⟩
  · have hx : Order.coheight (e.inv Q'.genericPoint) = 1 :=
      (Topology.IsOpenEmbedding.coheight_eq _ e.inv.isOpenEmbedding).trans Q'.coheight_genericPoint
    refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx, key _ Q' ?_⟩
    refine valuationOver_eq_of_map_genericPoint e.hom he _ Q' ?_
    change e.hom (AlgebraicGeometry.PrimeDivisor.genericPoint
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx)) = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, ← Scheme.Hom.comp_apply,
      e.inv_hom_id]
    rfl

/-- Along the programme of a bridge, the prime divisors of `V_0` and of `V_k` are matched by
their valuations of `k(Z_i)`. -/
private theorem bridge_steps (C : TerminalChain T) (i : ℕ) :
    ∀ k (hk : k ≤ (C.bridge i).P.m),
    haveI := isDominant_toBase C i 0 (Nat.zero_le _)
    haveI := isDominant_toBase C i k hk
    (∀ Q : MMP.Mori.PrimeDivisor ((C.bridge i).P.model 0),
      ∃ Q' : MMP.Mori.PrimeDivisor ((C.bridge i).P.model k),
        Q'.valuationOver ((C.bridge i).P.toBase k) =
          Q.valuationOver ((C.bridge i).P.toBase 0)) ∧
    (∀ Q' : MMP.Mori.PrimeDivisor ((C.bridge i).P.model k),
      ∃ Q : MMP.Mori.PrimeDivisor ((C.bridge i).P.model 0),
        Q'.valuationOver ((C.bridge i).P.toBase k) =
          Q.valuationOver ((C.bridge i).P.toBase 0))
  | 0, _ => ⟨fun Q => ⟨Q, rfl⟩, fun Q => ⟨Q, rfl⟩⟩
  | k + 1, hk => by
    obtain ⟨IH₁, IH₂⟩ := bridge_steps C i k (Nat.le_of_succ_le hk)
    obtain ⟨S₁, S₂⟩ := flip_step C i k hk
    refine ⟨fun Q => ?_, fun Q' => ?_⟩
    · obtain ⟨Q₁, h₁⟩ := IH₁ Q
      obtain ⟨Q₂, h₂⟩ := S₁ Q₁
      exact ⟨Q₂, h₂.trans h₁⟩
    · obtain ⟨Q₁, h₁⟩ := S₂ Q'
      obtain ⟨Q₂, h₂⟩ := IH₂ Q₁
      exact ⟨Q₂, h₁.trans h₂⟩

/-- Every `ord_P` has a prime divisor as its centre on every junction `Y_i`. -/
private theorem exists_centre_junction (C : TerminalChain T)
    (P : MMP.Mori.PrimeDivisor (C.junction 0).Y) : ∀ i,
    haveI := (C.junction 0).isBirationalMorphism.isDominant
    haveI := (C.junction i).isBirationalMorphism.isDominant
    ∃ Q : MMP.Mori.PrimeDivisor (C.junction i).Y,
      T.Corresponds i (P.valuationOver (C.junction 0).p) (Q.valuationOver (C.junction i).p)
  | 0 => ⟨P, rfl⟩
  | i + 1 => by
    obtain ⟨Q, hQ⟩ := exists_centre_junction C P i
    obtain ⟨Qm, hm⟩ := (bridge_steps C i _ le_rfl).1 Q
    obtain ⟨Q', h'⟩ := (end_step C i).1 Qm
    exact ⟨Q', _, hQ, h'.trans (hm.trans (valuationOver_toBase_zero C i Q))⟩

/-- Every prime divisor of a junction `Y_i` is the centre of some `ord_P`. -/
private theorem exists_centre_junction_of_primeDivisor (C : TerminalChain T) : ∀ i
    (Q : MMP.Mori.PrimeDivisor (C.junction i).Y),
    haveI := (C.junction 0).isBirationalMorphism.isDominant
    haveI := (C.junction i).isBirationalMorphism.isDominant
    ∃ P : MMP.Mori.PrimeDivisor (C.junction 0).Y,
      T.Corresponds i (P.valuationOver (C.junction 0).p) (Q.valuationOver (C.junction i).p)
  | 0, Q => ⟨Q, rfl⟩
  | i + 1, Q' => by
    obtain ⟨Qm, h'⟩ := (end_step C i).2 Q'
    obtain ⟨Q, hm⟩ := (bridge_steps C i _ le_rfl).2 Qm
    obtain ⟨P, hP⟩ := exists_centre_junction_of_primeDivisor C i Q
    exact ⟨P, _, hP, h'.trans (hm.trans (valuationOver_toBase_zero C i Q))⟩

/-- Every `ord_P` has a prime divisor as its centre on every model. -/
theorem exists_isPrimeDivisorCentre (C : TerminalChain T) (x : C.ModelIndex)
    (P : MMP.Mori.PrimeDivisor (C.junction 0).Y) : ∃ Q, IsPrimeDivisorCentre C P x Q := by
  obtain ⟨i, _ | k⟩ := x
  · obtain ⟨Q, hQ⟩ := exists_centre_junction C P i
    exact ⟨Q, _, hQ, rfl⟩
  · obtain ⟨Q, hQ⟩ := exists_centre_junction C P i
    obtain ⟨Qk, hk⟩ := (bridge_steps C i k k.2.le).1 Q
    exact ⟨Qk, _, hQ, isDominant_toBase C i k k.2.le,
      hk.trans (valuationOver_toBase_zero C i Q)⟩

/-- Every prime divisor of a model is the centre of some `ord_P`. -/
theorem exists_isPrimeDivisorCentre_left (C : TerminalChain T) (x : C.ModelIndex)
    (Q : MMP.Mori.PrimeDivisor (C.model x)) : ∃ P, IsPrimeDivisorCentre C P x Q := by
  obtain ⟨i, _ | k⟩ := x
  · obtain ⟨P, hP⟩ := exists_centre_junction_of_primeDivisor C i Q
    exact ⟨P, _, hP, rfl⟩
  · obtain ⟨Q₀, h₀⟩ := (bridge_steps C i k k.2.le).2 Q
    obtain ⟨P, hP⟩ := exists_centre_junction_of_primeDivisor C i Q₀
    exact ⟨P, _, hP, isDominant_toBase C i k k.2.le,
      h₀.trans (valuationOver_toBase_zero C i Q₀)⟩

/-- The centre map `P ↦ c_M(ord_P)` from the prime divisors of `Y_0` to the prime divisors of
the model `M` of index `x` of a terminal chain, as an equivalence: every `ord_P` has exactly one
centre on `M` (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsPrimeDivisorCentre`), and
every prime divisor of `M` is the centre of exactly one `ord_P`. -/
noncomputable def primeDivisorEquivModel (C : TerminalChain T) (x : C.ModelIndex) :
    MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.model x) :=
  Equiv.ofBijective (fun P => (exists_isPrimeDivisorCentre C x P).choose)
    ⟨fun P P' (h : (exists_isPrimeDivisorCentre C x P).choose =
          (exists_isPrimeDivisorCentre C x P').choose) => IsPrimeDivisorCentre.unique_left
        (exists_isPrimeDivisorCentre C x P).choose_spec
        (h ▸ (exists_isPrimeDivisorCentre C x P').choose_spec),
      fun Q => (exists_isPrimeDivisorCentre_left C x Q).elim fun P hP =>
        ⟨P, IsPrimeDivisorCentre.unique
          (exists_isPrimeDivisorCentre C x P).choose_spec hP⟩⟩

/-- The image of `P` under `primeDivisorEquivModel` is the centre of `ord_P`. -/
theorem isPrimeDivisorCentre_primeDivisorEquivModel (C : TerminalChain T) (x : C.ModelIndex)
    (P : MMP.Mori.PrimeDivisor (C.junction 0).Y) :
    C.IsPrimeDivisorCentre P x (C.primeDivisorEquivModel x P) :=
  (exists_isPrimeDivisorCentre C x P).choose_spec

/-- For every model `M` of a terminal chain, the centre map `P ↦ c_M(ord_P)` is a bijection from
the prime divisors of `Y_0` onto the prime divisors of `M`: a prime divisor `Q` of `M` is the
centre of `ord_P` exactly when `Q` is the image of `P` under the equivalence
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.primeDivisorEquivModel`. -/
@[mmp "prop_oai4_terminal_chain_d"]
public theorem isPrimeDivisorCentre_iff_primeDivisorEquivModel_eq (C : TerminalChain T)
    (x : C.ModelIndex) (P : MMP.Mori.PrimeDivisor (C.junction 0).Y)
    (Q : MMP.Mori.PrimeDivisor (C.model x)) :
    C.IsPrimeDivisorCentre P x Q ↔ C.primeDivisorEquivModel x P = Q :=
  ⟨(isPrimeDivisorCentre_primeDivisorEquivModel C x P).unique,
    fun h => h ▸ isPrimeDivisorCentre_primeDivisorEquivModel C x P⟩

/-- The preimage of `Q` under `primeDivisorEquivModel` is the `P` whose `ord_P` has centre `Q`. -/
theorem isPrimeDivisorCentre_primeDivisorEquivModel_symm (C : TerminalChain T)
    (x : C.ModelIndex) (Q : MMP.Mori.PrimeDivisor (C.model x)) :
    C.IsPrimeDivisorCentre ((C.primeDivisorEquivModel x).symm Q) x Q :=
  (isPrimeDivisorCentre_iff_primeDivisorEquivModel_eq C x _ Q).2 (Equiv.apply_symm_apply _ _)

end MMP.Fourfold.StabilizedSmallKltTail.TerminalChain
