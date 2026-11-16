module

public import MMP.RingTheory.Kaehler.PluriformProduct
public import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
public import MMP.RingTheory.DualizingComplex.FlatLocalExtension
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryPushforward
public import MMP.AlgebraicGeometry.Morphisms.Birational.ZariskiMainTheorem
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor

/-!
# Adjunction along a normal divisor that is Cartier in codimension two

Let `X` be a normal variety of dimension `n + 1` over a perfect field `k`, and `S ⊂ X` a reduced
divisor which is normal and is Cartier at every point of `X` of codimension two lying on `S`.
Since `S` is normal, it is the disjoint union of its irreducible components `S_a`, each a normal
prime divisor of `X`. Let `B` be a `ℚ`-divisor without components in `S` such that `K_X + S + B`
is `ℚ`-Cartier. Then `X` is regular at the generic point of every prime divisor of every `S_a`,
so the restriction `B|_{S_a}` is defined; there is a nonzero rational top form `ω` with
`ord_{S_a} ω = -1` for every `a`; for each such `ω` and each Poincaré residue `Res_{S_a} ω`,
`div ω` and `div (Res_{S_a} ω)` are canonical divisors and
`(div ω + S + B)|_{S_a} = div (Res_{S_a} ω) + B|_{S_a}`; consequently
`(K_X + S + B)|_{S_a} ∼_ℚ K_{S_a} + B|_{S_a}` for all canonical divisors `K_X` such that
`K_X + S + B` has no component in `S` (so that the restriction is defined), and
`K_{S_a} + B|_{S_a}` is `ℚ`-Cartier, and Cartier when `K_X + S + B` is.

On a log resolution `f : Y ⟶ X` of `(X, S + B)`, for `S` a single such prime divisor, with
`S' = f⁻¹_* S` disjoint from `f⁻¹_* B`, the restriction `f_S : S' ⟶ S` is a proper birational
morphism from a smooth variety, and the crepant boundary of `(S, B|_S)` on `S'` is
`-∑ᵢ eᵢ Eᵢ|_{S'}`, where the `Eᵢ` are the `f`-exceptional prime divisors and
`eᵢ = a(Eᵢ, X, S + B)`.

## Main results

* `MMP.Mori.adjunction_restrict_of_isCartierAt_coheight_eq_two`: adjunction
  `(K_X + S + B)|_{S_a} ∼_ℚ K_{S_a} + B|_{S_a}`, via Poincaré residues.
* `MMP.Mori.isCrepantBoundary_restrict_of_isLogResolution`: adjunction on a log resolution.

## Implementation notes

The normal divisor `S` is given by its components: a finite family of closed immersions
`ι a : T a ⟶ X` of normal integral schemes onto pairwise disjoint prime divisors `P a` of `X`, and
`S = ∑ₐ P a` as a Weil divisor. A divisor on `S = ⨆ₐ T a` is a family of divisors on the `T a`,
and the assertions about `S` are made componentwise. The ground field is only assumed perfect.

The heart of the first result is the local residue computation: for a top form `τ` with a simple
pole along `P a` and residue `ρ`, `div ρ = (div τ + P a)|_{T a}`. In the second, `S'` is a closed
immersion `ι' : T' ⟶ Y` onto `P' = f⁻¹_* P`, and `f_S` is any factorisation of `ι' ≫ f` through
`ι`; it exists and is unique since `ι` is a monomorphism. The second result is proved by
showing that residues and restriction commute with pull-back to the strict transform.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Remark 5.47
  and the proof of Proposition 5.46
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

/-! ## Adjunction along a normal divisor Cartier in codimension two -/

private theorem one_le_ord_iff_mem_maximalIdeal {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {y : X} (hy : Order.coheight y = 1)
    {c : X.presheaf.stalk y} (hc : c ≠ 0) :
    1 ≤ X.ord (algebraMap (X.presheaf.stalk y) X.functionField c) y ↔
      c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  have hDVR : IsDiscreteValuationRing (X.presheaf.stalk y) :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hy
  have hKr : Ring.KrullDimLE 1 (X.presheaf.stalk y) := krullDimLE_of_coheight_le hy.le
  have hz : algebraMap (X.presheaf.stalk y) X.functionField c ≠ 0 := by
    intro h
    exact hc (IsFractionRing.injective (X.presheaf.stalk y) X.functionField
      (h.trans (map_zero _).symm))
  have hnn : 0 ≤ X.ord (algebraMap (X.presheaf.stalk y) X.functionField c) y :=
    (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hy hz).mp ⟨c, rfl⟩
  have h0 : X.ord (algebraMap (X.presheaf.stalk y) X.functionField c) y = 0 ↔ IsUnit c := by
    rw [Scheme.ord_eq_iff hy hz]
    have hfrac : Scheme.ordHom y hy (algebraMap (X.presheaf.stalk y) X.functionField c) =
        Ring.ordFrac (X.presheaf.stalk y) (algebraMap (X.presheaf.stalk y) X.functionField c) :=
      rfl
    rw [hfrac, ofAdd_zero]
    exact (Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing).symm
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← h0]
  omega

private theorem ord_mul_inv {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) (z : X) : X.ord (f * g⁻¹) z = X.ord f z - X.ord g z := by
  have h1 : X.ord (g * g⁻¹) z = X.ord g z + X.ord g⁻¹ z := Scheme.ord_mul hg (inv_ne_zero hg)
  rw [mul_inv_cancel₀ hg, Scheme.ord_one] at h1
  rw [Scheme.ord_mul hf (inv_ne_zero hg)]
  omega

private theorem ord_inv {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X.functionField} (hf : f ≠ 0) (z : X) : X.ord f⁻¹ z = -X.ord f z := by
  simpa [Scheme.ord_one] using ord_mul_inv one_ne_zero hf z

/-- A germ at `ι q` restricts to zero on the integral closed subscheme `T` exactly when its
generization to the generic point of `T` lies in the maximal ideal there. -/
private theorem stalkMap_eq_zero_iff {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (ι : T ⟶ X) [IsClosedImmersion ι] (q : T) (a : X.presheaf.stalk (ι q)) :
    (ι.stalkMap q).hom a = 0 ↔ X.presheaf.stalkSpecializes
      ((genericPoint_specializes q).map ι.continuous) a ∈ IsLocalRing.maximalIdeal _ := by
  letI : Field (T.presheaf.stalk (genericPoint T)) := inferInstanceAs (Field T.functionField)
  rw [← IsLocalRing.ker_eq_maximalIdeal _ (ι.stalkMap_surjective (genericPoint T)), RingHom.mem_ker,
    ι.stalkSpecializes_stalkMap_apply (genericPoint T) q (genericPoint_specializes q) a]
  exact ⟨fun h => by rw [h, map_zero],
    fun h => Scheme.stalkSpecializes_injective _ (h.trans (map_zero _).symm)⟩

/-- The local ring of a normal scheme at the generic point of a prime divisor is regular. -/
private theorem isRegularLocalRing_stalk_genericPoint {T : Scheme.{u}} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] (Q : MMP.Mori.PrimeDivisor T) :
    IsRegularLocalRing (T.presheaf.stalk Q.genericPoint) := by
  have := Q.isDiscreteValuationRing_localRing
  exact inferInstanceAs (IsRegularLocalRing Q.localRing)

private theorem exists_span_ker_stalkMap
    {X T : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T]
    (ι : T ⟶ X) [IsClosedImmersion ι] (q : T) (hp : Order.coheight (ι (genericPoint T)) = 1)
    (g : X.functionField) (hg : g ≠ 0) (hgp : X.ord g (ι (genericPoint T)) = 1)
    (hg0 : ∀ y : X, Order.coheight y = 1 → y ⤳ ι q → y ≠ ι (genericPoint T) →
      X.ord g y = 0) :
    ∃ s : X.presheaf.stalk (ι q), s ≠ 0 ∧ RingHom.ker (ι.stalkMap q).hom = Ideal.span {s} := by
  classical
  set p := ι (genericPoint T) with hpdef
  have hηq : genericPoint T ⤳ q := genericPoint_specializes q
  have hpx : p ⤳ ι q := hηq.map ι.continuous
  have halg : ∀ a, algebraMap (X.presheaf.stalk p) X.functionField
      (X.presheaf.stalkSpecializes hpx a) =
      algebraMap (X.presheaf.stalk (ι q)) X.functionField a :=
    fun a => Scheme.algebraMap_stalkSpecializes hpx a
  have hspinj : Function.Injective (X.presheaf.stalkSpecializes hpx) :=
    Scheme.stalkSpecializes_injective hpx
  have hker : ∀ a : X.presheaf.stalk (ι q), (ι.stalkMap q).hom a = 0 ↔
      X.presheaf.stalkSpecializes hpx a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) :=
    stalkMap_eq_zero_iff ι q
  have hg_mem : g ∈ (algebraMap (X.presheaf.stalk (ι q)) X.functionField).range := by
    refine Scheme.mem_range_algebraMap_stalk_of_forall_zero_le_ord (ι q) hg fun y hy hyx => ?_
    by_cases hyp : y = p
    · subst hyp
      rw [hgp]
      exact zero_le_one
    · rw [hg0 y hy hyx hyp]
  obtain ⟨s, hs⟩ := hg_mem
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk (ι q)) X.functionField) :=
    IsFractionRing.injective _ _
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hg (by rw [← hs, map_zero])
  refine ⟨s, hs0, ?_⟩
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  constructor
  · intro ha
    by_cases ha0 : a = 0
    · exact ⟨0, by rw [ha0, zero_mul]⟩
    have hm := (hker a).mp ha
    have hc0 : X.presheaf.stalkSpecializes hpx a ≠ 0 := fun h =>
      ha0 (hspinj (h.trans (map_zero _).symm))
    have hz : algebraMap (X.presheaf.stalk (ι q)) X.functionField a ≠ 0 := fun h =>
      ha0 (hinj (h.trans (map_zero _).symm))
    have hord := (one_le_ord_iff_mem_maximalIdeal hp hc0).mpr hm
    rw [halg] at hord
    have hw : algebraMap (X.presheaf.stalk (ι q)) X.functionField a * g⁻¹ ∈
        (algebraMap (X.presheaf.stalk (ι q)) X.functionField).range := by
      refine Scheme.mem_range_algebraMap_stalk_of_forall_zero_le_ord (ι q)
        (mul_ne_zero hz (inv_ne_zero hg)) fun y hy hyx => ?_
      rw [Scheme.ord_mul hz (inv_ne_zero hg), ord_inv hg _]
      by_cases hyp : y = p
      · subst hyp
        omega
      · rw [hg0 y hy hyx hyp]
        have hr : algebraMap (X.presheaf.stalk (ι q)) X.functionField a ∈
            (algebraMap (X.presheaf.stalk y) X.functionField).range :=
          Scheme.range_algebraMap_stalk_le_of_specializes hyx ⟨a, rfl⟩
        have := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hy hz).mp hr
        omega
    obtain ⟨b, hb⟩ := hw
    refine ⟨b, hinj ?_⟩
    rw [map_mul, hb, hs, inv_mul_cancel_right₀ hg]
  · rintro ⟨b, rfl⟩
    rw [map_mul, (hker s).mpr, mul_zero]
    have hc0 : X.presheaf.stalkSpecializes hpx s ≠ 0 := fun h =>
      hs0 (hspinj (h.trans (map_zero _).symm))
    refine (one_le_ord_iff_mem_maximalIdeal hp hc0).mp ?_
    rw [halg, hs, hgp]

private theorem isRegularLocalRing_stalk_of_ker
    {X T : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T]
    (ι : T ⟶ X) [IsClosedImmersion ι] (q : T) (s : X.presheaf.stalk (ι q)) (hs0 : s ≠ 0)
    (hker : RingHom.ker (ι.stalkMap q).hom = Ideal.span {s})
    (hB : IsRegularLocalRing (T.presheaf.stalk q)) :
    IsRegularLocalRing (X.presheaf.stalk (ι q)) := by
  have hsurj : Function.Surjective (ι.stalkMap q).hom := ι.stalkMap_surjective q
  let e : (X.presheaf.stalk (ι q) ⧸ Ideal.span {s}) ≃+* T.presheaf.stalk q :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have hreg : IsRegularLocalRing (X.presheaf.stalk (ι q) ⧸ Ideal.span {s}) :=
    IsRegularLocalRing.of_ringEquiv e.symm
  have hfs : (ι.stalkMap q).hom s = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self s
  refine (MMP.isRegularLocalRing_factorial_and_of_quotient_span_singleton
    (X.presheaf.stalk (ι q))).2 s ?_ ?_ hreg
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map (ι.stalkMap q).hom
    rw [hfs] at this
    exact not_isUnit_zero this
  · intro 𝔭 h𝔭 hs𝔭
    rw [IsDomain.minimalPrimes_eq_singleton_bot] at h𝔭
    rw [Set.mem_singleton_iff.mp h𝔭] at hs𝔭
    exact hs0 (Ideal.mem_bot.mp hs𝔭)

private theorem arith_aux {d : WithBot ℕ∞} {n : ℕ} {c : ℕ∞} (h1 : d + 1 = (n : WithBot ℕ∞))
    (h2 : d + (c : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞)) : c = 2 := by
  induction d using WithBot.recBotCoe with
  | bot =>
    exfalso
    simp at h1
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this, top_add] at h1
      exact absurd (WithBot.coe_injective h1) (ENat.top_ne_coe n)
    | coe m =>
      induction c using ENat.recTopCoe with
      | top =>
        exfalso
        have : ((m : ℕ∞) : WithBot ℕ∞) + ((⊤ : ℕ∞) : WithBot ℕ∞) =
            (((m : ℕ∞) + ⊤ : ℕ∞) : WithBot ℕ∞) := rfl
        rw [this, add_top] at h2
        exact absurd (WithBot.coe_injective h2) fun h => by
          have := ENat.top_ne_coe (n + 1)
          push_cast at this
          exact this h
      | coe c =>
        have e1 : m + 1 = n := by exact_mod_cast h1
        have e2 : m + c = n + 1 := by exact_mod_cast h2
        obtain rfl : c = 2 := by omega
        rfl

private theorem arith_aux' {e : WithBot ℕ∞} {n : ℕ} (h : e + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    e = (n : WithBot ℕ∞) := by
  induction e using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.bot_add, ← WithBot.coe_natCast] at h
    exact WithBot.bot_ne_coe h
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this, top_add] at h
      exact absurd (WithBot.coe_injective h) fun h => by
        have := ENat.top_ne_coe (n + 1)
        push_cast at this
        exact this h
    | coe m =>
      have h' : m + 1 = n + 1 := by exact_mod_cast h
      obtain rfl : m = n := by omega
      rfl

/-- A prime divisor `T ⊂ X` of a variety of dimension `n + 1` has dimension `n`. -/
private theorem topologicalKrullDim_eq_of_range_eq_support
    {k : Type u} [Field k] {X T : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} (hdim : topologicalKrullDim X = n + 1) (ι : T ⟶ X) [IsClosedImmersion ι]
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range ι.base = (P.support : Set X)) :
    topologicalKrullDim T = n := by
  have hPP := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX P.genericPoint
  rw [P.coheight_genericPoint, hdim] at hPP
  have hT : topologicalKrullDim T = topologicalKrullDim (closure {P.genericPoint} : Set X) := by
    have e : (closure {P.genericPoint} : Set X) = Set.range ι.base := by
      rw [hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rw [e]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Topology.IsEmbedding.toHomeomorph ι.isEmbedding).isHomeomorph)
  rw [hT, arith_aux' (e := topologicalKrullDim (closure {P.genericPoint} : Set X)) (n := n)
    (by simpa using hPP)]

private theorem coheight_map_genericPoint_eq_two
    {k : Type u} [Field k] {X T : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} (hdim : topologicalKrullDim X = n + 1) (ι : T ⟶ X) [IsClosedImmersion ι]
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range ι.base = (P.support : Set X))
    (Q : MMP.Mori.PrimeDivisor T) :
    Order.coheight (ι Q.genericPoint) = 2 := by
  have hQ := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (ι ≫ sX) Q.genericPoint
  rw [Q.coheight_genericPoint] at hQ
  have hx := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (ι Q.genericPoint)
  have hcl : topologicalKrullDim (closure {ι Q.genericPoint} : Set X) =
      topologicalKrullDim (closure {Q.genericPoint} : Set T) := by
    have e : (closure {ι Q.genericPoint} : Set X) = ι.base '' closure {Q.genericPoint} := by
      rw [← Set.image_singleton, ← ι.isClosedEmbedding.closure_image_eq]
    rw [e]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Topology.IsEmbedding.homeomorphImage ι.isEmbedding _).isHomeomorph).symm
  rw [topologicalKrullDim_eq_of_range_eq_support sX hdim ι P hP] at hQ
  rw [hcl, hdim] at hx
  exact arith_aux (by simpa using hQ) hx

/-- A divisor whose restriction to an open `V` is Cartier has a local equation near every point
of `V`. -/
private theorem exists_isLocalEquation_of_isCartier_restrictOpen {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {D : Divisor X} {V : X.Opens}
    (h : Divisor.IsCartier (D.restrictOpen V)) {x : X} (hx : x ∈ V) :
    ∃ W : X.Opens, x ∈ W ∧ ∃ φ : (RationalFunctions X)ˣ, D.IsLocalEquation W φ := by
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨x, hx⟩)
  obtain ⟨W, hxW, φ', hφ'⟩ := h ⟨x, hx⟩
  obtain ⟨g', hg', hφg'⟩ := MMP.Positivity.exists_ord_eq_of_units φ'
  obtain ⟨g, rfl⟩ := (functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤
    ⟨⟨x, hx⟩, trivial⟩).2 g'
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (g := g)
    (fun h0 => hg' (by rw [h0, map_zero]))
  refine ⟨V.ι ''ᵁ W, ⟨⟨x, hx⟩, hxW, rfl⟩, φ, fun E hE => ?_⟩
  have hEW : E.genericPoint ∈ V.ι ''ᵁ W := (E.genericPoint_mem_iff _).2 hE
  obtain ⟨y, hyW, hy⟩ := hEW
  obtain ⟨E₀, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff V.ι E).2 ⟨y, hy⟩
  have hgp : V.ι E₀.genericPoint = V.ι y :=
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm.trans hy.symm
  have hE₀ : (E₀.support ∩ (W : Set V)).Nonempty := by
    rw [← PrimeDivisor.genericPoint_mem_iff]
    have : E₀.genericPoint = y := V.ι.isOpenEmbedding.injective hgp
    change E₀.genericPoint ∈ W
    rw [this]
    exact hyW
  have h1 := hφ' E₀ hE₀
  rw [DivisorWithCoeffs.coeff_restrictOpen] at h1
  rw [h1, hφg', hφ, MMP.Positivity.ord_functionFieldMap_of_isIso V.ι E₀ _
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

/-- A closed immersion of an integral scheme onto a prime divisor `P` maps the generic point to
the generic point of `P`. -/
private theorem map_genericPoint_eq {X T : Scheme.{u}} [IsIntegral T] (ι : T ⟶ X)
    [IsClosedImmersion ι] (P : PrimeDivisor X) (hP : Set.range ι.base = (P.support : Set X)) :
    ι (genericPoint T) = P.genericPoint := by
  have h1 : IsGenericPoint (ι (genericPoint T)) (closure (ι.base '' Set.univ)) :=
    (genericPoint_spec T).image ι.continuous
  rw [Set.image_univ, ι.isClosedEmbedding.isClosed_range.closure_eq, hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact h1.eq (isGenericPoint_closure)

open Classical in
private theorem coeff_sum_single_eq {X : Scheme.{u}} {J : Type*} [Fintype J]
    (P : J → MMP.Mori.PrimeDivisor X)
    (hdisj : Pairwise fun a b => Disjoint ((P a).support : Set X) (P b).support)
    (a : J) (x : X) (hx : x ∈ (P a).support) (Γ : MMP.Mori.PrimeDivisor X)
    (hΓ : x ∈ Γ.support) :
    (∑ b, Finsupp.single (P b) (1 : ℤ)) Γ = if Γ = P a then 1 else 0 := by
  classical
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single a]
  · rw [Finsupp.single_apply]
    simp only [eq_comm]
  · intro b _ hba
    rw [Finsupp.single_apply, if_neg]
    intro hbΓ
    subst hbΓ
    exact Set.disjoint_left.mp (hdisj hba) hΓ hx
  · simp

section CoreRestriction

open Classical

section StalkIdeal

variable {X : Scheme.{u}}

private theorem stalkIdeal_eq_stalk' (I : X.IdealSheafData) (x : X) :
    I.stalkIdeal x = IdealSheafData.stalk I x := by
  unfold Scheme.IdealSheafData.stalkIdeal
  apply le_antisymm
  · exact iSup_le fun U => (IdealSheafData.stalk_eq_map_germ I x U.1 U.2).symm.le
  · obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
    rw [IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU]
    exact le_iSup (fun U : {U : X.affineOpens // x ∈ U.1.1} =>
      Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1)) ⟨⟨U, hU⟩, hxU⟩

private theorem stalkIdeal_primeDivisor (E : MMP.Mori.PrimeDivisor X) {x : X}
    (hx : E.genericPoint ⤳ x) :
    E.idealSheaf.stalkIdeal x = MMP.Intersection.primeOfSpecializes hx := by
  have hE : E = AlgebraicGeometry.PrimeDivisor.ofCoheightOne E.genericPoint
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E) :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
  have h1 : E.idealSheaf = Stacks.Chow.integralComponentAt E.genericPoint := by
    conv_lhs => rw [hE]
    rfl
  rw [h1, stalkIdeal_eq_stalk']
  have h2 := Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk x
    ⟨MMP.Intersection.primeOfSpecializes hx, inferInstance⟩
  rw [MMP.Intersection.fromSpecStalk_primeOfSpecializes hx] at h2
  exact h2

private theorem ord_algebraMap_eq_toNat_ord [IsIntegral X] [IsLocallyNoetherian X] (x : X)
    (hx : Order.coheight x = 1) {c : X.presheaf.stalk x} (hc : c ≠ 0) :
    X.ord (algebraMap _ X.functionField c) x = ((Ring.ord (X.presheaf.stalk x) c).toNat : ℤ) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hne : algebraMap _ X.functionField c ≠ 0 := by
    rwa [map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  rw [Scheme.ord_eq_iff hx hne]
  change Ring.ordFrac _ _ = _
  rw [Ring.ordFrac_eq_ord _ hc]
  have hnz : c ∈ nonZeroDivisors _ := mem_nonZeroDivisors_of_ne_zero hc
  rw [Ring.ordMonoidWithZeroHom_eq_coe _ hnz (n := (Ring.ord _ c).toNat)
    (ENat.coe_toNat (Ring.ord_ne_top hnz)).symm]

private theorem genericPoint_specializes_of_mem_support (E : MMP.Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ E.support) : E.genericPoint ⤳ x := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
  exact specializes_iff_mem_closure.mpr hx

end StalkIdeal

private theorem ordHom_algebraMap_isUnit {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (y : Y) (hy : Order.coheight y = 1)
    {a : Y.presheaf.stalk y} (ha : IsUnit a) :
    Y.ordHom y hy (algebraMap _ Y.functionField a) = 1 := by
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk y) := krullDimLE_of_coheight_le hy.le
  exact Ring.ordFrac_of_isUnit ha

private theorem ord_algebraMap_of_isUnit {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (y : Y) (hy : Order.coheight y = 1)
    {a : Y.presheaf.stalk y} (ha : IsUnit a) : Y.ord (algebraMap _ Y.functionField a) y = 0 := by
  rw [Scheme.ord_eq_iff hy ((ha.map _).ne_zero), ordHom_algebraMap_isUnit y hy ha]
  rfl

section PrimeCase

open MMP.Intersection

variable {Y T : Scheme.{u}} [IsIntegral Y]
  [IsLocallyNoetherian Y] (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T]
      [IsLocallyNoetherian T]

private theorem eq_of_specializes_of_coheight_eq_one {X : Scheme.{u}} {x y : X} (h : x ⤳ y)
    (hx : Order.coheight x = 1) (hy : Order.coheight y = 1) : x = y := by
  by_contra hne
  by_cases h' : y ⤳ x
  · exact hne (h.antisymm h').eq
  have hlt : y < x := lt_of_le_not_ge h h'
  have := Order.coheight_strictAnti hlt (by rw [hx]; decide)
  rw [hx, hy] at this
  exact lt_irrefl _ this

open MMP.Intersection in
private theorem coheight_fromSpecStalk_span_eq_one {X : Scheme.{u}} [IsIntegral X] {y' : X}
    [IsNoetherianRing (X.presheaf.stalk y')] {p0 : X.presheaf.stalk y'} (hp : Prime p0) :
    Order.coheight (X.fromSpecStalk y'
      ⟨Ideal.span {p0}, (Ideal.span_singleton_prime hp.ne_zero).mpr hp⟩) = 1 := by
  set q : PrimeSpectrum (X.presheaf.stalk y') :=
    ⟨Ideal.span {p0}, (Ideal.span_singleton_prime hp.ne_zero).mpr hp⟩
  have hz : X.fromSpecStalk y' q ⤳ y' := fromSpecStalk_specializes y' q
  have hpz : primeOfSpecializes hz = Ideal.span {p0} :=
    comap_maximalIdeal_stalkSpecializes_fromSpecStalk y' q
  apply le_antisymm (coheight_le_one_of_primeOfSpecializes_eq_span hz hpz)
  rw [Order.one_le_iff_pos, pos_iff_ne_zero]
  intro h0
  have hmax := Order.coheight_eq_zero.mp h0
  have hzη : X.fromSpecStalk y' q = genericPoint X :=
    (Specializes.antisymm (hmax (genericPoint_specializes _)) (genericPoint_specializes _)).eq
  have hbot : primeOfSpecializes hz = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_bot]
    have hc' : X.presheaf.stalkSpecializes hz c ∈ IsLocalRing.maximalIdeal _ := hc
    have hfield : IsField (X.presheaf.stalk (X.fromSpecStalk y' q)) := by
      rw [hzη]; exact Field.toIsField X.functionField
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield, Ideal.mem_bot] at hc'
    exact stalkSpecializes_injective hz (hc'.trans (map_zero _).symm)
  rw [hpz, Ideal.span_singleton_eq_bot] at hbot
  exact hp.ne_zero hbot

open MMP.Intersection in
/-- `primeOfSpecializes` depends only on the generizing point, not on the specialization proof. -/
private theorem primeOfSpecializes_congr {X : Scheme.{u}} {a b y' : X} (e : a = b) (h1 : a ⤳ y')
    (h2 : b ⤳ y') : primeOfSpecializes h1 = primeOfSpecializes h2 := by
  subst e; rfl

open MMP.Intersection Classical in
/-- Along a prime divisor `E` through `y'`, a prime `p₀` of `𝒪_{X,y'}` cutting out the
codimension-one point `z` has order one if `η_E = z` and zero otherwise. -/
private theorem ord_prime_eq_ite {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {y' : X}
    {p0 : X.presheaf.stalk y'} (hp : Prime p0) {z : X} (hz : z ⤳ y')
    (hpz : primeOfSpecializes hz = Ideal.span {p0}) (hz1 : Order.coheight z = 1)
    (E : MMP.Mori.PrimeDivisor X) (hE : y' ∈ E.support) :
    X.ord (algebraMap _ X.functionField p0) E.genericPoint =
      if E.genericPoint = z then 1 else 0 := by
  have hsp := genericPoint_specializes_of_mem_support E hE
  have hspπ : X.presheaf.stalkSpecializes hsp p0 ≠ 0 := by
    intro h0
    exact hp.ne_zero (stalkSpecializes_injective hsp (h0.trans (map_zero _).symm))
  rw [← Scheme.algebraMap_stalkSpecializes hsp, ord_algebraMap_eq_toNat_ord _
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E) hspπ]
  split_ifs with hEz
  · have : primeOfSpecializes hsp = Ideal.span {p0} := by
      rw [← hpz]
      exact primeOfSpecializes_congr hEz hsp hz
    rw [ord_stalkSpecializes_eq_one hsp this]
    rfl
  · have hnot : p0 ∉ primeOfSpecializes hsp := by
      intro hmem
      apply hEz
      have hle : primeOfSpecializes hz ≤ primeOfSpecializes hsp := by
        rw [hpz, Ideal.span_le, Set.singleton_subset_iff]
        exact hmem
      exact (eq_of_specializes_of_coheight_eq_one (specializes_of_primeOfSpecializes_le hz hsp hle)
        hz1 (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E)).symm
    rw [ord_stalkSpecializes_of_notMem hsp hnot]
    rfl

open Classical in
/-- **The prime case of the restriction of a principal divisor.** A prime `p0` of `𝒪_{Y,y'}`,
`y' = j(η_Q)`, with nonzero restriction to `T` is a uniformizer exactly along one prime divisor
`E_π` of `Y` through `y'`, it is a unit along the others, and `v_Q(p0|_T)` is the local
intersection length of `E_π` with `T` at `Q`. -/
private theorem exists_primeDivisor_of_prime (Q : MMP.Mori.PrimeDivisor T)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk (j Q.genericPoint)))
    {p0 : Y.presheaf.stalk (j Q.genericPoint)} (hπ : Prime p0)
    (hψp0 : (j.stalkMap Q.genericPoint).hom p0 ≠ 0) :
    ∃ Eπ : MMP.Mori.PrimeDivisor Y, j Q.genericPoint ∈ Eπ.support ∧
      (∀ E : MMP.Mori.PrimeDivisor Y, j Q.genericPoint ∈ E.support →
        Y.ord (algebraMap _ Y.functionField p0) E.genericPoint = if E = Eπ then 1 else 0) ∧
      T.ord (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
          ((j.stalkMap Q.genericPoint).hom p0)) Q.genericPoint =
        (Eπ.intersectionLength j Q : ℤ) := by
  classical
  have := hreg
  let q : PrimeSpectrum (Y.presheaf.stalk (j Q.genericPoint)) :=
    ⟨Ideal.span {p0}, (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ⟩
  set z := Y.fromSpecStalk (j Q.genericPoint) q
  have hz : z ⤳ (j Q.genericPoint) := fromSpecStalk_specializes (j Q.genericPoint) q
  have hpz : primeOfSpecializes hz = Ideal.span {p0} :=
    comap_maximalIdeal_stalkSpecializes_fromSpecStalk (j Q.genericPoint) q
  have hz1 : Order.coheight z = 1 := coheight_fromSpecStalk_span_eq_one hπ
  let Eπ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hz1
  have hEπ : Eπ.genericPoint = z := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hz1
  have hy'Eπ : (j Q.genericPoint) ∈ Eπ.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    change (j Q.genericPoint) ∈ closure {Eπ.genericPoint}
    rw [hEπ]
    exact hz.mem_closure
  refine ⟨Eπ, hy'Eπ, fun E hE => ?_, ?_⟩
  · rw [ord_prime_eq_ite hπ hz hpz hz1 E hE, ← hEπ]
    exact if_congr AlgebraicGeometry.PrimeDivisor.genericPoint_injective.eq_iff rfl rfl
  · have hC := ord_algebraMap_eq_toNat_ord Q.genericPoint
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q) hψp0
    rw [hC]
    have hsp : Eπ.genericPoint ⤳ (j Q.genericPoint) := hEπ ▸ hz
    unfold MMP.Mori.PrimeDivisor.intersectionLength
    rw [stalkIdeal_primeDivisor Eπ hsp]
    have : primeOfSpecializes hsp = Ideal.span {p0} := by
      rw [← hpz]
      congr 1
    rw [this, Ideal.map_span, Set.image_singleton]
    rfl

private theorem ord_algebraMap_isUnit_at {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {x x' : X} (h : x' ⤳ x) (hx' : Order.coheight x' = 1) {c : X.presheaf.stalk x}
    (hc : IsUnit c) : X.ord (algebraMap _ X.functionField c) x' = 0 := by
  rw [← Scheme.algebraMap_stalkSpecializes h]
  exact ord_algebraMap_of_isUnit x' hx' (hc.map _)

end PrimeCase

variable {Y T : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (j : T ⟶ Y)
  [IsClosedImmersion j] [IsIntegral T] [IsLocallyNoetherian T]

private theorem ord_stalkMap_eq_sum_intersectionLength_mul_ord
    (Q : MMP.Mori.PrimeDivisor T)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk (j Q.genericPoint)))
    (r : Y.presheaf.stalk (j Q.genericPoint)) (hr : (j.stalkMap Q.genericPoint).hom r ≠ 0) :
    ∃ S0 : Finset (MMP.Mori.PrimeDivisor Y),
      (∀ E : MMP.Mori.PrimeDivisor Y, j Q.genericPoint ∈ E.support →
        Y.ord (algebraMap _ Y.functionField r) E.genericPoint ≠ 0 → E ∈ S0) ∧
      ∀ S : Finset (MMP.Mori.PrimeDivisor Y), S0 ⊆ S →
        T.ord (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
            ((j.stalkMap Q.genericPoint).hom r)) Q.genericPoint =
          ∑ E ∈ S, if j Q.genericPoint ∈ E.support then
            (E.intersectionLength j Q : ℤ) * Y.ord (algebraMap _ Y.functionField r) E.genericPoint
          else 0 := by
  classical
  have := hreg
  have := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk (j Q.genericPoint))
  induction r using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd (map_zero _) hr
  | h₂ x hx =>
    have hv : ∀ E : MMP.Mori.PrimeDivisor Y, j Q.genericPoint ∈ E.support →
        Y.ord (algebraMap _ Y.functionField x) E.genericPoint = 0 := fun E hE =>
      ord_algebraMap_isUnit_at (genericPoint_specializes_of_mem_support E hE)
        (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E) hx
    refine ⟨∅, fun E hE hne => (hne (hv E hE)).elim, fun S _ => ?_⟩
    rw [ord_algebraMap_isUnit_at specializes_rfl
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q) (hx.map _)]
    symm
    refine Finset.sum_eq_zero fun E _ => ?_
    split_ifs with hE
    · rw [hv E hE, mul_zero]
    · rfl
  | h₃ a p ha hp ih =>
    have hpa : (j.stalkMap Q.genericPoint).hom p * (j.stalkMap Q.genericPoint).hom a ≠ 0 := by
      rwa [← map_mul]
    obtain ⟨S0, hS0, hf⟩ := ih (right_ne_zero_of_mul hpa)
    obtain ⟨Eπ, hEπ, hv, hT⟩ := exists_primeDivisor_of_prime j Q hreg hp (left_ne_zero_of_mul hpa)
    have hpK : algebraMap _ Y.functionField p ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hp.ne_zero
    have haK : algebraMap _ Y.functionField a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha
    have hmul : ∀ E : MMP.Mori.PrimeDivisor Y,
        Y.ord (algebraMap _ Y.functionField (p * a)) E.genericPoint =
          Y.ord (algebraMap _ Y.functionField p) E.genericPoint +
            Y.ord (algebraMap _ Y.functionField a) E.genericPoint := fun E => by
      rw [map_mul, Scheme.ord_mul hpK haK]
    refine ⟨insert Eπ S0, fun E hE hne => ?_, fun S hS => ?_⟩
    · rw [hmul, hv E hE] at hne
      by_cases h : E = Eπ
      · simp [h]
      · rw [if_neg h, zero_add] at hne
        exact Finset.mem_insert_of_mem (hS0 E hE hne)
    · have hC : algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
          ((j.stalkMap Q.genericPoint).hom p) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (left_ne_zero_of_mul hpa)
      have hC' : algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
          ((j.stalkMap Q.genericPoint).hom a) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (right_ne_zero_of_mul hpa)
      rw [map_mul, map_mul, Scheme.ord_mul hC hC', hT,
        hf S ((Finset.subset_insert _ _).trans hS)]
      have hsplit : ∀ E ∈ S, (if j Q.genericPoint ∈ E.support then (E.intersectionLength j Q : ℤ) *
          Y.ord (algebraMap _ Y.functionField (p * a)) E.genericPoint else 0) =
          (if j Q.genericPoint ∈ E.support then (E.intersectionLength j Q : ℤ) *
            Y.ord (algebraMap _ Y.functionField p) E.genericPoint else 0) +
          (if j Q.genericPoint ∈ E.support then (E.intersectionLength j Q : ℤ) *
            Y.ord (algebraMap _ Y.functionField a) E.genericPoint else 0) := by
        intro E _
        split_ifs
        · rw [hmul, mul_add]
        · rw [add_zero]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single_of_mem Eπ (hS (Finset.mem_insert_self _ _))]
      · rw [if_pos hEπ, hv Eπ hEπ, if_pos rfl, mul_one]
      · intro E _ hE
        split_ifs with h
        · rw [hv E h, if_neg hE, mul_zero]
        · rfl

end CoreRestriction

section RestrictLemmas

open Classical

private theorem stalkMap_eq_zero_iff_aux {X T : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral T] (ι : T ⟶ X) [IsClosedImmersion ι] (q : T)
    (hp : Order.coheight (ι (genericPoint T)) = 1) (c : X.presheaf.stalk (ι q))
    (hc : c ≠ 0) :
    (ι.stalkMap q).hom c = 0 ↔
      1 ≤ X.ord (algebraMap (X.presheaf.stalk (ι q)) X.functionField c) (ι (genericPoint T)) := by
  have hηq : genericPoint T ⤳ q := genericPoint_specializes q
  have hpx : ι (genericPoint T) ⤳ ι q := hηq.map ι.continuous
  have hc' : X.presheaf.stalkSpecializes hpx c ≠ 0 := fun h =>
    hc (Scheme.stalkSpecializes_injective hpx (h.trans (map_zero _).symm))
  rw [← Scheme.algebraMap_stalkSpecializes hpx c, one_le_ord_iff_mem_maximalIdeal hp hc']
  exact stalkMap_eq_zero_iff ι q c

private theorem exists_restrictFF {X T : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral T] [IsLocallyNoetherian T]
    (ι : T ⟶ X) [IsClosedImmersion ι] (P : MMP.Mori.PrimeDivisor X)
    (hηP : ι (genericPoint T) = P.genericPoint)
    (g : X.functionField) (hg : g ≠ 0) (hgP : X.ord g P.genericPoint = 0) :
    ∃ ĝ : T.functionField, ĝ ≠ 0 ∧
      ∀ (Q : MMP.Mori.PrimeDivisor T) (s : X.presheaf.stalk (ι Q.genericPoint)) (_ : s ≠ 0)
        (_ : RingHom.ker (ι.stalkMap Q.genericPoint).hom = Ideal.span {s})
        (_ : IsRegularLocalRing (X.presheaf.stalk (ι Q.genericPoint)))
        (D : MMP.Mori.Divisor X)
        (_ : ∀ E : MMP.Mori.PrimeDivisor X, ι Q.genericPoint ∈ E.support →
          X.ord g E.genericPoint = D.coeff E)
        (_ : (Function.support (MMP.Mori.DivisorWithCoeffs.restrictCoeff ι D)).Finite),
        (D.restrict ι).coeff Q = T.ord ĝ Q.genericPoint := by
  set p := ι (genericPoint T) with hp
  have hp1 : Order.coheight p = 1 := by rw [hηP]; exact P.coheight_genericPoint
  have hgp0 : X.ord g p = 0 := by rw [hηP]; exact hgP
  obtain ⟨ag, hag⟩ := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hp1 hg).mpr hgp0.ge
  obtain ⟨bg, hbg⟩ := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hp1
    (inv_ne_zero hg)).mpr (by rw [ord_inv hg _, hgp0]; simp)
  have hunit : ag * bg = 1 := IsFractionRing.injective (X.presheaf.stalk p) X.functionField
    (by rw [map_mul, hag, hbg, mul_inv_cancel₀ hg, map_one])
  let fη := (ι.stalkMap (genericPoint T)).hom
  refine ⟨algebraMap (T.presheaf.stalk (genericPoint T)) T.functionField (fη ag), ?_, ?_⟩
  · intro h
    have h1 := (map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h
    have := congrArg fη hunit
    rw [map_mul, h1, zero_mul, map_one] at this
    exact zero_ne_one this
  intro Q s hs0 hker hreg D hloc hfin
  classical
  haveI := hreg
  have hηQ : genericPoint T ⤳ Q.genericPoint := genericPoint_specializes _
  have hpx : p ⤳ ι Q.genericPoint := hηQ.map ι.continuous
  have hUFD : UniqueFactorizationMonoid (X.presheaf.stalk (ι Q.genericPoint)) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  let alg := algebraMap (X.presheaf.stalk (ι Q.genericPoint)) X.functionField
  have halginj : Function.Injective alg := IsFractionRing.injective _ _
  obtain ⟨a0, b0, hb0, hab⟩ :=
    IsFractionRing.div_surjective (A := X.presheaf.stalk (ι Q.genericPoint))
      (K := X.functionField) g
  have hb0' : b0 ≠ 0 := nonZeroDivisors.ne_zero hb0
  obtain ⟨a', b', c, hrel, hca, hcb⟩ := UniqueFactorizationMonoid.exists_reduced_factors' a0 b0 hb0'
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hcb
    exact hb0' hcb.symm
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcb
    exact hb0' hcb.symm
  have hcK : alg c ≠ 0 := (map_ne_zero_iff _ halginj).mpr hc0
  have hab' : alg a' / alg b' = g := by
    rw [← hab, ← hca, ← hcb, map_mul, map_mul, mul_div_mul_left _ _ hcK]
  have ha'0 : a' ≠ 0 := by
    rintro rfl
    apply hg
    rw [← hab', map_zero, zero_div]
  have haK : alg a' ≠ 0 := (map_ne_zero_iff _ halginj).mpr ha'0
  have hbK : alg b' ≠ 0 := (map_ne_zero_iff _ halginj).mpr hb'0
  have hpq : X.ord (alg a') p = X.ord (alg b') p := by
    have := ord_mul_inv haK hbK p
    rw [← div_eq_mul_inv, hab', hgp0] at this
    omega
  have hnv : (ι.stalkMap Q.genericPoint).hom a' ≠ 0 ∧ (ι.stalkMap Q.genericPoint).hom b' ≠ 0 := by
    by_contra hcon
    have hz : (ι.stalkMap Q.genericPoint).hom a' = 0 ∧ (ι.stalkMap Q.genericPoint).hom b' = 0 := by
      by_cases h1 : (ι.stalkMap Q.genericPoint).hom a' = 0
      · refine ⟨h1, ?_⟩
        have := (stalkMap_eq_zero_iff_aux ι Q.genericPoint hp1 a' ha'0).mp h1
        exact (stalkMap_eq_zero_iff_aux ι Q.genericPoint hp1 b' hb'0).mpr (hpq ▸ this)
      · have h2 : (ι.stalkMap Q.genericPoint).hom b' = 0 := by
          by_contra h2
          exact hcon ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have := (stalkMap_eq_zero_iff_aux ι Q.genericPoint hp1 b' hb'0).mp h2
        exact (stalkMap_eq_zero_iff_aux ι Q.genericPoint hp1 a' ha'0).mpr (hpq ▸ this)
    have hsa : s ∣ a' := Ideal.mem_span_singleton.mp (hker ▸ RingHom.mem_ker.mpr hz.1)
    have hsb : s ∣ b' := Ideal.mem_span_singleton.mp (hker ▸ RingHom.mem_ker.mpr hz.2)
    have hsu : IsUnit s := hrel hsa hsb
    have hfs : (ι.stalkMap Q.genericPoint).hom s = 0 :=
      RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self s)
    exact not_isUnit_zero (hfs ▸ hsu.map (ι.stalkMap Q.genericPoint).hom)
  let fη := (ι.stalkMap (genericPoint T)).hom
  let algT := algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
  have hTinj : Function.Injective algT := IsFractionRing.injective _ _
  have key : ∀ c : X.presheaf.stalk (ι Q.genericPoint),
      algT ((ι.stalkMap Q.genericPoint).hom c) =
        algebraMap (T.presheaf.stalk (genericPoint T)) T.functionField
          (fη (X.presheaf.stalkSpecializes hpx c)) := by
    intro c
    rw [← Scheme.algebraMap_stalkSpecializes hηQ,
      ← ι.stalkSpecializes_stalkMap_apply (genericPoint T) Q.genericPoint hηQ c]
    have hid : ∀ z : T.presheaf.stalk (genericPoint T),
        @algebraMap _ _ _ _ (stalkFunctionFieldAlgebra T (genericPoint T)) z =
          algebraMap (T.presheaf.stalk (genericPoint T)) T.functionField z := fun z => by
      change (T.presheaf.stalkSpecializes _).hom z = z
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    rw [hid]
  have hspec : X.presheaf.stalkSpecializes hpx a' = ag * X.presheaf.stalkSpecializes hpx b' := by
    apply IsFractionRing.injective (X.presheaf.stalk p) X.functionField
    rw [map_mul, hag, Scheme.algebraMap_stalkSpecializes hpx a',
      Scheme.algebraMap_stalkSpecializes hpx b', ← hab', div_mul_cancel₀ _ hbK]
  have hγ : algT ((ι.stalkMap Q.genericPoint).hom a') =
      algebraMap (T.presheaf.stalk (genericPoint T)) T.functionField (fη ag) *
        algT ((ι.stalkMap Q.genericPoint).hom b') := by
    rw [key a', key b', hspec, map_mul, map_mul]
  have haT2 : algT ((ι.stalkMap Q.genericPoint).hom a') ≠ 0 :=
    (map_ne_zero_iff _ hTinj).mpr hnv.1
  have hbT2 : algT ((ι.stalkMap Q.genericPoint).hom b') ≠ 0 :=
    (map_ne_zero_iff _ hTinj).mpr hnv.2
  have hĝ : algebraMap (T.presheaf.stalk (genericPoint T)) T.functionField (fη ag) =
      algT ((ι.stalkMap Q.genericPoint).hom a') *
        (algT ((ι.stalkMap Q.genericPoint).hom b'))⁻¹ := by
    rw [hγ, mul_assoc, mul_inv_cancel₀ hbT2, mul_one]
  obtain ⟨Sa, hSa, hfa⟩ := ord_stalkMap_eq_sum_intersectionLength_mul_ord ι Q hreg a' hnv.1
  obtain ⟨Sb, hSb, hfb⟩ := ord_stalkMap_eq_sum_intersectionLength_mul_ord ι Q hreg b' hnv.2
  set S : Finset (MMP.Mori.PrimeDivisor X) := D.support ∪ Sa ∪ Sb with hS
  have hDS : D.support ⊆ S := fun E hE => by simp [hS, hE]
  have hSaS : Sa ⊆ S := fun E hE => by simp [hS, hE]
  have hSbS : Sb ⊆ S := fun E hE => by simp [hS, hE]
  rw [MMP.Mori.DivisorWithCoeffs.coeff_restrict ι hfin Q, hĝ, ord_mul_inv haT2 hbT2, hfa S hSaS,
    hfb S hSbS, ← Finset.sum_sub_distrib]
  rw [Finsupp.sum, Finset.sum_subset hDS (fun E _ hE => by
    rw [Finsupp.notMem_support_iff.mp hE, smul_zero])]
  refine Finset.sum_congr rfl fun E _ => ?_
  by_cases hxE : ι Q.genericPoint ∈ E.support
  · rw [if_pos hxE, if_pos hxE, ← mul_sub, nsmul_eq_mul]
    have := ord_mul_inv haK hbK E.genericPoint
    rw [← div_eq_mul_inv, hab'] at this
    rw [← this, hloc E hxE]
    rfl
  · rw [if_neg hxE, if_neg hxE, sub_zero,
      MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem ι E hxE]
    simp

end RestrictLemmas

section Residue

open KaehlerDifferential TensorProduct

/-- At a point with regular local ring of a scheme locally of finite type over a perfect field,
the local ring is formally smooth, Noetherian and essentially of finite type over the field. -/
private theorem stalk_facts_of_isRegularLocalRing {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (x : X)
    (hx : IsRegularLocalRing (X.presheaf.stalk x)) :
    letI := MMP.Mori.stalkAlgebra sX x
    Algebra.FormallySmooth k (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧
      Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  let := MMP.Mori.stalkAlgebra sX x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU' : IsAffineOpen U := hU
  let x' : U := ⟨x, hxU⟩
  let := MMP.Mori.sectionAlgebra sX U
  have := MMP.Mori.finiteType_sectionAlgebra sX hU'
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
  have := MMP.Mori.isScalarTower_section_stalk sX U x'
  have := hU'.isLocalization_stalk x'
  set q := (hU'.primeIdealOf x').asIdeal
  have := Algebra.isSeparableExtension_of_perfectField k q.ResidueField
  have hs : Algebra.IsSmoothAt k q :=
    (Algebra.isSmoothAt_iff_isRegularLocalRing q (X.presheaf.stalk x)).mpr hx
  have : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk x) := .of_isLocalization _ q.primeCompl
  have : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing k _
  refine ⟨?_, IsLocalization.isNoetherianRing q.primeCompl _ inferInstance,
    .comp k Γ(X, U) (X.presheaf.stalk x)⟩
  exact Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
      (X.presheaf.stalk x)).restrictScalars k)

private theorem alt_eq_det_smul {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Fintype ι] [DecidableEq ι] (e : Module.Basis ι R M)
    (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) : f v = e.det v • f e := by
  have : f = e.det.smulRight (f e) := by
    refine e.ext_alternating fun σ hσ => ?_
    let p := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσ)
    have h1 : (fun i => e (σ i)) = ⇑e ∘ ⇑p := rfl
    rw [h1, AlternatingMap.smulRight_apply, f.map_perm, e.det.map_perm, e.det_self]
    rw [Units.smul_def, Units.smul_def, zsmul_eq_mul, mul_one, Int.cast_smul_eq_zsmul]
  conv_lhs => rw [this]
  rfl

private theorem ιMulti_sum_eq_det_smul {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {n : ℕ}
    (c : Matrix (Fin n) (Fin n) R) (u : Fin n → W) :
    exteriorPower.ιMulti R n (fun i => ∑ j, c i j • u j) =
      c.det • exteriorPower.ιMulti R n u := by
  let L : (Fin n → R) →ₗ[R] W := Fintype.linearCombination R u
  let f := (exteriorPower.ιMulti R n (M := W)).compLinearMap L
  have h := alt_eq_det_smul (Pi.basisFun R (Fin n)) f (fun i => c i)
  have e1 : f (fun i => c i) = exteriorPower.ιMulti R n (fun i => ∑ j, c i j • u j) := by
    simp [f, L, Fintype.linearCombination_apply]
  have e2 : f (Pi.basisFun R (Fin n)) = exteriorPower.ιMulti R n u := by
    simp only [f, AlternatingMap.compLinearMap_apply]
    congr 1; funext i
    simp [L, Fintype.linearCombination_apply_single]
  rw [← e1, h, e2, Module.Basis.det_apply]
  congr 1
  rw [← Matrix.det_transpose]
  congr 1

/-- `ιMulti` of a spanning family of `n` vectors generates the `n`-th exterior power. -/
private theorem span_ιMulti_eq_top {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {n : ℕ}
    (e : Fin n → W) (he : Submodule.span R (Set.range e) = ⊤) :
    Submodule.span R {exteriorPower.ιMulti R n e} = ⊤ := by
  rw [eq_top_iff, ← exteriorPower.ιMulti_span R n W, Submodule.span_le]
  rintro - ⟨v, rfl⟩
  have : ∀ i, ∃ c : Fin n → R, ∑ j, c j • e j = v i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).mp (he ▸ Submodule.mem_top)
  choose c hc using this
  have hv : v = fun i => ∑ j, (Matrix.of c) i j • e j := funext fun i => (hc i).symm
  rw [hv, ιMulti_sum_eq_det_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- If `Ω^d_{A/k}` has a generator with nonzero image in `Ω^d_{K/k}` (`d ≠ 0`), then `Ω_{A/k}`
has rank `d`. -/
private theorem finrank_eq_of_generator {k A K : Type*} [CommRing k] [CommRing A] [IsDomain A]
    [Algebra k A] [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K]
    [IsFractionRing A K] [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]] {d : ℕ} (hd : d ≠ 0)
    {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (h0 : MMP.Mori.topFormsMap k A K d σ ≠ 0) : Module.finrank A Ω[A⁄k] = d := by
  have hK := MMP.Mori.finrank_kaehlerDifferential_eq_of_isFractionRing (k := k) (A := A) (K := K)
  have : Module.Finite K Ω[K⁄k] := Module.Finite.of_basis
    ((Module.Free.chooseBasis A Ω[A⁄k]).ofIsLocalizedModule K (nonZeroDivisors A)
      (KaehlerDifferential.map k k A K))
  have hspan := MMP.Mori.span_singleton_topFormsMap (k := k) (K := K) (d := d)
    (nonZeroDivisors A) hσ
  have h1 : Module.finrank K (⋀[K]^d Ω[K⁄k]) = 1 := by
    apply le_antisymm
    · rw [← finrank_top, ← hspan]
      exact (finrank_span_singleton h0).le
    · exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, h0⟩
  rw [exteriorPower.finrank_eq, hK, Nat.choose_eq_one_iff] at h1
  exact h1.resolve_left hd

private theorem map_det_eq_of_row_zero {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (h : ∀ j : Fin n, φ (M 0 j.succ) = 0) :
    φ M.det = φ (M 0 0) * φ (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, map_sum, Fin.sum_univ_succ]
  have : ∑ j : Fin n, φ ((-1) ^ (j.succ : ℕ) * M 0 j.succ *
      (M.submatrix Fin.succ j.succ.succAbove).det) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [map_mul, map_mul, h j, mul_zero, zero_mul]
  rw [this, add_zero, map_mul, map_mul]
  simp [Fin.succAbove_zero]

/-- `Matrix.map` commutes with `det`, in the direction used for rewriting. -/
private theorem det_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) : (M.map f).det = f M.det :=
  (RingHom.map_det f M).symm

section Core

variable {k A K B : Type*} [CommRing k] [CommRing A] [IsDomain A] [Algebra k A] [Field K]
  [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] [Field B] [Algebra k B]
      [Algebra A B] [IsScalarTower k A B]

/-- The image of a combination of differentials under `Ω_A → Ω_R`. -/
private theorem map_sum_smul {R : Type*} [CommRing R] [Algebra k R] [Algebra A R]
    [IsScalarTower k A R]
    {n : ℕ} (c : Fin n → A) (e : Fin n → Ω[A⁄k]) :
    KaehlerDifferential.map k k A R (∑ j, c j • e j) =
      ∑ j, algebraMap A R (c j) • KaehlerDifferential.map k k A R (e j) := by
  simp only [map_sum, LinearMap.map_smul, algebraMap_smul]

/-- **The residue does not depend on the presentation.** -/
private theorem residue_core {n : ℕ} (t0 a0 : A) (x0 : Fin n → A) (ht0 : algebraMap A B t0 = 0)
    (hspan : Submodule.span A (Set.range (Fin.cons (D k A t0) fun i => D k A (x0 i) :
      Fin (n + 1) → Ω[A⁄k])) = ⊤)
    (hne : exteriorPower.ιMulti K (n + 1) (Fin.cons (D k K (algebraMap A K t0))
      fun i => D k K (algebraMap A K (x0 i)) : Fin (n + 1) → Ω[K⁄k]) ≠ 0)
    {t g u : A} (x : Fin n → A) (hu : IsUnit u) (ht : t = u * t0)
    (hτ : (algebraMap A K g * (algebraMap A K t)⁻¹) • exteriorPower.ιMulti K (n + 1)
        (Fin.cons (D k K (algebraMap A K t)) fun i => D k K (algebraMap A K (x i)) :
          Fin (n + 1) → Ω[K⁄k]) =
      (algebraMap A K a0 * (algebraMap A K t0)⁻¹) • exteriorPower.ιMulti K (n + 1)
        (Fin.cons (D k K (algebraMap A K t0)) fun i => D k K (algebraMap A K (x0 i)) :
          Fin (n + 1) → Ω[K⁄k])) :
    algebraMap A B g • exteriorPower.ιMulti B n (fun i => D k B (algebraMap A B (x i))) =
      algebraMap A B a0 • exteriorPower.ιMulti B n (fun i => D k B (algebraMap A B (x0 i))) := by
  classical
  set e : Fin (n + 1) → Ω[A⁄k] := Fin.cons (D k A t0) fun i => D k A (x0 i) with he
  have hmem : ∀ ω : Ω[A⁄k], ∃ c : Fin (n + 1) → A, ∑ j, c j • e j = ω := fun ω =>
    (Submodule.mem_span_range_iff_exists_fun A).mp (hspan ▸ Submodule.mem_top)
  obtain ⟨c, hc⟩ := hmem (D k A u)
  choose r hr using fun i => hmem (D k A (x i))
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
    Fin.cons (fun j => (if j = 0 then u else 0) + t0 * c j) r
  have hM0 : ∀ j, M 0 j = (if j = 0 then u else 0) + t0 * c j := fun j => rfl
  have hMs : ∀ i j, M i.succ j = r i j := fun i j => rfl
  -- the rows of `M` express `dt, dx_i` in terms of `e`
  have hrow : ∀ i, ∑ j, M i j • e j = (Fin.cons (D k A t) fun i => D k A (x i) :
      Fin (n + 1) → Ω[A⁄k]) i := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [hM0, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_smul, ← Finset.smul_sum, hc,
        Fin.cons_zero, ht, Derivation.leibniz]
      simp only [he, Fin.cons_zero]
    · simp only [hMs, hr, Fin.cons_succ]
  -- the `K`-side
  have hK : (Fin.cons (D k K (algebraMap A K t)) fun i => D k K (algebraMap A K (x i)) :
      Fin (n + 1) → Ω[K⁄k]) = fun i => ∑ j, (M.map (algebraMap A K)) i j •
        (Fin.cons (D k K (algebraMap A K t0)) fun i => D k K (algebraMap A K (x0 i)) :
          Fin (n + 1) → Ω[K⁄k]) j := by
    funext i
    have := congrArg (KaehlerDifferential.map k k A K) (hrow i)
    rw [map_sum_smul] at this
    calc _ = KaehlerDifferential.map k k A K ((Fin.cons (D k A t) fun i => D k A (x i) :
          Fin (n + 1) → Ω[A⁄k]) i) := by refine Fin.cases ?_ (fun i => ?_) i <;> simp
      _ = _ := this.symm
      _ = _ := Finset.sum_congr rfl fun j _ => by
        rw [Matrix.map_apply]
        congr 1
        refine Fin.cases ?_ (fun j => ?_) j <;> simp [he]
  rw [hK, ιMulti_sum_eq_det_smul, det_map, smul_smul] at hτ
  have hT0 : algebraMap A K t0 ≠ 0 := by
    intro h0
    apply hne
    apply AlternatingMap.map_coord_zero _ (0 : Fin (n + 1))
    simp [h0]
  have hcoef := smul_left_injective K hne hτ
  have hT : algebraMap A K t = algebraMap A K u * algebraMap A K t0 := by rw [ht, map_mul]
  have hkey : g * M.det = a0 * u := by
    apply IsFractionRing.injective A K
    have hu0 : algebraMap A K u ≠ 0 := (hu.map _).ne_zero
    rw [hT] at hcoef
    field_simp at hcoef
    rw [map_mul, map_mul]
    linear_combination hcoef
  -- the `B`-side
  set φ := algebraMap A B
  have hrow0 : ∀ j : Fin n, φ (M 0 j.succ) = 0 := fun j => by
    rw [hM0]; simp [ht0]
  have hdet := map_det_eq_of_row_zero φ M hrow0
  rw [hM0, if_pos rfl] at hdet
  simp only [map_add, map_mul, ht0, zero_mul, add_zero] at hdet
  have hB : (fun i => D k B (φ (x i))) = fun i => ∑ l, ((M.submatrix Fin.succ Fin.succ).map φ) i l •
      (fun l => D k B (φ (x0 l))) l := by
    funext i
    have := congrArg (KaehlerDifferential.map k k A B) (hrow i.succ)
    rw [map_sum_smul, Fin.sum_univ_succ] at this
    simp only [Fin.cons_succ, KaehlerDifferential.map_D, Fin.cons_zero, he] at this
    rw [← this]
    simp [φ, ht0, hMs]
  rw [hB, ιMulti_sum_eq_det_smul, det_map, smul_smul]
  congr 1
  have h2 := congrArg φ hkey
  rw [map_mul, map_mul, hdet] at h2
  have hu' : IsUnit (φ u) := hu.map φ
  apply hu'.mul_right_cancel
  linear_combination h2

end Core

/-- **Nakayama**, for a surjection `A → B` of local rings: a family whose image in `B ⊗ M` is a
basis spans `M`. -/
private theorem span_eq_top_of_isBasis_tmul {A B M : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Nontrivial B] [Algebra A B] (hsurj : Function.Surjective (algebraMap A B))
    [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M] {m : ℕ}
    (hm : Module.finrank A M = m) (v : Fin m → M)
    (hli : LinearIndependent B (fun i => (1 : B) ⊗ₜ[A] v i))
    (hsp : Submodule.span B (Set.range fun i => (1 : B) ⊗ₜ[A] v i) = ⊤) :
    Submodule.span A (Set.range v) = ⊤ := by
  classical
  let b₀ := Module.Free.chooseBasis A M
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A M) = m := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hm]
  let b : Module.Basis (Fin m) A M := b₀.reindex (Fintype.equivFinOfCardEq hcard)
  let bB := Algebra.TensorProduct.basis B b
  have hdetB := (bB.is_basis_iff_det).mp ⟨hli, hsp⟩
  have hmat : bB.toMatrix (fun i => (1 : B) ⊗ₜ[A] v i) =
      (b.toMatrix v).map (algebraMap A B) := by
    ext i j
    simp [Module.Basis.toMatrix_apply, bB, Algebra.TensorProduct.basis_repr_tmul]
  rw [Module.Basis.det_apply, hmat, det_map, ← Module.Basis.det_apply] at hdetB
  have hdet : IsUnit (b.det v) := by
    obtain ⟨U, hU⟩ := hdetB
    obtain ⟨w', hw'⟩ := hsurj (↑U⁻¹ : B)
    have hk : b.det v * w' - 1 ∈ RingHom.ker (algebraMap A B) := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, hw', ← hU, Units.mul_inv, sub_self]
    have hker : RingHom.ker (algebraMap A B) ≤ IsLocalRing.maximalIdeal A :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    by_contra hnu
    have h1 : b.det v * w' ∈ IsLocalRing.maximalIdeal A :=
      Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    have h2 := Ideal.sub_mem _ h1 (hker hk)
    rw [sub_sub_cancel] at h2
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  exact ((b.is_basis_iff_det).mpr hdet).2

/-- **Coordinates adapted to a principal smooth quotient of a local ring.** -/
private theorem exists_coordinates_local {k A C : Type*} [Field k] [CommRing A] [IsDomain A]
    [IsLocalRing A] [Algebra k A] [Algebra.FormallySmooth k A] [Module.Free A Ω[A⁄k]]
    [Module.Finite A Ω[A⁄k]] [CommRing C] [IsLocalRing C] [Algebra k C] [Algebra A C]
    [IsScalarTower k A C] [Algebra.FormallySmooth k C] [Module.FinitePresentation C Ω[C⁄k]]
    (hsurj : Function.Surjective (algebraMap A C)) {t0 : A} (ht0 : t0 ≠ 0)
    (hker : RingHom.ker (algebraMap A C) = Ideal.span {t0}) {n : ℕ}
    (hrank : Module.finrank A Ω[A⁄k] = n + 1) :
    ∃ x0 : Fin n → A, Submodule.span A (Set.range (Fin.cons (D k A t0) fun i => D k A (x0 i) :
        Fin (n + 1) → Ω[A⁄k])) = ⊤ ∧
      LinearIndependent C (fun i => D k C (algebraMap A C (x0 i))) ∧
      Submodule.span C (Set.range fun i => D k C (algebraMap A C (x0 i))) = ⊤ := by
  classical
  set φ := algebraMap A C with hφ
  have ht0mem : t0 ∈ RingHom.ker φ := hker ▸ Ideal.mem_span_singleton_self t0
  have hφt0 : φ t0 = 0 := RingHom.mem_ker.mp ht0mem
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k) (P := A) (A := C)
    hsurj).mp inferInstance
  set w0 : C ⊗[A] Ω[A⁄k] := (1 : C) ⊗ₜ D k A t0 with hw0def
  have hw0 : kerCotangentToTensor k A C ((RingHom.ker φ).toCotangent ⟨t0, ht0mem⟩) = w0 := by
    rw [kerCotangentToTensor_toCotangent]
  -- `c • w0 = 0` forces `c = 0`
  have hw0inj : ∀ c : C, c • w0 = 0 → c = 0 := by
    intro c hc
    obtain ⟨c', rfl⟩ := hsurj c
    have h1 : c' • (RingHom.ker φ).toCotangent ⟨t0, ht0mem⟩ = 0 := by
      have h2 := congrArg l (show c' • w0 = 0 by rw [← algebraMap_smul C c' w0]; exact hc)
      rw [map_smul, map_zero, ← hw0] at h2
      rw [← h2]
      exact congrArg (c' • ·) (LinearMap.congr_fun hl _).symm
    rw [← map_smul, Ideal.toCotangent_eq_zero] at h1
    have h3 : c' * t0 ∈ (Ideal.span {t0}) ^ 2 := by rw [← hker]; exact h1
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h3
    obtain ⟨d, hd⟩ := h3
    have h4 : c' = t0 * d := by
      apply mul_right_cancel₀ ht0
      rw [hd]; ring
    rw [h4, map_mul, hφt0, zero_mul]
  -- the differentials of `C` are free and generated by the `d(φ a)`
  have : Module.Free C Ω[C⁄k] := Module.free_of_flat_of_isLocalRing
  have hspanC : Submodule.span C (Set.range fun a : A => D k C (φ a)) = ⊤ := by
    rw [eq_top_iff, ← span_range_derivation, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨a, rfl⟩ := hsurj c
    exact Submodule.subset_span ⟨a, rfl⟩
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _ hspanC
  have : Finite κ := Module.Finite.finite_basis b
  let : Fintype κ := Fintype.ofFinite κ
  -- the family `1 ⊗ dt₀, 1 ⊗ d(a i)` is a basis of `C ⊗ Ω_A`
  let w : Fin 1 ⊕ κ → C ⊗[A] Ω[A⁄k] := Sum.elim (fun _ => w0) (fun i => (1 : C) ⊗ₜ D k A (a i))
  have hmapw : ∀ i, KaehlerDifferential.mapBaseChange k A C (w (Sum.inr i)) = b i := by
    intro i
    simp [w, hb, KaehlerDifferential.mapBaseChange_tmul, hφ]
  have hmapw0 : KaehlerDifferential.mapBaseChange k A C w0 = 0 := by
    simp [w0, KaehlerDifferential.mapBaseChange_tmul, ← hφ, hφt0]
  have hker' : ∀ z, KaehlerDifferential.mapBaseChange k A C z = 0 → ∃ c : C, z = c • w0 := by
    intro z hz
    obtain ⟨y, rfl⟩ := (exact_kerCotangentToTensor_mapBaseChange k A C hsurj z).mp hz
    obtain ⟨⟨e, he⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
    rw [hker, Ideal.mem_span_singleton'] at he
    obtain ⟨d, rfl⟩ := he
    refine ⟨φ d, ?_⟩
    rw [kerCotangentToTensor_toCotangent, Derivation.leibniz, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← algebraMap_smul C t0,
      ← algebraMap_smul C d, ← hφ, hφt0, zero_smul, add_zero]
  have hli : LinearIndependent C w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hm := congrArg (KaehlerDifferential.mapBaseChange k A C) hg
    rw [map_sum, map_zero, Fintype.sum_sum_type] at hm
    simp only [map_smul, w, Sum.elim_inl, Sum.elim_inr, hmapw0, smul_zero,
      Finset.sum_const_zero, zero_add] at hm
    have hgr : ∀ i, g (Sum.inr i) = 0 := by
      have := (Fintype.linearIndependent_iff.mp b.linearIndependent) (fun i => g (Sum.inr i))
      refine this ?_
      rw [← hm]
      exact Finset.sum_congr rfl fun i _ => by rw [← hmapw i]; rfl
    have hgl : g (Sum.inl 0) = 0 := by
      apply hw0inj
      rw [Fintype.sum_sum_type] at hg
      simpa [w, hgr] using hg
    rintro (i | i)
    · rw [Subsingleton.elim i 0]; exact hgl
    · exact hgr i
  have hsp : Submodule.span C (Set.range w) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    set c := b.repr (KaehlerDifferential.mapBaseChange k A C z)
    have hz : KaehlerDifferential.mapBaseChange k A C
        (z - ∑ i, c i • w (Sum.inr i)) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul, hmapw]
      rw [b.sum_repr, sub_self]
    obtain ⟨c0, hc0⟩ := hker' _ hz
    have : z = c0 • w (Sum.inl 0) + ∑ i, c i • w (Sum.inr i) := by
      show z = c0 • w0 + _
      rw [← hc0, sub_add_cancel]
    rw [this]
    refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  have hcard : Fintype.card κ = n := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge)
    rw [Module.finrank_baseChange, hrank, Fintype.card_sum, Fintype.card_fin] at this
    omega
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  have hbe : (fun i => D k C (φ (a (e.symm i)))) = b ∘ e.symm := by
    funext i
    simp [hb]
  refine ⟨fun i => a (e.symm i), ?_, ?_, ?_⟩
  · let σ : Fin (n + 1) → Fin 1 ⊕ κ := Fin.cons (Sum.inl 0) fun i => Sum.inr (e.symm i)
    have heq : w ∘ σ = fun i => (1 : C) ⊗ₜ[A]
        (Fin.cons (D k A t0) fun i => D k A (a (e.symm i)) : Fin (n + 1) → Ω[A⁄k]) i := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [σ, w, w0]
      · simp [σ, w]
    have hσ : Function.Bijective σ := by
      refine ⟨?_, ?_⟩
      · rw [Fin.cons_injective_iff]
        exact ⟨by simp, Sum.inr_injective.comp e.symm.injective⟩
      · rintro (i | i)
        · exact ⟨0, by rw [Subsingleton.elim i 0]; rfl⟩
        · exact ⟨(e i).succ, by simp [σ]⟩
    apply span_eq_top_of_isBasis_tmul hsurj hrank
    · exact heq ▸ hli.comp σ hσ.1
    · rw [← heq, Set.range_comp, hσ.2.range_eq, Set.image_univ, hsp]
  · rw [hbe]
    exact b.linearIndependent.comp _ e.symm.injective
  · rw [hbe, Set.range_comp, e.symm.surjective.range_eq, Set.image_univ, b.span_eq]

section Stalks

variable {k : Type u} [Field k] {Y T : Scheme.{u}} (sY : Y ⟶ Spec (.of k))

private theorem isScalarTower_stalkMap (j : T ⟶ Y) (x : T) :
    letI := MMP.Mori.stalkAlgebra sY (j x)
    letI := MMP.Mori.stalkAlgebra (j ≫ sY) x
    letI := (j.stalkMap x).hom.toAlgebra
    IsScalarTower k (Y.presheaf.stalk (j x)) (T.presheaf.stalk x) := by
  let := MMP.Mori.stalkAlgebra sY (j x)
  let := MMP.Mori.stalkAlgebra (j ≫ sY) x
  let := (j.stalkMap x).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ sY).appTop ≫
        T.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫
        Y.presheaf.germ ⊤ (j x) (TopologicalSpace.Opens.mem_top _)) ≫ j.stalkMap x := by
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Hom.germ_stalkMap]
    rfl
  exact congrArg CommRingCat.Hom.hom h

variable [IsIntegral Y] [IsLocallyNoetherian Y]

variable {sY}

private theorem ordHom_algebraMap_irreducible (y : Y) (hy : Order.coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] {ϖ : Y.presheaf.stalk y}
    (hϖ : Irreducible ϖ) :
    Y.ordHom y hy (algebraMap _ Y.functionField ϖ) = WithZero.exp 1 :=
  Ring.ordFrac_irreducible hϖ

/-- A uniformizer of the local ring at a codimension-one point has order one. -/
private theorem ord_algebraMap_irreducible (y : Y) (hy : Order.coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] {ϖ : Y.presheaf.stalk y}
    (hϖ : Irreducible ϖ) : Y.ord (algebraMap _ Y.functionField ϖ) y = 1 := by
  rw [Scheme.ord_eq_iff hy ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero),
    ordHom_algebraMap_irreducible y hy hϖ]
  rfl

/-- An element of order one in the local ring at a codimension-one point is a unit multiple of
a uniformizer. -/
private theorem exists_isUnit_eq_mul_of_ord_eq_one (y : Y) (hy : Order.coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] {ϖ : Y.presheaf.stalk y}
    (hϖ : Irreducible ϖ) {t : Y.presheaf.stalk y}
    (ht : Y.ord (algebraMap _ Y.functionField t) y = 1) :
    ∃ v : Y.presheaf.stalk y, IsUnit v ∧ t = v * ϖ := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  obtain ⟨m, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hϖ
  have hne : algebraMap _ Y.functionField (w * ϖ ^ m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht0
  rw [Scheme.ord_eq_iff hy hne, map_mul, map_mul, map_pow, map_pow,
    ordHom_algebraMap_irreducible y hy hϖ, ordHom_algebraMap_isUnit y hy w.isUnit, one_mul,
    ← WithZero.exp_nsmul, WithZero.exp_eq_coe_ofAdd] at ht
  have hm : (m : ℤ) • (1 : ℤ) = 1 := by exact_mod_cast WithZero.coe_injective ht
  obtain rfl : m = 1 := by simpa using hm
  exact ⟨w, w.isUnit, by rw [pow_one]⟩

/-- A rational function of order `-1` at a codimension-one point is `a / ϖ` for a unit `a`. -/
private theorem exists_isUnit_eq_div_of_ord_eq_neg_one (y : Y) (hy : Order.coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] {ϖ : Y.presheaf.stalk y}
    (hϖ : Irreducible ϖ) {f : Y.functionField} (hf0 : f ≠ 0) (hf : Y.ord f y = -1) :
    ∃ a : Y.presheaf.stalk y, IsUnit a ∧
      f = algebraMap _ Y.functionField a * (algebraMap _ Y.functionField ϖ)⁻¹ := by
  obtain ⟨z, w, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hf0
  rw [Scheme.ord_eq_iff hy hf0, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
    ordHom_algebraMap_irreducible y hy hϖ, ordHom_algebraMap_isUnit y hy w.isUnit, one_mul,
    ← WithZero.exp_zsmul, WithZero.exp_eq_coe_ofAdd] at hf
  have hz : z • (1 : ℤ) = -1 := by exact_mod_cast WithZero.coe_injective hf
  obtain rfl : z = -1 := by simpa using hz
  exact ⟨w, w.isUnit, by rw [Units.smul_def, Algebra.smul_def, zpow_neg_one]⟩

end Stalks

private theorem ιMulti_ne_zero_of_linearIndependent {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W]
    {n : ℕ} {v : Fin n → W} (hv : LinearIndependent K v) : exteriorPower.ιMulti K n v ≠ 0 := by
  classical
  let b := Module.Basis.span hv
  have hb : (fun i => ((b i : Submodule.span K (Set.range v)) : W)) = v := by
    funext i
    simp [b, Module.Basis.span_apply]
  have hmap : exteriorPower.map n (Submodule.span K (Set.range v)).subtype
      (exteriorPower.ιMulti K n b) = exteriorPower.ιMulti K n v := by
    rw [exteriorPower.map_apply_ιMulti]
    exact congrArg _ hb
  intro h0
  have h1 : exteriorPower.ιMulti K n b = 0 := by
    apply exteriorPower.map_injective_field (n := n) (Submodule.injective_subtype _)
    rw [hmap, h0, map_zero]
  have h2 := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) h1
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero, b.det_self] at h2
  exact one_ne_zero h2

private theorem eq_smul_tprod_iff {K M : Type*} [CommSemiring K] [AddCommMonoid M] [Module K M]
    (a : TensorPower K 1 M) (c : K) (w : M) :
    a = c • PiTensorProduct.tprod K (fun _ : Fin 1 => w) ↔
      PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => M) 0 a = c • w := by
  rw [← (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => M) 0).injective.eq_iff,
    map_smul, PiTensorProduct.subsingletonEquiv_apply_tprod]

private theorem eq_smul_tprod_smul_iff {K M : Type*} [CommSemiring K] [AddCommMonoid M]
    [Module K M] (a : TensorPower K 1 M) (c d : K) (w : M) :
    a = c • PiTensorProduct.tprod K (fun _ : Fin 1 => d • w) ↔
      PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => M) 0 a = (c * d) • w := by
  rw [eq_smul_tprod_iff, mul_smul]

section Presentation

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [IsLocallyNoetherian Y]

/-- A form with a simple pole at `y` forces the top forms of `𝒪_{Y,y}` to have a generator with
nonzero image in the rational forms. -/
private theorem exists_generator_of_ordAt_eq_neg_one (y : Y) {d : ℕ}
    (τ : RationalPluriForms sY d 1)
    (hτ : (letI := stalkAlgebra sY y; letI := functionFieldAlgebra sY;
      haveI := isScalarTower_stalk_functionField sY y
      ordAt (k := k) (d := d) (m := 1) (Y.presheaf.stalk y) (fun f => Y.ord f y) τ) = -1) :
    letI := stalkAlgebra sY y; letI := functionFieldAlgebra sY
    haveI := isScalarTower_stalk_functionField sY y
    ∃ σ : ⋀[Y.presheaf.stalk y]^d Ω[Y.presheaf.stalk y⁄k],
      Submodule.span (Y.presheaf.stalk y) {σ} = ⊤ ∧
        topFormsMap k (Y.presheaf.stalk y) Y.functionField d σ ≠ 0 := by
  classical
  by_contra h
  simp only [ordAt, dif_neg h] at hτ
  exact absurd hτ (by decide)

/-- A presentation `τ = a₀ · dϖ/ϖ ∧ dx₀` from any coordinates `(ϖ, x₀)` at a codimension-one
point where `τ` has a simple pole. -/
private theorem exists_unit_presentation (y : Y) (hy : Order.coheight y = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] {n : ℕ}
    (τ : RationalPluriForms sY (n + 1) 1) (hτ0 : τ ≠ 0)
    (hτy : (letI := stalkAlgebra sY y; letI := functionFieldAlgebra sY;
      haveI := isScalarTower_stalk_functionField sY y
      ordAt (k := k) (d := n + 1) (m := 1) (Y.presheaf.stalk y) (fun f => Y.ord f y) τ) = -1)
    (ϖ : Y.presheaf.stalk y) (x0 : Fin n → Y.presheaf.stalk y) (hϖ : Irreducible ϖ)
    (hspan : letI := stalkAlgebra sY y
      Submodule.span (Y.presheaf.stalk y) (Set.range
        (Fin.cons (D k _ ϖ) fun i => D k _ (x0 i) : Fin (n + 1) → Ω[Y.presheaf.stalk y⁄k])) = ⊤) :
    letI := functionFieldAlgebra sY
    ∃ a0 : Y.presheaf.stalk y, IsUnit a0 ∧
      exteriorPower.ιMulti Y.functionField (n + 1)
          (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
            fun i => D k Y.functionField (algebraMap _ _ (x0 i))) ≠ 0 ∧
      PiTensorProduct.subsingletonEquiv (R := Y.functionField)
          (s := fun _ : Fin 1 => ⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k]) 0 τ =
        (algebraMap _ Y.functionField a0 * (algebraMap _ Y.functionField ϖ)⁻¹) •
          exteriorPower.ιMulti Y.functionField (n + 1)
            (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
              fun i => D k Y.functionField (algebraMap _ _ (x0 i))) := by
  classical
  let := stalkAlgebra sY y
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY y
  obtain ⟨σ, hσ, hσ0⟩ := exists_generator_of_ordAt_eq_neg_one sY y τ hτy
  set e : Fin (n + 1) → Ω[Y.presheaf.stalk y⁄k] := Fin.cons (D k _ ϖ) fun i => D k _ (x0 i)
  have hgen := span_ιMulti_eq_top e hspan
  have himage : topFormsMap k _ Y.functionField (n + 1) (exteriorPower.ιMulti _ (n + 1) e) =
      exteriorPower.ιMulti Y.functionField (n + 1)
          (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
            fun i => D k Y.functionField (algebraMap _ _ (x0 i))) := by
    rw [topFormsMap_ιMulti]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [e]
  have hω0 : topFormsMap k _ Y.functionField (n + 1) (exteriorPower.ιMulti _ (n + 1) e) ≠ 0 := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (hgen ▸ Submodule.mem_top (x := σ))
    intro h0
    apply hσ0
    rw [map_smul, h0, smul_zero]
  have hord := ordAt_eq (k := k) (A := Y.presheaf.stalk y) (v := fun f => Y.ord f y) (m := 1)
    (fun _ _ hx hy' => Scheme.ord_mul hx hy') (fun _ ha => ord_algebraMap_of_isUnit y hy ha) hgen
    hω0 τ
  set f := formCoeff (k := k) (m := 1) (Y.presheaf.stalk y) hgen hω0 τ
  have hf : f ≠ 0 := fun h0 => hτ0 ((formCoeff_eq_zero_iff (m := 1) hgen hω0 τ).mp h0)
  obtain ⟨a0, ha0, hfa⟩ := exists_isUnit_eq_div_of_ord_eq_neg_one y hy hϖ hf (hord ▸ hτy)
  refine ⟨a0, ha0, himage ▸ hω0, ?_⟩
  have hτf := (formCoeff_smul_basis (k := k) (m := 1) (A := Y.presheaf.stalk y) hgen hω0 τ).symm
  rw [← hfa, ← himage]
  have hb := ZTensorPower.basis_ofNat (topFormsBasis (Y.presheaf.stalk y) hgen hω0) 1
  rw [topFormsBasis_apply] at hb
  exact (eq_smul_tprod_iff τ f _).mp (hτf.trans (congrArg (f • ·) hb))

end Presentation

section Main

variable {k : Type u} [Field k] {Y T : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [IsLocallyNoetherian Y] (j : T ⟶ Y) [IsIntegral T]

private theorem ordForm_eq_ordAt (P : MMP.Mori.PrimeDivisor Y) {d : ℕ} {m : ℤ}
    (τ : RationalPluriForms sY d m) (y : Y) (hy : y = P.genericPoint) :
    P.ordForm τ = (letI := stalkAlgebra sY y; letI := functionFieldAlgebra sY;
      haveI := isScalarTower_stalk_functionField sY y
      ordAt (k := k) (Y.presheaf.stalk y) (fun f => Y.ord f y) τ) := by
  subst hy; rfl

private theorem isPoincareResidue_iff {n : ℕ} (τ : RationalPluriForms sY (n + 1) 1)
    (ρ : RationalPluriForms (j ≫ sY) n 1) :
    MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ ↔
      (letI := functionFieldAlgebra sY
      letI := functionFieldAlgebra (j ≫ sY)
      ∃ (t g : Y.presheaf.stalk (j (genericPoint T)))
        (x : Fin n → Y.presheaf.stalk (j (genericPoint T))),
        Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1 ∧
        PiTensorProduct.subsingletonEquiv (R := Y.functionField)
            (s := fun _ : Fin 1 => ⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k]) 0 τ =
          (algebraMap _ Y.functionField g * (algebraMap _ Y.functionField t)⁻¹) •
            exteriorPower.ιMulti Y.functionField (n + 1)
              (Fin.cons (D k Y.functionField (algebraMap _ _ t))
                fun i => D k Y.functionField (algebraMap _ _ (x i))) ∧
        PiTensorProduct.subsingletonEquiv (R := T.functionField)
            (s := fun _ : Fin 1 => ⋀[T.functionField]^n Ω[T.functionField⁄k]) 0 ρ =
          (j.stalkMap (genericPoint T)).hom g • exteriorPower.ιMulti T.functionField n
            fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x i))) := by
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  unfold MMP.Fourfold.IsPoincareResidue
  refine exists_congr fun t => exists_congr fun g => exists_congr fun x => and_congr Iff.rfl
    (and_congr ?_ ?_)
  · exact eq_smul_tprod_smul_iff _ _ _ _
  · exact eq_smul_tprod_iff _ _ _

private theorem exists_residue_data [PerfectField k] [LocallyOfFiniteType sY] [IsNormal Y]
    [IsClosedImmersion j]
    (P : MMP.Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint) {n : ℕ}
    (τ : RationalPluriForms sY (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1) :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra sY
    letI := functionFieldAlgebra (j ≫ sY)
    ∃ (ϖ a0 : Y.presheaf.stalk (j (genericPoint T)))
      (x0 : Fin n → Y.presheaf.stalk (j (genericPoint T))),
      Irreducible ϖ ∧ IsUnit a0 ∧
      Submodule.span (Y.presheaf.stalk (j (genericPoint T))) (Set.range
        (Fin.cons (D k _ ϖ) fun i => D k _ (x0 i) :
          Fin (n + 1) → Ω[Y.presheaf.stalk (j (genericPoint T))⁄k])) = ⊤ ∧
      LinearIndependent T.functionField
        (fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x0 i))) ∧
      Submodule.span T.functionField
        (Set.range fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x0 i))) = ⊤ ∧
      exteriorPower.ιMulti Y.functionField (n + 1)
          (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
            fun i => D k Y.functionField (algebraMap _ _ (x0 i))) ≠ 0 ∧
      PiTensorProduct.subsingletonEquiv (R := Y.functionField)
          (s := fun _ : Fin 1 => ⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k]) 0 τ =
        (algebraMap _ Y.functionField a0 * (algebraMap _ Y.functionField ϖ)⁻¹) •
          exteriorPower.ιMulti Y.functionField (n + 1)
            (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
              fun i => D k Y.functionField (algebraMap _ _ (x0 i))) ∧
      Module.finrank Y.functionField Ω[Y.functionField⁄k] = n + 1 ∧
      Module.Finite Y.functionField Ω[Y.functionField⁄k] := by
  classical
  have hy : Order.coheight (j (genericPoint T)) = 1 := by rw [hP]; exact P.coheight_genericPoint
  set y := j (genericPoint T) with hydef
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hy
  let := stalkAlgebra sY y
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY y
  let := functionFieldAlgebra (j ≫ sY)
  let := (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalkMap sY j (genericPoint T)
  obtain ⟨hfsA, -, hefA⟩ := stalk_facts_of_isRegularLocalRing sY y inferInstance
  obtain ⟨hfsB, -, hefB⟩ := stalk_facts_of_isRegularLocalRing (j ≫ sY) (genericPoint T)
    (inferInstanceAs (IsRegularLocalRing T.functionField))
  have : Module.Free (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k] :=
    Module.free_of_flat_of_isLocalRing
  have hsurj : Function.Surjective
      (algebraMap (Y.presheaf.stalk y) (T.presheaf.stalk (genericPoint T))) :=
    j.stalkMap_surjective _
  rw [ordForm_eq_ordAt sY P τ y hP] at hτ
  obtain ⟨σ, hσ, hσ0⟩ := exists_generator_of_ordAt_eq_neg_one sY y τ hτ
  have hrank := finrank_eq_of_generator (Nat.succ_ne_zero n) hσ hσ0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk y)
  have hker : RingHom.ker (algebraMap (Y.presheaf.stalk y) (T.presheaf.stalk (genericPoint T))) =
      Ideal.span {ϖ} :=
    (IsLocalRing.ker_eq_maximalIdeal _ hsurj).trans
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ)
  obtain ⟨x0, hspan, hli, hspanB⟩ := exists_coordinates_local (k := k) hsurj hϖ.ne_zero hker hrank
  obtain ⟨a0, ha0, hne, hτE⟩ := exists_unit_presentation sY y hy τ hτ0 hτ ϖ x0 hϖ hspan
  refine ⟨ϖ, a0, x0, hϖ, ha0, hspan, hli, hspanB, hne, hτE, ?_, ?_⟩
  · exact (MMP.Mori.finrank_kaehlerDifferential_eq_of_isFractionRing (k := k)
      (A := Y.presheaf.stalk y) (K := Y.functionField)).trans hrank
  · exact Module.Finite.of_basis
      ((Module.Free.chooseBasis (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄k]).ofIsLocalizedModule
        Y.functionField (nonZeroDivisors _) (KaehlerDifferential.map k k _ Y.functionField))

/-- Every residue is the residue `ā₀ · dx̄₀` of a fixed presentation `(ϖ, a₀, x₀)`. -/
private theorem residue_eq_of_isPoincareResidue [IsClosedImmersion j] {n : ℕ}
    (hy : Order.coheight (j (genericPoint T)) = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk (j (genericPoint T)))]
    (τ : RationalPluriForms sY (n + 1) 1) {ρ : RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ)
    (ϖ a0 : Y.presheaf.stalk (j (genericPoint T)))
    (x0 : Fin n → Y.presheaf.stalk (j (genericPoint T))) (hϖ : Irreducible ϖ)
    (hspan : letI := stalkAlgebra sY (j (genericPoint T))
      Submodule.span (Y.presheaf.stalk (j (genericPoint T))) (Set.range
        (Fin.cons (D k _ ϖ) fun i => D k _ (x0 i) :
          Fin (n + 1) → Ω[Y.presheaf.stalk (j (genericPoint T))⁄k])) = ⊤)
    (hne : letI := functionFieldAlgebra sY
      exteriorPower.ιMulti Y.functionField (n + 1)
          (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
            fun i => D k Y.functionField (algebraMap _ _ (x0 i))) ≠ 0)
    (hτE : letI := functionFieldAlgebra sY
      PiTensorProduct.subsingletonEquiv (R := Y.functionField)
          (s := fun _ : Fin 1 => ⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k]) 0 τ =
        (algebraMap _ Y.functionField a0 * (algebraMap _ Y.functionField ϖ)⁻¹) •
          exteriorPower.ιMulti Y.functionField (n + 1)
            (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
              fun i => D k Y.functionField (algebraMap _ _ (x0 i)))) :
    letI := functionFieldAlgebra (j ≫ sY)
    PiTensorProduct.subsingletonEquiv (R := T.functionField)
        (s := fun _ : Fin 1 => ⋀[T.functionField]^n Ω[T.functionField⁄k]) 0 ρ =
      (j.stalkMap (genericPoint T)).hom a0 • exteriorPower.ιMulti T.functionField n
        fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x0 i)) := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  let := functionFieldAlgebra (j ≫ sY)
  let := (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalkMap sY j (genericPoint T)
  obtain ⟨t, g, x, ht, hτ', hρ⟩ := (isPoincareResidue_iff sY j τ ρ).mp h
  obtain ⟨v, hv, rfl⟩ := exists_isUnit_eq_mul_of_ord_eq_one _ hy hϖ ht
  rw [hρ]
  have hφϖ : (j.stalkMap (genericPoint T)).hom ϖ = 0 := by
    have hmem : ϖ ∈ RingHom.ker (j.stalkMap (genericPoint T)).hom := by
      rw [IsLocalRing.ker_eq_maximalIdeal _ (j.stalkMap_surjective _)]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
    exact hmem
  exact residue_core (k := k) (K := Y.functionField) (B := T.functionField) ϖ a0 x0 hφϖ hspan
    hne x hv rfl (hτ'.symm.trans hτE)

end Main

section LocalCoordinates

private theorem span_map_D_eq_top {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A]
    [Algebra k B] [Algebra A B] [IsScalarTower k A B] (M : Submonoid A) [IsLocalization M B]
    {m : ℕ} (v : Fin m → A) (hv : Submodule.span A (Set.range fun i => D k A (v i)) = ⊤) :
    Submodule.span B (Set.range fun i => D k B (algebraMap A B (v i))) = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_map_derivation_of_isLocalization k A B M,
    Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have ha : D k A a ∈ Submodule.span A (Set.range fun i => D k A (v i)) := hv ▸ Submodule.mem_top
  have h2 := Submodule.mem_map_of_mem (f := KaehlerDifferential.map k k A B) ha
  rw [Submodule.map_span, ← Set.range_comp] at h2
  have h3 : (KaehlerDifferential.map k k A B ∘ fun i => D k A (v i)) =
      fun i => D k B (algebraMap A B (v i)) := by
    funext i
    simp
  rw [h3] at h2
  exact Submodule.span_le_restrictScalars A B _ h2

variable {k : Type u} [Field k]

private theorem isScalarTower_stalkSpecializes {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {x x' : X}
    (h : x' ⤳ x) :
    letI := MMP.Mori.stalkAlgebra sX x
    letI := MMP.Mori.stalkAlgebra sX x'
    letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsScalarTower k (X.presheaf.stalk x) (X.presheaf.stalk x') := by
  let := MMP.Mori.stalkAlgebra sX x
  let := MMP.Mori.stalkAlgebra sX x'
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x' (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _)) ≫
          X.presheaf.stalkSpecializes h := by
    simp
  exact congrArg CommRingCat.Hom.hom this

private theorem formCoeff_eq_of_subsingletonEquiv {A K : Type*} [CommRing A] [Algebra k A]
    [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] {d : ℕ}
    {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (h0 : MMP.Mori.topFormsMap k A K d σ ≠ 0) (τ : MMP.Mori.PluriForms k K d 1) (c : K)
    (h : PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => ⋀[K]^d Ω[K⁄k]) 0 τ =
      c • MMP.Mori.topFormsMap k A K d σ) :
    MMP.Mori.formCoeff A hσ h0 τ = c := by
  have hb := MMP.Mori.ZTensorPower.basis_ofNat (MMP.Mori.topFormsBasis A hσ h0) 1
  rw [MMP.Mori.topFormsBasis_apply] at hb
  have hτ : τ = c • MMP.Mori.ZTensorPower.basis (MMP.Mori.topFormsBasis A hσ h0) 1 () := by
    have := (eq_smul_tprod_iff τ c _).mpr h
    exact this.trans (congrArg (c • ·) hb.symm)
  rw [hτ, MMP.Mori.formCoeff_smul]
  unfold MMP.Mori.formCoeff
  rw [Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]

private theorem cons_D_eq {k' A : Type*} [CommRing k'] [CommRing A] [Algebra k' A] {n : ℕ} (t : A)
    (x : Fin n → A) :
    (Fin.cons (D k' A t) fun i => D k' A (x i) : Fin (n + 1) → Ω[A⁄k']) =
      fun i => D k' A ((Fin.cons t x : Fin (n + 1) → A) i) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

end LocalCoordinates

section Obligations

variable {k : Type u} [Field k] {Y T : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [CompactSpace Y] [IsLocallyNoetherian Y] [PerfectField k] [LocallyOfFiniteType sY] [IsNormal Y]
  {n : ℕ} (hY : topologicalKrullDim Y = n + 1)
      (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T] [CompactSpace T] [IsLocallyNoetherian T]
          [IsNormal T] (P : MMP.Mori.PrimeDivisor Y) (hP : j
              (genericPoint T) = P.genericPoint) (τ : MMP.Mori.RationalPluriForms sY (n + 1) 1)
                  (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)

include hY hP hτ0 hτ

/-- **The residues of `τ` in coordinates.** There is a presentation `τ = a₀ · dϖ/ϖ ∧ dx₀` in the
local ring at the generic point of `T`, with `a₀` a unit and `dx̄₀` linearly independent on `T`
(a uniformizer `ϖ` and lifts `x₀` of smooth coordinates on `T` give a basis `dϖ, dx₀` of the
differentials of `𝒪_{Y,T}`), and the residues of `τ` are exactly the forms `ā₀ · dx̄₀`. -/
private theorem exists_isPoincareResidue_iff :
    letI := MMP.Mori.functionFieldAlgebra (j ≫ sY)
    ∃ (a0 : Y.presheaf.stalk (j (genericPoint T)))
      (x0 : Fin n → Y.presheaf.stalk (j (genericPoint T))), IsUnit a0 ∧
      LinearIndependent T.functionField
        (fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x0 i))) ∧
      ∀ ρ, MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ ↔
        PiTensorProduct.subsingletonEquiv (R := T.functionField)
            (s := fun _ : Fin 1 => ⋀[T.functionField]^n Ω[T.functionField⁄k]) 0 ρ =
          (j.stalkMap (genericPoint T)).hom a0 • exteriorPower.ιMulti T.functionField n
            fun i => D k T.functionField ((j.stalkMap (genericPoint T)).hom (x0 i)) := by
  have hy : Order.coheight (j (genericPoint T)) = 1 := by rw [hP]; exact P.coheight_genericPoint
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hy
  obtain ⟨ϖ, a0, x0, hϖ, ha0, hspan, hli, -, hne, hτE, -, -⟩ :=
    exists_residue_data sY j P hP τ hτ0 hτ
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  refine ⟨a0, x0, ha0, hli, fun ρ => ⟨fun h =>
    residue_eq_of_isPoincareResidue sY j hy τ h ϖ a0 x0 hϖ hspan hne hτE, fun h =>
    (isPoincareResidue_iff sY j τ ρ).mpr ⟨ϖ, a0, x0, ord_algebraMap_irreducible _ hy hϖ, hτE, h⟩⟩⟩

private theorem exists_isPoincareResidue :
    ∃ ρ, MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ := by
  obtain ⟨a0, x0, -, -, H⟩ := exists_isPoincareResidue_iff sY hY j P hP τ hτ0 hτ
  exact ⟨_, (H _).mpr (LinearEquiv.apply_symm_apply _ _)⟩

/-- The residue of a form with a simple pole is nonzero. -/
private theorem ne_zero_of_isPoincareResidue
    {ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ) : ρ ≠ 0 := by
  obtain ⟨a0, x0, ha0, hli, H⟩ := exists_isPoincareResidue_iff sY hY j P hP τ hτ0 hτ
  let := MMP.Mori.functionFieldAlgebra (j ≫ sY)
  rintro rfl
  exact smul_ne_zero (ha0.map _).ne_zero (ιMulti_ne_zero_of_linearIndependent hli)
    (((H 0).mp h).symm.trans (map_zero _))

open MMP.Intersection in
/-- **The residue in local coordinates at a point of `T`.** At a prime divisor `Q` of `T`, with
`y' = j(η_Q)`, there are `a, b ∈ 𝒪_{Y,y'}` with nonzero restrictions to `T` such that
`ord_Q(Res τ) = v_Q(a|_T) - v_Q(b|_T)` and `div_Y τ + T` has coefficient `v_E(a) - v_E(b)` along
every prime divisor `E` through `y'`: with `t'` a generator of the ideal of `T` at `y'` and `x'`
adapted coordinates, `τ = (a/b) · dt'/t' ∧ dx'`, the residue is `(a/b)|_T · dx̄'`, and `dx̄'`
generates the top forms of `𝒪_{T,Q}`. -/
private theorem exists_local_presentation_at
    {ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (hreg : ∀ Q : MMP.Mori.PrimeDivisor T, IsRegularLocalRing (Y.presheaf.stalk (j Q.genericPoint)))
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ) (Q : MMP.Mori.PrimeDivisor T) :
    ∃ a b : Y.presheaf.stalk (j Q.genericPoint),
      (j.stalkMap Q.genericPoint).hom a ≠ 0 ∧ (j.stalkMap Q.genericPoint).hom b ≠ 0 ∧
      Q.ordForm ρ =
        T.ord (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
            ((j.stalkMap Q.genericPoint).hom a)) Q.genericPoint -
          T.ord (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
            ((j.stalkMap Q.genericPoint).hom b)) Q.genericPoint ∧
      ∀ E : MMP.Mori.PrimeDivisor Y, j Q.genericPoint ∈ E.support →
        (MMP.Mori.divisorOfForm τ + Finsupp.single P (1 : ℤ) : MMP.Mori.Divisor Y) E =
          Y.ord (algebraMap _ Y.functionField a) E.genericPoint -
            Y.ord (algebraMap _ Y.functionField b) E.genericPoint := by
  classical
  have hy : Order.coheight (j (genericPoint T)) = 1 := by rw [hP]; exact P.coheight_genericPoint
  have := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk hy
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hKrank, -⟩ := exists_residue_data sY j P hP τ hτ0 hτ
  have hTsp : genericPoint T ⤳ Q.genericPoint := genericPoint_specializes _
  have hsp : j (genericPoint T) ⤳ j Q.genericPoint := j.base.hom.map_specializes hTsp
  have := hreg Q
  have := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk (j Q.genericPoint))
  have hcompat : ∀ a, (j.stalkMap (genericPoint T)).hom (Y.presheaf.stalkSpecializes hsp a) =
      T.presheaf.stalkSpecializes hTsp ((j.stalkMap Q.genericPoint).hom a) := fun a =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ hTsp a
  have hkerψ : RingHom.ker (j.stalkMap Q.genericPoint).hom = primeOfSpecializes hsp := by
    ext a
    exact (RingHom.mem_ker).trans (stalkMap_eq_zero_iff j Q.genericPoint a)
  letI : Algebra (Y.presheaf.stalk (j Q.genericPoint)) (Y.presheaf.stalk (j (genericPoint T))) :=
    (Y.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (Y.presheaf.stalk (j (genericPoint T)))
      (primeOfSpecializes hsp) := isLocalization_stalkSpecializes hsp
  have hpne : primeOfSpecializes hsp ≠ ⊥ := by
    intro hb
    have hm := IsLocalization.AtPrime.map_eq_maximalIdeal (primeOfSpecializes hsp)
      (Y.presheaf.stalk (j (genericPoint T)))
    rw [hb, Ideal.map_bot] at hm
    exact IsDiscreteValuationRing.not_a_field _ hm.symm
  obtain ⟨t', ht'p, ht'⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot inferInstance hpne
  have hz1 := coheight_fromSpecStalk_span_eq_one ht'
  set q' : PrimeSpectrum (Y.presheaf.stalk (j Q.genericPoint)) :=
    ⟨Ideal.span {t'}, (Ideal.span_singleton_prime ht'.ne_zero).mpr ht'⟩ with hq'
  have hz' : Y.fromSpecStalk _ q' ⤳ j Q.genericPoint := fromSpecStalk_specializes _ q'
  have hpz' : primeOfSpecializes hz' = Ideal.span {t'} :=
    comap_maximalIdeal_stalkSpecializes_fromSpecStalk _ q'
  have hz'y : Y.fromSpecStalk _ q' = j (genericPoint T) := by
    apply eq_of_specializes_of_coheight_eq_one _ hz1 hy
    apply specializes_of_primeOfSpecializes_le hz' hsp
    rw [hpz', Ideal.span_le, Set.singleton_subset_iff]
    exact ht'p
  have hp_eq : primeOfSpecializes hsp = Ideal.span {t'} :=
    (primeOfSpecializes_congr hz'y.symm hsp hz').trans hpz'
  have hker : RingHom.ker (j.stalkMap Q.genericPoint).hom = Ideal.span {t'} := hkerψ.trans hp_eq
  -- coordinates at `y'`
  let := stalkAlgebra sY (j Q.genericPoint)
  let := stalkAlgebra (j ≫ sY) Q.genericPoint
  letI : Algebra (Y.presheaf.stalk (j Q.genericPoint)) (T.presheaf.stalk Q.genericPoint) :=
    (j.stalkMap Q.genericPoint).hom.toAlgebra
  have := isScalarTower_stalkMap sY j Q.genericPoint
  obtain ⟨hfsR, -, hefR⟩ := stalk_facts_of_isRegularLocalRing sY (j Q.genericPoint) (hreg Q)
  obtain ⟨hfsC, -, hefC⟩ := stalk_facts_of_isRegularLocalRing (j ≫ sY) Q.genericPoint
    (isRegularLocalRing_stalk_genericPoint Q)
  have : Module.Free (Y.presheaf.stalk (j Q.genericPoint))
      Ω[Y.presheaf.stalk (j Q.genericPoint)⁄k] := Module.free_of_flat_of_isLocalRing
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY (j Q.genericPoint)
  have hrank : Module.finrank (Y.presheaf.stalk (j Q.genericPoint))
      Ω[Y.presheaf.stalk (j Q.genericPoint)⁄k] = n + 1 :=
    (MMP.Mori.finrank_kaehlerDifferential_eq_of_isFractionRing (k := k)
      (A := Y.presheaf.stalk (j Q.genericPoint)) (K := Y.functionField)).symm.trans hKrank
  obtain ⟨x', hspanR, hliC, hspanC⟩ := exists_coordinates_local (k := k)
    (A := Y.presheaf.stalk (j Q.genericPoint)) (C := T.presheaf.stalk Q.genericPoint)
    (j.stalkMap_surjective _) ht'.ne_zero hker hrank
  -- coordinates at the generic point of `T`
  let := stalkAlgebra sY (j (genericPoint T))
  have := isScalarTower_stalkSpecializes sY hsp
  have hspanR' := hspanR
  rw [cons_D_eq] at hspanR'
  have hspan_y := span_map_D_eq_top (k := k) (A := Y.presheaf.stalk (j Q.genericPoint))
    (B := Y.presheaf.stalk (j (genericPoint T))) (primeOfSpecializes hsp).primeCompl _ hspanR'
  set ϖ := Y.presheaf.stalkSpecializes hsp t' with hϖdef
  set x0 : Fin n → Y.presheaf.stalk (j (genericPoint T)) :=
    fun i => Y.presheaf.stalkSpecializes hsp (x' i) with hx0def
  have hspan_y' : Submodule.span (Y.presheaf.stalk (j (genericPoint T))) (Set.range
      (Fin.cons (D k _ ϖ) fun i => D k _ (x0 i) :
        Fin (n + 1) → Ω[Y.presheaf.stalk (j (genericPoint T))⁄k])) = ⊤ := by
    rw [cons_D_eq]
    convert hspan_y using 3
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  have hϖ : Irreducible ϖ := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal (primeOfSpecializes hsp)
        (Y.presheaf.stalk (j (genericPoint T))), hp_eq, Ideal.map_span, Set.image_singleton]
    rfl
  have hτy := (ordForm_eq_ordAt sY P τ _ hP).symm.trans hτ
  obtain ⟨a0, ha0, hne, hτE⟩ := exists_unit_presentation sY _ hy τ hτ0 hτy ϖ x0 hϖ hspan_y'
  have hρE := residue_eq_of_isPoincareResidue sY j hy τ h ϖ a0 x0 hϖ hspan_y' hne hτE
  -- write `a₀ = a / b`
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (primeOfSpecializes hsp).primeCompl a0
  have hab' : a0 * Y.presheaf.stalkSpecializes hsp b = Y.presheaf.stalkSpecializes hsp a := by
    rw [← hab]
    exact IsLocalization.mk'_spec _ a b
  have hbunit : IsUnit (Y.presheaf.stalkSpecializes hsp b) := IsLocalization.map_units _ b
  have hap : a ∉ primeOfSpecializes hsp := by
    intro hm
    have hu : IsUnit (Y.presheaf.stalkSpecializes hsp a) := hab' ▸ ha0.mul hbunit
    exact (IsLocalRing.mem_maximalIdeal _).mp hm hu
  have hbp : (b : Y.presheaf.stalk (j Q.genericPoint)) ∉ primeOfSpecializes hsp := b.2
  have hψa : (j.stalkMap Q.genericPoint).hom a ≠ 0 := fun h0 => by
    have h1 : a ∈ RingHom.ker (j.stalkMap Q.genericPoint).hom := RingHom.mem_ker.mpr h0
    rw [hkerψ] at h1; exact hap h1
  have hψb : (j.stalkMap Q.genericPoint).hom b ≠ 0 := fun h0 => by
    have h1 : (b : Y.presheaf.stalk (j Q.genericPoint)) ∈ RingHom.ker
        (j.stalkMap Q.genericPoint).hom :=
      RingHom.mem_ker.mpr h0
    rw [hkerψ] at h1; exact hbp h1
  -- `a₀ = a / b` on `T`
  have hspT : ∀ c : T.presheaf.stalk Q.genericPoint,
      T.presheaf.stalkSpecializes hTsp c = algebraMap _ T.functionField c := fun c => rfl
  have hCa : algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
      ((j.stalkMap Q.genericPoint).hom a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hψa
  have hCb : algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
      ((j.stalkMap Q.genericPoint).hom b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hψb
  have hφa0 : (j.stalkMap (genericPoint T)).hom a0 =
      algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom a) *
        (algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom b))⁻¹ := by
    have h1 := congrArg (j.stalkMap (genericPoint T)).hom hab'
    rw [map_mul, hcompat, hcompat, hspT, hspT] at h1
    rw [← h1, mul_assoc, mul_inv_cancel₀ hCb, mul_one]
  refine ⟨a, b, hψa, hψb, ?_, ?_⟩
  · let := functionFieldAlgebra (j ≫ sY)
    have := isScalarTower_stalk_functionField (j ≫ sY) Q.genericPoint
    set σC := exteriorPower.ιMulti (T.presheaf.stalk Q.genericPoint) n
      (fun i => D k (T.presheaf.stalk Q.genericPoint) ((j.stalkMap Q.genericPoint).hom (x' i)))
    have hgenC := span_ιMulti_eq_top _ hspanC
    have himgC : topFormsMap k _ T.functionField n σC = exteriorPower.ιMulti T.functionField n
        (fun i => D k T.functionField (algebraMap _ T.functionField
          ((j.stalkMap Q.genericPoint).hom (x' i)))) := by
      rw [topFormsMap_ιMulti]
      congr 1
      funext i
      simp
    have hliK : LinearIndependent T.functionField (fun i => D k T.functionField
        (algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom (x' i)))) := by
      let bC := Module.Basis.mk hliC hspanC.ge
      let bK := bC.ofIsLocalizedModule T.functionField (nonZeroDivisors _)
        (KaehlerDifferential.map k k (T.presheaf.stalk Q.genericPoint) T.functionField)
      have hfun : (fun i => D k T.functionField
          (algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom (x' i)))) = ⇑bK := by
        funext i
        simp [bK, bC, Module.Basis.ofIsLocalizedModule_apply]
        rfl
      rw [hfun]
      exact bK.linearIndependent
    have h0C : topFormsMap k _ T.functionField n σC ≠ 0 :=
      himgC ▸ ιMulti_ne_zero_of_linearIndependent hliK
    have hρE' : PiTensorProduct.subsingletonEquiv (R := T.functionField)
        (s := fun _ : Fin 1 => ⋀[T.functionField]^n Ω[T.functionField⁄k]) 0 ρ =
        (j.stalkMap (genericPoint T)).hom a0 • topFormsMap k _ T.functionField n σC := by
      rw [hρE, himgC]
      congr 2
      funext i
      rw [hx0def]
      simp only
      rw [hcompat, hspT]
    rw [MMP.Mori.PrimeDivisor.ordForm_eq Q ρ hgenC h0C,
      formCoeff_eq_of_subsingletonEquiv hgenC h0C ρ _ hρE', hφa0, ord_mul_inv hCa hCb]
  · intro E hE
    have hEsp := genericPoint_specializes_of_mem_support E hE
    have hE1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
    let := stalkAlgebra sY E.genericPoint
    letI : Algebra (Y.presheaf.stalk (j Q.genericPoint)) (Y.presheaf.stalk E.genericPoint) :=
      (Y.presheaf.stalkSpecializes hEsp).hom.toAlgebra
    have := isScalarTower_stalkSpecializes sY hEsp
    have : IsLocalization.AtPrime (Y.presheaf.stalk E.genericPoint) (primeOfSpecializes hEsp) :=
      isLocalization_stalkSpecializes hEsp
    have := isScalarTower_stalk_functionField sY E.genericPoint
    have hspanE := span_map_D_eq_top (k := k) (A := Y.presheaf.stalk (j Q.genericPoint))
      (B := Y.presheaf.stalk E.genericPoint) (primeOfSpecializes hEsp).primeCompl _ hspanR'
    set eE : Fin (n + 1) → Ω[Y.presheaf.stalk E.genericPoint⁄k] := fun i =>
      D k _ (algebraMap _ (Y.presheaf.stalk E.genericPoint)
        ((Fin.cons t' x' : Fin (n + 1) → Y.presheaf.stalk (j Q.genericPoint)) i))
    have hgenE := span_ιMulti_eq_top eE hspanE
    have himgE : topFormsMap k _ Y.functionField (n + 1) (exteriorPower.ιMulti _ (n + 1) eE) =
        exteriorPower.ιMulti Y.functionField (n + 1)
          (Fin.cons (D k Y.functionField (algebraMap _ _ ϖ))
            fun i => D k Y.functionField (algebraMap _ _ (x0 i))) := by
      rw [topFormsMap_ιMulti]
      congr 1
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [eE, KaehlerDifferential.map_D, Fin.cons_zero, hϖdef]
        exact congrArg _ ((Scheme.algebraMap_stalkSpecializes hEsp t').trans
          (Scheme.algebraMap_stalkSpecializes hsp t').symm)
      · simp only [eE, KaehlerDifferential.map_D, Fin.cons_succ, hx0def]
        exact congrArg _ ((Scheme.algebraMap_stalkSpecializes hEsp (x' i)).trans
          (Scheme.algebraMap_stalkSpecializes hsp (x' i)).symm)
    have h0E : topFormsMap k _ Y.functionField (n + 1) (exteriorPower.ιMulti _ (n + 1) eE) ≠ 0 :=
      himgE ▸ hne
    have hcoef := formCoeff_eq_of_subsingletonEquiv hgenE h0E τ _ (hτE.trans (by rw [himgE]))
    have hDE : (MMP.Mori.divisorOfForm τ + Finsupp.single P (1 : ℤ) : MMP.Mori.Divisor Y) E =
        E.ordForm τ + if E = P then 1 else 0 := by
      rw [Finsupp.add_apply, Finsupp.single_apply]
      congr 1
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · rfl
    rw [hDE, E.ordForm_eq τ hgenE h0E, hcoef]
    -- the coefficient `a₀ / ϖ` is `a / (b t')`
    have hRa : algebraMap _ Y.functionField a ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]
      rintro rfl; exact hap (Ideal.zero_mem _)
    have hRb : algebraMap _ Y.functionField (b : Y.presheaf.stalk (j Q.genericPoint)) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]
      intro h0; apply hbp; rw [h0]; exact Ideal.zero_mem _
    have hRt : algebraMap _ Y.functionField t' ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht'.ne_zero
    have ha0' : algebraMap _ Y.functionField a0 = algebraMap _ Y.functionField a *
        (algebraMap _ Y.functionField (b : Y.presheaf.stalk (j Q.genericPoint)))⁻¹ := by
      have h1 := congrArg (algebraMap _ Y.functionField) hab'
      rw [map_mul, Scheme.algebraMap_stalkSpecializes, Scheme.algebraMap_stalkSpecializes] at h1
      rw [← h1, mul_assoc, mul_inv_cancel₀ hRb, mul_one]
    have hϖK : algebraMap _ Y.functionField ϖ = algebraMap _ Y.functionField t' :=
      Scheme.algebraMap_stalkSpecializes hsp t'
    rw [ha0', hϖK, ord_mul_inv (mul_ne_zero hRa (inv_ne_zero hRb)) hRt,
      ord_mul_inv hRa hRb]
    -- the order of `t'` along `E`
    have ht'E := ord_prime_eq_ite ht' hz' hpz' hz1 E hE
    rw [hz'y, hP] at ht'E
    rw [ht'E]
    have hiff : E.genericPoint = P.genericPoint ↔ E = P :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective.eq_iff
    by_cases hEP : E = P
    · rw [if_pos (hiff.mpr hEP), if_pos hEP]; ring
    · rw [if_neg (fun h => hEP (hiff.mp h)), if_neg hEP]; ring

/-- **The local computation of the divisor of the residue.** At a prime divisor `Q` of `T`,
with `y' = j(η_Q)`, choose local coordinates `t', x'` of `𝒪_{Y,y'}` adapted to `T` and write
`τ = F · dt'/t' ∧ dx'`; then `ord_Q(Res τ) = v_Q(F|_T)`, while `div_Y τ + T` agrees with
`div F` along the prime divisors through `y'`, and restricting the principal divisor `div F`
to `T` gives `v_Q(F|_T)`. -/
private theorem ordForm_eq_sum_intersectionLength
    {ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (hreg : ∀ Q : MMP.Mori.PrimeDivisor T, IsRegularLocalRing (Y.presheaf.stalk (j Q.genericPoint)))
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ) (Q : MMP.Mori.PrimeDivisor T) :
    Q.ordForm ρ = (MMP.Mori.divisorOfForm τ + Finsupp.single P 1).sum
      fun E d => E.intersectionLength j Q • d := by
  classical
  obtain ⟨a, b, ha, hb, hQ, hD⟩ := exists_local_presentation_at sY hY j P hP τ hτ0 hτ hreg h Q
  obtain ⟨Sa, hSa, hfa⟩ := ord_stalkMap_eq_sum_intersectionLength_mul_ord j Q (hreg Q) a ha
  obtain ⟨Sb, hSb, hfb⟩ := ord_stalkMap_eq_sum_intersectionLength_mul_ord j Q (hreg Q) b hb
  set D := MMP.Mori.divisorOfForm τ + Finsupp.single P (1 : ℤ) with hDdef
  set S := D.support ∪ Sa ∪ Sb
  have h1 : D.sum (fun E d => E.intersectionLength j Q • d) =
      ∑ E ∈ S, if j Q.genericPoint ∈ E.support then
          (E.intersectionLength j Q : ℤ) * D E else 0 := by
    rw [Finsupp.sum]
    rw [Finset.sum_subset (s₁ := D.support) (s₂ := S) (by
      intro E hE; simp [S, hE]) (by
      intro E _ hE
      rw [Finsupp.notMem_support_iff] at hE
      simp [hE])]
    refine Finset.sum_congr rfl fun E _ => ?_
    split_ifs with hE
    · rw [nsmul_eq_mul]
    · rw [MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem j E hE, zero_smul]
  have h2 : ∀ E ∈ S, (if j Q.genericPoint ∈ E.support then
      (E.intersectionLength j Q : ℤ) * D E else 0) =
      (if j Q.genericPoint ∈ E.support then (E.intersectionLength j Q : ℤ) *
        Y.ord (algebraMap _ Y.functionField a) E.genericPoint else 0) -
      (if j Q.genericPoint ∈ E.support then (E.intersectionLength j Q : ℤ) *
        Y.ord (algebraMap _ Y.functionField b) E.genericPoint else 0) := by
    intro E _
    split_ifs with hE
    · rw [hD E hE, mul_sub]
    · rw [sub_zero]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_sub_distrib,
    ← hfa S (by intro E hE; simp [S, hE]), ← hfb S (by intro E hE; simp [S, hE]), hQ]

/-- The divisor of the residue is `(div_Y τ + T)|_T`. -/
private theorem divisorOfForm_eq_restrict_of_isPoincareResidue
    {ρ : MMP.Mori.RationalPluriForms (j ≫ sY) n 1}
    (hreg : ∀ Q : MMP.Mori.PrimeDivisor T, IsRegularLocalRing (Y.presheaf.stalk (j Q.genericPoint)))
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ) :
    MMP.Mori.divisorOfForm ρ =
      (MMP.Mori.divisorOfForm τ + Finsupp.single P 1).restrict j := by
  classical
  have hy : Order.coheight (j (genericPoint T)) = 1 := by rw [hP]; exact P.coheight_genericPoint
  set D := MMP.Mori.divisorOfForm τ + Finsupp.single P (1 : ℤ) with hDdef
  have hDP : D P = 0 := by
    simp only [D, Finsupp.add_apply, Finsupp.single_eq_same]
    change P.ordForm τ + 1 = 0
    rw [hτ]; rfl
  have : AlgebraicGeometry.IsNoetherian T := ⟨⟩
  have hgen : ∀ s : T, Order.coheight s = 0 → s = genericPoint T := fun s hs => by
    have hle : s ≤ genericPoint T := genericPoint_specializes s
    exact (Specializes.antisymm (Order.coheight_eq_zero.mp hs hle) hle).eq
  have hpure : ∀ s : T, Order.coheight s = 0 → Order.coheight (j s) = 1 := fun s hs => by
    rw [hgen s hs]; exact hy
  have hD : ∀ E ∈ D.support, ∀ s : T, Order.coheight s = 0 → j s ≠ E.genericPoint := by
    intro E hE s hs hjs
    rw [hgen s hs, hP] at hjs
    have : P = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hjs
    rw [Finsupp.mem_support_iff, ← this] at hE
    exact hE hDP
  ext Q
  change Q.ordForm ρ = (D.restrict j).coeff Q
  rw [MMP.Mori.DivisorWithCoeffs.coeff_restrict_of_pure j D hpure hD Q]
  exact ordForm_eq_sum_intersectionLength sY hY j P hP τ hτ0 hτ hreg h Q

end Obligations

end Residue

section CanonicalDivisorExistence

open Opposite TopologicalSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' := by
  have h (C : irreducibleComponents Y) : C.1 = Set.univ :=
    Set.eq_univ_of_univ_subset (C.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))
  exact Subtype.ext (Subtype.ext ((h _).trans (h _).symm))

private theorem gp_specializes_aux {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_gp_aux {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_stalkSpecializes_apply {Y : Scheme.{u}} {x y z : Y}
    (h : x ⤳ y) (h' : y ⤳ z) (h'' : x ⤳ z) (s : Y.presheaf.stalk z) :
    (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.stalkSpecializes h').hom s) =
      (Y.presheaf.stalkSpecializes h'').hom s :=
  TopCat.Presheaf.stalkSpecializes_comp_apply _ h h' s

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (gp_specializes_aux Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective_aux {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (gp_specializes_aux Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_gp_aux Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (gp_specializes_aux E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (gp_specializes_aux E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (gp_specializes_aux E.component)).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective_aux E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The irreducible component `X` of the integral scheme `X`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]; exact h⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_gp_aux Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective_aux Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_gp_aux Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_gp_aux Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (gp_specializes_aux _)).hom
      ((X.presheaf.stalkSpecializes (specializes_gp_aux _)).hom (e.symm _)))) = _
  rw [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_gp_aux Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF]
    rw [evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨x, hx, hxe⟩
      rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      rw [← hx]
      exact x.2
    obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
    exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))
  · intro h E' hE'
    exact (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · have h' : restrictRF U V ψ₁.1 = restrictRF U V ψ₂.1 := congrArg Subtype.val h
    exact Subtype.ext (restrictRF_injective U V h')
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to an open subscheme is the
restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
private theorem nonempty_divisorialSheaf_restrictOpen_iso (D : Divisor X) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] :
    Nonempty (Divisor.divisorialSheaf (D.restrictOpen U) ≅ D.divisorialSheaf.restrict U.ι) :=
  ⟨(@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom U D)).symm⟩

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- A normal variety of dimension `n` over a perfect field has a canonical divisor. -/
public theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS with hT
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  haveI : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  haveI : IsDominant T.ι := Opens.isDominant_ι (T.isOpen.dense ⟨_, (Classical.arbitrary T).2⟩)
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  haveI : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  haveI : IsIntegral T := inferInstance
  haveI : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq hS T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : KS.restrictOpen T = KT := by
    ext W
    rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso KS T
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

end CanonicalDivisorExistence

/-- The kernel of the stalk map `𝒪_{X,η} ⟶ 𝒪_{T,Q}` at the generic point `η` of a prime divisor `Q`
of a component of `S` is generated by a local equation `s` of `S` at `η`. -/
private theorem exists_ker_stalkMap_eq_span
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
    {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    {J : Type*} [Fintype J] {T : J → Scheme.{u}} (ι : ∀ a, T a ⟶ X)
    [∀ a, IsClosedImmersion (ι a)] [∀ a, IsIntegral (T a)] [∀ a, IsNormal (T a)]
    [∀ a, IsLocallyNoetherian (T a)]
    (P : J → MMP.Mori.PrimeDivisor X) (hP : ∀ a, Set.range (ι a).base = ((P a).support : Set X))
    (hdisj : Pairwise fun a b => Disjoint ((P a).support : Set X) (P b).support)
    (hcart : ∀ x : X, Order.coheight x = 2 → (∃ a, x ∈ (P a).support) →
      MMP.Flips.IsCartierAt (∑ a, Finsupp.single (P a) (1 : ℤ)) x)
    (a : J) (Q : MMP.Mori.PrimeDivisor (T a)) :
    ∃ s : X.presheaf.stalk (ι a Q.genericPoint), s ≠ 0 ∧
      RingHom.ker ((ι a).stalkMap Q.genericPoint).hom = Ideal.span {s} := by
  have hηp := map_genericPoint_eq (ι a) (P a) (hP a)
  have hp : Order.coheight ((ι a) (genericPoint (T a))) = 1 := by
    rw [hηp]; exact (P a).coheight_genericPoint
  have hcoh : Order.coheight ((ι a) Q.genericPoint) = 2 :=
    coheight_map_genericPoint_eq_two sX hdim (ι a) (P a) (hP a) Q
  have hxP : (ι a) Q.genericPoint ∈ (P a).support := (hP a) ▸ ⟨Q.genericPoint, rfl⟩
  obtain ⟨U, hxU, hU⟩ := hcart _ hcoh ⟨a, hxP⟩
  obtain ⟨W, hxW, φ, hφ⟩ := exists_isLocalEquation_of_isCartier_restrictOpen hU hxU
  obtain ⟨g, hg0, hg⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  have hgen : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.genericPoint ⤳ (ι a) Q.genericPoint →
      (∑ b, Finsupp.single (P b) (1 : ℤ)) Γ = Γ.ord φ := by
    intro Γ hΓ
    have hmem : Γ.genericPoint ∈ W := hΓ.mem_open W.isOpen hxW
    have := hφ Γ ⟨Γ.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' Γ, hmem⟩
    exact this
  have hsupp : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.genericPoint ⤳ (ι a) Q.genericPoint →
      (ι a) Q.genericPoint ∈ Γ.support := by
    intro Γ hΓ
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hΓ.mem_closure
  have hspec : (P a).genericPoint ⤳ (ι a) Q.genericPoint := by
    have := hxP
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at this
    exact this
  have hgp : X.ord g ((ι a) (genericPoint (T a))) = 1 := by
    rw [hηp, ← hg (P a), ← hgen (P a) hspec,
      coeff_sum_single_eq P hdisj a _ hxP (P a) hxP, if_pos rfl]
  have hgy : ∀ y : X, Order.coheight y = 1 → y ⤳ (ι a) Q.genericPoint →
      y ≠ (ι a) (genericPoint (T a)) → X.ord g y = 0 := by
    intro y hy hyx hyne
    have hΓg := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hy
    set Γ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy
    have hyx' : Γ.genericPoint ⤳ (ι a) Q.genericPoint := hΓg ▸ hyx
    rw [← hΓg, ← hg Γ, ← hgen Γ hyx',
      coeff_sum_single_eq P hdisj a _ hxP Γ (hsupp Γ hyx'), if_neg]
    intro hΓ
    apply hyne
    rw [← hΓg, hΓ, hηp]
  exact exists_span_ker_stalkMap (ι a) Q.genericPoint hp g hg0 hgp hgy

/-- `X` is regular at the generic point of every prime divisor of every component of `S`:
`𝒪_{X,η}/(s)` is a discrete valuation ring for a local equation `s` of `S` at `η`. -/
private theorem isRegularLocalRing_stalk_map_genericPoint
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
    {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    {J : Type*} [Fintype J] {T : J → Scheme.{u}} (ι : ∀ a, T a ⟶ X)
    [∀ a, IsClosedImmersion (ι a)] [∀ a, IsIntegral (T a)] [∀ a, IsNormal (T a)]
    [∀ a, IsLocallyNoetherian (T a)]
    (P : J → MMP.Mori.PrimeDivisor X) (hP : ∀ a, Set.range (ι a).base = ((P a).support : Set X))
    (hdisj : Pairwise fun a b => Disjoint ((P a).support : Set X) (P b).support)
    (hcart : ∀ x : X, Order.coheight x = 2 → (∃ a, x ∈ (P a).support) →
      MMP.Flips.IsCartierAt (∑ a, Finsupp.single (P a) (1 : ℤ)) x)
    (a : J) (Q : MMP.Mori.PrimeDivisor (T a)) :
    IsRegularLocalRing (X.presheaf.stalk (ι a Q.genericPoint)) := by
  obtain ⟨s, hs0, hker⟩ := exists_ker_stalkMap_eq_span sX hdim ι P hP hdisj hcart a Q
  exact isRegularLocalRing_stalk_of_ker (ι a) Q.genericPoint s hs0 hker
    (isRegularLocalRing_stalk_genericPoint Q)

/-- A nonzero rational top form is nonzero as a `1`-canonical form. -/
private theorem toPluriForms_ne_zero {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) {d : ℕ} {σ : RationalTopForms sX d} (hσ : σ ≠ 0) :
    σ.toPluriForms sX ≠ 0 := by
  intro h
  apply hσ
  letI := functionFieldAlgebra sX
  have := congrArg (PiTensorProduct.subsingletonEquiv (R := X.functionField)
    (s := fun _ : Fin 1 => (⋀[X.functionField]^d Ω[X.functionField⁄k])) 0) h
  erw [PiTensorProduct.subsingletonEquiv_apply_tprod] at this
  exact this.trans (map_zero _)

/-- There is a nonzero rational top form with a simple pole along every `P a`: twist a basis
form by a rational function with prescribed orders along the finitely many `P a`. -/
private theorem exists_form_ordForm_eq_neg_one
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    {J : Type*} [Fintype J] (P : J → MMP.Mori.PrimeDivisor X) :
    (∃ ω : RationalTopForms sX (n + 1), ω ≠ 0 ∧ ∀ a, (P a).ordForm ω.toPluriForms = -1) := by
  have hV := hX.1
  have hd : topologicalKrullDim X = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  obtain ⟨b⟩ := MMP.Fourfold.exists_basis_topForms (sX := sX) hd
  let ω₀ : RationalTopForms sX (n + 1) := b ()
  have hω₀ : ω₀ ≠ 0 := b.ne_zero ()
  have hsmul : ∀ (g : X.functionField) (σ : RationalTopForms sX (n + 1)),
      (g • σ).toPluriForms sX = g • σ.toPluriForms sX := by
    intro g σ
    letI := functionFieldAlgebra sX
    have := (PiTensorProduct.tprod X.functionField
      (s := fun _ : Fin 1 => ⋀[X.functionField]^(n + 1) Ω[X.functionField⁄k])).map_smul_univ
      (fun _ => g) (fun _ => σ)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one] at this
    exact this
  classical
  obtain ⟨φ, hφ⟩ := MMP.Mori.PrimeDivisor.exists_ord_eq k sX hV (Finset.univ.image P)
    (fun D => -1 - D.ordForm (ω₀.toPluriForms sX))
  let Z₀ : irreducibleComponents X := topComponent X
  have hcomp : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.component = Z₀ := fun Γ => Subtype.ext (by
    have h : (Γ.component : Set X) ∈ ({Set.univ} : Set (Set X)) :=
      irreducibleComponents_eq_singleton (X := X) ▸ Γ.component.2
    exact h)
  set f := MMP.Threefold.Mori.Helpers.evalFF Z₀ (φ : RationalFunctions X) with hfdef
  have hf : f ≠ 0 := (φ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Z₀)).ne_zero
  refine ⟨f • ω₀, smul_ne_zero hf hω₀, fun a => ?_⟩
  rw [hsmul, (P a).ordForm_smul_of_topologicalKrullDim_eq hd hf (toPluriForms_ne_zero sX hω₀)]
  have := hφ (P a) (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hcomp] at this
  rw [this]
  ring

section RestrictLoc

open Classical

private theorem restrictCoeff_finite_aux {X T : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    (ι : T ⟶ X) (P : MMP.Mori.PrimeDivisor X) (hηP : ι (genericPoint T) = P.genericPoint)
    {R : Type*} [AddCommMonoid R] (D : MMP.Mori.DivisorWithCoeffs R X) (hDP : D.coeff P = 0) :
    (Function.support (MMP.Mori.DivisorWithCoeffs.restrictCoeff ι D)).Finite := by
  haveI : IsNoetherian T := { }
  refine MMP.Mori.DivisorWithCoeffs.finite_support_restrictCoeff ι D ?_
  intro E hE s hs hmem
  have hs' : s = genericPoint T := by
    have hle : s ≤ genericPoint T := genericPoint_specializes s
    exact (Specializes.antisymm (Order.coheight_eq_zero.mp hs hle) hle).eq
  subst hs'
  rw [hηP] at hmem
  have hEP : E = P := MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes
    (genericPoint_specializes_of_mem_support E hmem)
  rw [Finsupp.mem_support_iff, hEP] at hE
  exact hE hDP

private theorem restrict_coeff_of_isLocalEquation {X T : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    (ι : T ⟶ X) [IsClosedImmersion ι] (P : MMP.Mori.PrimeDivisor X)
    (hηP : ι (genericPoint T) = P.genericPoint)
    (hker : ∀ Q : MMP.Mori.PrimeDivisor T, ∃ s : X.presheaf.stalk (ι Q.genericPoint), s ≠ 0 ∧
      RingHom.ker (ι.stalkMap Q.genericPoint).hom = Ideal.span {s})
    (hreg : ∀ Q : MMP.Mori.PrimeDivisor T, IsRegularLocalRing (X.presheaf.stalk (ι Q.genericPoint)))
    (D : MMP.Mori.Divisor X) (hDP : D.coeff P = 0) (W : X.Opens)
    (φ : (RationalFunctions X)ˣ) (hφ : D.IsLocalEquation W φ) :
    ∃ ĝ : T.functionField, ĝ ≠ 0 ∧ ∀ Q : MMP.Mori.PrimeDivisor T, ι Q.genericPoint ∈ W →
      (D.restrict ι).coeff Q = T.ord ĝ Q.genericPoint := by
  by_cases hne : (P.support ∩ (W : Set X)).Nonempty
  · obtain ⟨g, hg0, hg⟩ := MMP.Positivity.exists_ord_eq_of_units φ
    have hgP : X.ord g P.genericPoint = 0 := by
      rw [← hg P, ← hφ P hne]; exact hDP
    obtain ⟨ĝ, hĝ0, hĝ⟩ := exists_restrictFF ι P hηP g hg0 hgP
    refine ⟨ĝ, hĝ0, fun Q hQW => ?_⟩
    obtain ⟨s, hs0, hs⟩ := hker Q
    exact hĝ Q s hs0 hs (hreg Q) D (fun E hE => by
      rw [← hg E]; exact (hφ E ⟨ι Q.genericPoint, hE, hQW⟩).symm)
      (restrictCoeff_finite_aux ι P hηP D hDP)
  · refine ⟨1, one_ne_zero, fun Q hQW => absurd ?_ hne⟩
    refine ⟨ι Q.genericPoint, ?_, hQW⟩
    have h1 : ι (genericPoint T) ⤳ ι Q.genericPoint :=
      (genericPoint_specializes Q.genericPoint).map ι.continuous
    rw [hηP] at h1
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact h1.mem_closure

private theorem isCartier_restrict_aux {X T : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T]
    (ι : T ⟶ X) [IsClosedImmersion ι] (P : MMP.Mori.PrimeDivisor X)
    (hηP : ι (genericPoint T) = P.genericPoint)
    (hker : ∀ Q : MMP.Mori.PrimeDivisor T, ∃ s : X.presheaf.stalk (ι Q.genericPoint), s ≠ 0 ∧
      RingHom.ker (ι.stalkMap Q.genericPoint).hom = Ideal.span {s})
    (hreg : ∀ Q : MMP.Mori.PrimeDivisor T, IsRegularLocalRing (X.presheaf.stalk (ι Q.genericPoint)))
    (C : MMP.Mori.Divisor X) (hC : C.IsCartier) (hCP : C.coeff P = 0) :
    MMP.Mori.Divisor.IsCartier (C.restrict ι : MMP.Mori.Divisor T) := by
  intro y
  obtain ⟨W, hyW, φ, hφ⟩ := hC (ι y)
  obtain ⟨ĝ, hĝ0, hĝ⟩ := restrict_coeff_of_isLocalEquation ι P hηP hker hreg C hCP W φ hφ
  obtain ⟨φT, hφT⟩ := MMP.Positivity.exists_units_of_ne_zero hĝ0
  refine ⟨ι ⁻¹ᵁ W, hyW, φT, fun Γ ⟨x, hxΓ, hxV⟩ => ?_⟩
  have hΓgen : Γ.genericPoint ∈ ι ⁻¹ᵁ W :=
    (genericPoint_specializes_of_mem_support Γ hxΓ).mem_open (ι ⁻¹ᵁ W).isOpen hxV
  exact (hĝ Γ hΓgen).trans (hφT Γ).symm

private theorem restrict_principal_aux {X T : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T] [CompactSpace X]
    (ι : T ⟶ X) [IsClosedImmersion ι] (P : MMP.Mori.PrimeDivisor X)
    (hηP : ι (genericPoint T) = P.genericPoint)
    (hker : ∀ Q : MMP.Mori.PrimeDivisor T, ∃ s : X.presheaf.stalk (ι Q.genericPoint), s ≠ 0 ∧
      RingHom.ker (ι.stalkMap Q.genericPoint).hom = Ideal.span {s})
    (hreg : ∀ Q : MMP.Mori.PrimeDivisor T, IsRegularLocalRing (X.presheaf.stalk (ι Q.genericPoint)))
    (χ : (RationalFunctions X)ˣ) (hχ : (principalDivisor χ).coeff P = 0) :
    ∃ χT : (RationalFunctions T)ˣ, (principalDivisor χ).restrict ι = principalDivisor χT := by
  obtain ⟨ĝ, hĝ0, hĝ⟩ := restrict_coeff_of_isLocalEquation ι P hηP hker hreg (principalDivisor χ)
    hχ ⊤ χ (fun E _ => coeff_principalDivisor χ E)
  obtain ⟨χT, hχT⟩ := MMP.Positivity.exists_units_of_ne_zero hĝ0
  refine ⟨χT, Finsupp.ext fun Q => ?_⟩
  exact (hĝ Q trivial).trans (hχT Q).symm

section Lin

/-- The additive map `D ↦ ∑ᵢ dᵢ · length(𝒪_{T,Q}/I_{Dᵢ}𝒪_{T,Q})`. -/
private noncomputable def restrictAt {X T : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {R : Type*} [AddCommMonoid R] (ι : T ⟶ X) (Q : MMP.Mori.PrimeDivisor T) :
    MMP.Mori.DivisorWithCoeffs R X →+ R :=
  Finsupp.liftAddHom fun E : MMP.Mori.PrimeDivisor X =>
    (E.intersectionLength ι Q) • AddMonoidHom.id R

private theorem coeff_restrict_eq_restrictAt {X T : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    (ι : T ⟶ X) (P : MMP.Mori.PrimeDivisor X) (hηP : ι (genericPoint T) = P.genericPoint)
    {R : Type*} [AddCommMonoid R] (D : MMP.Mori.DivisorWithCoeffs R X) (hDP : D.coeff P = 0)
    (Q : MMP.Mori.PrimeDivisor T) : (D.restrict ι).coeff Q = restrictAt ι Q D :=
  MMP.Mori.DivisorWithCoeffs.coeff_restrict ι (restrictCoeff_finite_aux ι P hηP D hDP) Q

private theorem restrict_add_aux {X T : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    (ι : T ⟶ X) (P : MMP.Mori.PrimeDivisor X) (hηP : ι (genericPoint T) = P.genericPoint)
    {R : Type*} [AddCommMonoid R] (D₁ D₂ : MMP.Mori.DivisorWithCoeffs R X)
    (h₁ : D₁.coeff P = 0) (h₂ : D₂.coeff P = 0) :
    (D₁ + D₂).restrict ι = D₁.restrict ι + D₂.restrict ι := by
  refine Finsupp.ext fun Q => ?_
  have h12 : (D₁ + D₂).coeff P = 0 := by
    rw [show (D₁ + D₂).coeff P = D₁.coeff P + D₂.coeff P from rfl, h₁, h₂, add_zero]
  calc (D₁ + D₂).restrict ι Q = restrictAt ι Q (D₁ + D₂) :=
        coeff_restrict_eq_restrictAt ι P hηP (D₁ + D₂) h12 Q
    _ = restrictAt ι Q D₁ + restrictAt ι Q D₂ := map_add _ _ _
    _ = D₁.restrict ι Q + D₂.restrict ι Q := by
      rw [← coeff_restrict_eq_restrictAt ι P hηP D₁ h₁ Q,
        ← coeff_restrict_eq_restrictAt ι P hηP D₂ h₂ Q]
      rfl

private theorem restrict_zsmul_aux {X T : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    (ι : T ⟶ X) (P : MMP.Mori.PrimeDivisor X) (hηP : ι (genericPoint T) = P.genericPoint)
    {R : Type*} [AddCommGroup R] (m : ℤ) (D : MMP.Mori.DivisorWithCoeffs R X)
    (h : D.coeff P = 0) :
    (m • D).restrict ι = m • D.restrict ι := by
  refine Finsupp.ext fun Q => ?_
  have hm : (m • D).coeff P = 0 := by
    rw [show (m • D).coeff P = m • D.coeff P from rfl, h, smul_zero]
  calc (m • D).restrict ι Q = restrictAt ι Q (m • D) :=
        coeff_restrict_eq_restrictAt ι P hηP (m • D) hm Q
    _ = m • restrictAt ι Q D := map_zsmul _ _ _
    _ = (m • D.restrict ι) Q := by
      rw [← coeff_restrict_eq_restrictAt ι P hηP D h Q]
      rfl

private theorem restrictAt_toQ {X T : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (ι : T ⟶ X) (Q : MMP.Mori.PrimeDivisor T)
    (D : MMP.Mori.Divisor X) :
    restrictAt ι Q (MMP.Mori.Divisor.toQDivisor D) = ((restrictAt ι Q D : ℤ) : ℚ) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, Int.cast_add]
  | single E d =>
    have : MMP.Mori.Divisor.toQDivisor (Finsupp.single E d) = Finsupp.single E (d : ℚ) := by
      refine Finsupp.ext fun F => ?_
      change (MMP.Mori.Divisor.toQDivisor (Finsupp.single E d)).coeff F = _
      rw [MMP.Mori.Divisor.coeff_toQDivisor]
      show (((Finsupp.single E d : MMP.Mori.Divisor X) F : ℤ) : ℚ) =
        (Finsupp.single E (d : ℚ)) F
      by_cases hF : E = F
      · subst hF; simp
      · simp [Finsupp.single_apply, hF]
    rw [this]
    simp [restrictAt]

private theorem restrict_toQ_aux {X T : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    (ι : T ⟶ X) (P : MMP.Mori.PrimeDivisor X) (hηP : ι (genericPoint T) = P.genericPoint)
    (D : MMP.Mori.Divisor X) (h : D.coeff P = 0) :
    (MMP.Mori.Divisor.toQDivisor D).restrict ι = MMP.Mori.Divisor.toQDivisor (D.restrict ι) := by
  refine Finsupp.ext fun Q => ?_
  have hq : (MMP.Mori.Divisor.toQDivisor D).coeff P = 0 := by
    simp [h]
  calc (MMP.Mori.Divisor.toQDivisor D).restrict ι Q =
        restrictAt ι Q (MMP.Mori.Divisor.toQDivisor D) :=
        coeff_restrict_eq_restrictAt ι P hηP _ hq Q
    _ = ((restrictAt ι Q D : ℤ) : ℚ) := restrictAt_toQ ι Q D
    _ = (MMP.Mori.Divisor.toQDivisor (D.restrict ι)) Q := by
      rw [← coeff_restrict_eq_restrictAt ι P hηP D h Q]
      exact (MMP.Mori.Divisor.coeff_toQDivisor _ _).symm

end Lin

end RestrictLoc

section Adjunction

open Classical

/-- An integral closed subscheme of a normal variety, normal itself, is a normal variety. -/
private theorem isNormalVariety_comp_of_isClosedImmersion {k : Type u} [Field k]
    {X T : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (ι : T ⟶ X)
    [IsClosedImmersion ι] [IsIntegral T] [IsNormal T] : IsNormalVariety k (ι ≫ sX) := by
  have := hX.1
  exact ⟨⟨⟩, inferInstance⟩

/-- On a normal variety with a canonical divisor, the divisor of a nonzero rational top form is
a canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {d : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX d)
    {τ : RationalPluriForms sX d 1} (hτ : τ ≠ 0) :
    (divisorOfForm τ).IsCanonicalDivisor sX d :=
  hK.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ)

/-- Along a component `T` of `S = ∑_b P_b`, with the `P_b` pairwise disjoint, the restriction of
`S` sees only the component `P_a` containing `T`. -/
private theorem restrictAt_sum_single_eq {X T : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {J : Type*} [Fintype J]
    (P : J → MMP.Mori.PrimeDivisor X)
    (hdisj : Pairwise fun a b => Disjoint ((P a).support : Set X) (P b).support)
    (ι : T ⟶ X) (Q : MMP.Mori.PrimeDivisor T) (a : J) (hQ : ι Q.genericPoint ∈ (P a).support) :
    restrictAt ι Q (∑ b, Finsupp.single (P b) (1 : ℤ)) =
      restrictAt ι Q (Finsupp.single (P a) (1 : ℤ)) := by
  rw [map_sum, Finset.sum_eq_single a]
  · intro b _ hba
    simp only [restrictAt, Finsupp.liftAddHom_apply_single, AddMonoidHom.smul_apply,
      AddMonoidHom.id_apply]
    rw [MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem ι (P b)
      (fun h => Set.disjoint_left.mp (hdisj hba) h hQ), zero_smul]
  · simp

/-- The restriction of `D + B`, for a divisor `D` and a `ℚ`-divisor `B` without component `P`. -/
private theorem restrict_toQDivisor_add {X T : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    (ι : T ⟶ X) (P : MMP.Mori.PrimeDivisor X) (hηP : ι (genericPoint T) = P.genericPoint)
    (D : MMP.Mori.Divisor X) (hD : D.coeff P = 0) (B : QDivisor X) (hB : B.coeff P = 0) :
    (Divisor.toQDivisor D + B).restrict ι = Divisor.toQDivisor (D.restrict ι) + B.restrict ι := by
  rw [restrict_add_aux ι P hηP _ B (by simp [hD]) hB, restrict_toQ_aux ι P hηP D hD]

/-- `div τ + S` has no component `P_a` when `ord_{P_a} τ = -1`. -/
private theorem coeff_divisorOfForm_add_sum_single {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {J : Type*} [Fintype J] (P : J → MMP.Mori.PrimeDivisor X)
    (hdisj : Pairwise fun a b => Disjoint ((P a).support : Set X) (P b).support) (a : J) {d : ℕ}
    {τ : RationalPluriForms sX d 1} (hτ : (P a).ordForm τ = -1) :
    (divisorOfForm τ + ∑ b, Finsupp.single (P b) (1 : ℤ)).coeff (P a) = 0 := by
  have hxa : (P a).genericPoint ∈ (P a).support :=
    MMP.Positivity.PrimeDivisor.genericPoint_mem_support' (P a)
  change (divisorOfForm τ).coeff (P a) + (∑ b, Finsupp.single (P b) (1 : ℤ)) (P a) = 0
  rw [coeff_sum_single_eq P hdisj a _ hxa (P a) hxa, if_pos rfl]
  change (P a).ordForm τ + 1 = 0
  rw [hτ]; rfl

section Component

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
  {J : Type*} [Fintype J] {T : J → Scheme.{u}} (ι : ∀ a, T a ⟶ X)
  [∀ a, IsClosedImmersion (ι a)] [∀ a, IsIntegral (T a)] [∀ a, IsNormal (T a)]
  [∀ a, IsLocallyNoetherian (T a)] [∀ a, CompactSpace (T a)]
  (P : J → MMP.Mori.PrimeDivisor X) (hP : ∀ a, Set.range (ι a).base = ((P a).support : Set X))
  (hdisj : Pairwise fun a b => Disjoint ((P a).support : Set X) (P b).support)

include hdim hP hdisj

/-- **The adjunction formula on a component.** If `ord_{P_a} τ = -1` and `ρ = Res_{T_a} τ`, then
`(div τ + S)|_{T_a} = div ρ`. -/
private theorem restrict_divisorOfForm_add_eq
    (hreg : ∀ a (Q : MMP.Mori.PrimeDivisor (T a)),
      IsRegularLocalRing (X.presheaf.stalk (ι a Q.genericPoint)))
    (a : J) {τ : RationalPluriForms sX (n + 1) 1} (hτ0 : τ ≠ 0) (hτ : (P a).ordForm τ = -1)
    {ρ : RationalPluriForms (ι a ≫ sX) n 1}
    (hρ : MMP.Fourfold.IsPoincareResidue sX (ι a) n 1 τ ρ) :
    (divisorOfForm τ + ∑ b, Finsupp.single (P b) (1 : ℤ)).restrict (ι a) = divisorOfForm ρ := by
  have hηP := map_genericPoint_eq (ι a) (P a) (hP a)
  have h1 := coeff_divisorOfForm_add_sum_single P hdisj a hτ
  have h2 : (divisorOfForm τ + Finsupp.single (P a) (1 : ℤ)).coeff (P a) = 0 := by
    change (P a).ordForm τ + Finsupp.single (P a) (1 : ℤ) (P a) = 0
    rw [hτ, Finsupp.single_eq_same]; rfl
  rw [divisorOfForm_eq_restrict_of_isPoincareResidue sX hdim (ι a) (P a) hηP τ hτ0 hτ
    (hreg a) hρ]
  refine Finsupp.ext fun Q => ?_
  have hQ : ι a Q.genericPoint ∈ (P a).support := (hP a) ▸ ⟨Q.genericPoint, rfl⟩
  change ((divisorOfForm τ + ∑ b, Finsupp.single (P b) (1 : ℤ)).restrict (ι a)).coeff Q =
    ((divisorOfForm τ + Finsupp.single (P a) (1 : ℤ)).restrict (ι a)).coeff Q
  rw [coeff_restrict_eq_restrictAt (ι a) (P a) hηP _ h1 Q,
    coeff_restrict_eq_restrictAt (ι a) (P a) hηP _ h2 Q, map_add, map_add,
    restrictAt_sum_single_eq P hdisj (ι a) Q a hQ]

end Component

end Adjunction

/-- The residue clause of `adjunction_restrict_of_isCartierAt_coheight_eq_two`: for `ω` with a
simple pole along every `P a`, `div ω` is canonical, residues exist and are canonical, and
`(div ω + S + B)|_{T a} = div (Res ω) + B|_{T a}`. -/
private theorem residue_formula_aux
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    {J : Type*} [Fintype J] {T : J → Scheme.{u}} (ι : ∀ a, T a ⟶ X)
    [∀ a, IsClosedImmersion (ι a)] [∀ a, IsIntegral (T a)] [∀ a, IsNormal (T a)]
    [∀ a, IsLocallyNoetherian (T a)] [∀ a, CompactSpace (T a)]
    (P : J → MMP.Mori.PrimeDivisor X) (hP : ∀ a, Set.range (ι a).base = ((P a).support : Set X))
    (hdisj : Pairwise fun a b => Disjoint ((P a).support : Set X) (P b).support)
    (hcart : ∀ x : X, Order.coheight x = 2 → (∃ a, x ∈ (P a).support) →
      MMP.Flips.IsCartierAt (∑ a, Finsupp.single (P a) (1 : ℤ)) x)
    (B : QDivisor X) (hB : ∀ a, B.coeff (P a) = 0)
    (KX : Divisor X) (hKX : KX.IsCanonicalDivisor sX (n + 1)) :
    (∀ ω : RationalTopForms sX (n + 1), ω ≠ 0 → (∀ a, (P a).ordForm ω.toPluriForms = -1) →
      (topFormDivisor sX ω).IsCanonicalDivisor sX (n + 1) ∧
      ∀ a, (∃ ρ, MMP.Fourfold.IsPoincareResidue sX (ι a) n 1 ω.toPluriForms ρ) ∧
        ∀ ρ, MMP.Fourfold.IsPoincareResidue sX (ι a) n 1 ω.toPluriForms ρ →
          (divisorOfForm ρ).IsCanonicalDivisor (ι a ≫ sX) n ∧
          (Divisor.toQDivisor (topFormDivisor sX ω) +
              Divisor.toQDivisor (∑ b, Finsupp.single (P b) 1) + B).restrict (ι a) =
            Divisor.toQDivisor (divisorOfForm ρ) + B.restrict (ι a)) := by
  intro ω hω0 hω
  have hτ0 := toPluriForms_ne_zero sX hω0
  have hreg := fun a => isRegularLocalRing_stalk_map_genericPoint sX hdim ι P hP hdisj hcart a
  refine ⟨isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor hX hKX hτ0, fun a => ?_⟩
  have hηP := map_genericPoint_eq (ι a) (P a) (hP a)
  refine ⟨exists_isPoincareResidue sX hdim (ι a) (P a) hηP _ hτ0 (hω a), fun ρ hρ => ⟨?_, ?_⟩⟩
  · have hXT := isNormalVariety_comp_of_isClosedImmersion hX (ι a)
    obtain ⟨KT, hKT⟩ := exists_isCanonicalDivisor (ι a ≫ sX) hXT
      (topologicalKrullDim_eq_of_range_eq_support sX hdim (ι a) (P a) (hP a))
    exact isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor hXT hKT
      (ne_zero_of_isPoincareResidue sX hdim (ι a) (P a) hηP _ hτ0 (hω a) hρ)
  · rw [← map_add, topFormDivisor, restrict_toQDivisor_add (ι a) (P a) hηP _
      (coeff_divisorOfForm_add_sum_single P hdisj a (hω a)) B (hB a)]
    exact congrArg (Divisor.toQDivisor · + B.restrict (ι a))
      (restrict_divisorOfForm_add_eq hdim ι P hP hdisj hreg a hτ0 (hω a) hρ)

/-- `K + S + B` has no component `P a` when `K` has coefficient `-1` along `P a`. -/
private theorem coeff_toQDivisor_add_sum_single_add {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {J : Type*} [Fintype J] (P : J → MMP.Mori.PrimeDivisor X)
    (hdisj : Pairwise fun a b => Disjoint ((P a).support : Set X) (P b).support) (a : J)
    (B : QDivisor X) (hB : B.coeff (P a) = 0) {D : Divisor X} (hD : D.coeff (P a) = -1) :
    (Divisor.toQDivisor D + Divisor.toQDivisor (∑ b, Finsupp.single (P b) (1 : ℤ)) + B).coeff
      (P a) = 0 := by
  classical
  have hxa : (P a).genericPoint ∈ (P a).support :=
    MMP.Positivity.PrimeDivisor.genericPoint_mem_support' (P a)
  have hS : (∑ b, Finsupp.single (P b) (1 : ℤ) : Divisor X).coeff (P a) = 1 := by
    rw [show (∑ b, Finsupp.single (P b) (1 : ℤ) : Divisor X).coeff (P a) =
      (∑ b, Finsupp.single (P b) (1 : ℤ)) (P a) from rfl,
      coeff_sum_single_eq P hdisj a _ hxa (P a) hxa, if_pos rfl]
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor,
    Divisor.coeff_toQDivisor, hD, hS, hB]
  norm_num

/-- **The adjunction formula with the residue's divisor eliminated.** There is a canonical divisor
`D = div ω` of `X` with coefficient `-1` along every `P b` such that, for every canonical divisor
`K_S` of `T a`, `K_S + B|_{T a} = (D + S + B)|_{T a} + div ψ` for some rational function `ψ`. -/
private theorem exists_canonical_restrict_aux
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    {J : Type*} [Fintype J] {T : J → Scheme.{u}} (ι : ∀ a, T a ⟶ X)
    [∀ a, IsClosedImmersion (ι a)] [∀ a, IsIntegral (T a)] [∀ a, IsNormal (T a)]
    [∀ a, IsLocallyNoetherian (T a)] [∀ a, CompactSpace (T a)]
    (P : J → MMP.Mori.PrimeDivisor X) (hP : ∀ a, Set.range (ι a).base = ((P a).support : Set X))
    (hdisj : Pairwise fun a b => Disjoint ((P a).support : Set X) (P b).support)
    (hcart : ∀ x : X, Order.coheight x = 2 → (∃ a, x ∈ (P a).support) →
      MMP.Flips.IsCartierAt (∑ a, Finsupp.single (P a) (1 : ℤ)) x)
    (B : QDivisor X) (hB : ∀ a, B.coeff (P a) = 0)
    (KX : Divisor X) (hKX : KX.IsCanonicalDivisor sX (n + 1))
    (a : J) :
    ∃ D : Divisor X, D.IsCanonicalDivisor sX (n + 1) ∧ (∀ b, D.coeff (P b) = -1) ∧
      ∀ KS : Divisor (T a), KS.IsCanonicalDivisor (ι a ≫ sX) n →
        ∃ ψ : (RationalFunctions (T a))ˣ,
          Divisor.toQDivisor KS + B.restrict (ι a) =
            (Divisor.toQDivisor D + Divisor.toQDivisor (∑ b, Finsupp.single (P b) 1) +
              B).restrict (ι a) + Divisor.toQDivisor (principalDivisor ψ) := by
  obtain ⟨ω, hω0, hω⟩ := exists_form_ordForm_eq_neg_one sX hX hdim P
  obtain ⟨hcan, hres⟩ :=
    residue_formula_aux sX hX hdim ι P hP hdisj hcart B hB KX hKX ω hω0 hω
  refine ⟨topFormDivisor sX ω, hcan, fun b => by rw [coeff_topFormDivisor, hω b], fun KS hKS => ?_⟩
  obtain ⟨⟨ρ, hρ⟩, hρ'⟩ := hres a
  obtain ⟨hρK, heq⟩ := hρ' ρ hρ
  have hXT := isNormalVariety_comp_of_isClosedImmersion hX (ι a)
  obtain ⟨ψ, hψ⟩ :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (ι a ≫ sX) hXT hKS hρK
  refine ⟨ψ, ?_⟩
  rw [heq, show KS = divisorOfForm ρ + principalDivisor ψ by rw [← hψ]; abel, map_add]
  abel

/-- Adjunction up to `ℚ`-linear equivalence, for any canonical divisor of `X` with coefficient
`-1` along every `P b`. -/
private theorem qLinearlyEquivalent_aux
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    {J : Type*} [Fintype J] {T : J → Scheme.{u}} (ι : ∀ a, T a ⟶ X)
    [∀ a, IsClosedImmersion (ι a)] [∀ a, IsIntegral (T a)] [∀ a, IsNormal (T a)]
    [∀ a, IsLocallyNoetherian (T a)] [∀ a, CompactSpace (T a)]
    (P : J → MMP.Mori.PrimeDivisor X) (hP : ∀ a, Set.range (ι a).base = ((P a).support : Set X))
    (hdisj : Pairwise fun a b => Disjoint ((P a).support : Set X) (P b).support)
    (hcart : ∀ x : X, Order.coheight x = 2 → (∃ a, x ∈ (P a).support) →
      MMP.Flips.IsCartierAt (∑ a, Finsupp.single (P a) (1 : ℤ)) x)
    (B : QDivisor X) (hB : ∀ a, B.coeff (P a) = 0)
    (KX : Divisor X) (hKX : KX.IsCanonicalDivisor sX (n + 1)) :
    (∀ KX' : Divisor X, KX'.IsCanonicalDivisor sX (n + 1) → (∀ b, KX'.coeff (P b) = -1) →
      ∀ a (KS : Divisor (T a)),
      KS.IsCanonicalDivisor (ι a ≫ sX) n →
      QDivisor.QLinearlyEquivalent
        ((Divisor.toQDivisor KX' + Divisor.toQDivisor (∑ b, Finsupp.single (P b) 1) + B).restrict
          (ι a)) (Divisor.toQDivisor KS + B.restrict (ι a))) := by
  intro KX' hKX' hKX'P a KS hKS
  obtain ⟨D, hD, hDP, hKSeq⟩ :=
    exists_canonical_restrict_aux sX hX hdim ι P hP hdisj hcart B hB KX hKX a
  obtain ⟨ψ, hψ⟩ := hKSeq KS hKS
  obtain ⟨χ, hχ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hKX' hD
  have hηP := map_genericPoint_eq (ι a) (P a) (hP a)
  have hker := exists_ker_stalkMap_eq_span sX hdim ι P hP hdisj hcart a
  have hreg := isRegularLocalRing_stalk_map_genericPoint sX hdim ι P hP hdisj hcart a
  have hχP : (principalDivisor χ).coeff (P a) = 0 := by
    rw [← hχ, DivisorWithCoeffs.coeff_sub, hKX'P, hDP, sub_self]
  have hL := coeff_toQDivisor_add_sum_single_add P hdisj a B (hB a) (hDP a)
  obtain ⟨χT, hχT⟩ := restrict_principal_aux (ι a) (P a) hηP hker hreg χ hχP
  have e : Divisor.toQDivisor KX' + Divisor.toQDivisor (∑ b, Finsupp.single (P b) 1) + B =
      (Divisor.toQDivisor D + Divisor.toQDivisor (∑ b, Finsupp.single (P b) 1) + B) +
        Divisor.toQDivisor (principalDivisor χ) := by
    rw [show KX' = D + principalDivisor χ by rw [← hχ]; abel, map_add]
    abel
  rw [e, restrict_add_aux (ι a) (P a) hηP _ _ hL (by simp [hχP]),
    restrict_toQ_aux (ι a) (P a) hηP _ hχP, hχT, hψ]
  refine ⟨1, one_pos, χT * ψ⁻¹, ?_⟩
  rw [MMP.Mori.principalDivisor_mul, MMP.Mori.principalDivisor_inv, map_add, map_neg, Nat.cast_one,
    one_smul]
  abel

/-- The Cartier clause of `adjunction_restrict_of_isCartierAt_coheight_eq_two`: `K_{T a} +
B|_{T a}` is `ℚ`-Cartier, and Cartier when `K_X + S + B` is. -/
private theorem isQCartier_aux
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    {J : Type*} [Fintype J] {T : J → Scheme.{u}} (ι : ∀ a, T a ⟶ X)
    [∀ a, IsClosedImmersion (ι a)] [∀ a, IsIntegral (T a)] [∀ a, IsNormal (T a)]
    [∀ a, IsLocallyNoetherian (T a)] [∀ a, CompactSpace (T a)]
    (P : J → MMP.Mori.PrimeDivisor X) (hP : ∀ a, Set.range (ι a).base = ((P a).support : Set X))
    (hdisj : Pairwise fun a b => Disjoint ((P a).support : Set X) (P b).support)
    (hcart : ∀ x : X, Order.coheight x = 2 → (∃ a, x ∈ (P a).support) →
      MMP.Flips.IsCartierAt (∑ a, Finsupp.single (P a) (1 : ℤ)) x)
    (B : QDivisor X) (hB : ∀ a, B.coeff (P a) = 0)
    (KX : Divisor X) (hKX : KX.IsCanonicalDivisor sX (n + 1))
    (hKSB : (Divisor.toQDivisor KX + Divisor.toQDivisor (∑ a, Finsupp.single (P a) 1) +
      B).IsQCartier) :
    -- (3) `K_S + B|_S` is `ℚ`-Cartier, and Cartier when `K_X + S + B` is
    (∀ a (KS : Divisor (T a)), KS.IsCanonicalDivisor (ι a ≫ sX) n →
      QDivisor.IsQCartier (Divisor.toQDivisor KS + B.restrict (ι a)) ∧
      ((Divisor.toQDivisor KX + Divisor.toQDivisor (∑ b, Finsupp.single (P b) 1) +
          B).IsCartierDivisor →
        QDivisor.IsCartierDivisor (Divisor.toQDivisor KS + B.restrict (ι a)))) := by
  intro a KS hKS
  obtain ⟨D, hD, hDP, hKSeq⟩ :=
    exists_canonical_restrict_aux sX hX hdim ι P hP hdisj hcart B hB KX hKX a
  obtain ⟨ψ, hψ⟩ := hKSeq KS hKS
  obtain ⟨χ, hχ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hKX hD
  have hηP := map_genericPoint_eq (ι a) (P a) (hP a)
  have hker := exists_ker_stalkMap_eq_span sX hdim ι P hP hdisj hcart a
  have hreg := isRegularLocalRing_stalk_map_genericPoint sX hdim ι P hP hdisj hcart a
  set L := Divisor.toQDivisor D + Divisor.toQDivisor (∑ b, Finsupp.single (P b) (1 : ℤ)) + B
    with hLdef
  have hL : L.coeff (P a) = 0 := coeff_toQDivisor_add_sum_single_add P hdisj a B (hB a) (hDP a)
  have e : Divisor.toQDivisor KX + Divisor.toQDivisor (∑ b, Finsupp.single (P b) 1) + B =
      L + Divisor.toQDivisor (principalDivisor χ) := by
    rw [hLdef, show KX = D + principalDivisor χ by rw [← hχ]; abel, map_add]
    abel
  have key : ∀ m : ℤ,
      (m • (Divisor.toQDivisor KX + Divisor.toQDivisor (∑ b, Finsupp.single (P b) 1) +
        B)).IsCartierDivisor →
      (m • (Divisor.toQDivisor KS + B.restrict (ι a))).IsCartierDivisor := by
    rintro m ⟨D', hD', hcD'⟩
    set D'' := D' - m • principalDivisor χ with hD''def
    have hD'' : Divisor.toQDivisor D'' = m • L := by
      rw [hD''def, map_sub, hD', e, map_zsmul, smul_add, add_sub_cancel_right]
    have hD''P : D''.coeff (P a) = 0 := by
      have h := congrArg (fun E => DivisorWithCoeffs.coeff E (P a)) hD''
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, hL, smul_zero] at h
      exact_mod_cast h
    have hc : D''.IsCartier := hcD'.sub ((Divisor.isCartier_principalDivisor χ).zsmul m)
    have hr := isCartier_restrict_aux (ι a) (P a) hηP hker hreg D'' hc hD''P
    refine ⟨D''.restrict (ι a) + m • principalDivisor ψ, ?_,
      hr.add ((Divisor.isCartier_principalDivisor ψ).zsmul m)⟩
    rw [map_add, ← restrict_toQ_aux (ι a) (P a) hηP D'' hD''P, hD'',
      restrict_zsmul_aux (ι a) (P a) hηP m L hL, map_zsmul, hψ, smul_add]
  refine ⟨?_, fun h => ?_⟩
  · obtain ⟨m, hm, h⟩ := hKSB
    exact ⟨m, hm, key m h⟩
  · simpa using key 1 (by simpa using h)

/-- **Adjunction along a normal divisor Cartier in codimension two** (KM Remark 5.47). -/
@[mmp "lem_km5b_adjunction_cartier_codim_two"]
public theorem adjunction_restrict_of_isCartierAt_coheight_eq_two
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    {J : Type*} [Fintype J] {T : J → Scheme.{u}} (ι : ∀ a, T a ⟶ X)
    [∀ a, IsClosedImmersion (ι a)] [∀ a, IsIntegral (T a)] [∀ a, IsNormal (T a)]
    [∀ a, IsLocallyNoetherian (T a)] [∀ a, CompactSpace (T a)]
    (P : J → PrimeDivisor X) (hP : ∀ a, Set.range (ι a).base = ((P a).support : Set X))
    (hdisj : Pairwise fun a b => Disjoint ((P a).support : Set X) (P b).support)
    (hcart : ∀ x : X, Order.coheight x = 2 → (∃ a, x ∈ (P a).support) →
      MMP.Flips.IsCartierAt (∑ a, Finsupp.single (P a) (1 : ℤ)) x)
    (B : QDivisor X) (hB : ∀ a, B.coeff (P a) = 0)
    (KX : Divisor X) (hKX : KX.IsCanonicalDivisor sX (n + 1))
    (hKSB : (Divisor.toQDivisor KX + Divisor.toQDivisor (∑ a, Finsupp.single (P a) 1) +
      B).IsQCartier) :
    -- (1) regularity at the generic points of the prime divisors of `S`
    (∀ a (Q : PrimeDivisor (T a)),
      IsRegularLocalRing (X.presheaf.stalk (ι a Q.genericPoint)) ∧
        IsRegularLocalRing ((T a).presheaf.stalk Q.genericPoint)) ∧
    -- (2) forms with a simple pole along `S`, residues and the adjunction formula
    (∃ ω : RationalTopForms sX (n + 1), ω ≠ 0 ∧ ∀ a, (P a).ordForm ω.toPluriForms = -1) ∧
    (∀ ω : RationalTopForms sX (n + 1), ω ≠ 0 → (∀ a, (P a).ordForm ω.toPluriForms = -1) →
      (topFormDivisor sX ω).IsCanonicalDivisor sX (n + 1) ∧
      ∀ a, (∃ ρ, MMP.Fourfold.IsPoincareResidue sX (ι a) n 1 ω.toPluriForms ρ) ∧
        ∀ ρ, MMP.Fourfold.IsPoincareResidue sX (ι a) n 1 ω.toPluriForms ρ →
          (divisorOfForm ρ).IsCanonicalDivisor (ι a ≫ sX) n ∧
          (Divisor.toQDivisor (topFormDivisor sX ω) +
              Divisor.toQDivisor (∑ b, Finsupp.single (P b) 1) + B).restrict (ι a) =
            Divisor.toQDivisor (divisorOfForm ρ) + B.restrict (ι a)) ∧
    (∀ KX' : Divisor X, KX'.IsCanonicalDivisor sX (n + 1) → (∀ b, KX'.coeff (P b) = -1) →
      ∀ a (KS : Divisor (T a)),
      KS.IsCanonicalDivisor (ι a ≫ sX) n →
      QDivisor.QLinearlyEquivalent
        ((Divisor.toQDivisor KX' + Divisor.toQDivisor (∑ b, Finsupp.single (P b) 1) + B).restrict
          (ι a)) (Divisor.toQDivisor KS + B.restrict (ι a))) ∧
    -- (3) `K_S + B|_S` is `ℚ`-Cartier, and Cartier when `K_X + S + B` is
    (∀ a (KS : Divisor (T a)), KS.IsCanonicalDivisor (ι a ≫ sX) n →
      QDivisor.IsQCartier (Divisor.toQDivisor KS + B.restrict (ι a)) ∧
      ((Divisor.toQDivisor KX + Divisor.toQDivisor (∑ b, Finsupp.single (P b) 1) +
          B).IsCartierDivisor →
        QDivisor.IsCartierDivisor (Divisor.toQDivisor KS + B.restrict (ι a)))) :=
  ⟨fun a Q => ⟨isRegularLocalRing_stalk_map_genericPoint sX hdim ι P hP hdisj hcart a Q,
      isRegularLocalRing_stalk_genericPoint Q⟩,
    exists_form_ordForm_eq_neg_one sX hX hdim P,
    residue_formula_aux sX hX hdim ι P hP hdisj hcart B hB KX hKX,
    qLinearlyEquivalent_aux sX hX hdim ι P hP hdisj hcart B hB KX hKX,
    isQCartier_aux sX hX hdim ι P hP hdisj hcart B hB KX hKX hKSB⟩

/-! ## Adjunction on a log resolution -/

/-- The image under `f` of the strict transform `S' = f⁻¹_* S` lies in `S`. -/
private theorem map_mem_support {X Y : Scheme.{u}} (f : Y ⟶ X) (P : PrimeDivisor X)
    (P' : PrimeDivisor Y) (hP' : inverseTransformPrimeDivisor f P = some P') :
    ∀ y ∈ (P'.support : Set Y), f y ∈ (P.support : Set X) := by
  intro y ht
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at ht ⊢
  have hg :=
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP').1
  have h2 := image_closure_subset_closure_image f.continuous ⟨_, ht, rfl⟩
  rw [Set.image_singleton, hg] at h2
  exact h2

/-- The kernel of a closed immersion from a reduced scheme is the vanishing ideal of its
image. -/
private theorem ker_eq_vanishingIdeal {A B : Scheme.{u}} (g : A ⟶ B) [IsReduced A]
    [IsClosedImmersion g] :
    g.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range g.base)) := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  simp only [TopologicalSpace.Closeds.coe_top, Set.image_univ]

/-- The restriction `f_S` exists: `ι' ≫ f` factors through the closed immersion `ι`, since `T'`
is reduced and `f` maps `S' = f⁻¹_* S` into `S`. -/
private theorem exists_comp_eq {X Y T T' : Scheme.{u}} (f : Y ⟶ X) (ι : T ⟶ X)
    [IsClosedImmersion ι] (P : PrimeDivisor X) (hP : Set.range ι.base = (P.support : Set X))
    (P' : PrimeDivisor Y) (hP' : inverseTransformPrimeDivisor f P = some P')
    (ι' : T' ⟶ Y) [IsClosedImmersion ι'] [IsReduced T']
    (hι' : Set.range ι'.base = (P'.support : Set Y)) :
    ∃ fS : T' ⟶ T, fS ≫ ι = ι' ≫ f := by
  have hsub : Set.range (ι' ≫ f).base ⊆ (P.support : Set X) := by
    rintro _ ⟨t, rfl⟩
    exact map_mem_support f P P' hP' _ (hι' ▸ ⟨t, rfl⟩)
  have H : ι.ker ≤ (ι' ≫ f).ker := by
    have h1 : (ι' ≫ f).ker = Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range (ι' ≫ f).base)) := by
      rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
        ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
      simp
    rw [h1, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
      TopologicalSpace.Closeds.closure_le]
    refine hsub.trans ?_
    rw [← hP]
    exact Scheme.Hom.range_subset_ker_support _
  exact ⟨IsClosedImmersion.lift ι (ι' ≫ f) H, IsClosedImmersion.lift_fac _ _ _⟩

/-- `S'` is smooth: it is a component of the snc divisor `Ex(f) ∪ f⁻¹ Supp(S + B)`, whose
components are smooth, and `T'` is that component with its reduced structure. -/
private theorem isSmoothScheme_aux
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {T : Scheme.{u}} (ι : T ⟶ X) (P : PrimeDivisor X) (B : QDivisor X) (hB : B.coeff P = 0)
    {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsLogResolution sX (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single P 1) + B)) f)
    (hY : IsNormalVariety k (f ≫ sX))
    (P' : PrimeDivisor Y) (hP' : inverseTransformPrimeDivisor f P = some P')
    {T' : Scheme.{u}} (ι' : T' ⟶ Y) [IsClosedImmersion ι'] [IsIntegral T']
    (hι' : Set.range ι'.base = (P'.support : Set Y))
    (fS : T' ⟶ T) (hfS : fS ≫ ι = ι' ≫ f) : IsSmoothScheme (fS ≫ ι ≫ sX) := by
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNormal Y := hY.2
  have hg := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hP').1
  -- the generic point of `S'` lies in `f⁻¹ Supp(S + B)`
  have hmem : (P'.genericPoint : Y) ∈ ((exceptionalSet f ⊔
      (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single P 1) + B)).supp.preimage
        f.continuous : TopologicalSpace.Closeds Y) : Set Y) := by
    refine Or.inr ?_
    show f P'.genericPoint ∈
      (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single P 1) + B)).supp
    rw [hg, DivisorWithCoeffs.mem_supp_iff]
    refine ⟨P, ?_, ?_⟩
    · simp [DivisorWithCoeffs.coeff_single_self, hB]
    · exact MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P
  rcases hf.isSNCSubset with h0 | ⟨s, hs, hsnc⟩
  · rw [h0] at hmem
    exact hmem.elim
  rw [← hs] at hmem
  obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.mp hmem
  have hEP : E = P' := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E P' hPE
  subst hEP
  have hsupp : E ∈ (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support := by
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply,
      Finset.sum_eq_single_of_mem E hE (fun b _ hb => Finsupp.single_eq_of_ne' hb)]
    simp
  have hsm := hsnc.1 E hsupp
  -- `T'` is the reduced closed subscheme `E`
  haveI : IsIntegral E.idealSheaf.subscheme := E.integral
  have hker : ι'.ker = E.idealSheaf.subschemeι.ker := by
    rw [ker_eq_vanishingIdeal ι', ker_eq_vanishingIdeal E.idealSheaf.subschemeι, hι',
      Scheme.IdealSheafData.range_subschemeι]
  set g := IsClosedImmersion.lift E.idealSheaf.subschemeι ι' hker.symm.le
  haveI : IsIso g := IsClosedImmersion.isIso_lift E.idealSheaf.subschemeι ι' hker.symm
  have hfac : g ≫ E.idealSheaf.subschemeι = ι' := IsClosedImmersion.lift_fac _ _ _
  have heq : fS ≫ ι ≫ sX = g ≫ E.idealSheaf.subschemeι ≫ f ≫ sX := by
    rw [reassoc_of% hfS, reassoc_of% hfac]
  rw [heq]
  haveI : LocallyOfFiniteType (E.idealSheaf.subschemeι ≫ f ≫ sX) := inferInstance
  haveI : Smooth (E.idealSheaf.subschemeι ≫ f ≫ sX) := (isSmoothScheme_iff _).1 hsm
  haveI : LocallyOfFiniteType (g ≫ E.idealSheaf.subschemeι ≫ f ≫ sX) := inferInstance
  exact (isSmoothScheme_iff _).2 inferInstance

/-- `f_S : S' ⟶ S` is birational: over the biregular locus `W` of `f`, both `S ∩ W` and
`f(S' ∩ f⁻¹ W)` are the reduced closed subscheme of `W` with support the closure of `η_S`. -/
private theorem isBirationalMorphism_aux {X Y T T' : Scheme.{u}} (f : Y ⟶ X) (ι : T ⟶ X)
    [IsClosedImmersion ι] [IsIntegral T] (P : PrimeDivisor X)
    (hP : Set.range ι.base = (P.support : Set X))
    (P' : PrimeDivisor Y) (hP' : inverseTransformPrimeDivisor f P = some P')
    (ι' : T' ⟶ Y) [IsClosedImmersion ι'] [IsIntegral T']
    (hι' : Set.range ι'.base = (P'.support : Set Y))
    (fS : T' ⟶ T) (hfS : fS ≫ ι = ι' ≫ f) : IsBirationalMorphism fS := by
  have hW : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  obtain ⟨hg, hgW⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP'
  have hUV : ι' ⁻¹ᵁ (f ⁻¹ᵁ biregularLocus f) ≤ fS ⁻¹ᵁ (ι ⁻¹ᵁ biregularLocus f) := by
    intro t ht
    have : (fS ≫ ι).base t = (ι' ≫ f).base t := by rw [hfS]
    change (fS ≫ ι).base t ∈ biregularLocus f
    rw [this]
    exact ht
  obtain ⟨t0, ht0⟩ : (P'.genericPoint : Y) ∈ Set.range ι'.base :=
    hι' ▸ MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P'
  obtain ⟨s0, hs0⟩ : (P.genericPoint : X) ∈ Set.range ι.base :=
    hP ▸ MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P
  have ht0U : t0 ∈ ι' ⁻¹ᵁ (f ⁻¹ᵁ biregularLocus f) := by
    change f.base (ι'.base t0) ∈ biregularLocus f
    rw [ht0]; exact hgW
  have hs0V : s0 ∈ ι ⁻¹ᵁ biregularLocus f := by
    change ι.base s0 ∈ biregularLocus f
    rw [hs0, ← hg]; exact hgW
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE fS _ _ ⟨t0, ht0U⟩ ⟨s0, hs0V⟩ hUV ?_
  haveI : IsClosedImmersion (ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  have hcomp : fS.resLE _ _ hUV ≫ (ι ∣_ biregularLocus f) =
      ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫ (f ∣_ biregularLocus f) := by
    rw [← cancel_mono (biregularLocus f).ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, hfS]
  haveI hci : IsClosedImmersion
      (ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫ (f ∣_ biregularLocus f)) := inferInstance
  refine IsClosedImmersion.isIso_of_ker_eq _ _ _ hcomp ?_
  rw [ker_eq_vanishingIdeal, ker_eq_vanishingIdeal]
  congr 1
  have hfac : ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫ (f ∣_ biregularLocus f) ≫
      (biregularLocus f).ι = (ι' ⁻¹ᵁ (f ⁻¹ᵁ biregularLocus f)).ι ≫ ι' ≫ f := by
    simp only [morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc]
  have hfac' : (ι ∣_ biregularLocus f) ≫ (biregularLocus f).ι =
      (ι ⁻¹ᵁ biregularLocus f).ι ≫ ι := morphismRestrict_ι _ _
  apply le_antisymm
  · rw [TopologicalSpace.Closeds.closure_le]
    rintro _ ⟨t, rfl⟩
    apply subset_closure
    have h1 : ((ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫ (f ∣_ biregularLocus f)).base t).1
        = f.base (ι'.base t.1) := congrArg (fun g => g.base t) hfac
    obtain ⟨a, ha⟩ : ((ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫
        (f ∣_ biregularLocus f)).base t).1 ∈ Set.range ι.base := by
      rw [hP, h1]; exact map_mem_support f P P' hP' _ (hι' ▸ ⟨t.1, rfl⟩)
    have haV : a ∈ ι ⁻¹ᵁ biregularLocus f := by
      change ι.base a ∈ biregularLocus f
      rw [ha]; exact Subtype.property _
    refine ⟨⟨a, haV⟩, Subtype.ext ?_⟩
    exact (congrArg (fun g => g.base ⟨a, haV⟩) hfac').trans ha
  · rw [TopologicalSpace.Closeds.closure_le]
    rintro _ ⟨a, rfl⟩
    have e1 : (biregularLocus f).ι.base ((ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫
        (f ∣_ biregularLocus f)).base ⟨t0, ht0U⟩) = P.genericPoint := by
      refine (congrArg (fun g => g.base ⟨t0, ht0U⟩) hfac).trans ?_
      change f.base (ι'.base t0) = _
      rw [ht0, hg]
    have e2 : (biregularLocus f).ι.base ((ι ∣_ biregularLocus f).base a) = ι.base a.1 :=
      congrArg (fun g => g.base a) hfac'
    have hη : (ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫
        (f ∣_ biregularLocus f)).base ⟨t0, ht0U⟩ ⤳ (ι ∣_ biregularLocus f).base a := by
      rw [← (biregularLocus f).ι.isOpenEmbedding.isInducing.specializes_iff, e1, e2,
        specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← hP]
      exact ⟨a.1, rfl⟩
    exact hη.mem_closed (TopologicalSpace.Closeds.isClosed _) (subset_closure ⟨_, rfl⟩)

/-! ### Generic facts on discrepancies, restrictions, residues and pull-backs -/

/-- A discrepancy computed with a canonical divisor `K` is one for every canonical divisor
`K'` linearly equivalent to `K`. -/
private theorem isDiscrepancy_of_linearlyEquivalent {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {n : ℕ} {K K' : Divisor X} {Δ : QDivisor X} {D : DivisorOver k sX} {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) (hK' : K'.IsCanonicalDivisor sX n)
    (hKK' : K.LinearlyEquivalent K') : IsDiscrepancy sX n K' Δ D a := by
  obtain ⟨hX, -, m, hm, ⟨M, hM, hMc⟩, rest⟩ := ha
  obtain ⟨φ, hφ⟩ := hKK'
  refine ⟨hX, hK', m, hm, ⟨M - (m : ℤ) • principalDivisor φ, ?_,
    hMc.sub ((Divisor.isCartier_principalDivisor φ).zsmul _)⟩, rest⟩
  rw [map_sub, map_zsmul, hM, ← hφ, map_sub, smul_add, smul_add, smul_sub]
  abel

/-- The coefficients of the restriction of a divisor without component `P` along a closed
immersion of an integral scheme onto `P`. -/
private theorem coeff_restrict_eq_sum {R : Type*} [AddCommMonoid R] {X T : Scheme.{u}}
    [IsIntegral T] [TopologicalSpace.NoetherianSpace T] (ι : T ⟶ X) (P : PrimeDivisor X)
    (hgen : ι (genericPoint T) = P.genericPoint) (D : DivisorWithCoeffs R X) (hD : D.coeff P = 0)
    (Q : PrimeDivisor T) :
    (D.restrict ι).coeff Q = D.sum fun E d => E.intersectionLength ι Q • d := by
  have hgen' : ∀ s : T, Order.coheight s = 0 → s = genericPoint T := fun s hs => by
    have hle : s ≤ genericPoint T := genericPoint_specializes s
    exact (Specializes.antisymm (Order.coheight_eq_zero.mp hs hle) hle).eq
  refine DivisorWithCoeffs.coeff_restrict_of_pure ι D (fun s hs => ?_) (fun E hE s hs hjs => ?_) Q
  · rw [hgen' s hs, hgen]; exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  · rw [hgen' s hs, hgen] at hjs
    have : P = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hjs
    rw [Finsupp.mem_support_iff, ← this] at hE
    exact hE hD

/-- Multiplying a residue presentation by `φ ∈ 𝒪_{Y,y}` multiplies the residue by `φ̄`. -/
private theorem isPoincareResidue_smul {k : Type u} [Field k] {Y T : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral T] {j : T ⟶ Y}
    {n : ℕ} {σ : RationalPluriForms sY (n + 1) 1} {ρ : RationalPluriForms (j ≫ sY) n 1}
    (h : MMP.Fourfold.IsPoincareResidue sY j n 1 σ ρ)
    (φ : Y.presheaf.stalk (j (genericPoint T))) :
    letI := functionFieldAlgebra sY
    MMP.Fourfold.IsPoincareResidue sY j n 1 (algebraMap _ Y.functionField φ • σ)
      ((j.stalkMap (genericPoint T)).hom φ • ρ) := by
  obtain ⟨t, g, x, ht, hσ, hρ⟩ := h
  refine ⟨t, φ * g, x, ht, ?_, ?_⟩
  · rw [hσ, map_mul, mul_smul]
    rfl
  · rw [hρ, map_mul, mul_smul]
    rfl

/-- **Pull-back coefficients through a rational function.** If `M` is a Cartier divisor on `X`,
`M'` its pull-back along a dominant `f : Y ⟶ X`, and `r` a rational function on `X` with
`v_Γ(r) = c · coeff_Γ(M)` along every prime divisor `Γ` through `f(η_F)`, then
`c · coeff_F(M') = v_F(f^* r)`. -/
private theorem mul_coeff_isPullback_eq_ord {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} [IsDominant f] {M : Divisor X} (hMc : M.IsCartier)
    {hM : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ M.supp}
    {M' : Divisor Y} (h : M.IsPullback f hM M') (F : PrimeDivisor Y)
    {r : X.functionField} (hr : r ≠ 0) (c : ℤ)
    (hrc : ∀ Γ : PrimeDivisor X, f F.genericPoint ∈ Γ.support →
      X.ord r Γ.genericPoint = c * M.coeff Γ) :
    c * M'.coeff F = Y.ord (functionFieldMap f r) F.genericPoint := by
  obtain ⟨U, hU, φ, hφ⟩ := hMc (f F.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ F hU
    (pointComponent (f F.genericPoint))]
  set a := MMP.Threefold.Mori.Helpers.evalFF (pointComponent (f F.genericPoint))
    (φ : RationalFunctions X) with ha_def
  have ha : a ≠ 0 := (φ.isUnit.map _).ne_zero
  have hs : a ^ c * r⁻¹ ≠ 0 := mul_ne_zero (zpow_ne_zero _ ha) (inv_ne_zero hr)
  obtain ⟨u, hu, hus⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero (X := X)
    (f F.genericPoint) hs (fun Γ hΓ => by
      have hΓU : (Γ.support ∩ U).Nonempty := ⟨_, hΓ, hU⟩
      have hcomp : a = MMP.Threefold.Mori.Helpers.evalFF Γ.component
          (φ : RationalFunctions X) := by
        rw [ha_def, Subsingleton.elim
          (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X))
          (pointComponent (f F.genericPoint)) Γ.component]
      rw [Scheme.ord_mul (zpow_ne_zero _ ha) (inv_ne_zero hr), ord_zpow _ ha, ord_inv hr _,
        hrc Γ hΓ, hφ Γ hΓU, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, ← hcomp]
      ring)
  have h1 := functionFieldMap_algebraMap_stalk f F.genericPoint u
  rw [hus] at h1
  have h0 : Y.ord (functionFieldMap f (a ^ c * r⁻¹)) F.genericPoint = 0 := by
    rw [h1]; exact F.ord_algebraMap_of_isUnit (hu.map _)
  have hfa : functionFieldMap f a ≠ 0 := (map_ne_zero _).mpr ha
  have hfr : functionFieldMap f r ≠ 0 := (map_ne_zero _).mpr hr
  rw [map_mul, map_zpow₀, map_inv₀, Scheme.ord_mul (zpow_ne_zero _ hfa) (inv_ne_zero hfr),
    ord_zpow _ hfa, ord_inv hfr _] at h0
  linarith

/-- **The restriction of the divisor of a unit, through residues.** Let `j : T ⟶ Y` be an
integral closed subscheme with generic point that of the prime divisor `P`, on which the
divisor of the residue of every form `τ` with `ord_P τ = -1` is `(div τ + P)|_T`. Then for a unit
`u` of `𝒪_{Y,η_P}` and every prime divisor `Q` of `T`, `v_Q(ū) = coeff_Q(div(u)|_T)`: the
residue of `u τ` is `ū ρ`. -/
private theorem ord_stalkMap_eq_sum_of_isPoincareResidue {k : Type u} [Field k] [PerfectField k]
    {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY] {n : ℕ}
    (hdY : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = n + 1)
    {j : T ⟶ Y} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [LocallyOfFiniteType (j ≫ sY)]
    (hdT : letI := functionFieldAlgebra (j ≫ sY); (Algebra.trdeg k T.functionField).toNat = n)
    {P : PrimeDivisor Y} (hP : j (genericPoint T) = P.genericPoint)
    (hres : ∀ (τ : RationalPluriForms sY (n + 1) 1) (ρ : RationalPluriForms (j ≫ sY) n 1),
      τ ≠ 0 → P.ordForm τ = -1 → MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ →
      ∀ Q : PrimeDivisor T, Q.ordForm ρ = (divisorOfForm τ + Finsupp.single P 1).sum
        fun E d => E.intersectionLength j Q • d)
    {τ : RationalPluriForms sY (n + 1) 1} {ρ : RationalPluriForms (j ≫ sY) n 1}
    (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1) (hρ0 : ρ ≠ 0)
    (hρ : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ)
    {u : Y.presheaf.stalk (j (genericPoint T))} (hu : IsUnit u) {M : Divisor Y}
    (hM : ∀ E : PrimeDivisor Y,
      M.coeff E = Y.ord (algebraMap _ Y.functionField u) E.genericPoint)
    (Q : PrimeDivisor T) :
    T.ord ((j.stalkMap (genericPoint T)).hom u) Q.genericPoint =
      M.sum fun E d => E.intersectionLength j Q • d := by
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  have hau : algebraMap _ Y.functionField u ≠ 0 := (hu.map _).ne_zero
  have hju : (j.stalkMap (genericPoint T)).hom u ≠ 0 := (hu.map _).ne_zero
  have hτ'0 : algebraMap _ Y.functionField u • τ ≠ 0 := smul_ne_zero hau hτ0
  have hρ' := isPoincareResidue_smul hρ u
  have hsp : P.genericPoint ⤳ j (genericPoint T) := hP ▸ specializes_rfl
  have hordP : Y.ord (algebraMap _ Y.functionField u) P.genericPoint = 0 := by
    rw [← algebraMap_stalkSpecializes hsp u]
    exact P.ord_algebraMap_of_isUnit (hu.map _)
  have hτ' : P.ordForm (algebraMap _ Y.functionField u • τ) = -1 := by
    rw [P.ordForm_smul hdY hau hτ0, hordP, hτ, zero_add]
  have h1 := hres _ _ hτ'0 hτ' hρ' Q
  have h2 := hres _ _ hτ0 hτ hρ Q
  rw [Q.ordForm_smul hdT hju hρ0] at h1
  have hdiv : divisorOfForm (algebraMap _ Y.functionField u • τ) = divisorOfForm τ + M := by
    refine Finsupp.ext fun E => ?_
    rw [Finsupp.add_apply]
    change E.ordForm _ = E.ordForm τ + M.coeff E
    rw [E.ordForm_smul hdY hau hτ0, hM]
    ring
  rw [hdiv, add_right_comm, Finsupp.sum_add_index' (fun _ => smul_zero _)
    (fun _ _ _ => smul_add _ _ _), ← h2] at h1
  linarith

/-! ### Residues commute with pull-back to the strict transform -/

section ResiduePullback

open KaehlerDifferential

private theorem subsingletonEquiv_basis_one {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    (b : Module.Basis Unit K L) :
    PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => L) 0
      (ZTensorPower.basis b 1 ()) = b () := by
  erw [ZTensorPower.basis_ofNat b 1]
  exact PiTensorProduct.subsingletonEquiv_apply_tprod _ _

/-- Pull-back of top forms along a pull-back generator is `topFormsMap`. -/
private theorem subsingletonEquiv_pullbackForms {k : Type u} [Field k] {K K' : Type u} [Field K]
    [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω) (τ : PluriForms k K d 1) :
    PiTensorProduct.subsingletonEquiv (R := K') (s := fun _ : Fin 1 => ⋀[K']^d Ω[K'⁄k]) 0
        (pullbackForms (K' := K') 1 τ) =
      topFormsMap k K K' d
        (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => ⋀[K]^d Ω[K⁄k]) 0 τ) := by
  rw [pullbackForms_eq hω]
  unfold pullbackFormsAlong
  set b := basisOfSpanSingleton hω.1 hω.ne_zero
  conv_rhs => rw [← basis_unit_repr_smul (ZTensorPower.basis b 1) τ]
  erw [LinearEquiv.map_smul, LinearEquiv.map_smul, subsingletonEquiv_basis_one,
    subsingletonEquiv_basis_one, LinearMap.map_smul, algebraMap_smul]
  simp [b]

/-- Transport of a residue presentation along an equality of structure morphisms. -/
private theorem subsingletonEquiv_cast {k : Type u} [Field k] {T₁ : Scheme.{u}} [IsIntegral T₁]
    {n : ℕ} {s s' : T₁ ⟶ Spec (.of k)} (e : s = s')
    (H : RationalPluriForms s n 1 = RationalPluriForms s' n 1) (X : RationalPluriForms s n 1)
    (c : T₁.functionField) (v : Fin n → T₁.functionField)
    (hX : letI := functionFieldAlgebra s
      PiTensorProduct.subsingletonEquiv (R := T₁.functionField)
          (s := fun _ : Fin 1 => ⋀[T₁.functionField]^n Ω[T₁.functionField⁄k]) 0 X =
        c • exteriorPower.ιMulti T₁.functionField n (fun i => D k T₁.functionField (v i))) :
    letI := functionFieldAlgebra s'
    PiTensorProduct.subsingletonEquiv (R := T₁.functionField)
        (s := fun _ : Fin 1 => ⋀[T₁.functionField]^n Ω[T₁.functionField⁄k]) 0 (cast H X) =
      c • exteriorPower.ιMulti T₁.functionField n (fun i => D k T₁.functionField (v i)) := by
  subst e
  exact hX

variable {Y Y₁ T T₁ : Scheme.{u}} (g : Y₁ ⟶ Y) (j : T ⟶ Y) (j₁ : T₁ ⟶ Y₁) (h : T₁ ⟶ T)
  [IsIntegral T] [IsIntegral T₁] [IsIntegral Y] [IsIntegral Y₁] [IsDominant h] [IsDominant g]

private theorem map_genericPoint_eq_of_comp_eq (hh : h ≫ j = j₁ ≫ g) :
    g (j₁ (genericPoint T₁)) = j (genericPoint T) := by
  have := congrArg (fun f : T₁ ⟶ Y => f (genericPoint T₁)) hh
  simp only [Scheme.Hom.comp_apply] at this
  rw [← this, map_genericPoint_of_isDominant]

/-- The stalk map `𝒪_{Y, j(η_T)} → 𝒪_{Y₁, j₁(η_{T₁})}` of `g`. -/
private noncomputable def stalkMapAt (hh : h ≫ j = j₁ ≫ g) :
    Y.presheaf.stalk (j (genericPoint T)) ⟶ Y₁.presheaf.stalk (j₁ (genericPoint T₁)) :=
  (Y.presheaf.stalkCongr (.of_eq (map_genericPoint_eq_of_comp_eq g j j₁ h hh).symm)).hom ≫
    g.stalkMap (j₁ (genericPoint T₁))

private theorem stalkMapAt_functionField (hh : h ≫ j = j₁ ≫ g)
    (a : Y.presheaf.stalk (j (genericPoint T))) :
    algebraMap (Y₁.presheaf.stalk (j₁ (genericPoint T₁))) Y₁.functionField
        ((stalkMapAt g j j₁ h hh).hom a) =
      functionFieldMap g (algebraMap _ Y.functionField a) := by
  have key : stalkMapAt g j j₁ h hh ≫
        Y₁.presheaf.stalkSpecializes ((genericPoint_spec Y₁).specializes trivial) =
      Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
        (Y.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant g).symm)).hom ≫
          g.stalkMap (genericPoint Y₁) := by
    simp only [stalkMapAt, TopCat.Presheaf.stalkCongr_hom, Category.assoc]
    rw [← Scheme.Hom.stalkSpecializes_stalkMap, ← Category.assoc, ← Category.assoc]
    congr 1
    apply TopCat.Presheaf.stalk_hom_ext
    intro V hV
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes,
      TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes]
  exact congrArg (fun f => f.hom a) key

private theorem stalkMapAt_stalkMap (hh : h ≫ j = j₁ ≫ g)
    (a : Y.presheaf.stalk (j (genericPoint T))) :
    (j₁.stalkMap (genericPoint T₁)).hom ((stalkMapAt g j j₁ h hh).hom a) =
      functionFieldMap h ((j.stalkMap (genericPoint T)).hom a) := by
  have key : stalkMapAt g j j₁ h hh ≫ j₁.stalkMap (genericPoint T₁) =
      j.stalkMap (genericPoint T) ≫
        (T.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant h).symm)).hom ≫
          h.stalkMap (genericPoint T₁) := by
    simp only [stalkMapAt, Category.assoc, ← Scheme.Hom.stalkMap_comp]
    rw [Scheme.Hom.stalkMap_congr_point_assoc j _ _ (map_genericPoint_of_isDominant h).symm,
      ← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom (h ≫ j) (j₁ ≫ g) hh]
    simp only [TopCat.Presheaf.stalkCongr_hom]
    apply TopCat.Presheaf.stalk_hom_ext
    intro V hV
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc,
      TopCat.Presheaf.germ_stalkSpecializes_assoc]
    rfl
  exact congrArg (fun f => f.hom a) key

/-- **Residues commute with pull-back to the strict transform.** Let `g : Y₁ ⟶ Y` be a
birational morphism of normal varieties over a perfect field, `j : T ⟶ Y` an integral closed
subscheme onto the prime divisor `P`, `j₁ : T₁ ⟶ Y₁` one onto `P₁` with `g(η_{P₁}) = η_P`, `g`
an isomorphism of local rings at `η_{P₁}`, and `h : T₁ ⟶ T` birational with `h ≫ j = j₁ ≫ g`.
If `ρ = Res_T τ`, then `h^*ρ = Res_{T₁}(g^*τ)`. -/
private theorem isPoincareResidue_pullback {k : Type u} [Field k] [PerfectField k]
    (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [IsNormal Y] [LocallyOfFiniteType sY]
    [IsLocallyNoetherian Y₁] [IsNormal Y₁] [LocallyOfFiniteType (j ≫ sY)]
    (hgb : Function.Bijective (functionFieldMap g)) (hhb : Function.Bijective (functionFieldMap h))
    (hh : h ≫ j = j₁ ≫ g) (P : PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    (P₁ : PrimeDivisor Y₁) (hP₁ : j₁ (genericPoint T₁) = P₁.genericPoint)
    [IsIso (g.stalkMap P₁.genericPoint)] {n : ℕ}
    (hdY : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = n + 1)
    (hdT : letI := functionFieldAlgebra (j ≫ sY); (Algebra.trdeg k T.functionField).toNat = n)
    {τ : RationalPluriForms sY (n + 1) 1} {ρ : RationalPluriForms (j ≫ sY) n 1}
    (hρ : MMP.Fourfold.IsPoincareResidue sY j n 1 τ ρ) :
    MMP.Fourfold.IsPoincareResidue (g ≫ sY) j₁ n 1 (pullbackRationalPluriForms sY g τ)
      (cast (by rw [← Category.assoc, hh, Category.assoc]; rfl)
        (pullbackRationalPluriForms (j ≫ sY) h ρ)) := by
  classical
  obtain ⟨t, a0, x0, ht, hτE, hρE⟩ := (isPoincareResidue_iff sY j τ ρ).mp hρ
  set ψ := stalkMapAt g j j₁ h hh with hψdef
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (g ≫ sY)
  refine (isPoincareResidue_iff (g ≫ sY) j₁ _ _).mpr ⟨ψ.hom t, ψ.hom a0,
    fun i => ψ.hom (x0 i), ?_, ?_, ?_⟩
  · rw [hψdef, stalkMapAt_functionField g j j₁ h hh, hP₁,
      MMP.Positivity.ord_functionFieldMap_of_isIso g P₁ P (by
        rw [← hP₁, map_genericPoint_eq_of_comp_eq g j j₁ h hh, hP])]
    rw [← hP]
    exact ht
  · let := functionFieldMapAlgebra g
    have := isScalarTower_functionFieldMap sY g
    have hΦ : ∀ a, algebraMap Y.functionField Y₁.functionField (algebraMap _ Y.functionField a) =
        algebraMap _ Y₁.functionField (ψ.hom a) :=
      fun a => (stalkMapAt_functionField g j j₁ h hh a).symm
    obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sY g hgb hdY
    refine (subsingletonEquiv_pullbackForms hω τ).trans ?_
    rw [hτE, LinearMap.map_smul, MMP.Mori.topFormsMap_ιMulti,
      ← algebraMap_smul Y₁.functionField, map_mul, map_inv₀, hΦ, hΦ]
    congr 2
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [KaehlerDifferential.map_D, hΦ]
  · let := functionFieldAlgebra (j ≫ sY)
    let := functionFieldAlgebra (h ≫ j ≫ sY)
    let := functionFieldMapAlgebra h
    have := isScalarTower_functionFieldMap (j ≫ sY) h
    have hΦ : ∀ a, algebraMap T.functionField T₁.functionField ((j.stalkMap
        (genericPoint T)).hom a) =
        (j₁.stalkMap (genericPoint T₁)).hom (ψ.hom a) :=
      fun a => (stalkMapAt_stalkMap g j j₁ h hh a).symm
    obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective (j ≫ sY) h hhb hdT
    refine subsingletonEquiv_cast (k := k) (by rw [← Category.assoc, hh, Category.assoc]) _ _ _ _ ?_
    refine (subsingletonEquiv_pullbackForms hω ρ).trans ?_
    rw [hρE, LinearMap.map_smul, MMP.Mori.topFormsMap_ιMulti,
      ← algebraMap_smul T₁.functionField, hΦ]
    congr 2
    funext i
    simp [KaehlerDifferential.map_D, hΦ]

end ResiduePullback

/-- The pull-back of the zero form is zero. -/
private theorem pullbackRationalPluriForms_zero {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsDominant f] {d : ℕ}
    {m : ℤ} : pullbackRationalPluriForms sX f (0 : RationalPluriForms sX d m) = 0 := by
  unfold pullbackRationalPluriForms pullbackForms
  split_ifs with h
  · unfold pullbackFormsAlong
    erw [LinearEquiv.map_zero]
    simp only [Finsupp.coe_zero, Pi.zero_apply, map_zero, zero_smul]
    rfl
  · rfl

/-- Transporting the zero form along an equality of structure morphisms gives zero. -/
private theorem cast_zero_of_eq {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {d : ℕ}
    {m : ℤ} {s s' : X ⟶ Spec (.of k)} (e : s = s')
    (H : RationalPluriForms s d m = RationalPluriForms s' d m) :
    cast H (0 : RationalPluriForms s d m) = 0 := by
  subst e; rfl

/-- The divisor of a form is unchanged by transport along an equality of structure
morphisms. -/
private theorem divisorOfForm_cast {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X] {d : ℕ} {m : ℤ} {s s' : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType s] [LocallyOfFiniteType s'] (e : s = s')
    (H : RationalPluriForms s d m = RationalPluriForms s' d m) (τ : RationalPluriForms s d m) :
    divisorOfForm (cast H τ) = divisorOfForm τ := by
  subst e; rfl

/-- A sum `∑_E c_E • d_E` over a `ℚ`-divisor, as a sum over a finite set containing its
support. -/
private theorem sum_smul_eq_sum_of_support_subset {X : Scheme.{u}} (D : QDivisor X)
    (c : PrimeDivisor X → ℕ) {S : Finset (PrimeDivisor X)} (hS : D.support ⊆ S) :
    (D.sum fun E d => c E • d) = ∑ E ∈ S, (c E : ℚ) * D.coeff E := by
  rw [Finsupp.sum_of_support_subset D hS _ (fun _ _ => smul_zero _)]
  simp [nsmul_eq_mul, DivisorWithCoeffs.coeff_apply]

/-- The same for a divisor, cast to `ℚ`. -/
private theorem cast_sum_smul_eq_sum_of_support_subset {X : Scheme.{u}} (D : Divisor X)
    (c : PrimeDivisor X → ℕ) {S : Finset (PrimeDivisor X)} (hS : D.support ⊆ S) :
    (((D.sum fun E d => c E • d : ℤ)) : ℚ) = ∑ E ∈ S, (c E : ℚ) * (D.coeff E : ℚ) := by
  rw [Finsupp.sum_of_support_subset D hS _ (fun _ _ => smul_zero _), Int.cast_sum]
  simp [nsmul_eq_mul, DivisorWithCoeffs.coeff_apply]

/-- `∑_E c_E • d_E` over a divisor regarded as a `ℚ`-divisor. -/
private theorem sum_toQDivisor {X : Scheme.{u}} (A : Divisor X) (c : PrimeDivisor X → ℕ) :
    ((Divisor.toQDivisor A).sum fun E d => c E • d) =
      ((A.sum fun E d => c E • d : ℤ) : ℚ) := by
  have hS : (Divisor.toQDivisor A).support ⊆ A.support := by
    intro E hE
    rw [Finsupp.mem_support_iff] at hE ⊢
    intro h0
    apply hE
    change ((A.coeff E : ℤ) : ℚ) = 0
    rw [DivisorWithCoeffs.coeff_apply, h0, Int.cast_zero]
  rw [sum_smul_eq_sum_of_support_subset _ c hS,
    cast_sum_smul_eq_sum_of_support_subset A c (subset_refl _)]
  rfl

/-- Every nonzero rational `1`-canonical form is a nonzero rational top form. -/
private theorem exists_toPluriForms_eq {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) :
    ∃ ω : RationalTopForms sX n, ω ≠ 0 ∧ ω.toPluriForms sX = τ := by
  letI := functionFieldAlgebra sX
  have hω : RationalTopForms.toPluriForms sX (PiTensorProduct.subsingletonEquiv
      (R := X.functionField) (s := fun _ : Fin 1 => ⋀[X.functionField]^n Ω[X.functionField⁄k])
      0 τ : RationalTopForms sX n) = τ := by
    change PiTensorProduct.tprod X.functionField (fun _ : Fin 1 => PiTensorProduct.subsingletonEquiv
      (R := X.functionField) (s := fun _ : Fin 1 => ⋀[X.functionField]^n Ω[X.functionField⁄k])
      0 τ) = τ
    rw [← PiTensorProduct.subsingletonEquiv_symm_apply' (i₀ := (0 : Fin 1))]
    exact LinearEquiv.symm_apply_apply _ _
  refine ⟨_, fun h0 => hτ ?_, hω⟩
  rw [← hω, h0]
  change PiTensorProduct.tprod X.functionField (fun _ : Fin 1 =>
    (0 : ⋀[X.functionField]^n Ω[X.functionField⁄k])) = 0
  exact MultilinearMap.map_coord_zero _ (0 : Fin 1) rfl

/-- **Restriction commutes with pull-back.** Let `f : Y ⟶ X` be a dominant morphism of normal
integral schemes, `ι : T ⟶ X` and `ι' : T' ⟶ Y` integral closed subschemes onto the prime
divisors `P` and `P'` with `f(η_{P'}) = η_P`, `f` an isomorphism of local rings at `η_{P'}`, and
`f_S : T' ⟶ T` dominant with `f_S ≫ ι = ι' ≫ f`. Suppose that restricting the divisor of a unit
at the generic point of `P` (resp. `P'`) to `T` (resp. `T'`) gives the divisor of its
restriction. Then for every `ℚ`-Cartier `ℚ`-divisor `D` on `X` without component `P`,
`f_S^*(D|_T) = (f^*D)|_{T'}`. -/
private theorem isPullback_restrict_of_ord_stalkMap {X Y T T' : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsNoetherian T] [IsIntegral T'] [IsLocallyNoetherian T'] [IsNormal T'] [IsNoetherian T']
    (f : Y ⟶ X) [IsDominant f] (ι : T ⟶ X) (ι' : T' ⟶ Y) (fS : T' ⟶ T) [IsDominant fS]
    (hfS : fS ≫ ι = ι' ≫ f) (P : PrimeDivisor X) (P' : PrimeDivisor Y)
    (hgenT : ι (genericPoint T) = P.genericPoint) (hgenT' : ι' (genericPoint T') = P'.genericPoint)
    (hgP : f P'.genericPoint = P.genericPoint) [IsIso (f.stalkMap P'.genericPoint)]
    (hP : Set.range ι.base = (P.support : Set X))
    (D : QDivisor X) (hDq : D.IsQCartier)
    (hBX : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp)
    (hDP0 : D.coeff P = 0)
    (hbX : ∀ u : X.presheaf.stalk (ι (genericPoint T)), IsUnit u → ∀ M : Divisor X,
      (∀ E : PrimeDivisor X, M.coeff E = X.ord (algebraMap _ X.functionField u) E.genericPoint) →
      ∀ Q : PrimeDivisor T, T.ord ((ι.stalkMap (genericPoint T)).hom u) Q.genericPoint =
        M.sum fun E d => E.intersectionLength ι Q • d)
    (hbY : ∀ u : Y.presheaf.stalk (ι' (genericPoint T')), IsUnit u → ∀ M : Divisor Y,
      (∀ E : PrimeDivisor Y, M.coeff E = Y.ord (algebraMap _ Y.functionField u) E.genericPoint) →
      ∀ Q : PrimeDivisor T', T'.ord ((ι'.stalkMap (genericPoint T')).hom u) Q.genericPoint =
        M.sum fun E d => E.intersectionLength ι' Q • d) :
    ∀ hB' : ∀ Z : irreducibleComponents T',
      fS (componentGenericPoint T' Z) ∉ (D.restrict ι).supp,
      QDivisor.IsPullback fS (D.restrict ι) hB' ((D.pullback hDq hBX).restrict ι') := by
  classical
  set DY := D.pullback hDq hBX with hDYdef
  intro hB' m hm M hM hMc
  have hBM : ∀ Z : irreducibleComponents T', fS (componentGenericPoint T' Z) ∉ M.supp :=
    MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp fS M
  refine ⟨M.pullback hMc hBM, ?_, Divisor.isPullback_pullback hMc _⟩
  have hM'' := Divisor.isPullback_pullback (f := fS) hMc hBM
  set M'' := M.pullback hMc hBM
  refine DivisorWithCoeffs.ext' fun F => ?_
  rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, Int.cast_natCast]
  -- a local equation `g` of `N(K_X + S + B)` near the image of `η_F`
  obtain ⟨N, hN, DN, hDN, hDNc⟩ := hDq.exists_pos
  obtain ⟨DN', hDN', hDNpb⟩ := QDivisor.isPullback_pullback hDq hBX N hN DN hDN hDNc
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  set x := ι (fS F.genericPoint) with hxdef
  have hfx : f (ι' F.genericPoint) = x := by
    rw [hxdef, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hfS]
  obtain ⟨V, hxV, φ, hφ⟩ := hDNc x
  set g := MMP.Threefold.Mori.Helpers.evalFF (pointComponent x) (φ : RationalFunctions X)
    with hgdef
  have hev : ∀ Z, MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X) = g :=
    fun Z => by
      rw [hgdef, Subsingleton.elim
        (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) Z
        (pointComponent x)]
  have hg0 : g ≠ 0 := (φ.isUnit.map _).ne_zero
  have hordφ : ∀ E : PrimeDivisor X, E.ord φ = X.ord g E.genericPoint := fun E => by
    rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hev]
  have hDcoef : ∀ E : PrimeDivisor X, (DN.coeff E : ℚ) = N * D.coeff E := fun E => by
    have := congrArg (fun G : QDivisor X => G.coeff E) hDN
    simpa [DivisorWithCoeffs.coeff_smul] using this
  have hxP : x ∈ P.support := by rw [← hP]; exact ⟨_, rfl⟩
  have hPV : (P.support ∩ V).Nonempty := ⟨x, hxP, hxV⟩
  have hgPord : X.ord g P.genericPoint = 0 := by
    rw [← hordφ, ← hφ P hPV]
    have := hDcoef P
    rw [hDP0, mul_zero] at this
    exact_mod_cast this
  -- `g` as a unit at the generic point of `S`, and its restriction `ḡ` to `S`
  obtain ⟨u, hu, hug⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero (X := X)
    (ι (genericPoint T)) hg0 (fun Γ hΓ => by
      rw [hgenT] at hΓ
      obtain rfl : Γ = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (Γ.eq_genericPoint_of_mem_support hΓ
          (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)).symm
      exact hgPord)
  set gb : T.functionField := (ι.stalkMap (genericPoint T)).hom u with hgbdef
  have hgb0 : gb ≠ 0 := (hu.map _).ne_zero
  have hfactX := hbX u hu (principalDivisor φ) (fun E => by
    rw [coeff_principalDivisor, hordφ, hug])
  -- claim A: `v_Γ(ḡ) = N coeff_Γ((K_X + S + B)|_S)` along prime divisors through `f_S(η_F)`
  have hA : ∀ Γ : PrimeDivisor T, fS F.genericPoint ∈ Γ.support →
      (T.ord gb Γ.genericPoint : ℚ) = N * (D.restrict ι).coeff Γ := by
    intro Γ hΓ
    have hΓV : ι Γ.genericPoint ∈ V := by
      have hsp : Γ.genericPoint ⤳ fS F.genericPoint := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
        exact specializes_iff_mem_closure.mpr hΓ
      exact (hsp.map ι.continuous).mem_open V.isOpen hxV
    have hsub1 : (principalDivisor φ).support ⊆ DN.support ∪ (principalDivisor φ).support :=
      Finset.subset_union_right
    have hsub2 : D.support ⊆ DN.support ∪ (principalDivisor φ).support := by
      intro E hE
      refine Finset.mem_union_left _ ?_
      rw [Finsupp.mem_support_iff] at hE ⊢
      intro h0
      apply hE
      have := hDcoef E
      rw [DivisorWithCoeffs.coeff_apply, h0, Int.cast_zero] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hNq
    rw [hfactX Γ, cast_sum_smul_eq_sum_of_support_subset _ _ hsub1,
      coeff_restrict_eq_sum ι P hgenT D hDP0, sum_smul_eq_sum_of_support_subset _ _ hsub2,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun E _ => ?_
    by_cases hl : E.intersectionLength ι Γ = 0
    · simp [hl]
    · have hmem : ι Γ.genericPoint ∈ E.support := by
        by_contra hn
        exact hl (PrimeDivisor.intersectionLength_eq_zero_of_notMem ι E hn)
      rw [coeff_principalDivisor, ← hφ E ⟨_, hmem, hΓV⟩, hDcoef E]
      ring
  -- claim B: `v_F(f_S^* ḡ) = N coeff_F((f^*(K_X + S + B))|_{S'})`
  have hφ0 : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (principalDivisor φ).supp :=
    MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp f _
  set MY := principalDivisor (pullbackRationalFunction f φ hφ0) with hMYdef
  have hMY : ∀ G : PrimeDivisor Y, MY.coeff G = Y.ord (functionFieldMap f g) G.genericPoint :=
    fun G => by
      rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF
        (Divisor.isPullback_principalDivisor φ hφ0)
        (Divisor.isLocalEquation_principalDivisor φ ⊤) G trivial (pointComponent x)]
  set ψ := stalkMapAt f ι ι' fS hfS with hψdef
  have hψu : IsUnit (ψ.hom u) := hu.map _
  have hfactY := hbY (ψ.hom u) hψu MY (fun G => by
    rw [hMY, hψdef, stalkMapAt_functionField, hug])
  have hDNY : ∀ G : PrimeDivisor Y, f G.genericPoint ∈ V →
      DN'.coeff G = Y.ord (functionFieldMap f g) G.genericPoint := fun G hG => by
    rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hDNpb hφ G hG (pointComponent x)]
  have hDYcoef : ∀ G : PrimeDivisor Y, (DN'.coeff G : ℚ) = N * DY.coeff G := fun G => by
    have := congrArg (fun G' : QDivisor Y => G'.coeff G) hDN'
    simpa [DivisorWithCoeffs.coeff_smul] using this
  have hDYP' : DY.coeff P' = 0 := by
    have hPV' : f P'.genericPoint ∈ V := by
      rw [hgP]; exact (P.genericPoint_mem_iff V).mpr hPV
    have h1 := hDYcoef P'
    rw [hDNY P' hPV', MMP.Positivity.ord_functionFieldMap_of_isIso f P' P hgP, hgPord,
      Int.cast_zero] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hNq
  have hB : (T'.ord (functionFieldMap fS gb) F.genericPoint : ℚ) =
      N * (DY.restrict ι').coeff F := by
    have hsub1 : MY.support ⊆ DN'.support ∪ MY.support := Finset.subset_union_right
    have hsub2 : DY.support ⊆ DN'.support ∪ MY.support := by
      intro E hE
      refine Finset.mem_union_left _ ?_
      rw [Finsupp.mem_support_iff] at hE ⊢
      intro h0
      apply hE
      have := hDYcoef E
      rw [DivisorWithCoeffs.coeff_apply, h0, Int.cast_zero] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hNq
    rw [hgbdef, ← stalkMapAt_stalkMap f ι ι' fS hfS u, ← hψdef, hfactY F,
      cast_sum_smul_eq_sum_of_support_subset _ _ hsub1,
      coeff_restrict_eq_sum ι' P' hgenT' DY hDYP', sum_smul_eq_sum_of_support_subset _ _ hsub2,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun G _ => ?_
    by_cases hl : G.intersectionLength ι' F = 0
    · simp [hl]
    · have hmem : ι' F.genericPoint ∈ G.support := by
        by_contra hn
        exact hl (PrimeDivisor.intersectionLength_eq_zero_of_notMem ι' G hn)
      have hGV : f G.genericPoint ∈ V := by
        have hsp : G.genericPoint ⤳ ι' F.genericPoint := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem
          exact specializes_iff_mem_closure.mpr hmem
        have := (hsp.map f.continuous)
        rw [hfx] at this
        exact this.mem_open V.isOpen hxV
      rw [hMY, ← hDNY G hGV, DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
        hDYcoef G]
      ring
  -- conclusion
  have hmain := mul_coeff_isPullback_eq_ord hMc hM'' F (r := gb ^ (m : ℤ))
    (zpow_ne_zero _ hgb0) N (fun Γ hΓ => by
      have hMΓ : (M.coeff Γ : ℚ) = m * (D.restrict ι).coeff Γ := by
        have := congrArg (fun G : QDivisor T => G.coeff Γ) hM
        simpa [DivisorWithCoeffs.coeff_smul] using this
      have h1 : ((T.ord (gb ^ (m : ℤ)) Γ.genericPoint : ℤ) : ℚ) = N * M.coeff Γ := by
        rw [ord_zpow _ hgb0, Int.cast_mul, hA Γ hΓ, hMΓ]
        push_cast; ring
      exact_mod_cast h1)
  have hfgb : functionFieldMap fS gb ≠ 0 := (map_ne_zero _).mpr hgb0
  rw [map_zpow₀, ord_zpow _ hfgb] at hmain
  have h2 : ((N : ℤ) : ℚ) * (M''.coeff F : ℚ) = (m : ℚ) * (N * (DY.restrict ι').coeff F) := by
    rw [← hB]; exact_mod_cast hmain
  simp only [DivisorWithCoeffs.coeff_apply] at h2 ⊢
  have h3 : (N : ℚ) * ((M'' F : ℤ) : ℚ) = (N : ℚ) * ((m : ℚ) * (DY.restrict ι') F) := by
    push_cast at h2 ⊢; linarith
  exact mul_left_cancel₀ hNq h3

/-- A point of a closed subset of codimension at least two has coheight at least two. -/
private theorem two_le_coheight_of_mem {X : Scheme.{u}} {S : TopologicalSpace.Closeds X}
    (h2 : 2 ≤ closedsCodimension S) {x : X} (hx : x ∈ S) : 2 ≤ Order.coheight x := by
  have hsub : ((irreducibleSetEquivPoints (α := X)).symm x : Set X) ⊆ S :=
    S.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)
  have := le_closedsCodimension_iff.mp h2 _ hsub
  rwa [codimension_eq_coheight, Order.coheight_orderIso] at this

/-- A prime divisor of `Y` whose generic point maps to a point of coheight one is not
exceptional for a morphism `f : Y ⟶ X` to a separated normal scheme. -/
private theorem not_isExceptional_of_coheight_eq_one {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X)
    (E : PrimeDivisor Y) (hE : Order.coheight (f E.genericPoint) = 1) :
    ¬ RationalMap.IsExceptional f.toRationalMap E := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  intro h2
  have hmem : f E.genericPoint ∈ TopologicalSpace.Closeds.closure
      (f '' (E.idealSheaf.support : Set Y)) := by
    refine subset_closure ⟨E.genericPoint, ?_, rfl⟩
    exact MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E
  have := two_le_coheight_of_mem h2 hmem
  rw [hE] at this
  exact absurd this (by decide)

/-- The strict transform `f⁻¹_* P` of a prime divisor of a normal variety is not
`f`-exceptional. -/
private theorem strictTransform_notMem_exceptional {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (f : Y ⟶ X) {P : PrimeDivisor X}
    (P' : PrimeDivisor Y) (hP' : inverseTransformPrimeDivisor f P = some P')
    (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ E, E ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap E) : P' ∉ Ex := by
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) from
      Subsingleton.elim _ _]
    infer_instance
  refine fun h => not_isExceptional_of_coheight_eq_one f P' ?_ ((hEx P').mp h)
  rw [(MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP').1]
  exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P

open Classical in
/-- **The coefficients of `f^*(K_X + S + B)` along `S'`.** In the setting of
`isCrepantBoundary_restrict_aux`, with `K_X = div ω` and `K_Y = div f^*ω`, every prime divisor `G`
of `Y` meeting `S'` has `coeff_G f^*(K_X + S + B) = coeff_G(K_Y + S') - a(G, X, S + B)` if `G` is
exceptional, and `coeff_G(K_Y + S')` otherwise: a non-exceptional `G ≠ S'` is the strict
transform of a prime divisor `Q ≠ S` of `X` with discrepancy `-coeff_Q B`, and `coeff_Q B = 0`
since `f⁻¹_* B` misses `S'`. -/
private theorem coeff_pullback_eq_of_inter_nonempty {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hdim : topologicalKrullDim X = n + 1) (P : PrimeDivisor X) (B : QDivisor X)
    (hB : B.coeff P = 0) (KX : Divisor X) (hKX : KX.IsCanonicalDivisor sX (n + 1))
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX)) (hbir : IsBirationalMorphism f)
    (P' : PrimeDivisor Y) (hP' : inverseTransformPrimeDivisor f P = some P')
    (hdisj : Disjoint (P'.support : Set Y) ((inverseTransformDivisor f B).supp : Set Y))
    (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ E, E ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap E)
    (e : PrimeDivisor Y → ℚ)
    (he : ∀ E ∈ Ex, IsDiscrepancy sX (n + 1) KX (Divisor.toQDivisor (Finsupp.single P 1) + B)
      ⟨Y, f, hY, hbir, E⟩ (e E))
    (ω : RationalTopForms sX (n + 1)) (hω0 : ω ≠ 0)
    (hK0 : (topFormDivisor sX ω).IsCanonicalDivisor sX (n + 1))
    (hlinX : KX.LinearlyEquivalent (topFormDivisor sX ω))
    (hDq : (Divisor.toQDivisor (topFormDivisor sX ω) + Divisor.toQDivisor (Finsupp.single P 1) +
      B).IsQCartier)
    (hBX : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
      (Divisor.toQDivisor (topFormDivisor sX ω) + Divisor.toQDivisor (Finsupp.single P 1) +
        B).supp)
    (G : PrimeDivisor Y) (hG : (G.support ∩ P'.support).Nonempty) :
    haveI : IsDominant f := hbir.isDominant
    ((Divisor.toQDivisor (topFormDivisor sX ω) + Divisor.toQDivisor (Finsupp.single P 1) +
      B).pullback hDq hBX).coeff G =
      ((G.ordForm (pullbackRationalPluriForms sX f (ω.toPluriForms sX)) : ℚ) +
        if G = P' then 1 else 0) - if G ∈ Ex then e G else 0 := by
  classical
  haveI : IsDominant f := hbir.isDominant
  set D := Divisor.toQDivisor (topFormDivisor sX ω) + Divisor.toQDivisor (Finsupp.single P 1) + B
    with hDdef
  set DY := D.pullback hDq hBX with hDYdef
  set τY := pullbackRationalPluriForms sX f (ω.toPluriForms sX) with hτYdef
  set ΔY := DY - Divisor.toQDivisor (divisorOfForm τY) with hΔYdef
  have hdimN : topologicalKrullDim X = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; norm_cast
  have hpair : IsPair sX (Divisor.toQDivisor (Finsupp.single P 1) + B) :=
    ⟨hX, n + 1, topFormDivisor sX ω, hK0, by rw [← add_assoc]; exact hDq⟩
  have hcb : IsCrepantBoundary sX (n + 1) (topFormDivisor sX ω)
      (Divisor.toQDivisor (Finsupp.single P 1) + B) f hY hbir ΔY := by
    refine (isCrepantBoundary_iff_isPullback_topFormDivisor_add sX hpair hdimN ω hω0 f hY hbir
      ΔY).mpr ?_
    intro hB'
    have h1 : Divisor.toQDivisor (divisorOfForm τY) + ΔY = DY := by rw [hΔYdef]; abel
    rw [h1]
    have key : ∀ (D' : QDivisor X) (_ : D' = D)
        (hB'' : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D'.supp),
        QDivisor.IsPullback f D' hB'' DY := by
      rintro D' rfl hB''
      exact QDivisor.isPullback_pullback hDq hB''
    exact key _ (add_assoc _ _ _).symm hB'
  have hG' := hcb G
  have hΔ : ΔY.coeff G = DY.coeff G - G.ordForm τY := by
    simp [hΔYdef, coeff_divisorOfForm]
  obtain ⟨hgP, hgW⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP'
  have hP'Ex := strictTransform_notMem_exceptional hX f P' hP' Ex hEx
  by_cases hGEx : G ∈ Ex
  · have hGP' : G ≠ P' := fun h => hP'Ex (h ▸ hGEx)
    have h1 := isDiscrepancy_of_linearlyEquivalent (he G hGEx) hK0 hlinX
    have h2 := h1.eq hG'
    rw [if_pos hGEx, if_neg hGP']
    linarith
  · have hnot : ¬ (⟨Y, f, hY, hbir, G⟩ : DivisorOver k sX).IsExceptional :=
      fun h => hGEx ((hEx G).mpr h)
    obtain ⟨Q, hv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX _ hnot
    have hcen := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hv
    have hfG : f G.genericPoint = Q.genericPoint := hcen
    obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair hK0
      (DivisorOver.ofPrimeDivisor k hX Q)
    have e1 := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hv hcen hG' ha'
    have e2 := IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX ha'
    have hΔQ : ΔY.coeff G =
        ((DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℤ)) Q : ℤ) : ℚ) + B.coeff Q := by
      rw [e2] at e1
      simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor] at e1
      linarith
    rw [if_neg hGEx, sub_zero]
    by_cases hQP : Q = P
    · subst hQP
      have hGP' : G = P' := by
        have hV : f G.genericPoint ∈ biregularLocus f := by rw [hfG, ← hgP]; exact hgW
        have h1 := MMP.Threefold.Resolution.specializes_of_mem_biregularLocus f hV hgW
          (by rw [hfG, hgP])
        have h2 := MMP.Threefold.Resolution.specializes_of_mem_biregularLocus f hgW hV
          (by rw [hfG, hgP])
        exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h1.antisymm h2).eq
      rw [if_pos hGP']
      rw [DivisorWithCoeffs.coeff_single_self, hB] at hΔQ
      push_cast at hΔQ
      linarith
    · have hGP' : G ≠ P' := fun h => hQP (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (hfG.symm.trans ((congrArg (fun G : PrimeDivisor Y => f G.genericPoint) h).trans hgP)))
      rw [if_neg hGP']
      rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hQP)] at hΔQ
      have hBQ : B.coeff Q = 0 := by
        by_contra hBQ
        -- `G` is the strict transform of `Q`, a component of `B`
        have hzmt := (zariskiMain_of_isProper_of_isBirationalMorphism sX f hX.1 hY.1 hbir).1
        have hQV : Q.genericPoint ∈ biregularLocus f := by
          by_contra hn
          have := two_le_coheight_of_mem hzmt (x := Q.genericPoint) hn
          rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
          exact absurd this (by decide)
        have hinv : inverseTransformPrimeDivisor f Q = some G :=
          MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hfG
            (by rw [hfG]; exact hQV)
        have hcoef : (inverseTransformDivisor f B).coeff G = B.coeff Q :=
          MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hinv (fun Q' hQ' => by
            exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
              ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
                hQ').1.symm.trans hfG))
            B
        obtain ⟨z, hzG, hzP'⟩ := hG
        exact Set.disjoint_left.mp hdisj hzP'
          (DivisorWithCoeffs.support_subset_supp (by rw [hcoef]; exact hBQ) hzG)
      rw [hBQ] at hΔQ
      push_cast at hΔQ
      linarith

open Classical in
/-- **Restricting the coefficient identity to `S'`.** If a `ℚ`-divisor `D_Y` on `Y` agrees, along
every prime divisor `G` meeting `S' = P'`, with `K + S' - ∑_{E ∈ Ex} e_E E` (where `P'` is not in
`Ex` and `coeff_{P'} K = -1`), then `D_Y|_{S'} = (K + S')|_{S'} - ∑_{E ∈ Ex} e_E E|_{S'}`. -/
private theorem restrict_eq_add_neg_sum {Y T' : Scheme.{u}} [IsIntegral T']
    [TopologicalSpace.NoetherianSpace T'] (ι' : T' ⟶ Y) (P' : PrimeDivisor Y)
    (hgenT' : ι' (genericPoint T') = P'.genericPoint)
    (hι' : Set.range ι'.base = (P'.support : Set Y)) (DY : QDivisor Y) (K : Divisor Y)
    (hKP' : K.coeff P' = -1) (Ex : Finset (PrimeDivisor Y)) (hP'Ex : P' ∉ Ex)
    (e : PrimeDivisor Y → ℚ)
    (hcoef : ∀ G : PrimeDivisor Y, (G.support ∩ P'.support).Nonempty →
      DY.coeff G = ((K.coeff G : ℚ) + if G = P' then 1 else 0) - if G ∈ Ex then e G else 0) :
    DY.restrict ι' = Divisor.toQDivisor ((K + Finsupp.single P' 1).restrict ι') +
      (-∑ E ∈ Ex, e E • DivisorWithCoeffs.restrict ι' (Finsupp.single E (1 : ℚ))) := by
  have hDYP' : DY.coeff P' = 0 := by
    have := hcoef P' ⟨_, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P',
      MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P'⟩
    rw [if_pos rfl, if_neg hP'Ex, hKP'] at this
    rw [this]; push_cast; ring
  have hKP'0 : (K + Finsupp.single P' 1).coeff P' = 0 := by
    rw [DivisorWithCoeffs.coeff_add, hKP', DivisorWithCoeffs.coeff_single_self]; rfl
  refine DivisorWithCoeffs.ext' fun F => ?_
  have hsingle : ∀ E ∈ Ex, (DivisorWithCoeffs.restrict ι' (Finsupp.single E (1 : ℚ))).coeff F =
      (E.intersectionLength ι' F : ℚ) := by
    intro E hE
    have hEP' : E ≠ P' := fun h => hP'Ex (h ▸ hE)
    rw [coeff_restrict_eq_sum ι' P' hgenT' _ (DivisorWithCoeffs.coeff_single_of_ne hEP' _)]
    rw [Finsupp.sum_single_index (h := fun (G : PrimeDivisor Y) (d : ℚ) =>
      G.intersectionLength ι' F • d) (smul_zero _), nsmul_eq_mul, mul_one]
  set S := DY.support ∪ (K + Finsupp.single P' 1).support ∪ Ex with hS
  have h1 : DY.support ⊆ S := fun E hE => by simp [hS, hE]
  have h2 : (K + Finsupp.single P' 1).support ⊆ S := fun E hE => by simp [hS, hE]
  have h3 : Ex ⊆ S := fun E hE => by simp [hS, hE]
  rw [coeff_restrict_eq_sum ι' P' hgenT' DY hDYP', DivisorWithCoeffs.coeff_add,
    Divisor.coeff_toQDivisor, coeff_restrict_eq_sum ι' P' hgenT' _ hKP'0,
    sum_smul_eq_sum_of_support_subset _ _ h1, cast_sum_smul_eq_sum_of_support_subset _ _ h2,
    DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  have h4 : ∑ E ∈ Ex, (e E • DivisorWithCoeffs.restrict ι' (Finsupp.single E (1 : ℚ))) F =
      ∑ G ∈ S, (G.intersectionLength ι' F : ℚ) * if G ∈ Ex then e G else 0 := by
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_mem S Ex, Finset.inter_eq_right.mpr h3]
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [Finsupp.smul_apply, ← DivisorWithCoeffs.coeff_apply, hsingle E hE, smul_eq_mul, mul_comm]
  rw [h4, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun G _ => ?_
  by_cases hl : G.intersectionLength ι' F = 0
  · simp [hl]
  · have hmem : ι' F.genericPoint ∈ G.support := by
      by_contra hn
      exact hl (PrimeDivisor.intersectionLength_eq_zero_of_notMem ι' G hn)
    have hmemP' : ι' F.genericPoint ∈ P'.support := by rw [← hι']; exact ⟨_, rfl⟩
    rw [hcoef G ⟨_, hmem, hmemP'⟩, DivisorWithCoeffs.coeff_add]
    by_cases hGP' : G = P'
    · subst hGP'
      rw [DivisorWithCoeffs.coeff_single_self, if_pos rfl]
      push_cast; ring
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hGP'), if_neg hGP']
      push_cast; ring

/-- **The crepant boundary of `(S, B|_S)` on `S'`.** Write `K_X = div ω` with `ord_S ω = -1`
and `K_S = div ρ` for `ρ = Res_S ω`. Then `f_S^* ρ = Res_{S'} f^* ω`
(`isPoincareResidue_pullback`), restriction commutes with pull-back
(`isPullback_restrict_of_ord_stalkMap`), and restricting
`f^*(K_X + S + B) = K_Y + S' - ∑ eᵢ Eᵢ` near `S'` (`coeff_pullback_eq_of_inter_nonempty`) to
`S'` gives `f_S^*(K_S + B|_S) = K_{S'} - ∑ eᵢ Eᵢ|_{S'}`. -/
private theorem isCrepantBoundary_restrict_aux
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    {T : Scheme.{u}} (ι : T ⟶ X) [IsClosedImmersion ι] [IsIntegral T] [IsNormal T]
    [IsLocallyNoetherian T] [CompactSpace T]
    (P : PrimeDivisor X) (hP : Set.range ι.base = (P.support : Set X))
    (hcart : ∀ x : X, Order.coheight x = 2 → x ∈ P.support →
      MMP.Flips.IsCartierAt (Finsupp.single P (1 : ℤ)) x)
    (B : QDivisor X) (hB : B.coeff P = 0)
    (KX : Divisor X) (hKX : KX.IsCanonicalDivisor sX (n + 1))
    (hKSB : (Divisor.toQDivisor KX + Divisor.toQDivisor (Finsupp.single P 1) + B).IsQCartier)
    {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsLogResolution sX (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single P 1) + B)) f)
    (hY : IsNormalVariety k (f ≫ sX))
    (P' : PrimeDivisor Y) (hP' : inverseTransformPrimeDivisor f P = some P')
    (hdisj : Disjoint (P'.support : Set Y) ((inverseTransformDivisor f B).supp : Set Y))
    {T' : Scheme.{u}} (ι' : T' ⟶ Y) [IsClosedImmersion ι'] [IsIntegral T']
    (hι' : Set.range ι'.base = (P'.support : Set Y))
    (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ E, E ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap E)
    (e : PrimeDivisor Y → ℚ)
    (he : ∀ E ∈ Ex, IsDiscrepancy sX (n + 1) KX (Divisor.toQDivisor (Finsupp.single P 1) + B)
      ⟨Y, f, hY, hf.isBirationalMorphism, E⟩ (e E)) :
    ∀ fS : T' ⟶ T, fS ≫ ι = ι' ≫ f → IsSmoothScheme (fS ≫ ι ≫ sX) →
      ∀ (hT' : IsNormalVariety k (fS ≫ ι ≫ sX)) (hfS : IsBirationalMorphism fS),
        ∀ KS : Divisor T, KS.IsCanonicalDivisor (ι ≫ sX) n →
          IsCrepantBoundary (ι ≫ sX) n KS (B.restrict ι) fS hT' hfS
            (-∑ E ∈ Ex, e E • DivisorWithCoeffs.restrict ι' (Finsupp.single E (1 : ℚ))) := by
  intro fS hfS hsm hT' hbir KS hKS
  classical
  -- instances
  haveI : IsProper f := hf.isProper
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsDominant f := hf.isBirationalMorphism.isDominant
  haveI : LocallyOfFiniteType (fS ≫ ι ≫ sX) := hT'.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T' := LocallyOfFiniteType.isLocallyNoetherian (fS ≫ ι ≫ sX)
  haveI : IsNormal T' := hT'.2
  haveI : CompactSpace T' := QuasiCompact.compactSpace_of_compactSpace ι'
  haveI : IsProper (fS ≫ ι) := hfS ▸ inferInstance
  haveI : IsProper fS := IsProper.of_comp fS ι
  haveI : IsDominant fS := hbir.isDominant
  haveI : Smooth (f ≫ sX) := (isSmoothScheme_iff _).1 hf.isSmoothScheme
  have hsmT' : IsSmoothScheme (ι' ≫ f ≫ sX) := by
    rw [← reassoc_of% hfS]; exact hsm
  haveI : Smooth (ι' ≫ f ≫ sX) := (isSmoothScheme_iff _).1 hsmT'
  have hTv : IsNormalVariety k (ι ≫ sX) := by
    refine ⟨?_, inferInstance⟩
    haveI := hX.1
    exact AlgebraicGeometry.IsVariety.mk
  -- dimensions
  have hfb := hf.isBirationalMorphism.functionFieldMap_bijective
  have hfSb := hbir.functionFieldMap_bijective
  have hdX : (letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat) =
      n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (d := n + 1)
      (by rw [hdim]; norm_cast)
  have hdimY : topologicalKrullDim Y = n + 1 := by
    haveI := hX.1; haveI := hY.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      hf.isBirationalMorphism, hdim]
  have hdimT : topologicalKrullDim T = n := hKS.1
  have hdimT' : topologicalKrullDim T' = n := by
    haveI := hTv.1; haveI := hT'.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ι ≫ sX)
      (fS ≫ ι ≫ sX) hbir, hdimT]
  have hdY : (letI := functionFieldAlgebra (f ≫ sX); (Algebra.trdeg k Y.functionField).toNat) =
      n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := f ≫ sX) (d := n + 1)
      (by rw [hdimY]; norm_cast)
  have hdT := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := ι ≫ sX) hdimT
  have hdT' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := fS ≫ ι ≫ sX) hdimT'
  -- generic points
  obtain ⟨hgP, hgW⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP'
  haveI : IsIso (f.stalkMap P'.genericPoint) :=
    MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus f hgW
  have hgenT : ι (genericPoint T) = P.genericPoint := map_genericPoint_eq ι P hP
  have hgenT' : ι' (genericPoint T') = P'.genericPoint := map_genericPoint_eq ι' P' hι'
  -- adjunction on `X`
  have hsum : (∑ _a : Unit, Finsupp.single P (1 : ℤ)) = Finsupp.single P 1 := by simp
  obtain ⟨-, ⟨ω, hω0, hωP⟩, hres, -, hcartS⟩ :=
    adjunction_restrict_of_isCartierAt_coheight_eq_two sX hX hdim (J := Unit) (T := fun _ => T)
      (fun _ => ι) (fun _ => P) (fun _ => hP) (fun a b hab => (hab (Subsingleton.elim a b)).elim)
      (fun x hx hxP => by rw [hsum]; exact hcart x hx (hxP.elim fun _ h => h)) B (fun _ => hB)
      KX hKX (by rw [hsum]; exact hKSB)
  obtain ⟨hK0, hω'⟩ := hres ω hω0 hωP
  obtain ⟨⟨ρ, hρ⟩, hρdiv⟩ := hω' ()
  obtain ⟨hρcan, hρadj⟩ := hρdiv ρ hρ
  rw [hsum] at hρadj
  -- the form `f^*ω` on `Y` and its residue along `S'`
  set τY := pullbackRationalPluriForms sX f (ω.toPluriForms sX) with hτYdef
  have hτY : P'.ordForm τY = -1 := by
    rw [hτYdef, MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hfb hdX P' P hgP]
    exact hωP ()
  have hτY0 : τY ≠ 0 := fun h0 => by
    rw [h0, PrimeDivisor.ordForm_zero] at hτY
    exact absurd hτY (by decide)
  obtain ⟨ρY, hρYu, hρY0, hρYdiv, -⟩ :=
    MMP.Mori.existsUnique_isPoincareResidue_of_ordForm_eq_neg_one (f ≫ sX) hdimY ι' P' hgenT'
      τY hτY0 hτY
  have hR := isPoincareResidue_pullback f ι ι' fS sX hfb hfSb hfS P hgenT P' hgenT' hdX hdT hρ
  have hρYeq := (hρYu _).mp hR
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    apply hρY0
    rw [← hρYeq, pullbackRationalPluriForms_zero]
    exact cast_zero_of_eq (by rw [← Category.assoc, hfS, Category.assoc]) _
  -- the `ℚ`-Cartier divisor `K_X + S + B`, with `K_X = div ω`
  set K₀ := topFormDivisor sX ω with hK₀def
  have hlinX : KX.LinearlyEquivalent K₀ :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hKX hK0
  set D := Divisor.toQDivisor K₀ + Divisor.toQDivisor (Finsupp.single P 1) + B with hDdef
  have hDq : D.IsQCartier := by
    have h := (show (Divisor.toQDivisor KX +
        (Divisor.toQDivisor (Finsupp.single P 1) + B)).IsQCartier by
      rw [← add_assoc]; exact hKSB).add_of_linearlyEquivalent hlinX
    rwa [← add_assoc] at h
  have hBX : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp := by
    intro Z hZ
    rw [MMP.Threefold.Mori.CanonUniq.componentGenericPoint_eq,
      map_genericPoint_of_isDominant] at hZ
    obtain ⟨E, -, hE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support E hE
  set DY := D.pullback hDq hBX with hDYdef
  -- the residue `ρ` as a top form on `T`
  obtain ⟨ωT, hωT0, hωT⟩ := exists_toPluriForms_eq hρ0
  have hKT : topFormDivisor (ι ≫ sX) ωT = divisorOfForm ρ := by
    unfold topFormDivisor; rw [hωT]
  have hPairT : IsPair (ι ≫ sX) (B.restrict ι) :=
    isPair_of_isCanonicalDivisor hTv hKS (hcartS () KS hKS).1
  have hlinT : (topFormDivisor (ι ≫ sX) ωT).LinearlyEquivalent KS :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (ι ≫ sX) hTv (hKT ▸ hρcan) hKS
  -- the divisor of residues, on `T` and on `S'`
  haveI : IsNoetherian T := ⟨⟩
  haveI : IsNoetherian T' := ⟨⟩
  have hresX : ∀ (τ' : RationalPluriForms sX (n + 1) 1) (ρ' : RationalPluriForms (ι ≫ sX) n 1),
      τ' ≠ 0 → P.ordForm τ' = -1 → MMP.Fourfold.IsPoincareResidue sX ι n 1 τ' ρ' →
      ∀ Q : PrimeDivisor T, Q.ordForm ρ' = (divisorOfForm τ' + Finsupp.single P 1).sum
        fun E d => E.intersectionLength ι Q • d := by
    intro τ' ρ' hτ'0 hτ' hρ' Q
    obtain ⟨ω', hω'0, hω'τ⟩ := exists_toPluriForms_eq hτ'0
    obtain ⟨-, h2⟩ := hres ω' hω'0 (fun _ => by rw [hω'τ]; exact hτ')
    obtain ⟨-, hadj⟩ := (h2 ()).2 ρ' (by rw [hω'τ]; exact hρ')
    rw [hsum] at hadj
    have hc := congrArg (fun D : QDivisor T => D.coeff Q) hadj
    have hDP : (Divisor.toQDivisor (topFormDivisor sX ω') +
        Divisor.toQDivisor (Finsupp.single P 1) + B).coeff P = 0 := by
      simp [coeff_topFormDivisor, hω'τ, hτ', hB, DivisorWithCoeffs.coeff_single_self]
    rw [coeff_restrict_eq_sum ι P hgenT _ hDP, DivisorWithCoeffs.coeff_add,
      coeff_restrict_eq_sum ι P hgenT B hB, Divisor.coeff_toQDivisor, coeff_divisorOfForm,
      Finsupp.sum_add_index' (fun _ => smul_zero _) (fun _ _ _ => smul_add _ _ _), ← map_add,
      sum_toQDivisor] at hc
    have hc' : (((divisorOfForm (ω'.toPluriForms sX) + Finsupp.single P 1).sum
        fun E d => E.intersectionLength ι Q • d : ℤ) : ℚ) = (Q.ordForm ρ' : ℚ) := by
      unfold topFormDivisor at hc; linarith
    rw [hω'τ] at hc'
    exact_mod_cast hc'.symm
  have hresY : ∀ (τ' : RationalPluriForms (f ≫ sX) (n + 1) 1)
      (ρ' : RationalPluriForms (ι' ≫ f ≫ sX) n 1),
      τ' ≠ 0 → P'.ordForm τ' = -1 → MMP.Fourfold.IsPoincareResidue (f ≫ sX) ι' n 1 τ' ρ' →
      ∀ Q : PrimeDivisor T', Q.ordForm ρ' = (divisorOfForm τ' + Finsupp.single P' 1).sum
        fun E d => E.intersectionLength ι' Q • d := by
    intro τ' ρ' hτ'0 hτ' hρ' Q
    obtain ⟨ρ'', hu, -, hdiv, -⟩ :=
      MMP.Mori.existsUnique_isPoincareResidue_of_ordForm_eq_neg_one (f ≫ sX) hdimY ι' P'
        hgenT' τ' hτ'0 hτ'
    obtain rfl := (hu ρ').mp hρ'
    have h1 := congrArg (fun D : Divisor T' => D.coeff Q) hdiv
    simp only [coeff_divisorOfForm] at h1
    rw [h1]
    refine coeff_restrict_eq_sum ι' P' hgenT' _ ?_ Q
    simp [hτ', DivisorWithCoeffs.coeff_single_self]

  -- the two remaining identities
  have hΘ : DY.restrict ι' = Divisor.toQDivisor (divisorOfForm
      (pullbackRationalPluriForms (ι ≫ sX) fS ρ)) +
      (-∑ E ∈ Ex, e E • DivisorWithCoeffs.restrict ι' (Finsupp.single E (1 : ℚ))) := by
    have hcoef := fun G hG => coeff_pullback_eq_of_inter_nonempty sX hX hdim P B hB KX hKX f hY
      hf.isBirationalMorphism P' hP' hdisj Ex hEx e he ω hω0 hK0 hlinX hDq hBX G hG
    have hKP' : (divisorOfForm τY).coeff P' = -1 := by rw [coeff_divisorOfForm]; exact hτY
    rw [restrict_eq_add_neg_sum ι' P' hgenT' hι' DY (divisorOfForm τY) hKP' Ex
      (strictTransform_notMem_exceptional hX f P' hP' Ex hEx) e
      (fun G hG => by rw [coeff_divisorOfForm]; exact hcoef G hG), ← hρYdiv, ← hρYeq,
      divisorOfForm_cast (by rw [← Category.assoc, hfS, Category.assoc])]
  have hPB : ∀ hB' : ∀ Z : irreducibleComponents T',
      fS (componentGenericPoint T' Z) ∉ (D.restrict ι).supp,
      QDivisor.IsPullback fS (D.restrict ι) hB' (DY.restrict ι') := by
    have hDP0 : D.coeff P = 0 := by
      simp [hDdef, hK₀def, coeff_topFormDivisor, hωP (), hB, DivisorWithCoeffs.coeff_single_self]
    have hω0' : ω.toPluriForms sX ≠ 0 := toPluriForms_ne_zero sX hω0
    have hρY : MMP.Fourfold.IsPoincareResidue (f ≫ sX) ι' n 1 τY ρY := (hρYu ρY).mpr rfl
    exact isPullback_restrict_of_ord_stalkMap f ι ι' fS hfS P P' hgenT hgenT' hgP hP D hDq hBX
      hDP0 (fun u hu M hM Q => ord_stalkMap_eq_sum_of_isPoincareResidue (sY := sX) (n := n) hdX hdT
        hgenT hresX hω0' (hωP ()) hρ0 hρ hu hM Q)
      (fun u hu M hM Q => ord_stalkMap_eq_sum_of_isPoincareResidue (sY := f ≫ sX) (n := n) hdY
        (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := ι' ≫ f ≫ sX) hdimT')
        hgenT' hresY hτY0 hτY hρY0 hρY hu hM Q)
  have hcb : IsCrepantBoundary (ι ≫ sX) n (topFormDivisor (ι ≫ sX) ωT) (B.restrict ι) fS hT' hbir
      (-∑ E ∈ Ex, e E • DivisorWithCoeffs.restrict ι' (Finsupp.single E (1 : ℚ))) := by
    refine (isCrepantBoundary_iff_isPullback_topFormDivisor_add (ι ≫ sX) hPairT hdimT ωT hωT0 fS
      hT' hbir _).mpr ?_
    have e1 : Divisor.toQDivisor (topFormDivisor (ι ≫ sX) ωT) + B.restrict ι = D.restrict ι := by
      rw [hKT, ← hρadj]
    rw [e1, hωT, ← hΘ]
    exact hPB
  intro F
  exact isDiscrepancy_of_linearlyEquivalent (hcb F) hKS hlinT

/-- **Adjunction on a log resolution** (Kollár–Mori, proof of Proposition 5.46). Let `X` be a
normal variety of dimension `n + 1` over a perfect field, `S = ι(T)` a normal prime divisor `P`
Cartier in codimension two, `B` a `ℚ`-divisor without component `P` with `K_X + S + B`
`ℚ`-Cartier, and `f : Y ⟶ X` a log resolution of `(X, S + B)` with `S' = ι'(T') = f⁻¹_* S`
disjoint from `f⁻¹_* B`. If `Ex` is the set of `f`-exceptional prime divisors and
`e E = a(E, X, S + B)`, then `f|_{S'} : S' ⟶ S` exists, is a proper birational morphism from a
smooth variety, and `-∑_{E ∈ Ex} e E • E|_{S'}` is the crepant boundary of `(S, B|_S)` on `S'`. -/
@[mmp "lem_km5b_adjunction_log_resolution"]
public theorem isCrepantBoundary_restrict_of_isLogResolution
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    {T : Scheme.{u}} (ι : T ⟶ X) [IsClosedImmersion ι] [IsIntegral T] [IsNormal T]
    [IsLocallyNoetherian T] [CompactSpace T]
    (P : PrimeDivisor X) (hP : Set.range ι.base = (P.support : Set X))
    (hcart : ∀ x : X, Order.coheight x = 2 → x ∈ P.support →
      MMP.Flips.IsCartierAt (Finsupp.single P (1 : ℤ)) x)
    (B : QDivisor X) (hB : B.coeff P = 0)
    (KX : Divisor X) (hKX : KX.IsCanonicalDivisor sX (n + 1))
    (hKSB : (Divisor.toQDivisor KX + Divisor.toQDivisor (Finsupp.single P 1) + B).IsQCartier)
    {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsLogResolution sX (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single P 1) + B)) f)
    (hY : IsNormalVariety k (f ≫ sX))
    (P' : PrimeDivisor Y) (hP' : inverseTransformPrimeDivisor f P = some P')
    (hdisj : Disjoint (P'.support : Set Y) ((inverseTransformDivisor f B).supp : Set Y))
    {T' : Scheme.{u}} (ι' : T' ⟶ Y) [IsClosedImmersion ι'] [IsIntegral T']
    (hι' : Set.range ι'.base = (P'.support : Set Y))
    (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ E, E ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap E)
    (e : PrimeDivisor Y → ℚ)
    (he : ∀ E ∈ Ex, IsDiscrepancy sX (n + 1) KX (Divisor.toQDivisor (Finsupp.single P 1) + B)
      ⟨Y, f, hY, hf.isBirationalMorphism, E⟩ (e E)) :
    (∃ fS : T' ⟶ T, fS ≫ ι = ι' ≫ f) ∧
    ∀ fS : T' ⟶ T, fS ≫ ι = ι' ≫ f →
      IsProper fS ∧ IsSmoothScheme (fS ≫ ι ≫ sX) ∧
      ∃ (hT' : IsNormalVariety k (fS ≫ ι ≫ sX)) (hfS : IsBirationalMorphism fS),
        ∀ KS : Divisor T, KS.IsCanonicalDivisor (ι ≫ sX) n →
          IsCrepantBoundary (ι ≫ sX) n KS (B.restrict ι) fS hT' hfS
            (-∑ E ∈ Ex, e E • DivisorWithCoeffs.restrict ι' (Finsupp.single E (1 : ℚ))) := by
  haveI := hf.isProper
  obtain ⟨fS, hfS⟩ := exists_comp_eq f ι P hP P' hP' ι' hι'
  refine ⟨⟨fS, hfS⟩, fun fS hfS => ?_⟩
  have hsm := isSmoothScheme_aux sX ι P B hB f hf hY P' hP' ι' hι' fS hfS
  have hT' : IsNormalVariety k (fS ≫ ι ≫ sX) := by
    refine ⟨?_, isNormal_of_isRegular T' (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hsm)⟩
    haveI := hY.1
    have heq : fS ≫ ι ≫ sX = ι' ≫ f ≫ sX := by rw [reassoc_of% hfS]
    rw [heq]
    exact AlgebraicGeometry.IsVariety.mk
  have hbir := isBirationalMorphism_aux f ι P hP P' hP' ι' hι' fS hfS
  have : IsProper (fS ≫ ι) := hfS ▸ inferInstance
  exact ⟨IsProper.of_comp fS ι, hsm, hT', hbir, isCrepantBoundary_restrict_aux sX hX hdim ι P hP
    hcart B hB KX hKX hKSB f hf hY P' hP' hdisj ι' hι' Ex hEx e he fS hfS hsm hT' hbir⟩

end MMP.Mori
