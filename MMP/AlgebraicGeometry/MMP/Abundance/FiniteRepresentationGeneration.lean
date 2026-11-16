module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import MMP.RingTheory.Kaehler.PluriformProduct

/-!
# Klt pairs across conventions, and admissible generation from finite representations

Two results used in the fourfold programme.

**Klt pairs.** Let `X` be a normal variety of dimension `n` over a perfect field `k`, with
canonical divisor `K`, and let `B` be a `ℚ`-boundary on `X` (coefficients in `[0, 1]`) such that
`K + B` is `ℚ`-Cartier. Then `(X, B)` is Kawamata log terminal in the sense of *Flips and
abundance* (every log discrepancy `a_ℓ(F, B)` of a divisor `F` of `k(X)` with nonempty center
on `X` is positive) if and only if it is klt in the sense of Kollár–Mori
(`discrep(X, B) > -1` and `⌊B⌋ ≤ 0`). For `m > 0` with `m(K + B)` Cartier every discrepancy
lies in `m⁻¹ℤ`, so positivity of all log discrepancies bounds them below by `1/m`; every divisor
over `X` is realised on a proper model by Nagata compactification followed by normalization.

**Admissible generation.** Let `W` be the space of preadmissible section systems in degree `m`
of a finite collection of rational dlt pairs `(X_i, B_i)`. If `W` generates
`𝒪_{X_i}(m(K_{X_i} + B_i))` on every component, is stable under the crepant birational
identifications, these fix the restrictions to proper strata, and the crepant birational
self-maps of each component act on the `i`-th entries of `W` through finitely many maps, then
admissible systems generate in every positive multiple of a common degree `N m`, and every
preadmissible system has a preadmissible lift of its proper-stratum restrictions with invariant
`i`-th entry.

The crepant identifications are realised by a finite composition-closed set `H` of injective
monomial maps `w ↦ (φ_j^* w_{π j})_j` of `W`. For `w ∈ W` the orbit product
`t_j = ∏_{h ∈ H} (h w)_j` is invariant, because composing with a monomial map permutes `H`, and
admissible, because residues are multiplicative (`MMP.Fourfold.IsIteratedResidue.mul`) and
unique (`MMP.Fourfold.IsIteratedResidue.unique`). Near a point `x` a general `w` makes every
ratio `(h w)_i / s_i` to a local generator `s_i` a unit at `x`, as `k` is infinite and `H`
finite, so `t_i` generates, and so do its powers `t_i^c`, of degree `c |H| m`. The lift is an
average over the finite image of the self-maps.

## Main results

* `MMP.Fourfold.isKawamataLogTerminal_iff_isKltPair`: the two klt conditions agree.
* `MMP.Flips.IsDiscrepancy.eq_of_valuation_eq`: the *Flips and abundance* discrepancy of `F` is
  the Kollár–Mori discrepancy of every divisor over `X` with valuation `F`.
* `MMP.Flips.IsDiscrepancyWith.eq_of_isDiscrepancy`: the FA discrepancy computed with a form
  cutting out `K` is the Kollár–Mori discrepancy.
* `MMP.Flips.ProperDivisorOver.hasNonemptyCenter_valuation`: divisors over `X` with proper
  structure map have nonempty center.
* `MMP.Flips.exists_isDiscrepancy_intCast_div`: if `m(K + B)` is Cartier, the *Flips and
  abundance* discrepancy of every divisor over `X` with proper model exists and lies in `m⁻¹ℤ`.
* `MMP.Fourfold.exists_admissibleSections_generatesOn_of_finite`: admissible generation.
* `MMP.Fourfold.exists_admissibleSections_generatesOn_mul_of_finite`: admissible generation in
  every positive multiple `c N m` of a common degree.

## Implementation notes

The boundary of the klt dictionary is a `ℚ`-divisor `B`, viewed as an `ℝ`-divisor through
`MMP.Mori.QDivisor.toRDivisor` on the *Flips and abundance* side; `K` and `n` are explicit
arguments of both predicates.

The source's finite monomial group `G^r ⋊ 𝔖_r` and its orbit polynomials `σ_i(s)^{N!/i}` are
replaced by the set `H` and the powers of the orbit product of a suitably general `w`, of degrees
`c |H| m`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.13.5
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.22, 2.34
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-! ### Kawamata log terminal pairs: *Flips and abundance* versus Kollár–Mori -/

section KltDictionary

open TopologicalSpace
open scoped WithZero

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- The FA discrepancy computed with a form `ω` cutting out `K` is the Kollár–Mori
discrepancy. -/
theorem _root_.MMP.Flips.IsDiscrepancyWith.eq_of_isDiscrepancy {n : ℕ} {K : Divisor X}
    {B : QDivisor X} {ω : RationalPluriForms sX n 1} (hω : divisorOfForm ω = K) {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {E : Flips.ProperDivisorOver k sX} {a : ℝ}
    (h : Flips.IsDiscrepancyWith sX n (QDivisor.toRDivisor B) ω r L E a) {a' : ℚ}
    (ha' : IsDiscrepancy sX n K B E.toDivisorOver a') : a = a' := by
  obtain ⟨hX, hn, hω0, hLc, hsum, L', hpb, rfl⟩ := h
  have hco : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + (QDivisor.toRDivisor B).coeff Γ =
      ∑ j, r j * (L j).coeff Γ := by
    intro Γ
    have := congrArg (fun D : RDivisor X => D.coeff Γ) hsum
    simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
      Flips.coeff_sum_smul_toRDivisor] using this
  have hb : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) E.toDivisorOver
      (1 + ((E.toDivisorOver.ordPullback ω : ℝ) - ∑ j, r j * (L' j).coeff E.E)) :=
    ⟨hX, E.isProper, ω, hω0, ⟨K, ha'.2.1, fun Γ => by rw [← hω]; rfl⟩, m, r, L, L', hLc, hco,
      hpb, by ring⟩
  have := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha' hb
  linarith

/-- The FA discrepancy `a(F, B)` is the Kollár–Mori discrepancy of every divisor over `X` with
valuation `F`. -/
theorem _root_.MMP.Flips.IsDiscrepancy.eq_of_valuation_eq {n : ℕ} {K : Divisor X}
    {B : QDivisor X} {F : Valuation X.functionField ℤᵐ⁰} {a : ℝ}
    (h : Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor B) F a) {D : DivisorOver k sX}
    (hD : D.valuation = F) {a' : ℚ} (ha' : IsDiscrepancy sX n K B D a') : a = a' := by
  obtain ⟨hK, -, -, E, ω, m, r, L, hEF, hω, hw⟩ := h
  obtain ⟨a'', ha''⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy ha'.isPair hK E.toDivisorOver
  rw [hw.eq_of_isDiscrepancy hω ha'']
  have hv : E.toDivisorOver.valuation = D.valuation := hEF.trans hD.symm
  exact_mod_cast MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hv
    (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq ha'.1 hv) ha'' ha'

/-- The valuation of a divisor `E` over `X` whose structure map `E.f` is proper has nonempty
center on `X`. -/
theorem _root_.MMP.Flips.ProperDivisorOver.hasNonemptyCenter_valuation
    (E : Flips.ProperDivisorOver k sX) : Flips.HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

omit [PerfectField k] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] in
/-- If `M = m(K + B)` with `m > 0`, then `K + B = m⁻¹ M` as `ℝ`-divisors. -/
private theorem toRDivisor_add_eq_sum {K : Divisor X} {B : QDivisor X} {m : ℕ} (hm : 0 < m)
    {M : Divisor X} (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + B)) :
    Divisor.toRDivisor K + QDivisor.toRDivisor B =
      ∑ _j : Fin 1, (1 / (m : ℝ)) • Divisor.toRDivisor M := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine DivisorWithCoeffs.ext' fun Γ => ?_
  have := congrArg (fun G : QDivisor X => G.coeff Γ) hM
  simp at this
  have h' : (M.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by linear_combination this
  have h'' : (M.coeff Γ : ℝ) = m * (K.coeff Γ + B.coeff Γ) := by exact_mod_cast h'
  rw [Flips.coeff_sum_smul_toRDivisor, Fin.sum_univ_one, h'', DivisorWithCoeffs.coeff_add,
    Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor]
  field_simp

omit [PerfectField k] [CompactSpace X] [LocallyOfFiniteType sX] in
/-- If `m(K + B)` is Cartier, `K + B` is an `ℝ`-combination of Cartier divisors. -/
private theorem isCartierCombination_toRDivisor_add {K : Divisor X} {B : QDivisor X} {m : ℕ}
    (hm : 0 < m) {M : Divisor X}
    (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + B)) (hMc : M.IsCartier) :
    Flips.IsCartierCombination (Divisor.toRDivisor K + QDivisor.toRDivisor B) := by
  refine ⟨1, fun _ => 1 / (m : ℝ), fun _ => M, fun _ => hMc, ?_⟩
  rw [toRDivisor_add_eq_sum hm hM]
  simp only [Flips.toRDivisor_eq_mapCoeffs]

/-- If `M = m(K + B)` is Cartier, the FA discrepancy of every divisor over `X` with proper
structure map exists and lies in `m⁻¹ℤ`. -/
theorem _root_.MMP.Flips.exists_isDiscrepancy_intCast_div (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} {m : ℕ} (hm : 0 < m)
    {M : Divisor X} (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + B))
    (hMc : M.IsCartier) (E : Flips.ProperDivisorOver k sX) :
    ∃ z : ℤ, Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor B) E.valuation ((z : ℝ) / m) := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : CompactSpace E.Y := by
    have := E.isNormalVariety.1
    have := E.isProper
    exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hωK : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  obtain ⟨M', hM'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f hMc
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hsum : Divisor.toRDivisor (divisorOfForm ω) + QDivisor.toRDivisor B =
      ∑ _j : Fin 1, (1 / (m : ℝ)) • Divisor.toRDivisor M := by
    rw [hωK]; exact toRDivisor_add_eq_sum hm hM
  refine ⟨m * E.toDivisorOver.ordPullback ω - M'.coeff E.E, hK,
    isCartierCombination_toRDivisor_add hm hM hMc, E.hasNonemptyCenter_valuation,
    E, ω, 1, fun _ => 1 / (m : ℝ), fun _ => M, rfl, hωK, hX, hK.topologicalKrullDim_eq, hω0,
    fun _ => hMc, hsum, fun _ => M', fun _ => ⟨_, hM'⟩, ?_⟩
  rw [Fin.sum_univ_one]
  push_cast
  field_simp

/-- The normalization of `P` in a normal integral locally Noetherian scheme `Y`, along a
quasi-compact open immersion `j : Y ⟶ P` with `P` locally of finite type over a field, is normal
and finite over `P`, and `Y` is open in it. -/
private theorem isOpenImmersion_toNormalization_and_isNormal_and_isFinite {Y P : Scheme.{u}}
    {sP : P ⟶ Spec (.of k)} [LocallyOfFiniteType sP] (j : Y ⟶ P) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiSeparated j] [IsNormal Y] [IsLocallyNoetherian Y] :
    IsOpenImmersion (Scheme.Hom.toNormalization j) ∧
      IsNormal (Scheme.Hom.normalization j) ∧ IsFinite (Scheme.Hom.fromNormalization j) := by
  refine ⟨?_, AlgebraicGeometry.isNormal_normalization j fun V hV => ?_,
    isFinite_fromNormalization_of_locallyOfFiniteType j
    (isNagataScheme_of_locallyOfFiniteType_over_field k sP)⟩
  · have : IsOpenImmersion ((Limits.pullback.snd j j).toNormalization ≫ j.normalizationPullback j ≫
        Limits.pullback.fst _ _) := inferInstance
    rw [Scheme.Hom.toNormalization_normalizationPullback_fst j j] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion
      (Limits.pullback.fst j j) _).mp this
  · have : IsNoetherian V :=
      { toIsLocallyNoetherian := inferInstance
        toCompactSpace := isCompact_iff_compactSpace.mp hV }
    exact NoetherianSpace.finite_irreducibleComponents

/-- If `t ≫ g` is birational and `t` is an open immersion of integral schemes, `g` is
birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {Y P Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral P] [IsIntegral Z] (t : Y ⟶ P) [IsOpenImmersion t] (g : P ⟶ Z)
    (h : IsBirationalMorphism (t ≫ g)) : IsBirationalMorphism g := by
  obtain ⟨W, ⟨w, hw⟩, hWo⟩ := h.exists_isOpenImmersion
  let U : P.Opens := t ''ᵁ W
  let V : Z.Opens := (W.ι ≫ t ≫ g).opensRange
  have hUV : U ≤ g ⁻¹ᵁ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have hU : U.ι ≫ g = (t.isoImage W).inv ≫ W.ι ≫ t ≫ g := by
    rw [← Scheme.Hom.isoImage_inv_ι_assoc]
  have hc : g.resLE V U hUV ≫ V.ι = (t.isoImage W).inv ≫ W.ι ≫ t ≫ g := by
    rw [Scheme.Hom.resLE_comp_ι, hU]
  have : IsOpenImmersion (g.resLE V U hUV ≫ V.ι) := by rw [hc]; infer_instance
  have : IsOpenImmersion (g.resLE V U hUV) := IsOpenImmersion.of_comp _ V.ι
  refine Flips.isBirationalMorphism_of_isIso_resLE g U V ⟨t w, w, hw, rfl⟩ ⟨_, ⟨w, hw⟩, rfl⟩
    hUV ?_
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun ⟨z, hz⟩ => ?_⟩⟩
  obtain ⟨w, rfl⟩ := hz
  refine ⟨(t.isoImage W).hom w, ?_⟩
  apply V.ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, hc, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
  rfl

/-- **KM 2.22 for `g = 𝟙`.** Every divisor over a normal variety `X` has the valuation of a
divisor over `X` with proper structure map. -/
private theorem exists_properDivisorOver_valuation_eq (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) : ∃ E : Flips.ProperDivisorOver k sX, E.valuation = D.valuation := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have hYv := D.isNormalVariety.1
  have hXv := hX.1
  have : IsSeparated sX := hXv.toIsSeparated
  have : IsSeparated (D.f ≫ sX) := hYv.toIsSeparated
  have : LocallyOfFiniteType (D.f ≫ sX) := hYv.toLocallyOfFiniteType
  have : QuasiCompact (D.f ≫ sX) := hYv.toQuasiCompact
  have : IsSeparated D.f := IsSeparated.of_comp D.f sX
  have : LocallyOfFiniteType D.f := locallyOfFiniteType_of_comp D.f sX
  have : QuasiCompact D.f := QuasiCompact.of_comp D.f sX
  have : IsNoetherian X := {}
  have : QuasiSeparatedSpace X := inferInstance
  obtain ⟨c, hc⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace D.f
  obtain ⟨P, j, p, hj, hjq, hp, hjp⟩ : ∃ (P : Scheme.{u}) (j : D.Y ⟶ P) (p : P ⟶ X),
      IsOpenImmersion j ∧ QuasiCompact j ∧ IsProper p ∧ j ≫ p = D.f :=
    ⟨c.space, c.immersion, c.toBase, inferInstance, hc, inferInstance, Over.w c.obj.hom⟩
  have : IsSeparated j := by
    have : IsSeparated (j ≫ p) := by rw [hjp]; infer_instance
    exact IsSeparated.of_comp j p
  have : LocallyOfFiniteType (p ≫ sX) := inferInstance
  have : QuasiSeparated j := IsSeparated.instQuasiSeparated j
  obtain ⟨ht, hnorm, hfin⟩ :=
    isOpenImmersion_toNormalization_and_isNormal_and_isFinite (sP := p ≫ sX) j
  set t := j.toNormalization
  let g := j.fromNormalization ≫ p
  have htg : t ≫ g = D.f := by
    simp only [g, t, Scheme.Hom.toNormalization_fromNormalization_assoc, hjp]
  have hgv : IsNormalVariety k (g ≫ sX) :=
    ⟨(isVariety_iff k _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hnorm⟩
  have hgb : IsBirationalMorphism g :=
    isBirationalMorphism_of_isOpenImmersion_comp t g (htg ▸ D.isBirationalMorphism)
  let D' : DivisorOver k sX :=
    ⟨_, g, hgv, hgb, OpenWeilRestriction.primeDivisorMap t D.E⟩
  refine ⟨⟨D', inferInstance⟩, (MMP.Positivity.DivisorOver.valuation_eq_of_iso D D' ⊤
    t.opensRange trivial ⟨D.E.genericPoint, ?_⟩ (D.Y.topIso ≪≫ t.isoOpensRange) ?_ ?_).symm⟩
  · exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm
  · simp [D', htg]
  · apply Subtype.ext
    change (D.Y.topIso.hom ≫ t.isoOpensRange.hom ≫ t.opensRange.ι) ⟨D.E.genericPoint, trivial⟩ = _
    rw [Scheme.Hom.isoOpensRange_hom_ι]
    exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm

omit [PerfectField k] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] in
/-- The lattice bound: a discrepancy `z / m ∈ m⁻¹ℤ` with positive log discrepancy is at least
`1/m - 1`. -/
private theorem one_div_sub_one_le_of_pos {m : ℕ} (hm : 0 < m) {z : ℤ}
    (h : 0 < 1 + (z : ℝ) / m) : 1 / (m : ℝ) - 1 ≤ z / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hz : (0 : ℝ) < m + z := by
    have := mul_pos hm0 h
    rwa [mul_add, mul_one, mul_div_cancel₀ _ hm0.ne'] at this
  have hz1 : (1 : ℝ) ≤ m + z := by exact_mod_cast (show (0 : ℤ) < m + z by exact_mod_cast hz)
  rw [div_sub_one hm0.ne', div_le_div_iff_of_pos_right hm0]
  linarith

/-- **FA klt bounds the KM discrepancy.** If every FA log discrepancy of `(X, B)` is positive
and `m(K_X + B)` is Cartier, then `-1 < discrep(X, B)` (via the bound `1/m - 1`). -/
private theorem neg_one_lt_discrep_of_forall_pos (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} {m : ℕ} (hm : 0 < m)
    {M : Divisor X} (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + B))
    (hMc : M.IsCartier)
    (hpos : ∀ F, Flips.HasNonemptyCenter k sX F → ∀ b : ℝ,
      Flips.IsLogDiscrepancy sX n K (QDivisor.toRDivisor B) F b → 0 < b) :
    -1 < discrep sX n K B := by
  have hle : (((1 / (m : ℝ) - 1 : ℝ)) : EReal) ≤ discrep sX n K B := by
    refine le_discrep_iff.mpr fun D a _ ha => ?_
    obtain ⟨E, hE⟩ := exists_properDivisorOver_valuation_eq hX D
    obtain ⟨z, hz⟩ := Flips.exists_isDiscrepancy_intCast_div hX hK hm hM hMc E
    rw [← hz.eq_of_valuation_eq hE.symm ha]
    exact EReal.coe_le_coe_iff.mpr (one_div_sub_one_le_of_pos hm
      (hpos _ (E.hasNonemptyCenter_valuation) _ ⟨_, hz, rfl⟩))
  refine lt_of_lt_of_le ?_ hle
  have : (0 : ℝ) < 1 / m := by positivity
  rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by simp]
  exact EReal.coe_lt_coe_iff.mpr (by linarith)

end KltDictionary

/-- **FA klt and KM klt agree for rational boundaries.** Let `X` be a normal variety of
dimension `n` over a perfect field with canonical divisor `K`, and `B` a `ℚ`-divisor which is a
boundary (`0 ≤ coeff ≤ 1`) with `K + B` `ℚ`-Cartier. Then `(X, B)` is Kawamata log terminal in
the sense of `MMP.Flips.IsKawamataLogTerminal` if and only if it is klt in the sense of
`MMP.Mori.IsKltPair`. -/
@[mmp "lem_fourfold_fa_rational_klt_dictionary"]
public theorem isKawamataLogTerminal_iff_isKltPair {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] (n : ℕ) (K : Divisor X)
    (B : QDivisor X) (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX n)
    (hB : Flips.IsBoundary (QDivisor.toRDivisor B))
    (hKB : (Divisor.toQDivisor K + B).IsQCartier) :
    Flips.IsKawamataLogTerminal sX n K (QDivisor.toRDivisor B) ↔ Mori.IsKltPair sX n K B := by
  obtain ⟨m, hm, M, hM, hMc⟩ := hKB.exists_pos
  have hP : Mori.IsPair sX B := ⟨hX, n, K, hK, hKB⟩
  constructor
  · rintro ⟨-, -, -, hpos⟩
    refine ⟨⟨hX, hK, hKB⟩, ?_, ?_⟩
    · exact neg_one_lt_discrep_of_forall_pos hX hK hm hM hMc hpos
    · refine roundDown_nonpos_iff.mpr fun P => ?_
      obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
      have hωK : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
      obtain ⟨z, hz⟩ := Flips.exists_isDiscrepancy_intCast_div hX hK hm hM hMc
        ⟨DivisorOver.ofPrimeDivisor k hX P, (inferInstance : IsProper (𝟙 X))⟩
      have hKD : Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) +
          QDivisor.toRDivisor B) := hωK ▸ hz.2.1
      have hd := Flips.isDiscrepancy_divisorialValuation hX ω hω0 (hωK ▸ hK) hKD P
      rw [hωK] at hd
      have := hpos _ hd.2.2.1 _ ⟨_, hd, rfl⟩
      rw [QDivisor.coeff_toRDivisor] at this
      exact_mod_cast (by linarith : ((B.coeff P : ℚ) : ℝ) < 1)
  · rintro ⟨-, hdisc, hfl⟩
    have hcoeff := roundDown_nonpos_iff.mp hfl
    refine ⟨⟨hX, hB⟩, hK, ?_, ?_⟩
    · exact isCartierCombination_toRDivisor_add hm hM hMc
    · rintro F ⟨-, E, rfl⟩ b ⟨a, ha, rfl⟩
      obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK E.toDivisorOver
      rw [ha.eq_of_valuation_eq rfl ha']
      by_cases hE : E.toDivisorOver.IsExceptional
      · have := lt_of_lt_of_le hdisc (discrep_le hE ha')
        rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by simp] at this
        have : (-1 : ℝ) < a' := EReal.coe_lt_coe_iff.mp this
        linarith
      · obtain ⟨P, hPv⟩ :=
          MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX _ hE
        obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
          (DivisorOver.ofPrimeDivisor k hX P)
        have h1 := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hPv
          (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hPv) ha' hc
        rw [h1, hc.eq_neg_coeff_of_ofPrimeDivisor hX]
        have : ((B.coeff P : ℚ) : ℝ) < 1 := by exact_mod_cast hcoeff P
        push_cast
        linarith

/-! ### Finite birational representations and admissible generation -/

section AdmissibleGeneration

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- Pull-back of forms along self-maps of the function field is contravariantly functorial:
`σ^* ∘ τ^* = (σ τ)^*`, for `σ τ` the composite `a ↦ σ (τ a)` of pull-backs of birational maps. -/
private theorem pluriformPullback_pluriformPullback {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] {d : ℕ}
    (hX : topologicalKrullDim X = d) (m : ℤ) (σ τ : FunctionFieldEquiv sX sX)
    (x : RationalPluriForms sX d m) :
    pluriformPullback sX sX σ.toHom d m (pluriformPullback sX sX τ.toHom d m x) =
      pluriformPullback sX sX (σ * τ).toHom d m x :=
  pluriformPullback_comp hX hX hX m σ.toHom τ.toHom x

/-! ### The finite monomial set acting on preadmissible systems -/

section Monomial

variable {k : Type u} [Field k] {I : Type*} {X : I → Scheme.{u}} {sX : ∀ i, X i ⟶ Spec (.of k)}
  [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
  {B : ∀ i, QDivisor (X i)} {n m : ℕ} (R : ResidueRestriction sX B n m)

/-- The `j`-th entry of a preadmissible system, as a rational form. -/
private abbrev ent (w : preadmissibleSections R) (j : I) : RationalPluriForms (sX j) n m :=
  ((w : ∀ i, logPluricanonicalSections (sX i) n m (B i)) j : RationalPluriForms (sX j) n m)

/-- The maps `w ↦ φ^* w_{j'}` from preadmissible systems to forms on `X_j`, for crepant
`φ : (X_j, B_j) ⇢ (X_{j'}, B_{j'})`. -/
private def pullbackMaps (j j' : I) :
    Set (preadmissibleSections R → RationalPluriForms (sX j) n m) :=
  {F | ∃ φ : FunctionFieldEquiv (sX j) (sX j'),
    IsCrepantBirationalMap (sX j) (sX j') (B j) (B j') φ ∧
      ∀ w, F w = pluriformPullback (sX j) (sX j') φ.toHom n m (ent R w j')}

/-- The injective monomial maps of preadmissible systems: `(g w)_j = φ_j^* w_{π j}` for a
permutation `π` and crepant `φ_j`. -/
private def monomialMaps : Set (preadmissibleSections R → preadmissibleSections R) :=
  {g | Function.Injective g ∧
    ∃ π : Equiv.Perm I, ∀ j, (fun w => ent R (g w) j) ∈ pullbackMaps R j (π j)}

/-- Stability of the preadmissible systems under the crepant birational identifications: the
`i`-th entry may be replaced by the pull-back `σ^* s_j`, keeping the other entries. -/
private abbrev IsStable : Prop :=
  ∀ (i j : I) (σ : FunctionFieldEquiv (sX i) (sX j)),
    IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ →
    ∀ s ∈ preadmissibleSections R, ∃ t ∈ preadmissibleSections R,
      ((t i : logPluricanonicalSections (sX i) n m (B i)) : Mori.RationalPluriForms (sX i) n m) =
        pluriformPullback (sX i) (sX j) σ.toHom n m (s j) ∧ ∀ l, l ≠ i → t l = s l

/-- Finiteness of the images of the crepant self-maps on the `i`-th entries. -/
private abbrev FiniteImage : Prop :=
  ∀ i : I, (Set.range fun (σ : crepantBirationalAutomorphisms (sX i) (B i))
    (s : (preadmissibleSections R).map (LinearMap.proj i)) =>
    pluriformPullback (sX i) (sX i) (σ : FunctionFieldEquiv (sX i) (sX i)).toHom n m
      ((s : logPluricanonicalSections (sX i) n m (B i)) :
        Mori.RationalPluriForms (sX i) n m)).Finite

include R in
private theorem setting_facts (i : I) :
    CharZero k ∧ LocallyOfFiniteType (sX i) ∧ topologicalKrullDim (X i) = n := by
  have hP := R.setting.isPair i
  exact ⟨hP.charZero, hP.isPair.isNormalVariety.1.toLocallyOfFiniteType,
    R.setting.topologicalKrullDim_eq i⟩

include R in
/-- Composition of crepant pull-backs. -/
private theorem pullback_trans {j j' j'' : I} (φ : FunctionFieldEquiv (sX j) (sX j'))
    (ψ : FunctionFieldEquiv (sX j') (sX j'')) (x : RationalPluriForms (sX j'') n m) :
    letI : ∀ i, Algebra k (X i).functionField := fun i => functionFieldAlgebra (sX i)
    pluriformPullback (sX j) (sX j') φ.toHom n m
        (pluriformPullback (sX j') (sX j'') ψ.toHom n m x) =
      pluriformPullback (sX j) (sX j'') (FunctionFieldEquiv.toHom (sX j) (sX j'') (ψ.trans φ))
        n m x := by
  let : ∀ i, Algebra k (X i).functionField := fun i => functionFieldAlgebra (sX i)
  obtain ⟨_, _, hj⟩ := setting_facts R j
  obtain ⟨_, _, hj'⟩ := setting_facts R j'
  obtain ⟨_, _, hj''⟩ := setting_facts R j''
  exact pluriformPullback_comp hj hj' hj'' m φ.toHom ψ.toHom x

include R in
/-- `σ^{-1 *} σ^* = id`. -/
private theorem pullback_symm_pullback {j j' : I} (σ : FunctionFieldEquiv (sX j) (sX j'))
    (x : RationalPluriForms (sX j') n m) :
    letI : ∀ i, Algebra k (X i).functionField := fun i => functionFieldAlgebra (sX i)
    pluriformPullback (sX j') (sX j) (FunctionFieldEquiv.toHom (sX j') (sX j) σ.symm) n m
      (pluriformPullback (sX j) (sX j') σ.toHom n m x) = x := by
  let : ∀ i, Algebra k (X i).functionField := fun i => functionFieldAlgebra (sX i)
  rw [pullback_trans R]
  obtain ⟨_, _, hj'⟩ := setting_facts R j'
  have h1 : σ.trans σ.symm = (1 : FunctionFieldEquiv (sX j') (sX j')) := by
    ext a
    simp
  rw [h1]
  exact pluriformPullback_one hj' m x

include R in
/-- `σ^* σ^{-1 *} = id`. -/
private theorem pullback_pullback_symm {j j' : I} (σ : FunctionFieldEquiv (sX j) (sX j'))
    (x : RationalPluriForms (sX j) n m) :
    letI : ∀ i, Algebra k (X i).functionField := fun i => functionFieldAlgebra (sX i)
    pluriformPullback (sX j) (sX j') σ.toHom n m
      (pluriformPullback (sX j') (sX j) (FunctionFieldEquiv.toHom (sX j') (sX j) σ.symm) n m x) =
        x := by
  let : ∀ i, Algebra k (X i).functionField := fun i => functionFieldAlgebra (sX i)
  simpa using pullback_symm_pullback R (j := j') (j' := j) σ.symm x

include R in
private theorem pullbackMaps_finite
    (hfinite : FiniteImage R)
    (j j' : I) : (pullbackMaps R j j').Finite := by
  let : ∀ i, Algebra k (X i).functionField := fun i => functionFieldAlgebra (sX i)
  by_cases h : ∃ φ₀ : FunctionFieldEquiv (sX j) (sX j'),
      IsCrepantBirationalMap (sX j) (sX j') (B j) (B j') φ₀
  swap
  · refine Set.finite_empty.subset ?_
    rintro F ⟨φ, hφ, -⟩
    exact h ⟨φ, hφ⟩
  obtain ⟨φ₀, hφ₀⟩ := h
  refine ((hfinite j').image (fun G w => pluriformPullback (sX j) (sX j') φ₀.toHom n m
    (G ⟨(w : ∀ i, logPluricanonicalSections (sX i) n m (B i)) j', w, w.2, rfl⟩))).subset ?_
  rintro F ⟨φ, hφ, hF⟩
  have hψ : IsCrepantBirationalMap (sX j') (sX j') (B j') (B j') (φ.trans φ₀.symm) :=
    hφ₀.symm.trans hφ
  refine ⟨_, ⟨⟨φ.trans φ₀.symm, hψ⟩, rfl⟩, ?_⟩
  funext w
  rw [hF w]
  change pluriformPullback (sX j) (sX j') φ₀.toHom n m
    (pluriformPullback (sX j') (sX j') (FunctionFieldEquiv.toHom (sX j') (sX j')
      (φ.trans φ₀.symm)) n m (ent R w j')) = _
  rw [pullback_trans R]
  congr 2
  ext a
  simp

include R in
private theorem id_mem_monomialMaps : id ∈ monomialMaps R := by
  let : ∀ i, Algebra k (X i).functionField := fun i => functionFieldAlgebra (sX i)
  refine ⟨Function.injective_id, Equiv.refl I,
    fun j => ⟨(1 : FunctionFieldEquiv (sX j) (sX j)), fun v a => Iff.rfl, fun w => ?_⟩⟩
  obtain ⟨_, _, hj⟩ := setting_facts R j
  exact (pluriformPullback_one hj m _).symm

include R in
private theorem comp_mem_monomialMaps {g₁ g₂ : preadmissibleSections R → preadmissibleSections R}
    (h₁ : g₁ ∈ monomialMaps R) (h₂ : g₂ ∈ monomialMaps R) : g₁ ∘ g₂ ∈ monomialMaps R := by
  let : ∀ i, Algebra k (X i).functionField := fun i => functionFieldAlgebra (sX i)
  obtain ⟨hi₁, π₁, hπ₁⟩ := h₁
  obtain ⟨hi₂, π₂, hπ₂⟩ := h₂
  refine ⟨hi₁.comp hi₂, π₁.trans π₂, fun j => ?_⟩
  obtain ⟨φ₁, hφ₁, hF₁⟩ := hπ₁ j
  obtain ⟨φ₂, hφ₂, hF₂⟩ := hπ₂ (π₁ j)
  refine ⟨φ₂.trans φ₁, hφ₁.trans hφ₂, fun w => ?_⟩
  have e1 : ent R (g₁ (g₂ w)) j = _ := hF₁ (g₂ w)
  have e2 : ent R (g₂ w) (π₁ j) = _ := hF₂ w
  rw [e2] at e1
  exact e1.trans (pullback_trans R φ₁ φ₂ _)

include R in
private theorem monomialMaps_finite
    (hfinite : FiniteImage R) :
    (monomialMaps R).Finite := by
  have := R.setting.finite
  let f : (preadmissibleSections R → preadmissibleSections R) →
      ∀ j : I, preadmissibleSections R → RationalPluriForms (sX j) n m :=
    fun g j w => ent R (g w) j
  have hinj : Function.Injective f := by
    intro g₁ g₂ h
    funext w
    refine Subtype.ext (funext fun j => Subtype.ext ?_)
    exact congrFun (congrFun h j) w
  refine (Set.finite_iUnion fun π : Equiv.Perm I =>
    ((Set.Finite.pi (t := fun j => pullbackMaps R j (π j))
      fun j => pullbackMaps_finite R hfinite j (π j)).preimage hinj.injOn)).subset ?_
  rintro g ⟨-, π, hπ⟩
  exact Set.mem_iUnion.mpr ⟨π, fun j _ => hπ j⟩

/-- Monomial maps are additive on entries. -/
private theorem ent_map_add {g : preadmissibleSections R → preadmissibleSections R}
    (hg : g ∈ monomialMaps R) (w w' : preadmissibleSections R) (j : I) :
    ent R (g (w + w')) j = ent R (g w) j + ent R (g w') j := by
  obtain ⟨-, π, hπ⟩ := hg
  obtain ⟨φ, -, hF⟩ := hπ j
  have hF' : ∀ w, ent R (g w) j = _ := hF
  rw [hF', hF', hF', ← map_add]
  rfl

/-- Monomial maps are `k`-linear on entries. -/
private theorem ent_map_smul {g : preadmissibleSections R → preadmissibleSections R}
    (hg : g ∈ monomialMaps R) (c : k) (w : preadmissibleSections R) (j : I) :
    ent R (g (c • w)) j = c • ent R (g w) j := by
  obtain ⟨-, π, hπ⟩ := hg
  obtain ⟨φ, -, hF⟩ := hπ j
  have hF' : ∀ w, ent R (g w) j = _ := hF
  rw [hF', hF', ← map_smul]
  rfl

include R in
/-- The identity pull-back fixes a form. -/
private theorem ent_mem_pullbackMaps_self {g : preadmissibleSections R → preadmissibleSections R}
    {j : I} (h : ∀ w, ent R (g w) j = ent R w j) :
    (fun w => ent R (g w) j) ∈ pullbackMaps R j j := by
  let : ∀ i, Algebra k (X i).functionField := fun i => functionFieldAlgebra (sX i)
  obtain ⟨_, _, hj⟩ := setting_facts R j
  exact ⟨(1 : FunctionFieldEquiv (sX j) (sX j)), fun v a => Iff.rfl,
    fun w => (h w).trans (pluriformPullback_one hj m _).symm⟩

/-- **Every crepant identification is realized by a monomial map**: for crepant
`σ : (X_i, B_i) ⇢ (X_{i'}, B_{i'})` some monomial map `g` has `(g w)_i = σ^* w_{i'}`. For `i = i'`
it replaces the `i`-th entry, for `i ≠ i'` it is the interchange
`w ↦ A w + B w - w` of the two replacements `A`, `B` given by stability. -/
private theorem exists_mem_monomialMaps
    (hstable : IsStable R)
    (i i' : I) (σ : FunctionFieldEquiv (sX i) (sX i'))
    (hσ : IsCrepantBirationalMap (sX i) (sX i') (B i) (B i') σ) :
    ∃ g ∈ monomialMaps R, ∀ w, ent R (g w) i = pluriformPullback (sX i) (sX i') σ.toHom n m
      (ent R w i') := by
  classical
  let : ∀ i, Algebra k (X i).functionField := fun i => functionFieldAlgebra (sX i)
  by_cases hii : i = i'
  · subst hii
    choose T hTW hTi hTo using fun w : preadmissibleSections R => hstable i i σ hσ w w.2
    let g : preadmissibleSections R → preadmissibleSections R := fun w => ⟨T w, hTW w⟩
    have gi : ∀ w, ent R (g w) i = pluriformPullback (sX i) (sX i) σ.toHom n m (ent R w i) :=
      hTi
    have go : ∀ w l, l ≠ i → ent R (g w) l = ent R w l := fun w l hl => by
      change ((T w l : logPluricanonicalSections (sX l) n m (B l)) :
        RationalPluriForms (sX l) n m) = _
      rw [hTo w l hl]
    refine ⟨g, ⟨fun w w' hww => ?_, Equiv.refl I, fun j => ?_⟩, gi⟩
    · have hi : ent R w i = ent R w' i := by
        have := congrArg (fun v => ent R v i) hww
        simp only [gi] at this
        have h2 := congrArg (pluriformPullback (sX i) (sX i)
          (FunctionFieldEquiv.toHom (sX i) (sX i) σ.symm) n m) this
        simpa only [pullback_symm_pullback R] using h2
      refine Subtype.ext (funext fun l => Subtype.ext ?_)
      by_cases hl : l = i
      · subst hl; exact hi
      · have := congrArg (fun v => ent R v l) hww
        simp only [go _ _ hl] at this
        exact this
    · by_cases hj : j = i
      · subst hj
        exact ⟨σ, hσ, gi⟩
      · exact ent_mem_pullbackMaps_self R (go · j hj)
  · choose TA hTAW hTAi hTAo using fun w : preadmissibleSections R => hstable i i' σ hσ w w.2
    choose TB hTBW hTBi hTBo using fun w : preadmissibleSections R =>
      hstable i' i σ.symm hσ.symm w w.2
    let g : preadmissibleSections R → preadmissibleSections R :=
      fun w => ⟨TA w + TB w - w, sub_mem (add_mem (hTAW w) (hTBW w)) w.2⟩
    have gent : ∀ w l, ent R (g w) l = ((TA w l : logPluricanonicalSections (sX l) n m (B l)) :
        RationalPluriForms (sX l) n m) + ((TB w l : logPluricanonicalSections (sX l) n m (B l)) :
        RationalPluriForms (sX l) n m) - ent R w l := fun w l => rfl
    have gi : ∀ w, ent R (g w) i = pluriformPullback (sX i) (sX i') σ.toHom n m (ent R w i') :=
      fun w => by rw [gent, hTAi, hTBo w i hii, add_sub_cancel_right]
    have gi' : ∀ w, ent R (g w) i' = pluriformPullback (sX i') (sX i)
        (FunctionFieldEquiv.toHom (sX i') (sX i) σ.symm) n m (ent R w i) :=
      fun w => by rw [gent, hTBi, hTAo w i' (Ne.symm hii), add_sub_cancel_left]
    have go : ∀ w l, l ≠ i → l ≠ i' → ent R (g w) l = ent R w l := fun w l hl hl' => by
      rw [gent, hTAo w l hl, hTBo w l hl', add_sub_cancel_right]
    have hgg : ∀ w, g (g w) = w := fun w => by
      refine Subtype.ext (funext fun l => Subtype.ext ?_)
      change ent R (g (g w)) l = ent R w l
      by_cases hl : l = i
      · subst hl; rw [gi, gi', pullback_pullback_symm R]
      · by_cases hl' : l = i'
        · subst hl'; rw [gi', gi, pullback_symm_pullback R]
        · rw [go _ _ hl hl', go _ _ hl hl']
    refine ⟨g, ⟨Function.LeftInverse.injective hgg, Equiv.swap i i', fun j => ?_⟩, gi⟩
    by_cases hj : j = i
    · subst hj
      rw [Equiv.swap_apply_left]
      exact ⟨σ, hσ, gi⟩
    · by_cases hj' : j = i'
      · subst hj'
        rw [Equiv.swap_apply_right]
        exact ⟨σ.symm, hσ.symm, gi'⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hj hj']
        exact ent_mem_pullbackMaps_self R (go · j hj hj')

include R in
/-- In a finite set of injective maps closed under composition, every map is bijective. -/
private theorem bijective_of_mem_monomialMaps (hfin : (monomialMaps R).Finite)
    {g : preadmissibleSections R → preadmissibleSections R} (hg : g ∈ monomialMaps R) :
    Function.Bijective g := by
  have hit : ∀ a : ℕ, g^[a] ∈ monomialMaps R := fun a => by
    induction a with
    | zero => exact id_mem_monomialMaps R
    | succ a ih => rw [Function.iterate_succ']; exact comp_mem_monomialMaps R hg ih
  obtain ⟨a, b, hab, he⟩ := hfin.exists_lt_map_eq_of_forall_mem (f := fun a => g^[a]) hit
  refine ⟨hg.1, fun y => ⟨g^[b - a - 1] y, ?_⟩⟩
  have h1 : g^[a] ∘ g^[b - a] = g^[a] ∘ id := by
    rw [← Function.iterate_add, Nat.add_sub_cancel' hab.le]
    exact he.symm
  have h2 : g^[b - a] = id := (hit a).1.comp_left h1
  have h3 : b - a = (b - a - 1) + 1 := by omega
  rw [h3, Function.iterate_succ'] at h2
  exact congrFun h2 y

end Monomial

/-! ### Products of graded families -/

/-- **Products of a graded family.** For a predicate `P` on degrees and coefficients closed under
`(a, x), (b, y) ↦ (a + b, x y)`, the product of a nonempty finite family of degree-`m` elements
satisfies `P` in degree `|A| m`. -/
private theorem graded_prod {M : Type*} [CommMonoid M] (P : ℕ → M → Prop)
    (hP : ∀ a b x y, P a x → P b y → P (a + b) (x * y)) {ι : Type*} {A : Finset ι}
    (hA : A.Nonempty) (m : ℕ) (c : ι → M) (hc : ∀ i ∈ A, P m (c i)) :
    P (A.card * m) (∏ i ∈ A, c i) := by
  induction hA using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hc a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    rw [Finset.prod_cons, Finset.card_cons, Nat.succ_mul, mul_comm (c a)]
    exact hP _ _ _ _ (ih fun i hi => hc i (Finset.mem_cons_of_mem hi))
      (hc a (Finset.mem_cons_self a s))

section Single

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- Products of sections of `m(K + B)` with respect to a fixed top form are sections of
`|A| m (K + B)`. -/
private theorem prod_smul_formPow_mem {d m : ℕ} {B : QDivisor X}
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄k])
    {ι : Type*} {A : Finset ι} (hA : A.Nonempty) (c : ι → X.functionField)
    (hc : ∀ i ∈ A,
      (letI := functionFieldAlgebra sX; c i • formPow ω m : RationalPluriForms sX d m) ∈
      logPluricanonicalSections sX d m B) :
    (letI := functionFieldAlgebra sX; (∏ i ∈ A, c i) • formPow ω (A.card * m) :
      RationalPluriForms sX d ((A.card * m : ℕ) : ℤ)) ∈
      logPluricanonicalSections sX d (A.card * m) B := by
  let := functionFieldAlgebra sX
  refine graded_prod (fun a x => (x • formPow ω a : RationalPluriForms sX d a) ∈
    logPluricanonicalSections sX d a B) (fun a b x y hx hy => ?_) hA m c hc
  have := mul_mem_logPluricanonicalSections hx hy
  convert this using 1
  exact (RationalPluriForms.mul_smul_formPow ω a b x y).symm

/-- Powers of local generators are local generators. -/
private theorem generatesOn_pow_smul_formPow [PerfectField k] [LocallyOfFiniteType sX] {d m : ℕ}
    (hd : topologicalKrullDim X = d) {B : QDivisor X} {U : X.Opens}
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄k])
    {ι : Type*} {A : Finset ι} (hA : A.Nonempty) (f : X.functionField)
    (hf : GeneratesOn B m U (letI := functionFieldAlgebra sX; f • formPow ω m :
      RationalPluriForms sX d m)) :
    GeneratesOn B (A.card * m) U (letI := functionFieldAlgebra sX;
      (f ^ A.card) • formPow ω (A.card * m) : RationalPluriForms sX d ((A.card * m : ℕ) : ℤ)) := by
  let := functionFieldAlgebra sX
  rw [← Finset.prod_const]
  refine graded_prod (fun a x => GeneratesOn B a U (x • formPow ω a : RationalPluriForms sX d a))
    (fun a b x y hx hy => ?_) hA m (fun _ => f) (fun _ _ => hf)
  have := GeneratesOn.mul hd hx hy
  convert this using 1
  exact (RationalPluriForms.mul_smul_formPow ω a b x y).symm

omit [IsNormal X] in
/-- A unit of `𝒪_{X,x}` has order zero along every prime divisor meeting some neighbourhood of
`x`, namely the non-vanishing locus of a section representing it. -/
private theorem exists_open_ord_eq_zero {x : X} {a : X.presheaf.stalk x} (ha : IsUnit a) :
    ∃ U' : X.Opens, x ∈ U' ∧ ∀ Γ : Mori.PrimeDivisor X, (Γ.support ∩ U').Nonempty →
      X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) Γ.genericPoint = 0 := by
  obtain ⟨V, hxV, f, rfl⟩ := X.presheaf.exists_germ_eq a
  refine ⟨X.basicOpen f, (X.mem_basicOpen f x hxV).mpr ha, fun Γ ⟨y, hyΓ, hyU⟩ => ?_⟩
  have hη : Γ.genericPoint ∈ X.basicOpen f := by
    have hsp : Γ.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hyΓ
    exact hsp.mem_open (X.basicOpen f).isOpen hyU
  have hηV : Γ.genericPoint ∈ V := X.basicOpen_le f hη
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hu := (X.mem_basicOpen f Γ.genericPoint hηV).mp hη
  rw [Scheme.algebraMap_germ_eq_germToFunctionField,
    ← Scheme.algebraMap_germ_eq_germToFunctionField X hηV f]
  exact Γ.ord_algebraMap_of_isUnit hu

variable [PerfectField k] [LocallyOfFiniteType sX]

/-- **Algebraic Hartogs for ratios of sections**: if `f₁ ω^{⊗m}` generates `𝒪_X(m(K_X + B))` on
`U ∋ x`, every section `c ω^{⊗m}` of `m(K_X + B)` has `c / f₁ ∈ 𝒪_{X,x}`. -/
private theorem exists_stalk_eq_div {d m : ℕ} (hd : topologicalKrullDim X = d) {B : QDivisor X}
    {U : X.Opens} {x : X} (hx : x ∈ U)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]))
    {f₁ c : X.functionField}
    (hgen : GeneratesOn B m U (letI := functionFieldAlgebra sX; f₁ • formPow (b ()) m :
      RationalPluriForms sX d m))
    (hc : (letI := functionFieldAlgebra sX; c • formPow (b ()) m : RationalPluriForms sX d m) ∈
      logPluricanonicalSections sX d m B) :
    ∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = c / f₁ := by
  let := functionFieldAlgebra sX
  have hτ : (formPow (b ()) m : RationalPluriForms sX d m) ≠ 0 := by
    rw [← ZTensorPower.basis_natCast]
    exact (ZTensorPower.basis b m).ne_zero ()
  have hf₁ : f₁ ≠ 0 := fun h => hgen.1 (by rw [h]; exact zero_smul _ _)
  by_cases hc0 : c = 0
  · exact ⟨0, by rw [hc0, zero_div, map_zero]⟩
  refine Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg x
    (div_ne_zero hc0 hf₁) fun Γ hΓ => ?_
  have h1 := hgen.2 Γ ⟨x, hΓ, hx⟩
  have hcτ : (c • formPow (b ()) m : RationalPluriForms sX d m) ≠ 0 := smul_ne_zero hc0 hτ
  have h2 := (((mem_logPluricanonicalSections sX).mp hc).2 Γ ⟨x, hΓ, trivial⟩ hcτ)
  erw [Mori.PrimeDivisor.ordForm_smul_of_topologicalKrullDim_eq Γ hd hf₁ hτ] at h1
  erw [Mori.PrimeDivisor.ordForm_smul_of_topologicalKrullDim_eq Γ hd hc0 hτ] at h2
  simp only [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul] at h2
  have h3 : X.ord (c / f₁ * f₁) Γ.genericPoint =
      X.ord (c / f₁) Γ.genericPoint + X.ord f₁ Γ.genericPoint :=
    Γ.ord_mul_of_ne_zero _ _ (div_ne_zero hc0 hf₁) hf₁
  rw [div_mul_cancel₀ c hf₁] at h3
  have h4 := Int.floor_le (((m : ℕ) : ℤ) • B.coeff Γ)
  have h5 : ((((m : ℕ) : ℤ) • B.coeff Γ : ℚ)) = (m : ℚ) * B.coeff Γ := by
    rw [zsmul_eq_mul]; push_cast; ring
  rw [h5] at h4
  rw [h5] at h2
  generalize Γ.ordForm (sX := sX) (d := d) (m := m) (formPow (b ()) m) = o at h1 h2
  have h2' : (0 : ℚ) ≤ (X.ord c Γ.genericPoint : ℚ) + (o : ℚ) +
      (⌊(m : ℚ) * B.coeff Γ⌋ : ℚ) := by exact_mod_cast h2
  have h3' : (X.ord c Γ.genericPoint : ℚ) =
      (X.ord (c / f₁) Γ.genericPoint : ℚ) + (X.ord f₁ Γ.genericPoint : ℚ) := by
    exact_mod_cast h3
  push_cast at h1
  have h8 : (0 : ℚ) ≤ (X.ord (c / f₁) Γ.genericPoint : ℚ) := by linarith
  exact_mod_cast h8

end Single

/-! ### Residues of products along fixed top forms -/

section ResidueInterface

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}

/-- Residues of products of forms written along fixed top forms `ω` on `X` and `ω_S` on `S`. -/
private theorem iir_prod [CharZero k] {n m : ℕ} {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S}
    [IsIntegral S] (F : StratumAdjunctionData sX B ι BS) {e : ℕ}
    (hS : topologicalKrullDim S = e)
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^n Ω[X.functionField⁄k])
    (ωS : letI := functionFieldAlgebra (ι ≫ sX); ⋀[S.functionField]^e Ω[S.functionField⁄k])
    {κ : Type*} {A : Finset κ} (hA : A.Nonempty) (c : κ → X.functionField)
    (r : κ → S.functionField)
    (hc : ∀ i ∈ A, IsIteratedResidue sX B
      (letI := functionFieldAlgebra sX; c i • formPow ω m : RationalPluriForms sX n m) F e
      (letI := functionFieldAlgebra (ι ≫ sX); r i • formPow ωS m :
        RationalPluriForms (ι ≫ sX) e m)) :
    IsIteratedResidue sX B
      (letI := functionFieldAlgebra sX; (∏ i ∈ A, c i) • formPow ω (A.card * m) :
        RationalPluriForms sX n ((A.card * m : ℕ) : ℤ)) F e
      (letI := functionFieldAlgebra (ι ≫ sX); (∏ i ∈ A, r i) • formPow ωS (A.card * m) :
        RationalPluriForms (ι ≫ sX) e ((A.card * m : ℕ) : ℤ)) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (ι ≫ sX)
  have key := graded_prod (M := X.functionField × S.functionField)
    (fun a x => IsIteratedResidue sX B (x.1 • formPow ω a : RationalPluriForms sX n a) F e
      (x.2 • formPow ωS a : RationalPluriForms (ι ≫ sX) e a))
    (fun a b x y hx hy => ?_) hA m (fun i => (c i, r i)) hc
  · simpa only [Prod.fst_prod, Prod.snd_prod] using key
  · have := IsIteratedResidue.mul hx hy hS
    have h1 := RationalPluriForms.mul_smul_formPow ω a b x.1 y.1
    have h2 := RationalPluriForms.mul_smul_formPow (sX := ι ≫ sX) ωS a b x.2 y.2
    rw [h1, h2] at this
    exact this

end ResidueInterface

/-- Pull-backs of products of forms written along fixed top forms: if `φ^*(c' j ω'^{⊗m})` is
`c j ω^{⊗m}` for every `j ∈ A`, then `φ^*((∏ c') ω'^{⊗|A| m}) = (∏ c) ω^{⊗|A| m}`. -/
private theorem pluriformPullback_prod_smul_formPow {k : Type u} [Field k] {X X' : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']
    (φ : FunctionFieldHom sX sX') {d m : ℕ}
    (ω' : letI := functionFieldAlgebra sX'; ⋀[X'.functionField]^d Ω[X'.functionField⁄k])
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄k])
    {κ : Type*} {A : Finset κ} (hA : A.Nonempty) (c' : κ → X'.functionField)
    (c : κ → X.functionField)
    (hc : ∀ j ∈ A, pluriformPullback sX sX' φ d m
      (letI := functionFieldAlgebra sX'; c' j • formPow ω' m : RationalPluriForms sX' d m) =
      (letI := functionFieldAlgebra sX; c j • formPow ω m : RationalPluriForms sX d m)) :
    pluriformPullback sX sX' φ d ((A.card * m : ℕ) : ℤ)
      (letI := functionFieldAlgebra sX'; (∏ j ∈ A, c' j) • formPow ω' (A.card * m) :
        RationalPluriForms sX' d ((A.card * m : ℕ) : ℤ)) =
      (letI := functionFieldAlgebra sX; (∏ j ∈ A, c j) • formPow ω (A.card * m) :
        RationalPluriForms sX d ((A.card * m : ℕ) : ℤ)) := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  have key := graded_prod (M := X'.functionField × X.functionField)
    (fun a x => pluriformPullback sX sX' φ d a (x.1 • formPow ω' a : RationalPluriForms sX' d a) =
      (x.2 • formPow ω a : RationalPluriForms sX d a))
    (fun a b x y hx hy => ?_) hA m (fun j => (c' j, c j)) hc
  · simpa only [Prod.fst_prod, Prod.snd_prod] using key
  · have := pluriformPullback_mul φ (x.1 • formPow ω' a : RationalPluriForms sX' d a)
      (y.1 • formPow ω' b : RationalPluriForms sX' d b)
    rw [hx, hy, RationalPluriForms.mul_smul_formPow, RationalPluriForms.mul_smul_formPow] at this
    exact this

/-- Coordinates along a basis and its pull-back are transported by the field map. -/
private theorem coord_of_pullback_eq {k : Type u} [Field k] {S S' : Scheme.{u}}
    {s : S ⟶ Spec (.of k)} {s' : S' ⟶ Spec (.of k)} [IsIntegral S] [IsIntegral S'] {e : ℕ}
    (σ : FunctionFieldEquiv s s')
    (bS' : letI := functionFieldAlgebra s'
      Module.Basis Unit S'.functionField (⋀[S'.functionField]^e Ω[S'.functionField⁄k]))
    (bS : letI := functionFieldAlgebra s
      Module.Basis Unit S.functionField (⋀[S.functionField]^e Ω[S.functionField⁄k]))
    (hω : letI := functionFieldAlgebra s'; letI := functionFieldAlgebra s
      letI : Algebra S'.functionField S.functionField := σ.toHom.toRingHom.toAlgebra
      haveI : IsScalarTower k S'.functionField S.functionField :=
        IsScalarTower.of_algebraMap_eq fun c => (σ.toHom.commutes c).symm
      IsPullbackGenerator S.functionField (bS' ()))
    (hb : letI := functionFieldAlgebra s'; letI := functionFieldAlgebra s
      letI : Algebra S'.functionField S.functionField := σ.toHom.toRingHom.toAlgebra
      haveI : IsScalarTower k S'.functionField S.functionField :=
        IsScalarTower.of_algebraMap_eq fun c => (σ.toHom.commutes c).symm
      bS () = topFormsMap k S'.functionField S.functionField e (bS' ()))
    (a : ℕ) {ρ' : RationalPluriForms s' e a} {ρ : RationalPluriForms s e a}
    (hp : pluriformPullback s s' σ.toHom e a ρ' = ρ) :
    letI := functionFieldAlgebra s'; letI := functionFieldAlgebra s
    FunctionFieldEquiv.toHom s s' σ ((ZTensorPower.basis bS' a).repr ρ' ()) =
      (ZTensorPower.basis bS a).repr ρ () := by
  let := functionFieldAlgebra s'
  let := functionFieldAlgebra s
  subst hp
  rw [pluriformPullback_eq_repr_smul_formPow σ.toHom bS' hω bS hb a ρ']
  exact (repr_smul_formPow bS a _).symm

/-- **Bases adapted to a birational map of strata**: a basis `b'` of `Ω^e_{k(S')/k}` whose
pull-back `b` is a basis of `Ω^e_{k(S)/k}`; along them `σ^*` transports coordinates by `σ`. -/
private theorem exists_pullback_bases {k : Type u} [Field k] [CharZero k] {S S' : Scheme.{u}}
    {s : S ⟶ Spec (.of k)} {s' : S' ⟶ Spec (.of k)} [IsIntegral S] [IsIntegral S']
    [LocallyOfFiniteType s] [LocallyOfFiniteType s'] {e : ℕ} (hS : topologicalKrullDim S = e)
    (hS' : topologicalKrullDim S' = e) (σ : FunctionFieldEquiv s s') :
    letI := functionFieldAlgebra s'; letI := functionFieldAlgebra s
    ∃ (bS' : Module.Basis Unit S'.functionField (⋀[S'.functionField]^e Ω[S'.functionField⁄k]))
      (bS : Module.Basis Unit S.functionField (⋀[S.functionField]^e Ω[S.functionField⁄k])),
      (∀ (a : ℕ) (c : S'.functionField),
        pluriformPullback s s' σ.toHom e a (c • formPow (bS' ()) a) =
          (FunctionFieldEquiv.toHom s s' σ c • formPow (bS ()) a : RationalPluriForms s e a)) ∧
      ∀ (a : ℕ) {ρ' : RationalPluriForms s' e a} {ρ : RationalPluriForms s e a},
        pluriformPullback s s' σ.toHom e a ρ' = ρ →
        FunctionFieldEquiv.toHom s s' σ ((ZTensorPower.basis bS' a).repr ρ' ()) =
          (ZTensorPower.basis bS a).repr ρ () := by
  let := functionFieldAlgebra s'
  let := functionFieldAlgebra s
  obtain ⟨ω', hω'⟩ := exists_isPullbackGenerator_functionFieldHom hS hS' σ.toHom
  let : Algebra S'.functionField S.functionField := σ.toHom.toRingHom.toAlgebra
  have : IsScalarTower k S'.functionField S.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (σ.toHom.commutes c).symm
  let bS' := basisOfSpanSingleton hω'.1 hω'.ne_zero
  let bS := basisOfSpanSingleton hω'.2.1 hω'.2.2
  have hbS' : bS' () = ω' := basisOfSpanSingleton_apply _ _ _
  have hω'' := hbS' ▸ hω'
  have hb : bS () = topFormsMap k S'.functionField S.functionField e (bS' ()) := by
    rw [hbS']
    exact basisOfSpanSingleton_apply _ _ _
  refine ⟨bS', bS, fun a c => ?_, fun a ρ' ρ hp => coord_of_pullback_eq σ bS' bS hω'' hb a hp⟩
  rw [hb]
  exact pluriformPullback_smul_formPow σ.toHom hω'' a c

/-! ### The orbit system -/

section Orbit

variable {k : Type u} [Field k] {I : Type*} {X : I → Scheme.{u}} {sX : ∀ i, X i ⟶ Spec (.of k)}
  [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
  {B : ∀ i, QDivisor (X i)} {n m : ℕ} (R : ResidueRestriction sX B n m)

include R in
private theorem exists_topBasis (j : I) :
    letI := functionFieldAlgebra (sX j)
    Nonempty (Module.Basis Unit (X j).functionField
      (⋀[(X j).functionField]^n Ω[(X j).functionField⁄k])) := by
  obtain ⟨_, _, hd⟩ := setting_facts R j
  exact exists_basis_topForms hd

/-- A fixed basis of the line `Ω^n_{k(X_j)/k}`. -/
private noncomputable def topBasis (j : I) :
    letI := functionFieldAlgebra (sX j)
    Module.Basis Unit (X j).functionField (⋀[(X j).functionField]^n Ω[(X j).functionField⁄k]) :=
  (exists_topBasis R j).some

/-- The coefficient of a form of degree `m` along the fixed top form. -/
private noncomputable def coef (j : I) (v : RationalPluriForms (sX j) n m) : (X j).functionField :=
  letI := functionFieldAlgebra (sX j)
  (ZTensorPower.basis (topBasis R j) m).repr v ()

private theorem eq_coef_smul (j : I) (v : RationalPluriForms (sX j) n m) :
    v = (letI := functionFieldAlgebra (sX j)
      coef R j v • formPow (topBasis R j ()) m : RationalPluriForms (sX j) n m) := by
  let := functionFieldAlgebra (sX j)
  exact eq_repr_smul_formPow (topBasis R j) v

/-- The finite set of monomial maps. -/
private noncomputable def orbitSet (hfinite : FiniteImage R) :
    Finset (preadmissibleSections R → preadmissibleSections R) :=
  (monomialMaps_finite R hfinite).toFinset

private theorem mem_orbitSet {hfinite : FiniteImage R}
    {g : preadmissibleSections R → preadmissibleSections R} :
    g ∈ orbitSet R hfinite ↔ g ∈ monomialMaps R :=
  Set.Finite.mem_toFinset _

private theorem orbitSet_nonempty (hfinite : FiniteImage R) : (orbitSet R hfinite).Nonempty :=
  ⟨id, (mem_orbitSet R).mpr (id_mem_monomialMaps R)⟩

/-- The coefficient `∏_{h ∈ H} (h w)_j` of the orbit product. -/
private noncomputable def orbitCoef (hfinite : FiniteImage R) (w : preadmissibleSections R)
    (j : I) : (X j).functionField :=
  ∏ h ∈ orbitSet R hfinite, coef R j (ent R (h w) j)

/-- **The orbit product** `t_j = ∏_{h ∈ H} (h w)_j`, a section of `|H| m (K_{X_j} + B_j)`. -/
private noncomputable def orbitSystem (hfinite : FiniteImage R) (w : preadmissibleSections R) :
    ∀ j, logPluricanonicalSections (sX j) n ((orbitSet R hfinite).card * m) (B j) := fun j =>
  ⟨(letI := functionFieldAlgebra (sX j); orbitCoef R hfinite w j •
      formPow (topBasis R j ()) ((orbitSet R hfinite).card * m)),
    prod_smul_formPow_mem _ (orbitSet_nonempty R hfinite) _ fun h _ => by
      rw [← eq_coef_smul]
      exact ((h w : ∀ i, logPluricanonicalSections (sX i) n m (B i)) j).2⟩

/-- Left composition with a monomial map permutes the products over the orbit set. -/
private theorem prod_orbitSet_comp {hfinite : FiniteImage R} {M : Type*} [CommMonoid M]
    {g : preadmissibleSections R → preadmissibleSections R} (hg : g ∈ monomialMaps R)
    (F : (preadmissibleSections R → preadmissibleSections R) → M) :
    ∏ h ∈ orbitSet R hfinite, F (g ∘ h) = ∏ h ∈ orbitSet R hfinite, F h := by
  have hi : ∀ h ∈ orbitSet R hfinite, g ∘ h ∈ orbitSet R hfinite := fun h hh =>
    (mem_orbitSet R).mpr (comp_mem_monomialMaps R hg ((mem_orbitSet R).mp hh))
  have hinj : ∀ h₁ h₂ (_ : h₁ ∈ orbitSet R hfinite) (_ : h₂ ∈ orbitSet R hfinite),
      g ∘ h₁ = g ∘ h₂ → h₁ = h₂ := fun h₁ h₂ _ _ e => hg.1.comp_left e
  refine Finset.prod_bij (fun h _ => g ∘ h) hi (fun h₁ ha₁ h₂ ha₂ e => hinj h₁ h₂ ha₁ ha₂ e)
    (fun b hb => ?_) (fun _ _ => rfl)
  obtain ⟨a, ha, e⟩ := Finset.surj_on_of_inj_on_of_card_le (fun h _ => g ∘ h) hi hinj le_rfl b hb
  exact ⟨a, ha, e.symm⟩

/-- **The orbit product is invariant under the crepant identifications of whole components**:
`σ^* t_{i'} = t_i` for crepant `σ : (X_i, B_i) ⇢ (X_{i'}, B_{i'})`. -/
private theorem orbitSystem_invariant (hfinite : FiniteImage R)
    (hstable : IsStable R)
    (w : preadmissibleSections R) {i i' : I} (σ : FunctionFieldEquiv (sX i) (sX i'))
    (hσ : IsCrepantBirationalMap (sX i) (sX i') (B i) (B i') σ) :
    pluriformPullback (sX i) (sX i') σ.toHom n (((orbitSet R hfinite).card * m : ℕ) : ℤ)
      ((orbitSystem R hfinite w i' : logPluricanonicalSections (sX i') n _ (B i')) :
        RationalPluriForms (sX i') n _) =
      ((orbitSystem R hfinite w i : logPluricanonicalSections (sX i) n _ (B i)) :
        RationalPluriForms (sX i) n _) := by
  classical
  let : ∀ j, Algebra k (X j).functionField := fun j => functionFieldAlgebra (sX j)
  obtain ⟨hc, hl, hd⟩ := setting_facts R i
  obtain ⟨-, hl', hd'⟩ := setting_facts R i'
  obtain ⟨g, hgH, hg⟩ := exists_mem_monomialMaps R hstable i i' σ hσ
  set N := (orbitSet R hfinite).card
  have hω' := isPullbackGenerator_functionFieldHom hd hd' σ.toHom
    (ω := topBasis R i' ()) (by rw [← Set.range_unique, (topBasis R i').span_eq])
    ((topBasis R i').ne_zero ())
  let : Algebra (X i').functionField (X i).functionField := σ.toHom.toRingHom.toAlgebra
  have : IsScalarTower k (X i').functionField (X i).functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (σ.toHom.commutes c).symm
  set β := (topBasis R i).repr (topFormsMap k (X i').functionField (X i).functionField n
    (topBasis R i' ())) () with hβ
  have hβω : topFormsMap k (X i').functionField (X i).functionField n (topBasis R i' ()) =
      β • topBasis R i () := (basis_unit_repr_smul _ _).symm
  have hpull : ∀ (a : ℕ) (c : (X i').functionField),
      pluriformPullback (sX i) (sX i') σ.toHom n a (c • formPow (topBasis R i' ()) a) =
        (σ c * β ^ a) • formPow (topBasis R i ()) a := fun a c => by
    rw [pluriformPullback_smul_formPow σ.toHom hω' a c, hβω, formPow_smul, smul_smul]
    rfl
  have hcoef : ∀ h : preadmissibleSections R → preadmissibleSections R,
      coef R i (ent R (g (h w)) i) = σ (coef R i' (ent R (h w) i')) * β ^ m := fun h => by
      rw [hg]
      generalize ent R (h w) i' = v
      conv_lhs => rw [eq_coef_smul R i' v, hpull]
      exact repr_smul_formPow (topBasis R i) m _
  change pluriformPullback (sX i) (sX i') σ.toHom n (N * m : ℕ)
      (orbitCoef R hfinite w i' • formPow (topBasis R i' ()) (N * m)) =
    orbitCoef R hfinite w i • formPow (topBasis R i ()) (N * m)
  rw [hpull]
  congr 1
  unfold orbitCoef
  rw [← prod_orbitSet_comp R hgH (fun h => coef R i (ent R (h w) i))]
  simp only [Function.comp_apply, hcoef]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, mul_comm m N]
  congr 1
  exact map_prod σ _ _

/-- The orbit product has as iterated residue the product of the residue restrictions of the
`(h w)_i`, written along a basis `ω_S` of the top forms of the stratum. -/
private theorem isIteratedResidue_orbitSystem (hfinite : FiniteImage R)
    (w : preadmissibleSections R)
    (i : I) {S : Scheme.{u}} {ι : S ⟶ X i} {BS : QDivisor S}
    (F : StratumAdjunctionData (sX i) (B i) ι BS) {e : ℕ} (hS : topologicalKrullDim S = e)
    (bS : haveI := F.isIntegral_stratum; letI := functionFieldAlgebra (ι ≫ sX i);
      Module.Basis Unit S.functionField (⋀[S.functionField]^e Ω[S.functionField⁄k])) :
    haveI := F.isIntegral_stratum
    IsIteratedResidue (sX i) (B i)
      (letI := functionFieldAlgebra (sX i); orbitCoef R hfinite w i •
        formPow (topBasis R i ()) ((orbitSet R hfinite).card * m) :
        RationalPluriForms (sX i) n (((orbitSet R hfinite).card * m : ℕ) : ℤ)) F e
      (letI := functionFieldAlgebra (ι ≫ sX i);
        (∏ h ∈ orbitSet R hfinite, (ZTensorPower.basis bS m).repr
          (R.toFun i F e ((h w : ∀ j, logPluricanonicalSections (sX j) n m (B j)) i)) ()) •
        formPow (bS ()) ((orbitSet R hfinite).card * m) :
        RationalPluriForms (ι ≫ sX i) e (((orbitSet R hfinite).card * m : ℕ) : ℤ)) := by
  have := F.isIntegral_stratum
  have := (setting_facts R i).1
  let := functionFieldAlgebra (sX i)
  let := functionFieldAlgebra (ι ≫ sX i)
  exact iir_prod F hS (topBasis R i ()) (bS ()) (orbitSet_nonempty R hfinite)
    (fun h => coef R i (ent R (h w) i))
    (fun h => (ZTensorPower.basis bS m).repr
      (R.toFun i F e ((h w : ∀ j, logPluricanonicalSections (sX j) n m (B j)) i)) ())
    (fun h _ => by
      have := R.isIteratedResidue i F e
        ((h w : ∀ j, logPluricanonicalSections (sX j) n m (B j)) i) hS
      generalize R.toFun i F e
        ((h w : ∀ j, logPluricanonicalSections (sX j) n m (B j)) i) = ρ at this
      have e1 := eq_coef_smul R i (ent R (h w) i)
      have e2 := eq_repr_smul_formPow bS ρ
      change IsIteratedResidue (sX i) (B i) (ent R (h w) i) F e ρ at this
      rw [e1, e2] at this
      exact this)

private theorem coef_add (j : I) (v v' : RationalPluriForms (sX j) n m) :
    coef R j (v + v') = coef R j v + coef R j v' := by
  let := functionFieldAlgebra (sX j)
  have := (ZTensorPower.basis (topBasis R j) (m : ℤ)).repr.map_add v v'
  exact (DFunLike.congr_fun this ()).trans (Finsupp.add_apply _ _ _)

private theorem coef_zero (j : I) : coef R j (0 : RationalPluriForms (sX j) n m) = 0 := by
  let := functionFieldAlgebra (sX j)
  exact DFunLike.congr_fun (ZTensorPower.basis (topBasis R j) (m : ℤ)).repr.map_zero ()

private theorem coef_smul (j : I) (c : k) (v : RationalPluriForms (sX j) n m) :
    coef R j (c • v) = (letI := functionFieldAlgebra (sX j); algebraMap k (X j).functionField c) *
      coef R j v := by
  let := functionFieldAlgebra (sX j)
  have := (ZTensorPower.basis (topBasis R j) (m : ℤ)).repr.map_smul
    (algebraMap k (X j).functionField c) v
  exact (DFunLike.congr_fun this ()).trans (Finsupp.smul_apply _ _ _)

/-- **The orbit product generates near every point.** Given `x ∈ X_i`, choose a preadmissible
system `w` such that for every `h ∈ H` the ratio of `(h w)_i` to a local generator `s_i` is a unit
at `x` (possible since `H` is finite, `k` is infinite, and each condition fails only on a proper
subspace); then `t_i = ∏_h (h w)_i` is a unit times `s_i^{|H|}` near `x`. -/
private theorem exists_orbitSystem_generatesOn (hfinite : FiniteImage R)
    (hgen : ∀ (i : I) (x : X i), ∃ s ∈ preadmissibleSections R, ∃ U : (X i).Opens, x ∈ U ∧
      Mori.GeneratesOn (B i) m U ((s i : logPluricanonicalSections (sX i) n m (B i)) :
        Mori.RationalPluriForms (sX i) n m))
    (i : I) (x : X i) : ∃ w : preadmissibleSections R, ∃ U : (X i).Opens, x ∈ U ∧
      Mori.GeneratesOn (B i) ((orbitSet R hfinite).card * m) U
        ((orbitSystem R hfinite w i : logPluricanonicalSections (sX i) n _ (B i)) :
          RationalPluriForms (sX i) n _) := by
  classical
  obtain ⟨hc, hl, hd⟩ := setting_facts R i
  have : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  let := functionFieldAlgebra (sX i)
  let := stalkAlgebra (sX i) x
  have := isScalarTower_stalk_functionField (sX i) x
  obtain ⟨s₀, hs₀, U, hxU, hgU⟩ := hgen i x
  let w₀ : preadmissibleSections R := ⟨s₀, hs₀⟩
  set f₁ := coef R i (ent R w₀ i) with hf₁_def
  have hgen' : GeneratesOn (B i) m U
      (f₁ • formPow (topBasis R i ()) m : RationalPluriForms (sX i) n m) := by
    rw [← eq_coef_smul]; exact hgU
  have hf₁ : f₁ ≠ 0 := fun h => hgen'.1 (by rw [h]; exact zero_smul _ _)
  have hratio : ∀ (w : preadmissibleSections R) (h : preadmissibleSections R →
      preadmissibleSections R), ∃ a : (X i).presheaf.stalk x,
      algebraMap _ (X i).functionField a = coef R i (ent R (h w) i) / f₁ := fun w h =>
    exists_stalk_eq_div hd hxU (topBasis R i) hgen' (by
      rw [← eq_coef_smul]; exact ((h w : ∀ j, logPluricanonicalSections (sX j) n m (B j)) i).2)
  let Z : orbitSet R hfinite → Submodule k (preadmissibleSections R) := fun h =>
    { carrier := {w | ∃ a ∈ IsLocalRing.maximalIdeal ((X i).presheaf.stalk x),
        algebraMap _ (X i).functionField a = coef R i (ent R (h.1 w) i) / f₁}
      add_mem' := by
        rintro w w' ⟨a, ha, hae⟩ ⟨a', ha', hae'⟩
        refine ⟨a + a', add_mem ha ha', ?_⟩
        rw [map_add, hae, hae', ent_map_add R ((mem_orbitSet R).mp h.2), coef_add, add_div]
      zero_mem' := by
        refine ⟨0, zero_mem _, ?_⟩
        have := ent_map_smul R ((mem_orbitSet R).mp h.2) 0 0 i
        rw [zero_smul, zero_smul] at this
        change _ = coef R i (ent R (h.1 0) i) / f₁
        rw [this, map_zero, coef_zero, zero_div]
      smul_mem' := by
        rintro c w ⟨a, ha, hae⟩
        refine ⟨algebraMap k _ c * a, Ideal.mul_mem_left _ _ ha, ?_⟩
        change _ = coef R i (ent R (h.1 (c • w)) i) / f₁
        rw [map_mul, hae, ent_map_smul R ((mem_orbitSet R).mp h.2), coef_smul, mul_div_assoc,
          ← IsScalarTower.algebraMap_apply] }
  have hZ : ∀ h, Z h ≠ ⊤ := by
    intro h hZh
    obtain ⟨w₁, hw₁⟩ := (bijective_of_mem_monomialMaps R (monomialMaps_finite R hfinite)
      ((mem_orbitSet R).mp h.2)).2 w₀
    obtain ⟨a, ha, hae⟩ : w₁ ∈ Z h := hZh ▸ Submodule.mem_top
    change algebraMap _ _ a = coef R i (ent R (h.1 w₁) i) / f₁ at hae
    rw [hw₁, div_self hf₁, ← map_one (algebraMap ((X i).presheaf.stalk x) (X i).functionField)]
      at hae
    have := IsFractionRing.injective ((X i).presheaf.stalk x) (X i).functionField hae
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      ((Ideal.eq_top_iff_one _).mpr (this ▸ ha))
  obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top Z hZ
  have hunit : ∀ h : orbitSet R hfinite, ∃ a : (X i).presheaf.stalk x, IsUnit a ∧
      algebraMap _ (X i).functionField a = coef R i (ent R (h.1 w) i) / f₁ := fun h => by
    obtain ⟨a, hae⟩ := hratio w h.1
    refine ⟨a, ?_, hae⟩
    by_contra hna
    exact hw h ⟨a, (IsLocalRing.mem_maximalIdeal _).mpr hna, hae⟩
  choose a ha hae using hunit
  set u := ∏ h : orbitSet R hfinite, a h
  have hu : IsUnit u := IsUnit.prod_univ_iff.mpr ha
  obtain ⟨U', hxU', hU'⟩ := exists_open_ord_eq_zero hu
  refine ⟨w, U ⊓ U', ⟨hxU, hxU'⟩, ?_⟩
  have hcoef : orbitCoef R hfinite w i =
      algebraMap _ (X i).functionField u * f₁ ^ (orbitSet R hfinite).card := by
    unfold orbitCoef
    rw [← Finset.prod_attach]
    have e : ∀ h : orbitSet R hfinite, coef R i (ent R (h.1 w) i) =
        algebraMap _ (X i).functionField (a h) * f₁ := fun h => by
      rw [hae h, div_mul_cancel₀ _ hf₁]
    rw [Finset.prod_congr rfl (fun h _ => e h), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_attach, map_prod, Finset.univ_eq_attach]
  have hpow := generatesOn_pow_smul_formPow hd (topBasis R i ()) (orbitSet_nonempty R hfinite) f₁
    hgen'
  have hne : algebraMap _ (X i).functionField u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hu.ne_zero
  change GeneratesOn (B i) _ _ (orbitCoef R hfinite w i •
    formPow (topBasis R i ()) ((orbitSet R hfinite).card * m) :
      RationalPluriForms (sX i) n (((orbitSet R hfinite).card * m : ℕ) : ℤ))
  rw [hcoef, mul_smul]
  refine ⟨smul_ne_zero hne hpow.1, fun Γ hΓ => ?_⟩
  have h1 := hpow.2 Γ (hΓ.mono fun y hy => ⟨hy.1, hy.2.1⟩)
  have h2 := hU' Γ (hΓ.mono fun y hy => ⟨hy.1, hy.2.2⟩)
  erw [Mori.PrimeDivisor.ordForm_smul_of_topologicalKrullDim_eq Γ hd hne hpow.1]
  rw [h2, zero_add]
  exact h1

/-- The `|A|`-fold power `t^{|A|}` of the orbit product `t = ∏_{h ∈ H} (h w)`, a section of
`|A| |H| m (K_{X_j} + B_j)`. -/
private noncomputable def powSystem (hfinite : FiniteImage R) {A : Finset ℕ} (hA : A.Nonempty)
    (w : preadmissibleSections R) :
    ∀ j, logPluricanonicalSections (sX j) n (A.card * ((orbitSet R hfinite).card * m)) (B j) :=
  fun j =>
  ⟨(letI := functionFieldAlgebra (sX j); (∏ _a ∈ A, orbitCoef R hfinite w j) •
      formPow (topBasis R j ()) (A.card * ((orbitSet R hfinite).card * m))),
    prod_smul_formPow_mem _ hA _ fun _ _ => (orbitSystem R hfinite w j).2⟩

/-- **Powers of the orbit product are invariant under the crepant identifications of whole
components**: the `|A|`-th power of `orbitSystem_invariant`. -/
private theorem powSystem_invariant (hfinite : FiniteImage R)
    (hstable : IsStable R) {A : Finset ℕ} (hA : A.Nonempty)
    (w : preadmissibleSections R) {i i' : I} (σ : FunctionFieldEquiv (sX i) (sX i'))
    (hσ : IsCrepantBirationalMap (sX i) (sX i') (B i) (B i') σ) :
    pluriformPullback (sX i) (sX i') σ.toHom n
      ((A.card * ((orbitSet R hfinite).card * m) : ℕ) : ℤ)
      ((powSystem R hfinite hA w i' : logPluricanonicalSections (sX i') n _ (B i')) :
        RationalPluriForms (sX i') n _) =
      ((powSystem R hfinite hA w i : logPluricanonicalSections (sX i) n _ (B i)) :
        RationalPluriForms (sX i) n _) :=
  pluriformPullback_prod_smul_formPow σ.toHom _ _ hA _ _ fun _ _ =>
    orbitSystem_invariant R hfinite hstable w σ hσ

/-- **Residues of powers of the orbit product**: the `|A|`-th power of the product of the
residue restrictions of the `(h w)_i`. -/
private theorem residue_powSystem (hfinite : FiniteImage R) {A : Finset ℕ} (hA : A.Nonempty)
    (R' : ResidueRestriction sX B n (A.card * ((orbitSet R hfinite).card * m)))
    (w : preadmissibleSections R)
    (i : I) {S : Scheme.{u}} {ι : S ⟶ X i} {BS : QDivisor S}
    (F : StratumAdjunctionData (sX i) (B i) ι BS) {e : ℕ} (hS : topologicalKrullDim S = e)
    (bS : haveI := F.isIntegral_stratum; letI := functionFieldAlgebra (ι ≫ sX i);
      Module.Basis Unit S.functionField (⋀[S.functionField]^e Ω[S.functionField⁄k])) :
    haveI := F.isIntegral_stratum
    R'.toFun i F e (powSystem R hfinite hA w i) =
      (letI := functionFieldAlgebra (ι ≫ sX i);
        (∏ _a ∈ A, ∏ h ∈ orbitSet R hfinite, (ZTensorPower.basis bS m).repr
          (R.toFun i F e ((h w : ∀ j, logPluricanonicalSections (sX j) n m (B j)) i)) ()) •
        formPow (bS ()) (A.card * ((orbitSet R hfinite).card * m)) :
        RationalPluriForms (ι ≫ sX i) e
          ((A.card * ((orbitSet R hfinite).card * m) : ℕ) : ℤ)) := by
  have := F.isIntegral_stratum
  have := (setting_facts R i).1
  let := functionFieldAlgebra (sX i)
  let := functionFieldAlgebra (ι ≫ sX i)
  have h1 := R'.isIteratedResidue i F e (powSystem R hfinite hA w i) hS
  have h2 := iir_prod F hS (topBasis R i ()) (bS ()) hA (fun _ => orbitCoef R hfinite w i)
    (fun _ => ∏ h ∈ orbitSet R hfinite, (ZTensorPower.basis bS m).repr
          (R.toFun i F e ((h w : ∀ j, logPluricanonicalSections (sX j) n m (B j)) i)) ())
    (fun _ _ => isIteratedResidue_orbitSystem R hfinite w i F hS bS)
  exact IsIteratedResidue.unique h1 h2

/-- **Powers of the orbit product are admissible** in degree `|A| |H| m`, for every residue
restriction datum in that degree. -/
private theorem powSystem_mem_admissibleSections (hfinite : FiniteImage R)
    (hstable : IsStable R) {A : Finset ℕ} (hA : A.Nonempty)
    (R' : ResidueRestriction sX B n (A.card * ((orbitSet R hfinite).card * m)))
    (w : preadmissibleSections R) : powSystem R hfinite hA w ∈ admissibleSections R' := by
  classical
  intro i i' S S' ι ι' BS BS' F F' e _ _ hS hS' σ hσ
  obtain ⟨hc, hl, hd⟩ := setting_facts R i
  obtain ⟨-, hl', hd'⟩ := setting_facts R i'
  have hF := F.dim_add_length hd hS
  have hF' := F'.dim_add_length hd' hS'
  rcases Nat.eq_zero_or_pos F.length with h0 | h0 <;>
    rcases Nat.eq_zero_or_pos F'.length with h0' | h0'
  · cases F with
    | step => simp [StratumAdjunctionData.length] at h0
    | refl hp =>
      cases F' with
      | step => simp [StratumAdjunctionData.length] at h0'
      | refl hp' =>
        simp only [StratumAdjunctionData.length, add_zero] at hF
        subst hF
        have e1 := IsIteratedResidue.unique
          (R'.isIteratedResidue i (.refl hp) e (powSystem R hfinite hA w i) hS)
          (IsIteratedResidue.refl hp)
        have e2 := IsIteratedResidue.unique (R'.isIteratedResidue i' (.refl hp') e
          (powSystem R hfinite hA w i') hS') (IsIteratedResidue.refl hp')
        rw [e1, e2]
        have key : ∀ (s₁ : X i ⟶ Spec (.of k)) (s₂ : X i' ⟶ Spec (.of k)) (h₁ : sX i = s₁)
            (h₂ : sX i' = s₂) (σ : FunctionFieldEquiv s₁ s₂),
            IsCrepantBirationalMap s₁ s₂ (B i) (B i') σ →
            pluriformPullback s₁ s₂ σ.toHom e
              ((A.card * ((orbitSet R hfinite).card * m) : ℕ) : ℤ)
              (cast (congrArg (fun s => RationalPluriForms s e
                ((A.card * ((orbitSet R hfinite).card * m) : ℕ) : ℤ)) h₂)
                ((powSystem R hfinite hA w i' : logPluricanonicalSections (sX i') e _ (B i')) :
                  RationalPluriForms (sX i') e _)) =
              cast (congrArg (fun s => RationalPluriForms s e
                ((A.card * ((orbitSet R hfinite).card * m) : ℕ) : ℤ)) h₁)
                ((powSystem R hfinite hA w i : logPluricanonicalSections (sX i) e _ (B i)) :
                  RationalPluriForms (sX i) e _) := by
          intro s₁ s₂ h₁ h₂
          subst h₁ h₂
          intro σ hσ
          exact powSystem_invariant R hfinite hstable hA w σ hσ
        exact key _ _ (Category.id_comp _).symm (Category.id_comp _).symm σ hσ
  · omega
  · omega
  · haveI := F.isIntegral_stratum
    haveI := F'.isIntegral_stratum
    haveI : LocallyOfFiniteType (ι ≫ sX i) := F.isNormalVariety.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (ι' ≫ sX i') := F'.isNormalVariety.1.toLocallyOfFiniteType
    obtain ⟨bS', bS, hpull, hcoord⟩ := exists_pullback_bases hS hS' σ
    rw [residue_powSystem R hfinite hA R' w i F hS bS,
      residue_powSystem R hfinite hA R' w i' F' hS' bS', hpull]
    congr 1
    rw [map_prod]
    refine Finset.prod_congr rfl fun _ _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun h _ => ?_
    exact hcoord m ((h w).2 i i' F F' e h0 h0' hS hS' σ hσ)

/-- **Powers of the orbit product generate near every point.** -/
private theorem exists_powSystem_generatesOn (hfinite : FiniteImage R)
    (hgen : ∀ (i : I) (x : X i), ∃ s ∈ preadmissibleSections R, ∃ U : (X i).Opens, x ∈ U ∧
      Mori.GeneratesOn (B i) m U ((s i : logPluricanonicalSections (sX i) n m (B i)) :
        Mori.RationalPluriForms (sX i) n m))
    {A : Finset ℕ} (hA : A.Nonempty)
    (i : I) (x : X i) : ∃ w : preadmissibleSections R, ∃ U : (X i).Opens, x ∈ U ∧
      Mori.GeneratesOn (B i) (A.card * ((orbitSet R hfinite).card * m)) U
        ((powSystem R hfinite hA w i : logPluricanonicalSections (sX i) n _ (B i)) :
          RationalPluriForms (sX i) n _) := by
  obtain ⟨w, U, hxU, hU⟩ := exists_orbitSystem_generatesOn R hfinite hgen i x
  refine ⟨w, U, hxU, ?_⟩
  obtain ⟨hc, hl, hd⟩ := setting_facts R i
  let := functionFieldAlgebra (sX i)
  have := generatesOn_pow_smul_formPow hd (topBasis R i ()) hA (orbitCoef R hfinite w i) hU
  change GeneratesOn (B i) _ U ((∏ _a ∈ A, orbitCoef R hfinite w i) •
    formPow (topBasis R i ()) (A.card * ((orbitSet R hfinite).card * m)) :
      RationalPluriForms (sX i) n ((A.card * ((orbitSet R hfinite).card * m) : ℕ) : ℤ))
  rw [Finset.prod_const]
  exact this

end Orbit

/-- The generation half of `exists_admissibleSections_generatesOn_of_finite`: for `N = |H|` and
every `c > 0`, the `c`-th powers of the orbit products of general preadmissible systems under
the finite set `H` of monomial maps are admissible and generate in degree `c N m`. -/
private theorem exists_admissibleSections_generatesOn_mul {k : Type u} [Field k]
    {I : Type*} {X : I → Scheme.{u}} {sX : ∀ i, X i ⟶ Spec (.of k)}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {B : ∀ i, QDivisor (X i)} {n m : ℕ} (R : ResidueRestriction sX B n m)
    (hgen : ∀ (i : I) (x : X i), ∃ s ∈ preadmissibleSections R, ∃ U : (X i).Opens, x ∈ U ∧
      Mori.GeneratesOn (B i) m U ((s i : logPluricanonicalSections (sX i) n m (B i)) :
        Mori.RationalPluriForms (sX i) n m))
    (hstable : IsStable R)
    (hfinite : FiniteImage R) :
    ∃ N : ℕ, 0 < N ∧ ∀ c : ℕ, 0 < c → ∀ R' : ResidueRestriction sX B n (c * (N * m)),
      ∀ (i : I) (x : X i), ∃ s ∈ admissibleSections R', ∃ U : (X i).Opens, x ∈ U ∧
        Mori.GeneratesOn (B i) (c * (N * m)) U (s i).1 := by
  refine ⟨(orbitSet R hfinite).card, Finset.card_pos.mpr (orbitSet_nonempty R hfinite),
    fun c hc => ?_⟩
  have hA : (Finset.range c).Nonempty := Finset.nonempty_range_iff.mpr hc.ne'
  have key : ∀ R' : ResidueRestriction sX B n
      ((Finset.range c).card * ((orbitSet R hfinite).card * m)), ∀ (i : I) (x : X i),
      ∃ s ∈ admissibleSections R', ∃ U : (X i).Opens, x ∈ U ∧
        Mori.GeneratesOn (B i) ((Finset.range c).card * ((orbitSet R hfinite).card * m)) U
          (s i).1 := fun R' i x => by
    obtain ⟨w, U, hxU, hU⟩ := exists_powSystem_generatesOn R hfinite hgen hA i x
    exact ⟨powSystem R hfinite hA w, powSystem_mem_admissibleSections R hfinite hstable hA R' w,
      U, hxU, hU⟩
  rwa [Finset.card_range] at key

/-- The lifting half of `exists_admissibleSections_generatesOn_of_finite`: the average of a
preadmissible lift over the finite image of the crepant birational self-maps is invariant and
keeps the proper-stratum restrictions. -/
private theorem exists_invariant_preadmissible_lift {k : Type u} [Field k]
    {I : Type*} {X : I → Scheme.{u}} {sX : ∀ i, X i ⟶ Spec (.of k)}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {B : ∀ i, QDivisor (X i)} {n m : ℕ} (R : ResidueRestriction sX B n m)
    (hstable : IsStable R)
    (hfix : ∀ (i j : I) (σ : FunctionFieldEquiv (sX i) (sX j)),
      IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ →
      ∀ s ∈ preadmissibleSections R, ∀ t ∈ preadmissibleSections R,
        ((t i : logPluricanonicalSections (sX i) n m (B i)) : Mori.RationalPluriForms (sX i) n m) =
          pluriformPullback (sX i) (sX j) σ.toHom n m (s j) →
        ∀ {S : Scheme.{u}} {ι : S ⟶ X i} {BS : QDivisor S}
          (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ), 0 < F.length →
          topologicalKrullDim S = e → R.toFun i F e (t i) = R.toFun i F e (s i))
    (hfinite : FiniteImage R) :
    ∀ s ∈ preadmissibleSections R, ∀ i : I, ∃ t ∈ preadmissibleSections R,
      (∀ σ ∈ crepantBirationalAutomorphisms (sX i) (B i),
        pluriformPullback (sX i) (sX i) σ.toHom n m (t i) =
          (t i : Mori.RationalPluriForms (sX i) n m)) ∧
      ∀ {S : Scheme.{u}} {ι : S ⟶ X i} {BS : QDivisor S}
        (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ), 0 < F.length →
        topologicalKrullDim S = e → R.toFun i F e (t i) = R.toFun i F e (s i) := by
  classical
  intro s hs i
  have hP := R.setting.isPair i
  have := hP.charZero
  have : LocallyOfFiniteType (sX i) := hP.isPair.isNormalVariety.1.toLocallyOfFiniteType
  have hdim := R.setting.topologicalKrullDim_eq i
  have hfin := hfinite i
  let := hfin.fintype
  set Gs := Set.range fun (σ : crepantBirationalAutomorphisms (sX i) (B i))
        (s : (preadmissibleSections R).map (LinearMap.proj i)) =>
        pluriformPullback (sX i) (sX i) (σ : FunctionFieldEquiv (sX i) (sX i)).toHom n m
          ((s : logPluricanonicalSections (sX i) n m (B i)) :
            Mori.RationalPluriForms (sX i) n m)
  have hσ : ∀ φ : Gs, ∃ σ : crepantBirationalAutomorphisms (sX i) (B i),
      (fun (y : (preadmissibleSections R).map (LinearMap.proj i)) =>
        pluriformPullback (sX i) (sX i) (σ : FunctionFieldEquiv (sX i) (sX i)).toHom n m
          ((y : logPluricanonicalSections (sX i) n m (B i)) :
            Mori.RationalPluriForms (sX i) n m)) = φ := fun φ => φ.2
  choose σφ hσφ using hσ
  let si : (preadmissibleSections R).map (LinearMap.proj i) := ⟨s i, s, hs, rfl⟩
  have hT := fun φ : Gs => hstable i i (σφ φ) (σφ φ).2 s hs
  choose T hTW hTi hTo using hT
  have hne : Nonempty Gs := ⟨⟨_, 1, rfl⟩⟩
  set c : k := (Fintype.card Gs : k) with hc_def
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hti : (((c⁻¹ • ∑ φ, T φ) i : logPluricanonicalSections (sX i) n m (B i)) :
      Mori.RationalPluriForms (sX i) n m) = c⁻¹ • ∑ φ : Gs, (φ : _ → _) si := by
    simp only [Pi.smul_apply, Finset.sum_apply, Submodule.coe_smul, Submodule.coe_sum, hTi]
    congr 1
    exact Finset.sum_congr rfl fun φ _ => congrFun (hσφ φ) si
  refine ⟨c⁻¹ • ∑ φ, T φ, Submodule.smul_mem _ _ (Submodule.sum_mem _ fun φ _ => hTW φ),
    fun τ hτ => ?_, fun {S ι BS} F e hl hd => ?_⟩
  · rw [hti, map_smul, map_sum]
    congr 1
    let τ' : crepantBirationalAutomorphisms (sX i) (B i) := ⟨τ, hτ⟩
    let e : Gs → Gs := fun φ => ⟨_, τ' * σφ φ, rfl⟩
    have he_apply : ∀ φ : Gs, (e φ : _ → _) si =
        pluriformPullback (sX i) (sX i) τ.toHom n m ((φ : _ → _) si) := fun φ => by
      rw [← hσφ φ]
      exact (pluriformPullback_pluriformPullback (sX i) hdim m τ _ _).symm
    have he : Function.Injective e := by
      intro φ ψ hφψ
      have h := congrArg Subtype.val hφψ
      apply Subtype.ext
      rw [← hσφ φ, ← hσφ ψ]
      funext y
      have key : ∀ σ : crepantBirationalAutomorphisms (sX i) (B i),
          pluriformPullback (sX i) (sX i) (σ : FunctionFieldEquiv (sX i) (sX i)).toHom n m y =
            pluriformPullback (sX i) (sX i) τ⁻¹.toHom n m
              (pluriformPullback (sX i) (sX i)
                ((τ' * σ : crepantBirationalAutomorphisms (sX i) (B i)) :
                  FunctionFieldEquiv (sX i) (sX i)).toHom n m y) := fun σ => by
        rw [pluriformPullback_pluriformPullback (sX i) hdim m]
        congr
        change (σ : FunctionFieldEquiv (sX i) (sX i)) = τ⁻¹ * (τ * σ)
        rw [inv_mul_cancel_left]
      rw [key (σφ φ), key (σφ ψ)]
      exact congrArg (pluriformPullback (sX i) (sX i) τ⁻¹.toHom n m) (congrFun h y)
    exact (Finset.sum_congr rfl fun φ _ => (he_apply φ).symm).trans
      (Fintype.sum_bijective e (Finite.injective_iff_bijective.mp he) _ _ fun φ => rfl)
  · rw [Pi.smul_apply, Finset.sum_apply, map_smul, map_sum,
      Finset.sum_congr rfl fun φ _ => hfix i i _ (σφ φ).2 s hs (T φ) (hTW φ) (hTi φ) F e hl hd,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, ← hc_def,
      inv_smul_smul₀ hc]

/-- **Admissible generation in every positive multiple of a common degree.** Under the
hypotheses of `exists_admissibleSections_generatesOn_of_finite`, there is `N > 0` such that for
every `c > 0` the admissible systems in degree `c N m` generate on every component; and every
preadmissible system `s` has, for each `i`, a preadmissible lift `t` of the proper boundary
restrictions of `s_i` whose `i`-th entry is invariant under all crepant birational self-maps of
`(X_i, B_i)`. -/
public theorem exists_admissibleSections_generatesOn_mul_of_finite
    {k : Type u} [Field k] {I : Type*} {X : I → Scheme.{u}} {sX : ∀ i, X i ⟶ Spec (.of k)}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {B : ∀ i, QDivisor (X i)} {n m : ℕ} (R : ResidueRestriction sX B n m)
    (hgen : ∀ (i : I) (x : X i), ∃ s ∈ preadmissibleSections R, ∃ U : (X i).Opens, x ∈ U ∧
      Mori.GeneratesOn (B i) m U ((s i : logPluricanonicalSections (sX i) n m (B i)) :
        Mori.RationalPluriForms (sX i) n m))
    (hstable : ∀ (i j : I) (σ : FunctionFieldEquiv (sX i) (sX j)),
      IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ →
      ∀ s ∈ preadmissibleSections R, ∃ t ∈ preadmissibleSections R,
        ((t i : logPluricanonicalSections (sX i) n m (B i)) : Mori.RationalPluriForms (sX i) n m) =
          pluriformPullback (sX i) (sX j) σ.toHom n m (s j) ∧ ∀ l, l ≠ i → t l = s l)
    (hfix : ∀ (i j : I) (σ : FunctionFieldEquiv (sX i) (sX j)),
      IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ →
      ∀ s ∈ preadmissibleSections R, ∀ t ∈ preadmissibleSections R,
        ((t i : logPluricanonicalSections (sX i) n m (B i)) : Mori.RationalPluriForms (sX i) n m) =
          pluriformPullback (sX i) (sX j) σ.toHom n m (s j) →
        ∀ {S : Scheme.{u}} {ι : S ⟶ X i} {BS : QDivisor S}
          (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ), 0 < F.length →
          topologicalKrullDim S = e → R.toFun i F e (t i) = R.toFun i F e (s i))
    (hfinite : ∀ i : I, (Set.range fun (σ : crepantBirationalAutomorphisms (sX i) (B i))
        (s : (preadmissibleSections R).map (LinearMap.proj i)) =>
        pluriformPullback (sX i) (sX i) (σ : FunctionFieldEquiv (sX i) (sX i)).toHom n m
          ((s : logPluricanonicalSections (sX i) n m (B i)) :
            Mori.RationalPluriForms (sX i) n m)).Finite) :
    (∃ N : ℕ, 0 < N ∧ ∀ c : ℕ, 0 < c → ∀ R' : ResidueRestriction sX B n (c * (N * m)),
      ∀ (i : I) (x : X i), ∃ s ∈ admissibleSections R', ∃ U : (X i).Opens, x ∈ U ∧
        Mori.GeneratesOn (B i) (c * (N * m)) U (s i).1) ∧
    ∀ s ∈ preadmissibleSections R, ∀ i : I, ∃ t ∈ preadmissibleSections R,
      (∀ σ ∈ crepantBirationalAutomorphisms (sX i) (B i),
        pluriformPullback (sX i) (sX i) σ.toHom n m (t i) =
          (t i : Mori.RationalPluriForms (sX i) n m)) ∧
      ∀ {S : Scheme.{u}} {ι : S ⟶ X i} {BS : QDivisor S}
        (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ), 0 < F.length →
        topologicalKrullDim S = e → R.toFun i F e (t i) = R.toFun i F e (s i) :=
  ⟨exists_admissibleSections_generatesOn_mul R hgen hstable hfinite,
    exists_invariant_preadmissible_lift R hstable hfix hfinite⟩

/-- **Finite birational representations turn preadmissible generators into admissible
generators.** In the stratified setting `R` of a finite collection of rational dlt pairs
`(X_i, B_i)` in even degree `m`, suppose the preadmissible systems `preadmissibleSections R`
generate `𝒪_{X_i}(m(K_{X_i} + B_i))` on every component, are stable under replacing the `i`-th
entry by its pull-back `σ^* s_j` along any crepant birational map `σ : (X_i, B_i) ⇢ (X_j, B_j)`,
that such a replacement keeps the residue restrictions on all proper strata of `X_i`, and that
each group `crepantBirationalAutomorphisms` acts on the `i`-th entries through finitely many
maps. Then for some `N > 0` the admissible systems in degree `N m` generate on every component;
and every preadmissible system `s` has, for each `i`, a preadmissible lift `t` of the proper
boundary restrictions of `s_i` whose `i`-th entry is invariant under all crepant birational
self-maps of `(X_i, B_i)`. -/
@[mmp "lem_fourfold_finite_representation_admissible_generation"]
public theorem exists_admissibleSections_generatesOn_of_finite
    {k : Type u} [Field k] {I : Type*} {X : I → Scheme.{u}} {sX : ∀ i, X i ⟶ Spec (.of k)}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {B : ∀ i, QDivisor (X i)} {n m : ℕ} (R : ResidueRestriction sX B n m)
    (hgen : ∀ (i : I) (x : X i), ∃ s ∈ preadmissibleSections R, ∃ U : (X i).Opens, x ∈ U ∧
      Mori.GeneratesOn (B i) m U ((s i : logPluricanonicalSections (sX i) n m (B i)) :
        Mori.RationalPluriForms (sX i) n m))
    (hstable : ∀ (i j : I) (σ : FunctionFieldEquiv (sX i) (sX j)),
      IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ →
      ∀ s ∈ preadmissibleSections R, ∃ t ∈ preadmissibleSections R,
        ((t i : logPluricanonicalSections (sX i) n m (B i)) : Mori.RationalPluriForms (sX i) n m) =
          pluriformPullback (sX i) (sX j) σ.toHom n m (s j) ∧ ∀ l, l ≠ i → t l = s l)
    (hfix : ∀ (i j : I) (σ : FunctionFieldEquiv (sX i) (sX j)),
      IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ →
      ∀ s ∈ preadmissibleSections R, ∀ t ∈ preadmissibleSections R,
        ((t i : logPluricanonicalSections (sX i) n m (B i)) : Mori.RationalPluriForms (sX i) n m) =
          pluriformPullback (sX i) (sX j) σ.toHom n m (s j) →
        ∀ {S : Scheme.{u}} {ι : S ⟶ X i} {BS : QDivisor S}
          (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ), 0 < F.length →
          topologicalKrullDim S = e → R.toFun i F e (t i) = R.toFun i F e (s i))
    (hfinite : ∀ i : I, (Set.range fun (σ : crepantBirationalAutomorphisms (sX i) (B i))
        (s : (preadmissibleSections R).map (LinearMap.proj i)) =>
        pluriformPullback (sX i) (sX i) (σ : FunctionFieldEquiv (sX i) (sX i)).toHom n m
          ((s : logPluricanonicalSections (sX i) n m (B i)) :
            Mori.RationalPluriForms (sX i) n m)).Finite) :
    (∃ N : ℕ, 0 < N ∧ ∀ R' : ResidueRestriction sX B n (N * m), ∀ (i : I) (x : X i),
      ∃ s ∈ admissibleSections R', ∃ U : (X i).Opens, x ∈ U ∧
        Mori.GeneratesOn (B i) (N * m) U (s i).1) ∧
    ∀ s ∈ preadmissibleSections R, ∀ i : I, ∃ t ∈ preadmissibleSections R,
      (∀ σ ∈ crepantBirationalAutomorphisms (sX i) (B i),
        pluriformPullback (sX i) (sX i) σ.toHom n m (t i) =
          (t i : Mori.RationalPluriForms (sX i) n m)) ∧
      ∀ {S : Scheme.{u}} {ι : S ⟶ X i} {BS : QDivisor S}
        (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ), 0 < F.length →
        topologicalKrullDim S = e → R.toFun i F e (t i) = R.toFun i F e (s i) :=
  have h := exists_admissibleSections_generatesOn_mul_of_finite R hgen hstable hfix hfinite
  ⟨h.1.imp fun _ ⟨hN, hg⟩ => ⟨hN, by have h1 := hg 1 one_pos; rwa [one_mul] at h1⟩, h.2⟩

end AdmissibleGeneration

end MMP.Fourfold
