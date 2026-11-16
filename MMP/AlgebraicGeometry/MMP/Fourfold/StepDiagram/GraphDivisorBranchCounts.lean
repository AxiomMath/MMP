module

public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Graph divisors, unramified centres and bad branch counts of fourfold steps

Three facts about the steps `(X⁻, B⁻) → Z ← (X⁺, B⁺)` of a fourfold program.

* **The graph divisor.** For a step diagram with normalized graph `(G, u, v)` and graph divisor
  `H = u^* D⁻ - v^* D⁺`, the divisor `-H` is ample over `Z` for `g = u ≫ f⁻ = v ≫ f⁺`: on
  `X⁻ ×_Z X⁺` the divisor `p₁^*(-D⁻) + p₂^* D⁺` is ample over `Z`, and its pull-back along the
  finite morphism `(u, v) : G ⟶ X⁻ ×_Z X⁺` is `-H`.
* **Unramified centres.** Let `q : Yₑ ⟶ Y₀` be dominant étale, `μ : W ⟶ Y₀` projective and an
  isomorphism over a dense open, `E` a prime divisor of `W`, and `w` a normalized divisorial
  valuation of `k(Yₑ)` restricting to `e · ord_E` on `k(Y₀)`. The centre of `w` lifts, by the
  valuative criterion of properness, to a point `x` of `Wₑ = W ×_{Y₀} Yₑ` over the generic point
  of `E`. As `Wₑ ⟶ W` is étale, a uniformizer of `𝒪_{W,E}` generates the maximal ideal of
  `𝒪_{Wₑ,x}`, which is therefore a discrete valuation ring; hence `w = ord_{E'}` for
  `E' = closure {x}` and `e = 1`.
* **Bad branch counts.** On every model `X` of a terminal chain the normalization of the centre
  `S_h^X` of a label is finite, so each of its prime divisors maps onto an irreducible surface;
  sorting them by that surface writes the bad branch count along `W ⊆ X` as
  `∑_{V ⊆ W, dim V = 2} r_{V,h}`. Across a small flip `Y⁻ ⤏ Y⁺`, the strict transform of
  `S_h⁻` is the prime divisor of `Y⁺` over the codimension-one point `f⁻(η_{S_h⁻})` of `Z`, and
  it is the centre of `S_h` on `Y⁺`, so the identity holds on both sides.

## Main results

* `MMP.Fourfold.IsGraphDivisor.hasRelativelyAmpleMultiple_neg`: `-H` is `g`-ample.
* `MMP.Fourfold.exists_primeDivisor_valuationOver_eq_of_etale`: the centre of `w` on `Wₑ` is a
  prime divisor `E'` over `E`, with `w = ord_{E'}` and `e = 1`.
* `StabilizedSmallKltTail.PreparedChain.FlipMove.badBranchCount_eq_finsum_branchNumber`
  : for a small terminal flip of a prepared chain, the strict transform of `S_h⁻` exists and
  `e^±(S_h⁻) = ∑_{V ⊆ W^±, dim V = 2} r^±_{V,h}`.

## Implementation notes

* Relative ampleness of a `ℚ`-divisor is `MMP.Mori.QDivisor.HasRelativelyAmpleMultiple`: some
  positive multiple is a Cartier divisor ample over the base.
* Valuations are multiplicative, valued in `ℤᵐ⁰`, so `e · ord_E` is `g ↦ (ord_E g) ^ e`. The
  facts that `W` is integral, normal and locally Noetherian and that `μ` is dominant, which
  `ord_E` needs in order to be defined, are instance arguments; that `Wₑ` is integral, normal and
  locally Noetherian and `μₑ` dominant, which `ord_{E'}` needs, is proved and stated as part of
  the conclusion. The source works over `ℂ`; the unramified-centre statement is made over an
  arbitrary field `k`.
* The count `e⁺(S_h⁻)` is the bad branch count, along `W⁺`, of the strict transform
  `MMP.Fourfold.flipTransformPrimeDivisor μ.sourceMap μ.targetMap S_h⁻`, as in
  `MMP.Fourfold.IsFourfoldBadBranchCountPlus`. The sum over the irreducible surfaces `V ⊆ W^±`
  is a `finsum` over `IrreducibleCloseds` restricted to `V ⊆ W^±` and
  `topologicalKrullDim V = 2`. The model reached by the `k`-th flip of the `i`-th bridge is
  `V_{k+1}` or, when `k + 1 = m_i`, the next junction `Y_{i+1}`; in both cases its morphism to
  `T_k` is `g_k⁺` precomposed with an isomorphism.

## References

* OpenAI, *Projective lc fourfolds*, Chapter 2.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

/-! ### The graph divisor -/

section GraphDivisor

open MMP.Mori RingedSpaceModuleAdjunction Stacks.Ample Stacks.RelativeVeryAmple

/-- If `φ = (a, b) : W ⟶ X ×_S Y` is affine, `L` is `f`-ample and `N` is `g`-ample, then
`a^* L ⊗ b^* N` is ample relative to `a ≫ f`. -/
private theorem isRelativelyAmple_tensorModules_of_isAffineHom {S X Y W : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} {a : W ⟶ X} {b : W ⟶ Y} (h : a ≫ f = b ≫ g)
    [IsAffineHom (pullback.lift a b h)] (L : X.Modules) (N : Y.Modules)
    [IsInvertibleModule X L] [IsInvertibleModule Y N]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hN : Stacks.RelativeAmple.IsRelativelyAmple g N) :
    Stacks.RelativeAmple.IsRelativelyAmple (a ≫ f)
      (tensorModules W ((modulePullback a.toLRSHom.toShHom).obj L)
        ((modulePullback b.toLRSHom.toShHom).obj N)) := by
  have h1 := Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom
    (pullback.lift a b h) (pullback.fst f g ≫ f) _
    (Stacks.AmpleExternalTensor.isRelativelyAmple_externalTensor f g L N hL hN)
  have e := Stacks.AmpleExternalTensor.pullbackExternalTensorIso f g (pullback.lift a b h) L N
  simp only [pullback.lift_fst, pullback.lift_snd] at e
  rw [← Category.assoc, pullback.lift_fst] at h1
  exact (isRelativelyAmple_congr _ _ _ e).mp h1

/-- The ringed-space pull-back of a module along a morphism of schemes is the scheme pull-back. -/
private noncomputable def modulePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) :
    (modulePullback f.toLRSHom.toShHom).obj F ≅ (Scheme.Modules.pullback f).obj F :=
  (Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)).app F

/-- For a quasi-compact morphism, `f`-ampleness gives ampleness over every affine open. -/
private theorem stacks_of_isRelativelyAmple {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (L : X.Modules) [IsInvertibleModule X L] (hL : MMP.Mori.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L inferInstance hL

/-- If `(a, b) : W ⟶ X ×_S Y` is affine, `A` is an `f`-ample and `B` a `g`-ample Cartier divisor,
then `a^* A + b^* B` is ample relative to `a ≫ f`. -/
private theorem isRelativelyAmple_add_of_isPullback {S X Y W : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W]
    {f : X ⟶ S} {g : Y ⟶ S} [QuasiCompact f] [QuasiCompact g] {a : W ⟶ X} {b : W ⟶ Y}
    (h : a ≫ f = b ≫ g) [IsAffineHom (pullback.lift a b h)]
    {A : Divisor X} (hA : A.IsCartier) (hAf : A.IsRelativelyAmple f hA)
    {B : Divisor Y} (hB : B.IsCartier) (hBg : B.IsRelativelyAmple g hB)
    {A' B' : Divisor W} {ha : ∀ Z : irreducibleComponents W, a (componentGenericPoint W Z) ∉ A.supp}
    {hb : ∀ Z : irreducibleComponents W, b (componentGenericPoint W Z) ∉ B.supp}
    (hpa : A.IsPullback a ha A') (hpb : B.IsPullback b hb B') :
    (A' + B').IsRelativelyAmple (a ≫ f) ((hpa.isCartier hA).add (hpb.isCartier hB)) := by
  have hA' := hpa.isCartier hA
  have hB' := hpb.isCartier hB
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI := hB.isInvertibleModule_divisorialSheaf
  haveI := hA'.isInvertibleModule_divisorialSheaf
  haveI := hB'.isInvertibleModule_divisorialSheaf
  haveI := (hA'.add hB').isInvertibleModule_divisorialSheaf
  have h1 := isRelativelyAmple_tensorModules_of_isAffineHom h _ _
    (stacks_of_isRelativelyAmple f _ hAf) (stacks_of_isRelativelyAmple g _ hBg)
  have e : tensorModules W ((modulePullback a.toLRSHom.toShHom).obj A.divisorialSheaf)
      ((modulePullback b.toLRSHom.toShHom).obj B.divisorialSheaf) ≅ (A' + B').divisorialSheaf :=
    tensorModulesMapIso W (modulePullbackIso a _ ≪≫ (hpa.divisorialSheafIso (hBc := hA)).symm)
      (modulePullbackIso b _ ≪≫ (hpb.divisorialSheafIso (hBc := hB)).symm) ≪≫
      hA'.divisorialSheafTensorIso hB'
  exact MMP.Mori.IsRelativelyAmple.of_stacks _ _ ((isRelativelyAmple_congr _ _ _ e).mp h1)

/-- For a quasi-compact separated morphism `f`, the sum of two `f`-ample Cartier divisors is
`f`-ample: `O(A + B) ≅ Δ^*(O(A) ⊠ O(B))` and the diagonal of `f` is affine. -/
private theorem isRelativelyAmple_add {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {A B : Divisor X} (hA : A.IsCartier) (hAf : A.IsRelativelyAmple f hA)
    (hB : B.IsCartier) (hBf : B.IsRelativelyAmple f hB) :
    (A + B).IsRelativelyAmple f (hA.add hB) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI := hB.isInvertibleModule_divisorialSheaf
  haveI := (hA.add hB).isInvertibleModule_divisorialSheaf
  haveI : IsAffineHom (pullback.lift (𝟙 X) (𝟙 X) (rfl : 𝟙 X ≫ f = 𝟙 X ≫ f)) :=
    show IsAffineHom (pullback.diagonal f) from inferInstance
  have h := isRelativelyAmple_tensorModules_of_isAffineHom (rfl : 𝟙 X ≫ f = 𝟙 X ≫ f) _ _
    (stacks_of_isRelativelyAmple f _ hAf) (stacks_of_isRelativelyAmple f _ hBf)
  rw [Category.id_comp] at h
  refine MMP.Mori.IsRelativelyAmple.of_stacks _ _ ((isRelativelyAmple_congr _ _ _ ?_).mp h)
  exact tensorModulesMapIso X (modulePullbackIso _ _ ≪≫ (Scheme.Modules.pullbackId X).app _)
    (modulePullbackIso _ _ ≪≫ (Scheme.Modules.pullbackId X).app _) ≪≫
    hA.divisorialSheafTensorIso hB

/-- For a quasi-compact separated morphism `f`, every positive multiple of an `f`-ample Cartier
divisor is `f`-ample. -/
private theorem isRelativelyAmple_zsmul {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {L : Divisor X} (hL : L.IsCartier) (hLf : L.IsRelativelyAmple f hL)
    (n : ℕ) : (((n : ℤ) + 1) • L).IsRelativelyAmple f (hL.zsmul _) := by
  induction n with
  | zero => simpa using hLf
  | succ n ih =>
    convert isRelativelyAmple_add _ ih _ hLf using 2
    push_cast
    rw [add_smul, one_smul]

end GraphDivisor

open MMP.Mori in
/-- For a step diagram with normalized graph `(G, u, v)` and graph divisor `H`, the divisor `-H`
is ample relative to the structure map `g = u ≫ f⁻ : G ⟶ Z`. -/
@[mmp "lem_oai4_c1_graph_minus_h_ample"]
public theorem IsGraphDivisor.hasRelativelyAmpleMultiple_neg
    {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
    [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [CompactSpace G] [IsLocallyNoetherian G] [IsNormal G]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    {H : QDivisor G} (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H) :
    (-H).HasRelativelyAmpleMultiple (u ≫ fm) := by
  obtain ⟨Hm, Hp, hum, hvp, hHm, hHp, rfl⟩ := h.exists_pullback
  have hD := h.isFourfoldStepDiagram
  have hG := h.isNormalizedGraph
  haveI : IsIntegral G := hG.isIntegral
  haveI := isProper_of_isProjectiveMorphism fm hD.isProjectiveMorphism_minus
  haveI := isProper_of_isProjectiveMorphism fp hD.isProjectiveMorphism_plus
  haveI := hG.isFinite
  obtain ⟨m₁, hm₁, L₁, hL₁, hL₁q, hL₁a⟩ := hD.hasRelativelyAmpleMultiple_minus
  obtain ⟨m₂, hm₂, L₂, hL₂, hL₂q, hL₂a⟩ := hD.hasRelativelyAmpleMultiple_plus
  obtain ⟨k₁, rfl⟩ : ∃ k, m₁ = k + 1 := ⟨m₁ - 1, by omega⟩
  obtain ⟨k₂, rfl⟩ : ∃ k, m₂ = k + 1 := ⟨m₂ - 1, by omega⟩
  set N : ℕ := (k₁ + 1) * (k₂ + 1)
  have hNpos : 0 < N := by positivity
  -- the Cartier divisors `-N D⁻` and `N D⁺`, ample over `Z` up to sign
  set A₁ : Divisor Xm := ((k₂ : ℤ) + 1) • L₁
  set A₂ : Divisor Xp := ((k₁ : ℤ) + 1) • L₂
  have hqA₁ : Divisor.toQDivisor A₁ = (-(N : ℤ)) • (Divisor.toQDivisor K + B) := by
    simp only [A₁, map_zsmul, hL₁q, smul_smul, smul_neg, ← neg_smul]
    congr 1
    push_cast [N]
    ring
  have hq₁ : Divisor.toQDivisor ((-1 : ℤ) • A₁) = (N : ℤ) • (Divisor.toQDivisor K + B) := by
    rw [map_zsmul, hqA₁, smul_smul]
    simp
  have hq₂ : Divisor.toQDivisor A₂ = (N : ℤ) •
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B) := by
    simp only [A₂, map_zsmul, hL₂q, smul_smul]
    congr 1
  obtain ⟨A₁', hA₁'q, hpa⟩ := hHm N hNpos _ hq₁ ((hL₁.zsmul _).zsmul _)
  obtain ⟨A₂', hA₂'q, hpb⟩ := hHp N hNpos _ hq₂ (hL₂.zsmul _)
  have ha : ∀ T : irreducibleComponents G, u (componentGenericPoint G T) ∉ A₁.supp := by
    rw [QDivisor.supp_eq_of_toQDivisor_eq (by simpa using hNpos.ne') hqA₁]
    exact hum
  have hpa' : A₁.IsPullback u ha ((-1 : ℤ) • A₁') :=
    (hpa.zsmul ((hL₁.zsmul _).zsmul _) (-1) (by simpa using ha)).of_eq (by simp; rfl)
  have hamp := isRelativelyAmple_add_of_isPullback hG.comp_eq (hL₁.zsmul _)
    (isRelativelyAmple_zsmul hL₁ hL₁a k₂) (hL₂.zsmul _) (isRelativelyAmple_zsmul hL₂ hL₂a k₁)
    hpa' hpb
  refine ⟨N, hNpos, _, _, ?_, hamp⟩
  rw [map_add, map_zsmul, hA₁'q, hA₂'q, smul_smul, smul_neg, smul_sub]
  module

/-! ### Unramified centres under étale base change -/

section EtaleCentre

open MMP.Mori MMP.Intersection IsLocalRing
open scoped WithZero

/-- The base change of `μ` along `q`, restricted over `q⁻¹(U)`, is a pullback of `μ ∣_ U`
along `q ∣_ U`. -/
private lemma isPullback_restrict {Y₀ Yₑ W : Scheme.{u}} (q : Yₑ ⟶ Y₀) (μ : W ⟶ Y₀)
    (U : Y₀.Opens) :
    ∃ v : ((pullback.snd μ q) ⁻¹ᵁ (q ⁻¹ᵁ U)).toScheme ⟶ (μ ⁻¹ᵁ U).toScheme,
      IsPullback (pullback.snd μ q ∣_ (q ⁻¹ᵁ U)) v (q ∣_ U) (μ ∣_ U) := by
  have h3 := isPullback_morphismRestrict μ U
  have hc : (pullback.snd μ q ∣_ (q ⁻¹ᵁ U) ≫ q ∣_ U) ≫ U.ι =
      (((pullback.snd μ q) ⁻¹ᵁ (q ⁻¹ᵁ U)).ι ≫ pullback.fst μ q) ≫ μ := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι,
      Category.assoc, Category.assoc, ← pullback.condition]
  refine ⟨h3.lift _ _ hc,
    IsPullback.of_bot (h₂₁ := μ ∣_ U) (v₂₁ := (μ ⁻¹ᵁ U).ι) (v₂₂ := U.ι) ?_ ?_ h3⟩
  · rw [h3.lift_snd, morphismRestrict_ι]
    exact (isPullback_morphismRestrict (pullback.snd μ q) (q ⁻¹ᵁ U)).paste_vert
      (IsPullback.of_hasPullback μ q).flip
  · exact (h3.lift_fst _ _ hc).symm

/-- If `U` is a dense open of `Y₀` and `q : Yₑ ⟶ Y₀` is an open map with nonempty source, then
`q⁻¹(U)` is nonempty. -/
private lemma nonempty_preimage_of_dense {Y₀ Yₑ : Scheme.{u}} [Nonempty Yₑ] (q : Yₑ ⟶ Y₀)
    (hq : IsOpenMap q) {U : Y₀.Opens} (hU : Dense (U : Set Y₀)) :
    ((q ⁻¹ᵁ U : Yₑ.Opens) : Set Yₑ).Nonempty := by
  obtain ⟨x⟩ : Nonempty Yₑ := inferInstance
  obtain ⟨_, ⟨x', rfl⟩, hx'⟩ := hU.inter_open_nonempty _ hq.isOpen_range ⟨q x, x, rfl⟩
  exact ⟨x', hx'⟩

/-- A dominant morphism of integral schemes which is an isomorphism over a nonempty open induces
an isomorphism of function fields. -/
private lemma functionFieldMap_bijective_of_isIso {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] (U : X.Opens) (hU : (U : Set X).Nonempty)
    [IsIso (f ∣_ U)] : Function.Bijective (functionFieldMap f) := by
  obtain ⟨x, hx⟩ := hU
  have hne : ((f ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty :=
    ⟨_, ((inv (f ∣_ U)) ⟨x, hx⟩).2⟩
  have : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  exact MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion f _ hne

/-- A non-unit of the valuation ring of `v` has valuation `< 1`. -/
private lemma valuation_lt_one_of_mem_nonunits {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (r : v.valuationSubring) (hr : ¬ IsUnit r) : v (r : K) < 1 :=
  lt_of_le_of_ne ((v.mem_valuationSubring_iff _).1 r.2) fun h1 =>
    hr ((Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers v)
      (x := ⟨r, r.2⟩)).2 h1)

/-- **Existence of a centre along a proper birational morphism.** Let `f : X ⟶ Y` be a proper
dominant morphism of integral schemes inducing an isomorphism of function fields, and `w'` a
valuation of `k(X)` whose restriction `w` to `k(Y)` has a centre `y` on `Y`. Then `w'` has a
centre `x` on `X`. -/
private lemma exists_centre_of_isProper {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsProper f] (w : Valuation Y.functionField ℤᵐ⁰)
    (w' : Valuation X.functionField ℤᵐ⁰) (hw' : ∀ g, w' (functionFieldMap f g) = w g) (y : Y)
    (h1 : ∀ a : Y.presheaf.stalk y, w (algebraMap _ Y.functionField a) ≤ 1) :
    ∃ x : X, (∀ a : X.presheaf.stalk x, w' (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ maximalIdeal (X.presheaf.stalk x), w' (algebraMap _ X.functionField a) < 1 := by
  set R := w'.valuationSubring
  let φ : Y.presheaf.stalk y →+* R :=
    ((functionFieldMap f).comp (algebraMap (Y.presheaf.stalk y) Y.functionField)).codRestrict R
      fun a => (w'.mem_valuationSubring_iff _).2 (by simpa [hw'] using h1 a)
  have hy : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
  have hex : ValuativeCriterion.Existence f := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact h.1
  have hc : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap R X.functionField) =
      Y.presheaf.stalkSpecializes hy ≫ CommRingCat.ofHom (functionFieldMap f) := by
    ext a
    rfl
  have hsq : X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫
        (Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk y) := by
    rw [← functionFieldMap_fromSpecStalk, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hy,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hc]
    rfl
  let S : ValuativeCommSq f :=
    { R := R
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk y
      commSq := ⟨hsq⟩ }
  obtain ⟨l', hl₁', -⟩ := (hex S).exists_lift
  let l : Spec (.of R) ⟶ X := l'
  have hl₁ : Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ l =
      X.fromSpecStalk (genericPoint X) := hl₁'
  clear_value l
  clear hl₁'
  set x' := l (IsLocalRing.closedPoint R)
  let ψ := Scheme.stalkClosedPointTo l
  have hψ : ∀ a, algebraMap R X.functionField (ψ.hom a) =
      algebraMap (X.presheaf.stalk x') X.functionField a := by
    intro a
    have hgen : genericPoint X ⤳ x' := genericPoint_specializes _
    have key : Spec.map (ψ ≫ CommRingCat.ofHom (algebraMap R X.functionField)) ≫
        X.fromSpecStalk x' =
        Spec.map (X.presheaf.stalkSpecializes hgen) ≫ X.fromSpecStalk x' := by
      rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      exact (Spec.map_comp_assoc ψ _ _).trans
        (by rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]; exact hl₁)
    exact congrArg (fun g => g.hom a) (Spec.map_injective ((cancel_mono _).1 key))
  refine ⟨x', fun a => ?_, fun a ha => ?_⟩
  · rw [← hψ]
    exact (w'.mem_valuationSubring_iff _).1 (ψ.hom a).2
  · rw [← hψ]
    exact valuation_lt_one_of_mem_nonunits w' _ fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit ψ.hom a hu)

/-- **Unramified extensions of a discrete valuation ring.** Let `A → B` be a local,
formally unramified, essentially finite type homomorphism of local rings, with `A` a discrete
valuation ring and `B` a Noetherian domain. If a uniformizer `ϖ` of `A` does not vanish in `B`,
then `B` is a discrete valuation ring with uniformizer the image of `ϖ`. -/
private lemma isDiscreteValuationRing_of_formallyUnramified {A B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] {ϖ : A} (hϖ : Irreducible ϖ)
    (h0 : algebraMap A B ϖ ≠ 0) :
    IsDiscreteValuationRing B ∧ Irreducible (algebraMap A B ϖ) := by
  have hmax : maximalIdeal B = Ideal.span {algebraMap A B ϖ} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A),
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  have hnf : ¬ IsField B := by
    rwa [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
  have : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hnf).out 5 1).1 (⟨⟨_, hmax⟩⟩ : (maximalIdeal B).IsPrincipal)
  exact ⟨this, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax⟩

/-- If `p : P ⟶ W` is unramified and locally of finite type between integral schemes and `ϖ` is a
uniformizer of the discrete valuation ring `𝒪_{W,p x}`, then `𝒪_{P,x}` is a discrete valuation
ring with uniformizer the image of `ϖ`, and `x` has coheight one. -/
private lemma isDiscreteValuationRing_stalk_of_formallyUnramified {W P : Scheme.{u}}
    [IsIntegral W] [IsIntegral P] [IsLocallyNoetherian P] (p : P ⟶ W) [FormallyUnramified p]
    [LocallyOfFiniteType p] [IsDominant p] (x : P)
    [IsDiscreteValuationRing (W.presheaf.stalk (p x))]
    {ϖ : W.presheaf.stalk (p x)} (hϖ : Irreducible ϖ) :
    IsDiscreteValuationRing (P.presheaf.stalk x) ∧ Irreducible ((p.stalkMap x).hom ϖ) ∧
      Order.coheight x = 1 := by
  let φ := (p.stalkMap x).hom
  letI : Algebra (W.presheaf.stalk (p x)) (P.presheaf.stalk x) := φ.toAlgebra
  have : Algebra.FormallyUnramified (W.presheaf.stalk (p x)) (P.presheaf.stalk x) :=
    AlgebraicGeometry.FormallyUnramified.stalkMap (f := p) x
  have : Algebra.EssFiniteType (W.presheaf.stalk (p x)) (P.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap (f := p) x
  have : IsLocalHom (algebraMap (W.presheaf.stalk (p x)) (P.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom φ)
  have hφϖ : φ ϖ ≠ 0 := by
    intro h0
    have := MMP.Mori.functionFieldMap_algebraMap_stalk p x ϖ
    rw [show (p.stalkMap x).hom ϖ = 0 from h0, map_zero, map_eq_zero_iff _ (RingHom.injective _),
      map_eq_zero_iff _ (IsFractionRing.injective _ _)] at this
    exact hϖ.ne_zero this
  obtain ⟨hBdvr, hirr⟩ : _ ∧ Irreducible (φ ϖ) :=
    isDiscreteValuationRing_of_formallyUnramified hϖ hφϖ
  refine ⟨hBdvr, hirr, ?_⟩
  have h := IsDiscreteValuationRing.ringKrullDim_eq_one (P.presheaf.stalk x)
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- An open morphism with nonempty source into an irreducible scheme is dominant. -/
private lemma isDominant_of_isOpenMap {X Y : Scheme.{u}} [IrreducibleSpace Y] [Nonempty X]
    (f : X ⟶ Y) (hf : IsOpenMap f) : IsDominant f :=
  ⟨(hf.isOpen_range).dense (Set.range_nonempty _)⟩

/-- `ℤᵐ⁰`: `exp (-1) ^ e = exp (-1)` forces `e = 1`. -/
private lemma eq_one_of_exp_pow {e : ℕ} (h : (WithZero.exp (-1 : ℤ)) ^ e = WithZero.exp (-1)) :
    e = 1 := by
  rw [← WithZero.exp_nsmul, WithZero.exp_inj] at h
  simpa using h

/-- The local ring of a normal locally Noetherian integral scheme at the generic point of a
prime divisor `E` is a discrete valuation ring, with a uniformizer of `ord_E`-value `exp (-1)`. -/
private lemma exists_irreducible_divisorialValuation_eq {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : MMP.Mori.PrimeDivisor X) {z : X}
    (hz : z = E.genericPoint) :
    IsDiscreteValuationRing (X.presheaf.stalk z) ∧ ∃ ϖ : X.presheaf.stalk z, Irreducible ϖ ∧
      E.divisorialValuation (algebraMap _ X.functionField ϖ) = WithZero.exp (-1) := by
  subst hz
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  exact ⟨this, ϖ, hϖ, E.divisorialValuation_algebraMap_of_irreducible hϖ⟩

/-- `ord_E` is centred at the generic point of `E`: it is `≤ 1` on `𝒪_{X,E}` and `< 1` on its
maximal ideal. -/
private lemma divisorialValuation_centre {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : MMP.Mori.PrimeDivisor X) {z : X}
    (hz : z = E.genericPoint) :
    (∀ a : X.presheaf.stalk z, E.divisorialValuation (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ maximalIdeal (X.presheaf.stalk z),
        E.divisorialValuation (algebraMap _ X.functionField a) < 1 := by
  subst hz
  exact ⟨fun a => (E.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩,
    fun a ha => (E.divisorialValuation_algebraMap_lt_one_iff a).2 ha⟩

/-- Let `p : P ⟶ W` be formally unramified, locally of finite type and dominant between normal
locally Noetherian integral schemes, `W` separated over `k`, `E` a prime divisor of `W`, and `w'`
a valuation of `k(P)` taking the value `exp (-1)`, centred at `x`, whose restriction to `k(W)` is
`(ord_E)^e` with `e ≥ 1`. Then `w' = ord_{E'}` for a prime divisor `E'` of `P` over `E`, and
`e = 1`. -/
private lemma exists_primeDivisor_eq_of_formallyUnramified {k : Type u} [Field k]
    {W P : Scheme.{u}} (sW : W ⟶ Spec (.of k)) [IsSeparated sW] [IsIntegral W] [IsNormal W]
    [IsLocallyNoetherian W] [IsIntegral P] [IsNormal P] [IsLocallyNoetherian P] (p : P ⟶ W)
    [FormallyUnramified p] [LocallyOfFiniteType p] [IsDominant p] (E : MMP.Mori.PrimeDivisor W)
    {w' : Valuation P.functionField ℤᵐ⁰} {e : ℕ} (he : 1 ≤ e)
    (hwW : ∀ h, w' (functionFieldMap p h) = E.divisorialValuation h ^ e)
    (h3 : ∃ g, w' g = WithZero.exp (-1)) {x : P}
    (hx1 : ∀ a : P.presheaf.stalk x, w' (algebraMap _ P.functionField a) ≤ 1)
    (hx2 : ∀ a ∈ maximalIdeal (P.presheaf.stalk x), w' (algebraMap _ P.functionField a) < 1) :
    ∃ E' : MMP.Mori.PrimeDivisor P, p E'.genericPoint = E.genericPoint ∧
      w' = E'.divisorialValuation ∧ e = 1 := by
  let wW : Valuation W.functionField ℤᵐ⁰ := w'.comap (functionFieldMap p)
  have hwW' : ∀ h, wW h = E.divisorialValuation h ^ e := hwW
  have hstalk : ∀ a : W.presheaf.stalk (p x),
      wW (algebraMap _ W.functionField a) =
        w' (algebraMap _ P.functionField ((p.stalkMap x).hom a)) := fun a => by
    change w' (functionFieldMap p _) = _
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
  -- `p(x) = η_E`, by uniqueness of centres on the separated scheme `W`.
  have hpx : p x = E.genericPoint := by
    refine MMP.Positivity.DivisorOver.eq_of_dominates sW wW (fun a => ?_)
      (fun a ha => ?_) (fun a => ?_) (fun a ha => ?_)
    · rw [hstalk]
      exact hx1 _
    · rw [hstalk]
      exact hx2 _ (map_nonunit (p.stalkMap x).hom a ha)
    · rw [hwW']
      exact pow_le_one₀ zero_le' ((divisorialValuation_centre E rfl).1 a)
    · rw [hwW']
      exact pow_lt_one₀ zero_le' ((divisorialValuation_centre E rfl).2 a ha) (by omega)
  -- A uniformizer of `𝒪_{W,p(x)} = 𝒪_{W,E}`.
  obtain ⟨hAdvr, ϖ, hϖ, hϖv⟩ := exists_irreducible_divisorialValuation_eq E hpx
  -- `p` is unramified, so `ϖ` stays a uniformizer of `𝒪_{P,x}`.
  obtain ⟨hBdvr, hirr, hco⟩ := isDiscreteValuationRing_stalk_of_formallyUnramified p x hϖ
  -- The prime divisor `E'` with generic point `x`.
  set E' : MMP.Mori.PrimeDivisor P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE' : E'.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  obtain ⟨hv1, hv2⟩ := divisorialValuation_centre E' hE'.symm
  obtain ⟨-, ϖ', -, hϖ'⟩ := exists_irreducible_divisorialValuation_eq E' rfl
  refine ⟨E', hE' ▸ hpx, MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing
    (R := P.presheaf.stalk x) hx1 hx2 h3 hv1 hv2 ⟨_, hϖ'⟩, eq_one_of_exp_pow ?_⟩
  have h1 := hstalk ϖ
  rwa [hwW', hϖv, MMP.Positivity.DivisorOver.valuation_algebraMap_of_irreducible w' hx1 hx2 h3
    hirr] at h1

/-- Let `Y₀` be separated over `k`, `q : Yₑ ⟶ Y₀` dominant étale, `μ : W ⟶ Y₀` proper from a normal
integral `W` and an isomorphism over a dense open `U`, `E` a prime divisor of `W`, and `w` a
normalized divisorial valuation of `k(Yₑ)` whose restriction to `k(Y₀)` is `(ord_E)^e` with
`e ≥ 1`. Then there is a prime divisor `E'` of `Wₑ = W ×_{Y₀} Yₑ` whose generic point lies over
that of `E`, with `w = ord_{E'}` and `e = 1`. -/
private theorem exists_primeDivisor_valuationOver_eq_of_etale_of_isProper {k : Type u} [Field k]
    {Y₀ Yₑ W : Scheme.{u}} (s : Y₀ ⟶ Spec (.of k)) [IsSeparated s] [IsIntegral Y₀] [IsIntegral Yₑ]
    (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    [IsIntegral W] [IsNormal W] [IsLocallyNoetherian W] (μ : W ⟶ Y₀) [IsProper μ]
    [IsDominant μ] {U : Y₀.Opens} (hU : Dense (U : Set Y₀)) (hμU : MMP.Mori.IsBiregular μ U)
    [IsIntegral (pullback μ q)] [IsNormal (pullback μ q)] [IsLocallyNoetherian (pullback μ q)]
    [IsDominant (pullback.snd μ q)]
    (E : MMP.Mori.PrimeDivisor W) {w : Valuation Yₑ.functionField (WithZero (Multiplicative ℤ))}
    (hw : IsNormalizedDivisorialValuation k (q ≫ s) w) {e : ℕ} (he : 1 ≤ e)
    (hwE : ∀ g, w (functionFieldMap q g) = E.valuationOver μ g ^ e) :
    ∃ E' : MMP.Mori.PrimeDivisor (pullback μ q),
      pullback.fst μ q E'.genericPoint = E.genericPoint ∧
        w = E'.valuationOver (pullback.snd μ q) ∧ e = 1 := by
  set P := pullback μ q
  set p := pullback.fst μ q
  set m := pullback.snd μ q
  -- Function fields: `μ` and `μₑ` are birational.
  have : IsIso (μ ∣_ U) := hμU
  have hμbij : Function.Bijective (functionFieldMap μ) :=
    functionFieldMap_bijective_of_isIso μ U hU.nonempty
  have : IsIso (m ∣_ (q ⁻¹ᵁ U)) := by
    obtain ⟨v, hv⟩ := isPullback_restrict q μ U
    exact hv.isIso_fst_of_isIso
  have hmbij : Function.Bijective (functionFieldMap m) :=
    functionFieldMap_bijective_of_isIso m _ (nonempty_preimage_of_dense q q.isOpenMap hU)
  have : UniversallyOpen p := UniversallyOpen.of_flat _
  have : IsDominant p := isDominant_of_isOpenMap p p.isOpenMap
  -- The valuation `w` transported to `k(Wₑ)`.
  let eψ := RingEquiv.ofBijective (functionFieldMap m) hmbij
  let w' : Valuation P.functionField ℤᵐ⁰ := w.comap eψ.symm.toRingHom
  have hw' : ∀ g, w' (functionFieldMap m g) = w g := fun g => by
    change w (eψ.symm (eψ g)) = w g
    rw [RingEquiv.symm_apply_apply]
  -- The centre of `w` on `Yₑ`.
  obtain ⟨D, hDp, rfl⟩ := hw
  have hcY := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl
  -- The centre `x` of `w'` on `Wₑ`.
  obtain ⟨x, hx1, hx2⟩ := exists_centre_of_isProper m D.valuation w' hw' _ hcY
  -- The restriction of `w'` to `k(W)` is `ord_E ^ e`.
  have hwW : ∀ h, w' (functionFieldMap p h) = E.divisorialValuation h ^ e := by
    intro h
    obtain ⟨g, rfl⟩ := hμbij.2 h
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr pullback.condition,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, hw', hwE]
    rfl
  have h3 : ∃ g, w' g = WithZero.exp (-1) := by
    obtain ⟨g, hg⟩ := MMP.Positivity.DivisorOver.exists_valuation_eq_exp_neg_one D
    exact ⟨_, (hw' g).trans hg⟩
  obtain ⟨E', hpE', hww, he₁⟩ :=
    exists_primeDivisor_eq_of_formallyUnramified (μ ≫ s) p E he hwW h3 hx1 hx2
  refine ⟨E', hpE', ?_, he₁⟩
  ext g
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, ← hww, hw']

/-- A morphism which is an isomorphism over a dense open `U` of its target is dominant: its
range contains `U`. -/
private lemma isDominant_of_isIso_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : Y.Opens} (hU : Dense (U : Set Y)) [IsIso (f ∣_ U)] : IsDominant f := by
  refine ⟨hU.mono fun y hy => ?_⟩
  obtain ⟨z, hz⟩ := (f ∣_ U).homeomorph.surjective ⟨y, hy⟩
  exact ⟨z.1, by rw [← morphismRestrict_base_coe]; exact congrArg Subtype.val hz⟩

/-- A space with an open map to an irreducible space is irreducible as soon as the preimage
of some open set is irreducible: that preimage is dense. -/
private lemma irreducibleSpace_of_isIrreducible_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [IrreducibleSpace Y] {f : X → Y} (hf : IsOpenMap f) {O : Set Y}
    (hO : IsOpen O) (h : IsIrreducible (f ⁻¹' O)) : IrreducibleSpace X := by
  obtain ⟨x, hx⟩ := h.nonempty
  rw [irreducibleSpace_def]
  simpa [((hO.dense ⟨_, hx⟩).preimage hf).closure_eq] using h.closure

/-- **Étale base change of a birational morphism.** Let `q : Yₑ ⟶ Y₀` be étale with `Yₑ`
integral, and `μ : W ⟶ Y₀` an isomorphism over a dense open `U`, with `W` integral, normal and
locally Noetherian. Then `Wₑ = W ×_{Y₀} Yₑ` is integral, normal and locally Noetherian, and
`μₑ : Wₑ ⟶ Yₑ` is dominant. The projection `Wₑ ⟶ W` is étale, which gives normality (hence
reducedness) and local Noetherianity; `μₑ` is an isomorphism over `q⁻¹(U)`, so `μₑ⁻¹(q⁻¹(U))` is
irreducible, and it is the preimage of `μ⁻¹(U)` under the open projection `Wₑ ⟶ W`, so `Wₑ` is
irreducible. -/
private lemma isIntegral_isNormal_pullback_of_etale {Y₀ Yₑ W : Scheme.{u}} [IsIntegral Yₑ]
    (q : Yₑ ⟶ Y₀) [Etale q] [IsIntegral W] [IsNormal W] [IsLocallyNoetherian W] (μ : W ⟶ Y₀)
    {U : Y₀.Opens} (hU : Dense (U : Set Y₀)) (hμU : IsIso (μ ∣_ U)) :
    IsIntegral (pullback μ q) ∧ IsNormal (pullback μ q) ∧ IsLocallyNoetherian (pullback μ q) ∧
      IsDominant (pullback.snd μ q) := by
  have : Etale (pullback.fst μ q) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback μ q).flip ‹Etale q›
  have : UniversallyOpen q := UniversallyOpen.of_flat q
  have : UniversallyOpen (pullback.fst μ q) := UniversallyOpen.of_flat _
  have hN : IsNormal (pullback μ q) := isNormal_of_etale (pullback.fst μ q)
  -- `μₑ` is an isomorphism over `q⁻¹(U)`.
  have : IsIso (pullback.snd μ q ∣_ (q ⁻¹ᵁ U)) := by
    obtain ⟨v, hv⟩ := isPullback_restrict q μ U
    exact hv.isIso_fst_of_isIso
  set V := (pullback.snd μ q) ⁻¹ᵁ (q ⁻¹ᵁ U)
  obtain ⟨y, hy⟩ := nonempty_preimage_of_dense q q.isOpenMap hU
  have hqU : Dense ((q ⁻¹ᵁ U : Yₑ.Opens) : Set Yₑ) := (q ⁻¹ᵁ U).isOpen.dense ⟨y, hy⟩
  have : Nonempty (q ⁻¹ᵁ U).toScheme := ⟨⟨y, hy⟩⟩
  have : Nonempty V.toScheme := ⟨(inv (pullback.snd μ q ∣_ (q ⁻¹ᵁ U))) ⟨y, hy⟩⟩
  have : IsIntegral V.toScheme :=
    isIntegral_of_isOpenImmersion (pullback.snd μ q ∣_ (q ⁻¹ᵁ U))
  have hVirr : IsIrreducible (V : Set ↥(pullback μ q)) := by
    have := (IrreducibleSpace.isIrreducible_univ V.toScheme).image V.ι V.ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at this
  -- `V` is the preimage of `μ⁻¹(U)` under the open projection to `W`.
  have hVeq : (V : Set ↥(pullback μ q)) = pullback.fst μ q ⁻¹' (μ ⁻¹ᵁ U : Set W) := by
    ext x
    change q (pullback.snd μ q x) ∈ U ↔ μ (pullback.fst μ q x) ∈ U
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have : IrreducibleSpace ↥(pullback μ q) :=
    irreducibleSpace_of_isIrreducible_preimage (pullback.fst μ q).isOpenMap
      (μ ⁻¹ᵁ U).isOpen (hVeq ▸ hVirr)
  exact ⟨isIntegral_of_irreducibleSpace_of_isReduced _, hN, inferInstance,
    isDominant_of_isIso_morphismRestrict _ hqU⟩

end EtaleCentre

/-- **Unramified centres.** Let `q : Y_e ⟶ Y₀` be a dominant étale morphism of normal varieties
over `k`, `μ : W ⟶ Y₀` a projective morphism over `k` from a smooth variety `W` which is an
isomorphism over a dense open `U`, `E` a prime divisor of `W`, and `w` a normalized divisorial
valuation of `k(Y_e)` whose restriction to `k(Y₀)` is `(ord_E) ^ e` with `e ≥ 1`. Then there is a
prime divisor `E'` of `W_e = W ×_{Y₀} Y_e` whose generic point maps to that of `E` under the
projection `p : W_e ⟶ W`, with `w = ord_{E'}` (through `μ_e : W_e ⟶ Y_e`) and `e = 1`. The
conclusion also records that `W_e` is integral, normal and locally Noetherian and that `μ_e` is
dominant, which is what makes prime divisors of `W_e` and `ord_{E'}` meaningful. -/
@[mmp "lem_oai4_c2_etale_unramified_centre"]
public theorem exists_primeDivisor_valuationOver_eq_of_etale {k : Type*} [Field k]
    {Y₀ Yₑ W : Scheme.{_}} {s₀ : Y₀ ⟶ Spec (.of k)} {sₑ : Yₑ ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)}
    [IsVariety k s₀] [IsVariety k sₑ] [IsNormal Y₀] [IsNormal Yₑ]
    (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q] (hq : q ≫ s₀ = sₑ)
    [IsVariety k sW] [Smooth sW] [IsIntegral W] [IsNormal W] [IsLocallyNoetherian W]
    (μ : W ⟶ Y₀) (hμ : μ ≫ s₀ = sW) (hμp : IsProjectiveMorphism μ) [IsDominant μ]
    (U : Y₀.Opens) (hU : Dense (U : Set Y₀)) (hμU : IsIso (μ ∣_ U))
    (E : MMP.Mori.PrimeDivisor W) (w : Valuation Yₑ.functionField (WithZero (Multiplicative ℤ)))
    (hw : MMP.Intersection.IsNormalizedDivisorialValuation k sₑ w) (e : ℕ) (he : 1 ≤ e)
    (hwE : ∀ g, w (functionFieldMap q g) = E.valuationOver μ g ^ e) :
    ∃ (_ : IsIntegral (pullback μ q)) (_ : IsNormal (pullback μ q))
      (_ : IsLocallyNoetherian (pullback μ q)) (_ : IsDominant (pullback.snd μ q))
      (E' : MMP.Mori.PrimeDivisor (pullback μ q)),
      pullback.fst μ q E'.genericPoint = E.genericPoint ∧
        w = E'.valuationOver (pullback.snd μ q) ∧ e = 1 := by
  subst hq
  have : IsProper μ := isProper_of_isProjectiveMorphism μ hμp
  obtain ⟨h1, h2, h3, h4⟩ := isIntegral_isNormal_pullback_of_etale q μ hU hμU
  exact ⟨h1, h2, h3, h4,
    exists_primeDivisor_valuationOver_eq_of_etale_of_isProper s₀ q μ hU hμU E hw he hwE⟩

/-! ### Bad branch counts -/

section BadBranchCount

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP Order

/-- The closure of a point of a scheme has dimension the height of the point. -/
private theorem topologicalKrullDim_closure_singleton_eq_height {X : Scheme.{u}} (x : X) :
    topologicalKrullDim (closure {x} : Set X) = height x := by
  let T : Set X := closure {x}
  have hTc : IsClosed T := isClosed_closure
  haveI : QuasiSober T := hTc.isClosedEmbedding_subtypeVal.quasiSober
  have hpre : (specializationOrder T).toPreorder = (inferInstance : Preorder T) :=
    Preorder.ext fun a b => (Topology.IsInducing.subtypeVal.specializes_iff (x := b) (y := a)).symm
  have hheight : ∀ a : T, height a = height (a : X) := by
    refine height_eq_of_strictMono _ (Subtype.strictMono_coe _) fun a b hb => ?_
    have hbT : b ∈ T := (Scheme.le_iff_specializes.mp hb.le).mem_closed hTc a.2
    exact ⟨⟨b, hbT⟩, hb, rfl⟩
  have hx : x ∈ T := subset_closure rfl
  change krullDim (IrreducibleCloseds T) = _
  rw [@Order.krullDim_eq_of_orderIso _ _ _ (specializationOrder T).toPreorder
    irreducibleSetEquivPoints, hpre,
    krullDim_eq_iSup_height]
  refine le_antisymm (iSup_le fun a => ?_) (le_iSup_of_le ⟨x, hx⟩ ?_)
  · rw [hheight a]
    exact WithBot.coe_le_coe.mpr (height_mono (Scheme.le_iff_specializes.mpr
      (specializes_iff_mem_closure.mpr a.2)))
  · rw [hheight ⟨x, hx⟩]

/-- A finite morphism preserves heights in the specialization order: it maps strict
specializations to strict specializations, and specializations of the image lift, as the
morphism is closed. -/
private theorem height_apply_eq_of_isFinite {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g]
    (x : X) : height (g x) = height x := by
  have hmono : StrictMono g := fun a b hab => by
    have hba : b ⤳ a := Scheme.le_iff_specializes.mp hab.le
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr (hba.map g.continuous)) fun h => ?_
    have heq : g b = g a := ((hba.map g.continuous).antisymm (Scheme.le_iff_specializes.mp h)).eq
    exact hab.ne (MMP.Fourfold.eq_of_specializes_of_isFinite g hba heq).symm
  refine (height_eq_of_strictMono g hmono (fun a b hb => ?_) x).symm
  obtain ⟨a', ha', rfl⟩ := g.isClosedMap.specializingMap (Scheme.le_iff_specializes.mp hb.le)
  refine ⟨a', lt_of_le_not_ge (Scheme.le_iff_specializes.mpr ha') fun h => hb.ne ?_, rfl⟩
  rw [(Specializes.antisymm ha' (Scheme.le_iff_specializes.mp h)).eq]

/-- A finite morphism preserves the dimension of the closure of a point. -/
private theorem topologicalKrullDim_closure_image_singleton_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsFinite g] (x : X) :
    topologicalKrullDim (closure {g x} : Set Y) = topologicalKrullDim (closure {x} : Set X) := by
  rw [topologicalKrullDim_closure_singleton_eq_height,
    topologicalKrullDim_closure_singleton_eq_height, height_apply_eq_of_isFinite]

/-- Counting a preimage fibrewise: when every fibre of `f` is finite, the number of points
over `s` is the finitely supported sum over `s` of the fibre cardinalities (both sides vanish when
the preimage is infinite). -/
private theorem ncard_preimage_eq_finsum_ncard {α β : Type*} (f : α → β) (s : Set β)
    (hfib : ∀ b, (f ⁻¹' {b}).Finite) :
    (f ⁻¹' s).ncard = ∑ᶠ (b) (_ : b ∈ s), (f ⁻¹' {b}).ncard := by
  classical
  have hsupp : s ∩ Function.support (fun b => (f ⁻¹' {b}).ncard) = f '' (f ⁻¹' s) := by
    ext b
    simp only [Set.mem_inter_iff, Function.mem_support, ne_eq, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨hb, hne⟩
      obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero hne
      exact ⟨a, (show f a = b from ha) ▸ hb, ha⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, (Set.ncard_pos (hfib _)).mpr ⟨a, rfl⟩ |>.ne'⟩
  by_cases h : (f ⁻¹' s).Finite
  · rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := h.toFinset.image f)
      (by rw [Finset.coe_image, h.coe_toFinset, ← hsupp, Set.inter_assoc, Set.inter_self]),
      Set.ncard_eq_toFinset_card _ h, Finset.card_eq_sum_card_image f h.toFinset]
    refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    have ha' : f a ∈ s := (Set.Finite.mem_toFinset h).mp ha
    rw [← Set.ncard_coe_finset]
    congr 1
    ext a'
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq,
      Set.mem_singleton_iff]
    exact ⟨fun h' => h'.2, fun h' => ⟨h' ▸ ha', h'⟩⟩
  · rw [Set.Infinite.ncard h, finsum_mem_eq_zero_of_infinite]
    rw [hsupp]
    exact fun hfin => h ((hfin.biUnion fun b _ => hfib b).subset fun a ha =>
      Set.mem_biUnion (Set.mem_image_of_mem f ha) rfl)

/-- Cancelling `1` in `a + 1 = m + 1` in `WithBot ℕ∞`. -/
private theorem withBot_add_one_eq_natCast_succ {a : WithBot ℕ∞} {m : ℕ}
    (h : a + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) : a = m := by
  induction a using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add] at h
    exact absurd h WithBot.bot_ne_coe
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h' : (((⊤ + 1 : ℕ∞)) : WithBot ℕ∞) = ((m + 1 : ℕ) : ℕ∞) := h
      rw [top_add] at h'
      exact absurd (WithBot.coe_injective h').symm (ENat.coe_ne_top _)
    | coe e =>
      have h' : ((e + 1 : ℕ) : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← h]
        norm_cast
      have : e + 1 = m + 1 := by exact_mod_cast h'
      norm_cast
      omega

/-- On an integral scheme locally of finite type over a field, a prime divisor has codimension
one: its dimension plus one is the dimension of the scheme. -/
private theorem topologicalKrullDim_support_add_one {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    (P : MMP.Mori.PrimeDivisor X) :
    topologicalKrullDim (P.support : Set X) + 1 = topologicalKrullDim X := by
  let _ : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sX)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim k
    (MMP.Intersection.Scheme.Subvariety.ofPoint P.genericPoint)
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint, P.coheight_genericPoint] at h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact_mod_cast h

/-- The normalization of a prime divisor of a scheme locally of finite type over a field is
finite. -/
private theorem isFinite_primeDivisorNormalization {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (S : MMP.Mori.PrimeDivisor Y) :
    IsFinite (primeDivisorNormalization S) := by
  have := S.integral
  have : IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) :=
    isFinite_normalization_of_locallyOfFiniteType S.idealSheaf.subscheme
      (S.idealSheaf.subschemeι ≫ sY) _
  infer_instance

/-- The normalization of a prime divisor maps the generic point to the generic point. -/
private theorem primeDivisorNormalization_genericPoint {Y : Scheme.{0}}
    (S : MMP.Mori.PrimeDivisor Y) :
    letI := S.integral
    letI : IsIntegral (primeDivisorNormalizationScheme S) :=
      AlgebraicGeometry.Scheme.isIntegral_normalizationScheme S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
    primeDivisorNormalization S (genericPoint (primeDivisorNormalizationScheme S)) =
      S.genericPoint := by
  letI := S.integral
  letI : IsIntegral (primeDivisorNormalizationScheme S) :=
    AlgebraicGeometry.Scheme.isIntegral_normalizationScheme S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have hz : genericPoint (primeDivisorNormalizationScheme S) ∈
      genericPoints (primeDivisorNormalizationScheme S) := by
    rw [genericPoints_eq_singleton]
    rfl
  have h := Scheme.normalization_mem_genericPoints S.idealSheaf.subscheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) hz
  rw [genericPoints_eq_singleton] at h
  change S.idealSheaf.subschemeι _ = S.idealSheaf.subschemeι _
  congr 1

/-- The image `ν(P)` of every prime divisor `P` of the normalization `S^ν` of a prime divisor `S`
of an integral scheme `Y` of finite type over a field, of dimension `n + 2`, has dimension `n`. -/
private theorem topologicalKrullDim_closure_primeDivisorNormalization_genericPoint {k : Type}
    [Field k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (n : ℕ) (hY : topologicalKrullDim Y = (n + 2 : ℕ)) (S : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S)) :
    topologicalKrullDim (closure {primeDivisorNormalization S P.genericPoint} : Set Y) = n := by
  have := S.integral
  have := isFinite_primeDivisorNormalization sY S
  haveI : IsIntegral (primeDivisorNormalizationScheme S) :=
    AlgebraicGeometry.Scheme.isIntegral_normalizationScheme S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have hN : topologicalKrullDim (primeDivisorNormalizationScheme S) = (n + 1 : ℕ) := by
    have hS := topologicalKrullDim_support_add_one sY S
    rw [hY] at hS
    have hgen : closure {genericPoint (primeDivisorNormalizationScheme S)} = Set.univ :=
      (genericPoint_spec (primeDivisorNormalizationScheme S)).def
    rw [← (Homeomorph.Set.univ
        (primeDivisorNormalizationScheme S)).isHomeomorph.topologicalKrullDim_eq,
      ← hgen, ← topologicalKrullDim_closure_image_singleton_eq (primeDivisorNormalization S),
      primeDivisorNormalization_genericPoint, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact withBot_add_one_eq_natCast_succ hS
  have hP := topologicalKrullDim_support_add_one (primeDivisorNormalization S ≫ sY) P
  rw [hN, AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hP
  rw [topologicalKrullDim_closure_image_singleton_eq]
  exact withBot_add_one_eq_natCast_succ hP

/-- Only finitely many prime divisors of the normalization `S^ν` have a given image. -/
private theorem finite_primeDivisorNormalization_image_eq {k : Type}
    [Field k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) :
    {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
      closure {primeDivisorNormalization S P.genericPoint} = (V : Set Y)}.Finite := by
  have := isFinite_primeDivisorNormalization sY S
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober V.isIrreducible V.isClosed
  refine (Set.Finite.preimage AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
    ((primeDivisorNormalization S).finite_preimage_singleton ξ)).subset fun P hP => ?_
  exact (show IsGenericPoint _ (V : Set Y) from hP).eq hξ

/-- **Bad branch counts as sums of branch numbers.** For a prime divisor `S` of an integral
scheme `Y` of finite type over a field, of dimension `n + 2`, and a subset `W ⊆ Y`, the number of
prime divisors `P` of the normalization `ν : S^ν ⟶ S ⊆ Y` with `ν(P) ⊆ W` is the sum, over the
irreducible closed subsets `V ⊆ W` of dimension `n`, of the branch numbers of `S` along `V`. -/
private theorem badBranchCount_eq_finsum_branchNumber_of_dim {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (n : ℕ)
    (hY : topologicalKrullDim Y = (n + 2 : ℕ)) (S : MMP.Mori.PrimeDivisor Y) (W : Set Y) :
    badBranchCount S W = ∑ᶠ (V : IrreducibleCloseds Y)
      (_ : (V : Set Y) ⊆ W ∧ topologicalKrullDim (V : Set Y) = (n : ℕ)), branchNumber S V := by
  have := S.integral
  have := isFinite_primeDivisorNormalization sY S
  let ν := primeDivisorNormalization S
  let img : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) → IrreducibleCloseds Y :=
    fun P => ⟨closure {ν P.genericPoint}, isIrreducible_singleton.closure, isClosed_closure⟩
  have himg : ∀ P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S),
      ν '' P.support = (img P : Set Y) := fun P => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← ν.isClosedMap.closure_image_eq_of_continuous ν.continuous, Set.image_singleton]
    rfl
  have hfib : ∀ V, (img ⁻¹' {V}).Finite := fun V =>
    finite_primeDivisorNormalization_image_eq sY S V |>.subset fun P hP => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hP
      simp only [Set.mem_setOf_eq, ← hP]
      rfl
  have hbad : {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
      primeDivisorNormalization S '' P.support ⊆ W} =
      img ⁻¹' {V | (V : Set Y) ⊆ W ∧ topologicalKrullDim (V : Set Y) = (n : ℕ)} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [himg P]
    exact ⟨fun h => ⟨h, topologicalKrullDim_closure_primeDivisorNormalization_genericPoint sY n
      hY S P⟩, fun h => h.1⟩
  have hbranch : ∀ V : IrreducibleCloseds Y, branchNumber S V = (img ⁻¹' {V}).ncard := by
    intro V
    rw [branchNumber]
    congr 1
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [himg P]
    exact SetLike.coe_injective.eq_iff
  rw [badBranchCount, hbad, ncard_preimage_eq_finsum_ncard img _ hfib]
  simp only [Set.mem_setOf_eq, hbranch]

open StabilizedSmallKltTail in
/-- Every model of a terminal chain is of finite type over `ℂ` and of dimension four. -/
private theorem locallyOfFiniteType_and_topologicalKrullDim_model {T : StabilizedSmallKltTail}
    (C : T.TerminalChain) (x : C.ModelIndex) :
    LocallyOfFiniteType (C.modelStructure x) ∧ topologicalKrullDim (C.model x) = 4 := by
  rcases x with ⟨i, _ | ⟨_ | k, hk⟩⟩
  · exact ⟨(C.junction i).isProjectiveVariety.toLocallyOfFiniteType, (C.junction i).dim_eq⟩
  · exact ⟨(C.bridge i).P.isProjectiveVariety.toLocallyOfFiniteType, (C.bridge i).P.dim_eq⟩
  · have h := (C.bridge i).P.isFourfoldStepDiagram k (by omega)
    exact ⟨h.isProjectiveVariety_plus.toLocallyOfFiniteType, h.dim_plus⟩

/-- Valuations agreeing after composition with a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {K L Γ : Type*} [CommRing K] [CommRing L]
    [LinearOrderedCommMonoidWithZero Γ] {φ : K →+* L} (hφ : Function.Surjective φ)
    {v w : Valuation L Γ} (h : v.comap φ = w.comap φ) : v = w :=
  Valuation.ext fun x => by
    obtain ⟨y, rfl⟩ := hφ x
    exact congrArg (fun u : Valuation K Γ => u y) h

/-- The valuation of `k(X_i)` corresponding to a valuation of `k(X_0)` is unique. -/
private theorem corresponds_unique (S : StepSequence) {i : ℕ}
    {ξ : Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ))}
    {η η' : Valuation (S.X i).functionField (WithZero (Multiplicative ℤ))}
    (h : S.Corresponds i ξ η) (h' : S.Corresponds i ξ η') : η = η' := by
  induction i with
  | zero => exact h.trans h'.symm
  | succ i ih =>
    obtain ⟨ζ, hζ, hη⟩ := h
    obtain ⟨ζ', hζ', hη'⟩ := h'
    cases ih hζ hζ'
    have hb := (S.isFourfoldStepDiagram i).isBirationalMorphism_plus
    haveI := hb.isDominant
    exact valuation_eq_of_comap_eq hb.functionFieldMap_bijective.2 (hη.trans hη'.symm)

/-- A prime divisor of a normal variety is determined by its valuation of `k(B)`, for a dominant
morphism `f : Y ⟶ B` inducing a surjection of function fields. -/
private theorem primeDivisor_eq_of_valuationOver_eq {Y B : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral B] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsNormalVariety ℂ sY) (f : Y ⟶ B) [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) {P P' : MMP.Mori.PrimeDivisor Y}
    (h : P.valuationOver f = P'.valuationOver f) : P = P' := by
  have hY' : MMP.Mori.IsNormalVariety ℂ (𝟙 Y ≫ sY) := by rwa [Category.id_comp]
  let D : MMP.Mori.DivisorOver ℂ sY :=
    ⟨Y, 𝟙 Y, hY', MMP.Mori.isBirationalMorphism_of_isIso (𝟙 Y), P⟩
  let D' : MMP.Mori.DivisorOver ℂ sY :=
    ⟨Y, 𝟙 Y, hY', MMP.Mori.isBirationalMorphism_of_isIso (𝟙 Y), P'⟩
  have hD : D.valuation = D'.valuation := by
    change P.divisorialValuation.comap _ = P'.divisorialValuation.comap _
    rw [valuation_eq_of_comap_eq hf h]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hD)

/-- If `π : V ⟶ Z` is dominant and induces a surjection of function fields, so does every
morphism `π_k : V_k ⟶ Z`, `k ≤ m`, of a finite relative program over `Z` from `V`. -/
private theorem surjective_functionFieldMap_toBase_of_le {V Z : Scheme.{0}} [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] {sV : V ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {π : V ⟶ Z} [IsIntegral Z] {K : MMP.Mori.Divisor V}
    {Θ : MMP.Mori.QDivisor V}
    (P : RelativeFourfoldProgram sV sZ π K Θ) [IsDominant π]
    (hπ : Function.Surjective (functionFieldMap π)) :
    ∀ n ≤ P.m, ∃ _ : IsDominant (P.toBase n), Function.Surjective (functionFieldMap (P.toBase n))
  | 0, _ => ⟨‹_›, hπ⟩
  | n + 1, hn => by
    obtain ⟨hd, hs⟩ := surjective_functionFieldMap_toBase_of_le P hπ n (by omega)
    have hD := P.isFourfoldStepDiagram n (by omega)
    haveI := hD.isNormalVariety_target.1.toIsIntegral
    haveI := hD.isBirationalMorphism_minus.isDominant
    haveI := hD.isBirationalMorphism_plus.isDominant
    have heq := P.modelMap_eq n (by omega)
    have hpeq := P.πY_eq n (by omega)
    haveI : IsDominant (P.h n) := by
      have : IsDominant (P.g n ≫ P.h n) := heq ▸ hd
      exact IsDominant.of_comp (P.g n) (P.h n)
    have hcomp : IsDominant (P.gp n ≫ P.h n) := inferInstance
    change ∃ _ : IsDominant (P.πY n), Function.Surjective (functionFieldMap (P.πY n))
    have hd' : IsDominant (P.πY n) := hpeq ▸ hcomp
    refine ⟨hd', ?_⟩
    have hh : Function.Surjective (functionFieldMap (P.h n)) := by
      refine Function.Surjective.of_comp_left ?_
        hD.isBirationalMorphism_minus.functionFieldMap_bijective.1
      have : (functionFieldMap (P.g n)) ∘ (functionFieldMap (P.h n)) =
          functionFieldMap (P.toBase n) := by
        funext t
        rw [Function.comp_apply, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
        exact congrArg (fun φ => φ t)
          (MMP.Positivity.DivisorOver.functionFieldMap_congr heq.symm)
      rw [this]
      exact hs
    have : functionFieldMap (P.πY n) =
        (functionFieldMap (P.gp n)).comp (functionFieldMap (P.h n)) := by
      ext t
      rw [RingHom.comp_apply, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
      exact congrArg (fun φ => φ t) (MMP.Positivity.DivisorOver.functionFieldMap_congr hpeq)
    rw [this, RingHom.coe_comp]
    exact hD.isBirationalMorphism_plus.functionFieldMap_bijective.2.comp hh

open StabilizedSmallKltTail in
/-- On the model `V_k` of a bridge, the morphism `π_k : V_k ⟶ Z_i` induces a surjection of
function fields. -/
private theorem surjective_functionFieldMap_toBase {T : StabilizedSmallKltTail}
    (C : T.TerminalChain) (i : ℕ) (k : Fin (C.bridge i).P.m)
    [IsIntegral (T.Z i)] [IsDominant ((C.bridge i).P.toBase k)] :
    Function.Surjective (functionFieldMap ((C.bridge i).P.toBase k)) := by
  have hpb := (C.junction i).isBirationalMorphism
  have hfb := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus
  haveI := hpb.isDominant
  haveI := hfb.isDominant
  have hπ : Function.Surjective (functionFieldMap ((C.junction i).p ≫ T.f i)) := by
    have : functionFieldMap ((C.junction i).p ≫ T.f i) =
        (functionFieldMap (C.junction i).p).comp (functionFieldMap (T.f i)) := by
      ext t
      rw [RingHom.comp_apply, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    rw [this, RingHom.coe_comp]
    exact hpb.functionFieldMap_bijective.2.comp hfb.functionFieldMap_bijective.2
  exact (surjective_functionFieldMap_toBase_of_le (C.bridge i).P hπ k k.2.le).2

open StabilizedSmallKltTail in
/-- The centre of a label on a model of a terminal chain is unique. -/
private theorem isLabelCentre_unique {T : StabilizedSmallKltTail} (C : T.TerminalChain)
    {S : C.Label} {x : C.ModelIndex} {P P' : MMP.Mori.PrimeDivisor (C.model x)}
    (h : C.IsLabelCentre S x P) (h' : C.IsLabelCentre S x P') : P = P' := by
  rcases x with ⟨i, _ | k⟩
  · obtain ⟨w, hw, hPw⟩ := h
    obtain ⟨w', hw', hPw'⟩ := h'
    cases corresponds_unique T.toStepSequence hw hw'
    have hb := (C.junction i).isBirationalMorphism
    haveI := hb.isDominant
    exact primeDivisor_eq_of_valuationOver_eq (C.junction i).isQFactorial.1 (C.junction i).p
      hb.functionFieldMap_bijective.2 (hPw.trans hPw'.symm)
  · obtain ⟨w, hw, hdom, hPw⟩ := h
    obtain ⟨w', hw', _hdom', hPw'⟩ := h'
    cases corresponds_unique T.toStepSequence hw hw'
    haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    exact primeDivisor_eq_of_valuationOver_eq
      ((C.bridge i).P.isQFactorial k (by omega)).1 ((C.bridge i).P.toBase k)
      (surjective_functionFieldMap_toBase C i k) (hPw.trans hPw'.symm)

open StabilizedSmallKltTail in
/-- On every model `X` of a terminal chain, the bad branch count of the centre `P` of a label
along `W ⊆ X` is the sum, over the irreducible surfaces `V ⊆ W`, of the label's branch numbers
along `V`. -/
private theorem badBranchCount_eq_finsum_labelBranchNumber {T : StabilizedSmallKltTail}
    (C : T.TerminalChain) {S : C.Label} (x : C.ModelIndex) {P : MMP.Mori.PrimeDivisor (C.model x)}
    (hP : C.IsLabelCentre S x P) {r : IrreducibleCloseds (C.model x) → ℕ}
    (hr : ∀ V, C.IsLabelBranchNumber S x V (r V)) (W : Set (C.model x)) :
    badBranchCount P W = ∑ᶠ (V : IrreducibleCloseds (C.model x))
      (_ : (V : Set (C.model x)) ⊆ W ∧ topologicalKrullDim (V : Set (C.model x)) = 2), r V := by
  obtain ⟨hlft, hdim⟩ := locallyOfFiniteType_and_topologicalKrullDim_model C x
  have hr' : ∀ V, r V = branchNumber P V := fun V => by
    rcases hr V with ⟨P', hP', h⟩ | ⟨hno, -⟩
    · rw [h, isLabelCentre_unique C hP' hP]
    · exact absurd hP (hno P)
  simp only [hr']
  simpa only [Nat.cast_ofNat] using
    badBranchCount_eq_finsum_branchNumber_of_dim (C.modelStructure x) 2 (by rw [hdim]; rfl) P W

/-! ### The strict transform across a flip -/

section StrictTransform

variable {X Y : Scheme.{u}}

/-- A point outside the exceptional set of `f` has the same coheight as its image. -/
private theorem coheight_map_of_notMem_exceptionalSet {f : X ⟶ Y} {x : X}
    (hx : x ∉ (MMP.Mori.exceptionalSet f : Set X)) : Order.coheight (f x) = Order.coheight x := by
  set V := MMP.Mori.biregularLocus f
  have : IsIso (f ∣_ V) := MMP.Mori.isBiregular_biregularLocus f
  let q : (f ⁻¹ᵁ V).toScheme := ⟨x, not_not.mp hx⟩
  have h1 : Order.coheight (((f ∣_ V) ≫ V.ι) q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ ((f ∣_ V) ≫ V.ι).isOpenEmbedding
  have h2 : Order.coheight ((f ⁻¹ᵁ V).ι q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ (f ⁻¹ᵁ V).ι.isOpenEmbedding
  have h3 : ((f ∣_ V) ≫ V.ι) q = f x := by rw [morphismRestrict_ι]; rfl
  rw [← h3, h1, ← h2]
  rfl

/-- If the exceptional set of `f` has codimension at least two, it misses the generic point of
every prime divisor. -/
private theorem genericPoint_notMem_exceptionalSet {f : X ⟶ Y}
    (h2 : 2 ≤ MMP.Mori.closedsCodimension (MMP.Mori.exceptionalSet f))
    (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∉ (MMP.Mori.exceptionalSet f : Set X) := fun h => by
  have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 h
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- A morphism whose exceptional set has codimension at least two is biregular over the image
of the generic point of every prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus {f : X ⟶ Y}
    (h2 : 2 ≤ MMP.Mori.closedsCodimension (MMP.Mori.exceptionalSet f))
    (P : MMP.Mori.PrimeDivisor X) : f P.genericPoint ∈ MMP.Mori.biregularLocus f :=
  not_not.mp (genericPoint_notMem_exceptionalSet h2 P)

/-- Precomposing with an isomorphism does not shrink the biregular locus. -/
private theorem biregularLocus_le_biregularLocus_comp {A : Scheme.{u}} (φ : A ⟶ X) [IsIso φ]
    (f : X ⟶ Y) : MMP.Mori.biregularLocus f ≤ MMP.Mori.biregularLocus (φ ≫ f) :=
  sSup_le fun V hV => MMP.Mori.le_biregularLocus (by
    have : IsIso (f ∣_ V) := hV
    change IsIso ((φ ≫ f) ∣_ V)
    rw [morphismRestrict_comp]
    have h2 : IsIso (φ ∣_ (f ⁻¹ᵁ V)) := by infer_instance
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 this)

/-- The valuation of a prime divisor seen through a composite. -/
private theorem valuationOver_comp {Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsIntegral Z] (P : MMP.Mori.PrimeDivisor X) (a : X ⟶ Y)
    (b : Y ⟶ Z) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    P.valuationOver (a ≫ b) = (P.valuationOver a).comap (functionFieldMap b) :=
  Valuation.ext fun t => by
    simp only [Valuation.comap_apply, MMP.Mori.PrimeDivisor.valuationOver_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The valuation of a prime divisor through equal dominant morphisms. -/
private theorem valuationOver_congr [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] (P : MMP.Mori.PrimeDivisor X) {a b : X ⟶ Y} [IsDominant a] [IsDominant b]
    (h : a = b) : P.valuationOver a = P.valuationOver b := by
  subst h
  rfl

/-- If `f(η_E) = η_Q` and `f^♯ : 𝒪_{Y,Q} ⟶ 𝒪_{X,E}` is an isomorphism, then `v_E`, seen on
`k(Y)` through `f`, is `v_Q`. -/
private theorem valuationOver_eq_of_isIso [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (E : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (heq : f E.genericPoint = Q.genericPoint) [IsIso (f.stalkMap E.genericPoint)] :
    E.valuationOver f = Q.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E Q heq t]

/-- A proper birational morphism onto a normal scheme is an isomorphism of local rings over the
generic point of each prime divisor `Q` of the target. -/
private theorem exists_primeDivisor_isIso_stalkMap [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsProper f]
    (hf : MMP.Mori.IsBirationalMorphism f) (Q : MMP.Mori.PrimeDivisor Y) :
    ∃ E : MMP.Mori.PrimeDivisor X,
      f E.genericPoint = Q.genericPoint ∧ IsIso (f.stalkMap E.genericPoint) := by
  have := Q.isDiscreteValuationRing_localRing
  haveI := hf.isDominant
  obtain ⟨x, hx, hiso⟩ :=
    MMP.Intersection.exists_isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
      Q.genericPoint
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Q.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  exact ⟨E, hE ▸ hx, hE ▸ hiso⟩

/-- Every prime divisor of the target of an isomorphism is the image of a prime divisor of its
source. -/
theorem exists_primeDivisor_map_genericPoint_eq_of_isIso (φ : X ⟶ Y) [IsIso φ]
    (P : MMP.Mori.PrimeDivisor Y) :
    ∃ S : MMP.Mori.PrimeDivisor X, φ S.genericPoint = P.genericPoint := by
  have hφ : φ (inv φ P.genericPoint) = P.genericPoint := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hy : Order.coheight (inv φ P.genericPoint) = 1 := by
    rw [← Topology.IsOpenEmbedding.coheight_eq _ φ.isOpenEmbedding, hφ, P.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hy,
    (congrArg φ (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hy)).trans hφ⟩

end StrictTransform

/-- **The strict transform across a step diagram.** Let `X⁻ → Z ← X⁺` be a step diagram whose
morphism `f⁻` is small, and let `f : A ⟶ Z` be `f⁺` precomposed with an isomorphism
`φ : A ⟶ X⁺`. Every prime divisor `S` of `X⁻` has a strict transform `S⁺ = f⁻¹_* f⁻_* S` on `A`,
and `ord_{S⁺} = ord_S` as valuations of `k(Z)`. -/
private theorem exists_flipTransformPrimeDivisor_eq_some {Xm Xp Z A : Scheme.{0}}
    [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp]
    [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral A]
    [IsLocallyNoetherian A] [IsNormal A] {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : MMP.Mori.Divisor Xm} {B : MMP.Mori.QDivisor Xm}
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} (hD : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (hsm : IsSmallMorphism sXm sZ fm) (f : A ⟶ Z) (φ : A ⟶ Xp) [IsIso φ] (hf : f = φ ≫ fp)
    (S : MMP.Mori.PrimeDivisor Xm) :
    haveI := hD.isNormalVariety_target.1.toIsIntegral
    haveI := hD.isBirationalMorphism_minus.isDominant
    ∃ (S' : MMP.Mori.PrimeDivisor A) (_ : IsDominant f),
      flipTransformPrimeDivisor fm f S = some S' ∧ S'.valuationOver f = S.valuationOver fm := by
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated (Z ↘ Limits.terminal Scheme) := by
    have := hZ.1
    rw [show (Z ↘ Limits.terminal Scheme) = sZ ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hbm := hD.isBirationalMorphism_minus
  have hbp := hD.isBirationalMorphism_plus
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  haveI : IsProper fp := hD.isProper_plus
  subst hf
  -- `ζ = f⁻(η_S)` has codimension one, and is the generic point of a prime divisor `Q` of `Z`
  have hζ : Order.coheight (fm S.genericPoint) = 1 := by
    rw [coheight_map_of_notMem_exceptionalSet
      (genericPoint_notMem_exceptionalSet hsm.two_le_codimension S),
      S.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hζ
  have hQ : fm S.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hζ).symm
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Z.presheaf.stalk (fm S.genericPoint)) := by rw [hQ]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing fm hbm.functionFieldMap_bijective
    S.genericPoint
  -- the prime divisor of `X⁺` over `Q`, carried to `A`
  obtain ⟨P, hPQ, hPiso⟩ := exists_primeDivisor_isIso_stalkMap fp hbp Q
  obtain ⟨S', hS'⟩ := exists_primeDivisor_map_genericPoint_eq_of_isIso φ P
  have hS'Q : (φ ≫ fp) S'.genericPoint = Q.genericPoint := by
    rw [Scheme.Hom.comp_apply, hS', hPQ]
  have hfpiso : IsIso (fp.stalkMap (φ S'.genericPoint)) := by
    rw [hS']
    exact hPiso
  haveI : IsIso ((φ ≫ fp).stalkMap S'.genericPoint) := by
    rw [Scheme.Hom.stalkMap_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hfpiso inferInstance
  refine ⟨S', inferInstance, ?_, ?_⟩
  · unfold flipTransformPrimeDivisor
    rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm S Q).mpr hQ,
      Option.bind_some]
    refine MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      hS'Q ?_
    rw [hS'Q, ← hPQ]
    exact biregularLocus_le_biregularLocus_comp φ fp
      (map_genericPoint_mem_biregularLocus hD.isSmallMorphism_plus.two_le_codimension P)
  · rw [valuationOver_eq_of_isIso _ S' Q hS'Q, valuationOver_eq_of_isIso _ S Q hQ]

/-- Along an equality `a = b` of indices, the identification `V_a = V_b` of models of a relative
program is compatible with the morphisms `π_a`, `π_b` to the base. -/
private theorem eqToHom_comp_toBase {V Z : Scheme.{0}} [IsIntegral V] [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {π : V ⟶ Z} {K : MMP.Mori.Divisor V} {Θ : MMP.Mori.QDivisor V}
    (P : RelativeFourfoldProgram sV sZ π K Θ) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (modelSeq V P.Y) h) ≫ P.toBase b = P.toBase a := by
  subst h
  simp

/-- For the last flip of the `i`-th bridge of a terminal chain, the junction map to the next
model followed by `f⁺_i` agrees with the flip target map followed by `h_k`. -/
private theorem junction_comp_fp_eq_flipTargetMapOf {T : StabilizedSmallKltTail}
    (C : T.TerminalChain) (i : ℕ) (k : Fin (C.bridge i).P.m)
    (h : ¬k.1 + 1 < (C.bridge i).P.m) :
    ((C.junction (i + 1)).p ≫ T.fp i : C.model (C.flipTargetOf i k (isFalse h)) ⟶ _) =
      C.flipTargetMapOf i k (isFalse h) ≫ (C.bridge i).P.h k := by
  have hmk : (C.bridge i).P.m = k.1 + 1 := by omega
  change _ = ((C.bridge i).e.inv ≫ eqToHom _ ≫ (C.bridge i).P.gp k) ≫ (C.bridge i).P.h k
  rw [Category.assoc, Category.assoc, ← (C.bridge i).P.πY_eq k k.2]
  change _ = (C.bridge i).e.inv ≫ eqToHom _ ≫ (C.bridge i).P.toBase (k.1 + 1)
  rw [eqToHom_comp_toBase, (C.bridge i).toBase_end_eq, Iso.inv_hom_id_assoc]
  exacts [rfl, hmk]

open StabilizedSmallKltTail in
/-- **Labels across a flip of a bridge.** For the `k`-th flip `V_k → T_k ← V_{k+1}` of the `i`-th
bridge of a terminal chain and the centre `S⁻` of a label on `V_k`, the strict transform of `S⁻`
on the model reached by the flip is a prime divisor, and it is the centre of the label there. -/
private theorem exists_flipTransformPrimeDivisor_isLabelCentre {T : StabilizedSmallKltTail}
    (C : T.TerminalChain) (i : ℕ) (k : Fin (C.bridge i).P.m) {S : C.Label}
    {Sm : MMP.Mori.PrimeDivisor (C.model ⟨i, some k⟩)} (hm : C.IsLabelCentre S ⟨i, some k⟩ Sm) :
    ∃ Sp : MMP.Mori.PrimeDivisor (C.model (C.flipTarget i k)),
      flipTransformPrimeDivisor ((C.bridge i).P.g k) (C.flipTargetMap i k) Sm = some Sp ∧
        C.IsLabelCentre S (C.flipTarget i k) Sp := by
  have hD := (C.bridge i).P.isFourfoldStepDiagram k k.2
  have hsm := (C.bridge i).isSmallMorphism k k.2
  haveI := hD.isNormalVariety_target.1.toIsIntegral
  haveI := hD.isBirationalMorphism_minus.isDominant
  haveI := hD.isBirationalMorphism_plus.isDominant
  obtain ⟨w, hw, hdom, hSm⟩ := hm
  have heq := (C.bridge i).P.modelMap_eq k k.2
  have hpeq := (C.bridge i).P.πY_eq k k.2
  haveI : IsDominant ((C.bridge i).P.h k) :=
    have : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) := heq ▸ hdom
    IsDominant.of_comp ((C.bridge i).P.g k) _
  have key : ∀ {A : Scheme.{0}} [IsIntegral A] [IsLocallyNoetherian A] [IsNormal A]
      (f : A ⟶ (C.bridge i).P.T k) (φ : A ⟶ (C.bridge i).P.Y k) [IsIso φ]
      (_ : f = φ ≫ (C.bridge i).P.gp k),
      ∃ (Sp : MMP.Mori.PrimeDivisor A) (_ : IsDominant f),
        flipTransformPrimeDivisor ((C.bridge i).P.g k) f Sm = some Sp ∧
          Sp.valuationOver (f ≫ (C.bridge i).P.h k) = w.comap (functionFieldMap (T.f i)) := by
    intro A _ _ _ f φ _ hf
    obtain ⟨Sp, hd, hfl, hv⟩ := exists_flipTransformPrimeDivisor_eq_some hD hsm f φ hf Sm
    refine ⟨Sp, hd, hfl, ?_⟩
    rw [valuationOver_comp, hv]
    exact (valuationOver_comp (X := (C.bridge i).P.model k) Sm _ _).symm.trans
      ((valuationOver_congr (X := (C.bridge i).P.model k) Sm heq.symm).trans hSm)
  unfold TerminalChain.flipTarget TerminalChain.flipTargetMap
  generalize (inferInstance : Decidable (k.1 + 1 < (C.bridge i).P.m)) = d
  cases d with
  | isTrue h =>
    obtain ⟨Sp, hd, hfl, hv⟩ := key ((C.bridge i).P.gp k) (𝟙 _) (Category.id_comp _).symm
    have hd1 : IsDominant ((C.bridge i).P.toBase ((⟨k.1 + 1, h⟩ : Fin _) : ℕ)) := by
      change IsDominant ((C.bridge i).P.πY k)
      rw [hpeq]
      infer_instance
    refine ⟨Sp, hfl, w, hw, hd1, ?_⟩
    rw [← hv]
    exact @valuationOver_congr _ _ _ _ _ _ Sp _ _ hd1 _ hpeq
  | isFalse h =>
    have hmk : (C.bridge i).P.m = k.1 + 1 := by omega
    let φ : C.model (C.flipTargetOf i k (isFalse h)) ≅ (C.bridge i).P.Y k :=
      (C.bridge i).e.symm ≪≫ eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)
    obtain ⟨Sp, hd, hfl, hv⟩ := key (C.flipTargetMapOf i k (isFalse h)) φ.hom
      (Category.assoc _ _ _).symm
    haveI : IsDominant (X := C.model (C.flipTargetOf i k (isFalse h))) (C.junction (i + 1)).p :=
      (C.junction (i + 1)).isBirationalMorphism.isDominant
    refine ⟨Sp, hfl, Sp.valuationOver (C.junction (i + 1)).p, ⟨w, hw, ?_⟩, rfl⟩
    haveI : IsDominant (X := C.model (C.flipTargetOf i k (isFalse h)))
        ((C.junction (i + 1)).p ≫ T.fp i) :=
      ⟨(T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant.denseRange.comp
        (C.junction (i + 1)).isBirationalMorphism.isDominant.denseRange (Scheme.Hom.continuous _)⟩
    exact (valuationOver_comp (X := C.model (C.flipTargetOf i k (isFalse h))) Sp
      (C.junction (i + 1)).p (T.fp i)).symm.trans
        ((valuationOver_congr Sp (junction_comp_fp_eq_flipTargetMapOf C i k h)).trans hv)

end BadBranchCount

namespace StabilizedSmallKltTail.PreparedChain.FlipMove

variable {T : StabilizedSmallKltTail} {Q : PreparedChain T}

/-- For a small terminal flip `μ` of a bridge of a prepared chain and a label `S` with centre
`Sm` on `Y⁻`, the bad branch count of `Sm` along `W⁻` is the sum over the irreducible surfaces
`V ⊆ W⁻` of the branch numbers of `S` at `V` on `Y⁻`; and the strict transform `Sp` of `Sm` on
`Y⁺` is a prime divisor whose bad branch count along `W⁺` is the sum over the irreducible
surfaces `V ⊆ W⁺` of the branch numbers of `S` at `V` on `Y⁺`. -/
@[mmp "lem_oai4_c3_bad_branch_count_sum"]
public theorem badBranchCount_eq_finsum_branchNumber (μ : Q.FlipMove) (S : Q.chain.Label)
    {Sm : MMP.Mori.PrimeDivisor (Q.chain.model μ.source.1)}
    (hm : Q.chain.IsLabelCentre S μ.source.1 Sm)
    {rm : IrreducibleCloseds (Q.chain.model μ.source.1) → ℕ}
    {rp : IrreducibleCloseds (Q.chain.model μ.target.1) → ℕ}
    (hrm : ∀ V, Q.chain.IsLabelBranchNumber S μ.source.1 V (rm V))
    (hrp : ∀ V, Q.chain.IsLabelBranchNumber S μ.target.1 V (rp V)) :
    badBranchCount Sm (μ.badLocusSource : Set (Q.chain.model μ.source.1)) =
        ∑ᶠ (V : IrreducibleCloseds (Q.chain.model μ.source.1))
          (_ : (V : Set (Q.chain.model μ.source.1)) ⊆ μ.badLocusSource ∧
            topologicalKrullDim (V : Set (Q.chain.model μ.source.1)) = 2), rm V ∧
      ∃ Sp : MMP.Mori.PrimeDivisor (Q.chain.model μ.target.1),
        flipTransformPrimeDivisor μ.sourceMap μ.targetMap Sm = some Sp ∧
        badBranchCount Sp (μ.badLocusTarget : Set (Q.chain.model μ.target.1)) =
          ∑ᶠ (V : IrreducibleCloseds (Q.chain.model μ.target.1))
            (_ : (V : Set (Q.chain.model μ.target.1)) ⊆ μ.badLocusTarget ∧
              topologicalKrullDim (V : Set (Q.chain.model μ.target.1)) = 2), rp V := by
  refine ⟨badBranchCount_eq_finsum_labelBranchNumber Q.chain _ hm hrm _, ?_⟩
  obtain ⟨Sp, hfl, hp⟩ := exists_flipTransformPrimeDivisor_isLabelCentre Q.chain μ.1.1 μ.1.2 hm
  exact ⟨Sp, hfl, badBranchCount_eq_finsum_labelBranchNumber Q.chain _ hp hrp _⟩

end StabilizedSmallKltTail.PreparedChain.FlipMove

end MMP.Fourfold

end
