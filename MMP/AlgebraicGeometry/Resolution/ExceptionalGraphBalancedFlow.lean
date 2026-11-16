module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
import StacksFrontier.AlgebraicGeometry.ResidueFieldClosedImmersion
import MMP.AlgebraicGeometry.Resolution.Blowup.PointBlowupIsoOff
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import StacksFrontier.AlgebraicGeometry.Properties.DimensionFunctionClosure
import StacksFrontier.AlgebraicGeometry.Intersection.ExteriorProductIntersection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionZeroSplitting
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Balanced flows along conductor curves and conductor surfaces

Both results of this file correct prescribed branch coefficients by a *flow* on a finite
connected graph of exceptional components: demands `b` with `∑ b = 0` on the vertices of a finite
preconnected graph are the divergence of an antisymmetric flow supported on the edges. The flow is
obtained by routing the demand of every vertex to a fixed root along a walk; the flow of a walk
counts its darts with sign, and its divergence is the difference of the indicators of its ends.

**Surfaces.** Let `S₀` be a smooth surface over a field `k` of characteristic zero, `C ⊆ S₀` a
reduced curve, `x ∈ C` a closed point and `π : S_n → S₀` a finite sequence of point blowups which
blows up `x` and whose total transform `π⁻¹(C)_red` has simple normal crossings over `x`. Given
rational weights `a_λ` on the branches of `C` at `x` (the points `λ` of the birational transform
`C_n` over `x`) with `∑_λ [κ(λ) : κ(x)] a_λ = 0`, there are antisymmetric coefficients on the
intersection points of exceptional curves balancing the branch weights at every exceptional curve.
The vertices are the exceptional curves over `x`, joined when they meet, and the flow along
`E — E'` is placed at one point `q ∈ E ∩ E'`, divided by `[κ(q) : κ(x)]`; such a point exists
since a nonempty closed subset of a fibre of a proper morphism contains a closed point. The graph
is connected because, in characteristic zero, every stage is smooth and every blowup is a closed
map with connected fibres. The transcendence degree `tr.deg_k κ(z)` is a dimension function
bounded by `2`, equal on `C_i` to that of the image in `S₀`, so the branches are closed and
finitely many; and by simple normal crossings each branch lies on exactly one exceptional curve.

**Fourfolds.** Let `Y` be a normal complex fourfold, `Q` a reduced effective divisor, `r : Z ⟶ Y`
a projective resolution with `B` the reduced snc divisor supported on `r⁻¹(Q) ∪ Ex(r)`, and `V` a
conductor surface of `Q` lying in the smooth locus of `Y`, over whose generic point `r` is a
sequence of point blowups starting with the closed point. Given an oriented coefficient system
`a` whose branch legs (double surfaces `S ⊆ Q'ⱼ ∩ E` with `r(E) = V`, dominating `V`) have
degree-weighted sum `∑_S [κ(S) : κ(V)] a_S = 0`, there is an oriented system `c`, agreeing with
`a` off double surfaces of two components over `V`, such that `(r|_E)_* Z_E(c)` has coefficient
`0` along `V` for every component `E` over `V`. The vertices are the components of `B` over `V`,
joined when a double surface between them dominating `V` has nonzero total degree `N(E, E')`;
the correction on a double surface of the edge `(E, E')` is `f(E, E') / N(E, E')`.

## Main results

* `MMP.Resolution.exists_balanced_flow_of_sum_residueFieldDegree_mul_eq_zero`: balanced branch
  coefficients on the exceptional curves of an embedded resolution of a plane curve.
* `MMP.Fourfold.exists_orientedSurfaceCoefficients_rationalPushforward_coeff_eq_zero_of_mem_supp`:
  balancing along any surface `V ⊆ Supp Q` gives divisor cycles with no component along `V`;
  it needs neither the smoothness of `Y` at `η_V`, nor the conductor condition, nor the
  point-blowup structure of `r` over `η_V`.
* `MMP.Fourfold.exists_orientedSurfaceCoefficients_rationalPushforward_coeff_eq_zero`: generic
  balancing along a conductor surface gives vertical divisor cycles.
* `MMP.Fourfold.rationalCoeff_rationalProperPushforward_surfaceCoefficientDivisor_eq_finsum`: the
  coefficient along `V` of `(r|_E)_* Z_E(c)` is the degree-weighted sum of `c` over the double
  surfaces on `E` dominating `V`.
* `MMP.Fourfold.preconnected_components_over`: the components of `B` over `V`, joined along
  double surfaces dominating `V`, form a connected graph.

## Implementation notes

* The surface statement is made over `k` itself: a branch is a closed point of `C_n` over `x`,
  an intersection point is a closed point of `E ∩ E'`, and degrees are taken over `κ(x)` via
  `MMP.Mori.residueFieldDegree`. The source argues on the geometric dual trees after a finite
  Galois extension and descends; here the balancing is done directly over `k` on the connected
  dual graph (only connectedness, not the tree property, is used), so no descent is needed.
* In the fourfold statement the embedded resolution of the Weil divisor `Q` is recorded by its
  clauses, and the generic structure of `r` is the identification of the base change of `r` to
  `Spec 𝒪_{Y,η_V}` with the last stage of a `MMP.Resolution.PointBlowupSequence`. The proof does
  not pass through the surface statement on the generic fibre: the graph of components over `V`
  is connected because the fibre `r⁻¹(η_V)` is connected (Zariski), every point of that fibre
  lies on a component over `V`, and two components over `V` meeting in the fibre meet along a
  double surface dominating `V`, irreducible because `B` is snc and of positive degree over `V`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP

section Flow

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- The signed dart count of a walk: the number of times the walk traverses `x → y` minus the
number of times it traverses `y → x`. -/
private noncomputable def walkFlow {u v : V} (w : G.Walk u v) (x y : V) : ℚ :=
  ((w.darts.map (·.toProd)).count (x, y) : ℚ) - ((w.darts.map (·.toProd)).count (y, x) : ℚ)

private theorem walkFlow_eq_zero {u v : V} (w : G.Walk u v) {x y : V} (h : ¬ G.Adj x y) :
    walkFlow w x y = 0 := by
  have h1 : (x, y) ∉ w.darts.map (·.toProd) := by
    simp only [List.mem_map, not_exists, not_and]
    rintro ⟨⟨p1, p2⟩, hadj⟩ _ hd
    simp only [Prod.mk.injEq] at hd; obtain ⟨rfl, rfl⟩ := hd; exact h hadj
  have h2 : (y, x) ∉ w.darts.map (·.toProd) := by
    simp only [List.mem_map, not_exists, not_and]
    rintro ⟨⟨p1, p2⟩, hadj⟩ _ hd
    simp only [Prod.mk.injEq] at hd; obtain ⟨rfl, rfl⟩ := hd; exact h hadj.symm
  simp [walkFlow, List.count_eq_zero_of_not_mem h1, List.count_eq_zero_of_not_mem h2]

/-- The divergence of the flow of a walk is the indicator of its start minus that of its end. -/
private theorem sum_walkFlow [Fintype V] {u v : V} (w : G.Walk u v) (x : V) :
    ∑ y, walkFlow w x y = (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
  induction w with
  | nil => simp [walkFlow]
  | @cons a b c h p ih =>
    have key : ∀ y, walkFlow (SimpleGraph.Walk.cons h p) x y = walkFlow p x y +
        (if a = x then (if b = y then 1 else 0) else 0) -
          (if b = x then (if a = y then 1 else 0) else 0) := by
      intro y
      simp only [walkFlow, SimpleGraph.Walk.darts_cons, List.map_cons, List.count_cons,
        beq_iff_eq, Prod.mk.injEq, ← ite_and]
      push_cast
      simp only [and_comm (a := b = x)]
      ring
    simp only [key, Finset.sum_add_distrib, ih, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_const_zero]
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
      simp [hxa, hxb, hxc, eq_comm] <;> simp_all [eq_comm]

/-- On a finite preconnected graph, demands with zero total are the divergence of an
antisymmetric flow supported on the edges. -/
private theorem exists_flow [Fintype V] (hG : G.Preconnected) (b : V → ℚ)
    (hb : ∑ v, b v = 0) :
    ∃ f : V → V → ℚ, (∀ x y, f y x = -f x y) ∧ (∀ x y, ¬ G.Adj x y → f x y = 0) ∧
      ∀ x, ∑ y, f x y + b x = 0 := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨r⟩⟩
  · exact ⟨0, by simp, by simp, isEmptyElim⟩
  have W : ∀ v, G.Walk v r := fun v => (hG v r).some
  refine ⟨fun x y => -∑ v, b v * walkFlow (W v) x y, ?_, ?_, ?_⟩
  · intro x y
    simp only [walkFlow, neg_neg, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  · intro x y h
    simp [walkFlow_eq_zero _ h]
  · intro x
    rw [Finset.sum_neg_distrib, Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_walkFlow, mul_sub, Finset.sum_sub_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_ite_irrel]
    split_ifs <;> simp [hb]

end Flow

namespace Resolution

/-- A flow on the intersection graph of a finite family of sets can be placed on intersection
points: if any two members that meet share a point of nonzero weight `deg`, then an antisymmetric
flow `f` vanishing on disjoint pairs is, at every member `E`, the `deg`-weighted sum over the
other members `E'` and the points of `E ∩ E'` of antisymmetric point coefficients. The flow along
`E — E'` is put at one point of `E ∩ E'` of nonzero weight, divided by that weight. -/
private theorem exists_pointCoeff_of_flow {T : Type*} {P : Set T → Prop} [Fintype {E // P E}]
    (f : {E // P E} → {E // P E} → ℚ) (hfa : ∀ E E', f E' E = -f E E')
    (hf0 : ∀ E E', E.1 ∩ E'.1 = ∅ → f E E' = 0) (deg : T → ℚ)
    (hdeg : ∀ E E', P E → P E' → (E ∩ E').Nonempty → ∃ q ∈ E ∩ E', deg q ≠ 0) :
    ∃ c : Set T → Set T → T → ℚ, (∀ E E' q, c E' E q = -c E E' q) ∧
      ∀ E (hE : P E), ∑ᶠ (E' : Set T) (_ : P E') (_ : E' ≠ E) (q : T) (_ : q ∈ E ∩ E'),
        deg q * c E E' q = ∑ E', f ⟨E, hE⟩ E' := by
  classical
  set F : Set T → Set T → ℚ :=
    fun E E' => if h : P E ∧ P E' then f ⟨E, h.1⟩ ⟨E', h.2⟩ else 0 with hF
  have hFa : ∀ E E', F E' E = -F E E' := by
    intro E E'
    by_cases h1 : P E <;> by_cases h2 : P E'
    · simp only [hF, dif_pos (And.intro h2 h1), dif_pos (And.intro h1 h2)]
      exact hfa _ _
    all_goals simp [hF, h1, h2]
  set sel : Set T → T → Prop := fun Z q => ∃ h : ∃ q ∈ Z, deg q ≠ 0, q = h.choose with hsel
  set K : Set T → Set T → T → ℚ :=
    fun E E' q => if sel (E ∩ E') q then F E E' / deg q else 0 with hK
  refine ⟨K, fun E E' q => ?_, fun E hE => ?_⟩
  · simp only [hK, Set.inter_comm E' E, hFa E E', neg_div]
    split_ifs <;> simp
  -- each edge term collapses to the flow
  have hterm : ∀ E', P E' → ∑ᶠ (q : T) (_ : q ∈ E ∩ E'), deg q * K E E' q = F E E' := by
    intro E' hE'
    by_cases h : ∃ q ∈ E ∩ E', deg q ≠ 0
    · have hq0 := h.choose_spec
      have hs : ∀ q, sel (E ∩ E') q ↔ q = h.choose :=
        fun q => ⟨fun ⟨_, hq⟩ => hq, fun hq => ⟨h, hq⟩⟩
      have hq : ∀ q, (∑ᶠ (_ : q ∈ E ∩ E'), deg q * K E E' q) =
          if q = h.choose then F E E' else 0 := by
        intro q
        by_cases hq : q = h.choose
        · rw [if_pos hq, finsum_eq_dif, dif_pos (hq ▸ hq0.1)]
          simp only [hK, if_pos ((hs q).mpr hq)]
          rw [hq]
          exact mul_div_cancel₀ _ hq0.2
        · simp only [hK, if_neg (fun h' => hq ((hs q).mp h')), mul_zero, finsum_zero, if_neg hq]
      rw [finsum_congr hq, finsum_eq_single _ h.choose (fun q hq' => if_neg hq'), if_pos rfl]
    · have hempty : E ∩ E' = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp fun hne => h (hdeg E E' hE hE' hne)
      simp [hempty, hF, hE, hE', hf0 ⟨E, hE⟩ ⟨E', hE'⟩ hempty]
  have h1 : ∀ E', (∑ᶠ (_ : P E') (_ : E' ≠ E) (q : T) (_ : q ∈ E ∩ E'), deg q * K E E' q) =
      ∑ᶠ (_ : P E'), F E E' := by
    intro E'
    refine finsum_congr fun hE' => ?_
    by_cases hne : E' = E
    · subst hne
      have : F E' E' = 0 := by linarith [hFa E' E']
      simp [this]
    · rw [finsum_eq_dif, dif_pos hne, hterm E' hE']
  rw [finsum_congr h1, ← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun E' _ => ?_
  simp only [hF, dif_pos (show P E ∧ P E'.1 from ⟨hE, E'.2⟩)]

/-! ### Morphisms which are isomorphisms over an open -/

section IsoOver

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} [IsIso (f ∣_ U)]

/-- Over an open on which `f` restricts to an isomorphism, `f` is an open embedding. -/
private theorem isOpenEmbedding_ι_comp_of_isIso_restrict :
    Topology.IsOpenEmbedding ((f ⁻¹ᵁ U).ι ≫ f) := by
  rw [← morphismRestrict_ι]
  exact Scheme.Hom.isOpenEmbedding _

/-- A point mapping into `U` comes from the open `f⁻¹(U)`. -/
private theorem exists_ι_eq_of_mem {q : X} (hq : f q ∈ U) : ∃ z : (f ⁻¹ᵁ U).toScheme,
    (f ⁻¹ᵁ U).ι z = q := by
  have : q ∈ Set.range (f ⁻¹ᵁ U).ι := by rw [Scheme.Opens.range_ι]; exact hq
  exact this

/-- Over an open on which `f` restricts to an isomorphism, every point has a preimage. -/
private theorem exists_apply_eq_of_isIso_restrict {y : Y} (hy : y ∈ U) : ∃ q, f q = y := by
  have hrange : y ∈ Set.range ((f ∣_ U) ≫ U.ι) := by
    have hsurj : Function.Surjective (f ∣_ U) := fun w =>
      ⟨inv (f ∣_ U) w, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
    exact hy
  obtain ⟨q, hq⟩ := hrange
  rw [morphismRestrict_ι] at hq
  exact ⟨_, hq⟩

/-- Over an open on which `f` restricts to an isomorphism, `f` is injective. -/
private theorem eq_of_apply_eq_of_isIso_restrict {q q' : X} (hq : f q ∈ U) (he : f q = f q') :
    q = q' := by
  have hq' : f q' ∈ U := he ▸ hq
  obtain ⟨z, rfl⟩ := exists_ι_eq_of_mem f hq
  obtain ⟨z', rfl⟩ := exists_ι_eq_of_mem f hq'
  rw [(isOpenEmbedding_ι_comp_of_isIso_restrict f (U := U)).injective (a₁ := z) (a₂ := z') he]

/-- Over an open on which `f` restricts to an isomorphism, `f` reflects specialization. -/
private theorem specializes_iff_of_isIso_restrict {q q' : X} (hq : f q ∈ U) (hq' : f q' ∈ U) :
    q ⤳ q' ↔ f q ⤳ f q' := by
  obtain ⟨z, rfl⟩ := exists_ι_eq_of_mem f hq
  obtain ⟨z', rfl⟩ := exists_ι_eq_of_mem f hq'
  have h := (isOpenEmbedding_ι_comp_of_isIso_restrict f (U := U)).isInducing.specializes_iff
    (x := z) (y := z')
  have h' := (f ⁻¹ᵁ U).ι.isOpenEmbedding.isInducing.specializes_iff (x := z) (y := z')
  rw [h']
  exact h.symm

/-- Over an open on which `f` restricts to an isomorphism, `f` induces isomorphisms of residue
fields. -/
private theorem isIso_residueFieldMap_of_isIso_restrict {q : X} (hq : f q ∈ U) :
    IsIso (f.residueFieldMap q) := by
  haveI := isIso_stalkMap_of_isIso_morphismRestrict f inferInstance hq
  exact (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap q)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

end IsoOver

/-! ### One step of a point blowup sequence -/

section Step

variable {S₀ : Scheme.{u}} (s : PointBlowupSequence S₀)

/-- The blowup `σ_i` is proper. -/
private theorem isProper_σ (i : ℕ) (hi : (i : ℕ∞) < s.length) [IsLocallyNoetherian (s.S i)] :
    IsProper (s.σ i hi) := by
  unfold PointBlowupSequence.σ; infer_instance

/-- The blowup `σ_i` is an isomorphism over the complement of its centre. -/
private theorem isIso_σ_restrict (i : ℕ) (hi : (i : ℕ∞) < s.length) :
    IsIso (s.σ i hi ∣_ MMP.Resolution.Kollar.complPoint (s.isClosed_p i hi)) := by
  unfold PointBlowupSequence.σ
  rw [morphismRestrict_comp]
  haveI := MMP.Resolution.Kollar.isIso_blowUpToBase_restrict_compl_point (s.isClosed_p i hi)
  haveI : IsIso ((s.blowupIso i hi).hom ∣_ (blowUpToBase _ ⁻¹ᵁ
      MMP.Resolution.Kollar.complPoint (s.isClosed_p i hi))) :=
    by delta morphismRestrict; infer_instance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this ‹_›

private theorem mem_complPoint_iff {X : Scheme.{u}} {o : X} (ho : IsClosed ({o} : Set X)) (y : X) :
    y ∈ MMP.Resolution.Kollar.complPoint ho ↔ y ≠ o := Set.mem_compl_singleton_iff

/-- The support of the birational transform `C_{i+1}` is the closure of
`σ_i⁻¹(C_i) ∖ σ_i⁻¹(p_i)`. -/
private theorem support_transformedSubscheme_succ (C₀ : S₀.IdealSheafData) (i : ℕ)
    (hi : (i : ℕ∞) < s.length) [IsLocallyNoetherian (s.S i)] :
    ((s.transformedSubscheme C₀ (i + 1)).support : Set (s.S (i + 1))) =
      closure (s.σ i hi ⁻¹' ((s.transformedSubscheme C₀ i).support : Set (s.S i)) \
        s.σ i hi ⁻¹' {s.p i}) := by
  set I := Scheme.IdealSheafData.vanishingIdeal
    (⟨{s.p i}, s.isClosed_p i hi⟩ : TopologicalSpace.Closeds (s.S i)) with hI
  set T := s.transformedSubscheme C₀ i
  have hT : s.transformedSubscheme C₀ (i + 1) =
      (birationalTransform (s.p i) (s.isClosed_p i hi) T).comap (s.blowupIso i hi).hom := by
    rw [PointBlowupSequence.transformedSubscheme, dif_pos hi]
  have hE : ((exceptionalIdeal I).support : Set (blowUp I)) = blowUpToBase I ⁻¹' {s.p i} := by
    rw [← compl_inj_iff, ← MMP.Resolution.Kollar.preimage_compl_eq_compl_support_exceptionalIdeal]
    rfl
  have hB : ((birationalTransform (s.p i) (s.isClosed_p i hi) T).support : Set (blowUp I)) =
      closure (blowUpToBase I ⁻¹' (T.support : Set (s.S i)) \ blowUpToBase I ⁻¹' {s.p i}) := by
    haveI : IsLocallyNoetherian (blowUp I) :=
      LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase I)
    haveI : IsLocallyNoetherian (Limits.pullback T.subschemeι (blowUpToBase I)) :=
      LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.snd T.subschemeι (blowUpToBase I))
    rw [birationalTransform, Scheme.Hom.support_ker]
    congr 1
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Hom.coe_preimage, Set.image_preimage_eq_inter_range, Scheme.Pullback.range_snd,
      Scheme.IdealSheafData.range_subschemeι, ← hE, Set.diff_eq, Set.inter_comm]
    rfl
  rw [hT, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hB]
  exact (s.blowupIso i hi).hom.homeomorph.preimage_closure _

end Step

/-! ### Smoothness along a point blowup sequence in characteristic zero -/

section Smooth

/-- A morphism between affine schemes is `Spec` of its action on global sections. -/
private theorem eq_SpecMap_appTop {R T : CommRingCat.{u}} (h : Spec T ⟶ Spec R) :
    h = Spec.map ((Scheme.ΓSpecIso R).inv ≫ h.appTop ≫ (Scheme.ΓSpecIso T).hom) := by
  have := Scheme.toSpecΓ_naturality h
  rw [← SpecMap_ΓSpecIso_hom, ← SpecMap_ΓSpecIso_hom] at this
  rw [Spec.map_comp, Spec.map_comp, ← this, Category.assoc, ← Spec.map_comp]
  simp

/-- For `f : S ⟶ Spec R`, the composite `Spec κ(o) ⟶ S ⟶ Spec R` is `Spec` of the map
`R → κ(o)` induced by `f`. -/
private theorem fromSpecResidueField_comp_eq_SpecMap {R : CommRingCat.{u}} {S : Scheme.{u}}
    (f : S ⟶ Spec R) (o : S) :
    S.fromSpecResidueField o ≫ f =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ S.Γevaluation o) := by
  rw [eq_SpecMap_appTop (S.fromSpecResidueField o ≫ f), Scheme.Hom.comp_appTop, Category.assoc]
  congr 3
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.fromSpecStalk_appTop]
  simp
  rfl

/-- In characteristic zero, a closed point of a scheme locally of finite type over `k` is smooth
over `k`: its residue field is a finite, hence separable, extension of `k`. -/
private theorem smooth_fromSpecResidueField_comp {k : Type u} [Field k] [CharZero k]
    {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [LocallyOfFiniteType f] {o : S}
    (ho : IsClosed ({o} : Set S)) :
    Smooth (S.fromSpecResidueField o ≫ f) := by
  have := isClosed_singleton_iff_isClosedImmersion.1 ho
  have hft : RingHom.FiniteType
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ S.Γevaluation o).hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType),
      ← fromSpecResidueField_comp_eq_SpecMap]
    infer_instance
  rw [fromSpecResidueField_comp_eq_SpecMap, HasRingHomProperty.Spec_iff (P := @Smooth)]
  letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ S.Γevaluation o).hom.toAlgebra
  have : Algebra.FiniteType k (S.residueField o) := hft
  have : Module.Finite k (S.residueField o) := finite_of_finite_type_of_isJacobsonRing k _
  have := Algebra.FormallyEtale.of_isSeparable k (S.residueField o)
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.1 ‹_›⟩

/-- If a closed immersion `i` followed by `f` is smooth, so is the closed subscheme cut out by
the kernel of `i`, followed by `f`. -/
private theorem smooth_ker_subschemeι_comp {X Y Z : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (f : Y ⟶ Z) (h : Smooth (i ≫ f)) : Smooth (i.ker.subschemeι ≫ f) := by
  rw [← i.toImage_imageι, Category.assoc] at h
  have : Smooth (inv i.toImage ≫ i.toImage ≫ i.imageι ≫ f) := inferInstance
  rwa [IsIso.inv_hom_id_assoc] at this

/-- In characteristic zero, the reduced closed point of a scheme locally of finite type over `k`
is smooth over `k`. -/
private theorem smooth_subschemeι_vanishingIdeal_singleton_comp {k : Type u} [Field k]
    [CharZero k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [LocallyOfFiniteType f] {o : S}
    (ho : IsClosed ({o} : Set S)) :
    Smooth ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{o}, ho⟩ : TopologicalSpace.Closeds S)).subschemeι ≫ f) := by
  have := isClosed_singleton_iff_isClosedImmersion.1 ho
  rw [vanishingIdeal_singleton_eq_ker o ho]
  exact smooth_ker_subschemeι_comp _ f (smooth_fromSpecResidueField_comp f ho)

/-- In characteristic zero, the blowup of a closed point of a smooth `k`-scheme is a smooth blowup
in the sense of `MMP.Resolution.IsSmoothBlowup`. -/
private theorem isSmoothBlowup_vanishingIdeal_singleton {k : Type u} [Field k] [CharZero k]
    {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [Smooth f] {o : S} (ho : IsClosed ({o} : Set S)) :
    MMP.Resolution.IsSmoothBlowup f
      (Scheme.IdealSheafData.vanishingIdeal (⟨{o}, ho⟩ : TopologicalSpace.Closeds S)) := by
  haveI := smooth_subschemeι_vanishingIdeal_singleton_comp f ho
  exact ⟨MMP.Resolution.isSmoothScheme_of_smooth _, MMP.Resolution.isSmoothScheme_of_smooth _⟩

/-- In characteristic zero, every stage of a point blowup sequence of a smooth `k`-scheme is smooth
over `k`. -/
private theorem smooth_π_comp {k : Type u} [Field k] [CharZero k] {S₀ : Scheme.{u}}
    (sS : S₀ ⟶ Spec (.of k)) [Smooth sS] (s : PointBlowupSequence S₀) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length), Smooth (s.π i hi ≫ sS)
  | 0, _ => by simp only [PointBlowupSequence.π]; infer_instance
  | i + 1, hi => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    haveI := smooth_π_comp sS s i hlt.le
    haveI := (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup
      (s.π i hlt.le ≫ sS) _ (isSmoothBlowup_vanishingIdeal_singleton (s.π i hlt.le ≫ sS)
        (s.isClosed_p i hlt))).1
    show Smooth ((s.σ i hlt ≫ s.π i hlt.le) ≫ sS)
    unfold PointBlowupSequence.σ
    rw [Category.assoc, Category.assoc]
    infer_instance

end Smooth

/-! ### Transcendence degree as a dimension function -/

section Delta

variable {k : Type u} [Field k]

/-- The transcendence degree `tr.deg_k κ(z)` of a point of a `k`-scheme, read as the relative
dimension over `Spec k` with its zero dimension function. -/
private noncomputable abbrev trdegDim {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (z : X) : ℤ :=
  Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation k).dimensionFunction f z

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]

private theorem trdegDim_lt {x y : X} (h : x ⤳ y) (hne : x ≠ y) :
    trdegDim f y < trdegDim f x :=
  Stacks.Chow.relativeDimension_lt_of_mem_closure_of_ne (Stacks.Chow.fieldChowSituation k) f
    (specializes_iff_mem_closure.mp h) (Ne.symm hne)

private theorem trdegDim_eq_zero_of_isClosed {x : X} (hx : IsClosed ({x} : Set X)) :
    trdegDim f x = 0 :=
  Stacks.Chow.relativeDimension_eq_zero_of_isClosed (Stacks.Chow.fieldChowSituation k)
    (fun t _ => Stacks.Chow.fieldChowSituation_dimensionFunction k t) f x hx

private theorem trdegDim_nonneg (x : X) : 0 ≤ trdegDim f x :=
  Stacks.Chow.relativeDimension_nonneg (Stacks.Chow.fieldChowSituation k)
    (fun t _ => Stacks.Chow.fieldChowSituation_dimensionFunction k t) f x

private theorem isClosed_of_trdegDim_eq_zero {x : X} (h : trdegDim f x = 0) :
    IsClosed ({x} : Set X) := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨z, hz, hzcl⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set X))
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  by_cases hzx : z = x
  · subst hzx; exact hzcl
  · have := trdegDim_lt f (specializes_iff_mem_closure.mpr hz) (Ne.symm hzx)
    rw [trdegDim_eq_zero_of_isClosed f hzcl, h] at this
    exact absurd this (lt_irrefl 0)

private theorem trdegDim_comp_of_isIso {Y : Scheme.{u}} (g : Y ⟶ X) (y : Y)
    (h : IsIso (g.residueFieldMap y)) : trdegDim (g ≫ f) y = trdegDim f (g y) :=
  Stacks.Chow.relativeDimension_eq_of_residueFieldMap_isIso (Stacks.Chow.fieldChowSituation k)
    f g y h

/-- The dimension of `X` at `z` is `tr.deg_k κ(z) + dim 𝒪_{X,z}`. -/
private theorem topologicalKrullDimAt_eq_trdegDim_add (z : X) :
    topologicalKrullDimAt X z =
      (((trdegDim f z).toNat : ℕ) : WithBot ℕ∞) + ringKrullDim (X.presheaf.stalk z) := by
  rw [topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X f z,
    ← topologicalKrullDim_closure_singleton_eq_trdeg k X f z,
    Stacks.Chow.topologicalKrullDim_closure_singleton_eq k f z]

end Delta

/-! ### Points of the closure of a locally closed set -/

/-- In a locally Noetherian scheme, every point of the closure of a locally closed set `F ∩ O` is
a specialization of a point of `F ∩ O`. -/
private theorem exists_mem_specializes_of_mem_closure_scheme {X : Scheme.{u}}
    [IsLocallyNoetherian X] {F O : Set X} (hF : IsClosed F) (hO : IsOpen O) {y : X}
    (hy : y ∈ closure (F ∩ O)) : ∃ a ∈ F ∩ O, a ⤳ y := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  haveI : IsAffine W.toScheme := hW
  haveI : AlgebraicGeometry.IsNoetherian W.toScheme := ⟨⟩
  haveI : TopologicalSpace.NoetherianSpace (W : Set X) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace W.toScheme)
  haveI : QuasiSober (W : Set X) := inferInstanceAs (QuasiSober W.toScheme)
  have hy' : (⟨y, hyW⟩ : (W : Set X)) ∈
      closure ((Subtype.val ⁻¹' F) ∩ (Subtype.val ⁻¹' O) : Set (W : Set X)) := by
    rw [closure_subtype]
    have h1 := W.isOpen.inter_closure ⟨hyW, hy⟩
    refine closure_mono ?_ h1
    rintro z ⟨hzW, hzF, hzO⟩
    exact ⟨⟨z, hzW⟩, ⟨hzF, hzO⟩, rfl⟩
  obtain ⟨a, ⟨haF, haO⟩, ha⟩ := MMP.Resolution.exists_mem_specializes_of_mem_closure
    (hF.preimage continuous_subtype_val) (hO.preimage continuous_subtype_val) hy'
  exact ⟨a.1, ⟨haF, haO⟩, ha.map continuous_subtype_val⟩

/-! ### Dimension of a smooth surface -/

section SmoothSurface

variable {k : Type u} [Field k]

/-- A smooth surface over `k` has dimension two at every point. -/
private theorem topologicalKrullDimAt_eq_two {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 2 f] (z : X) : topologicalKrullDimAt X z = 2 := by
  rw [topologicalKrullDimAt_eq_fiber_of_subsingleton f z,
    AlgebraicGeometry.fiberDimensionAt_eq_of_smoothOfRelativeDimension f 2 z]
  rfl

/-- On a smooth surface over `k`, `tr.deg_k κ(z) + dim 𝒪_{X,z} = 2`. -/
private theorem trdegDim_add_ringKrullDim_eq_two {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 2 f] (z : X) :
    (((trdegDim f z).toNat : ℕ) : WithBot ℕ∞) + ringKrullDim (X.presheaf.stalk z) = 2 := by
  haveI := SmoothOfRelativeDimension.smooth 2 f
  rw [← topologicalKrullDimAt_eq_trdegDim_add f z, topologicalKrullDimAt_eq_two f z]

end SmoothSurface

/-! ### Generizations off the exceptional divisor -/

/-- Every point of the blowup of a closed point of a smooth `k`-scheme (characteristic zero) is a
specialization of a point not lying over the centre. -/
private theorem exists_specializes_blowUpToBase_ne {k : Type u} [Field k] [CharZero k]
    {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) [Smooth f] {o : S} (ho : IsClosed ({o} : Set S))
    (w : blowUp (Kollar.pointIdeal ho)) :
    ∃ η, η ⤳ w ∧ blowUpToBase (Kollar.pointIdeal ho) η ≠ o := by
  haveI : Smooth (blowUpToBase (Kollar.pointIdeal ho) ≫ f) :=
    (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup f _
      (isSmoothBlowup_vanishingIdeal_singleton f ho)).1
  have hreg := isRegularLocalRing_stalk_of_smooth_over_field
    (blowUpToBase (Kollar.pointIdeal ho) ≫ f) w
  haveI : IsDomain ((blowUp (Kollar.pointIdeal ho)).presheaf.stalk w) :=
    IsRegularLocalRing.isDomain _
  obtain ⟨a, ha, hspan⟩ :=
    Stacks.Divisors.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor
      (exceptionalIdeal (Kollar.pointIdeal ho))
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _) w
  have ha0 : a ≠ 0 := fun h => by
    rw [h] at ha
    exact not_isRegular_zero ha
  let P : PrimeSpectrum ((blowUp (Kollar.pointIdeal ho)).presheaf.stalk w) :=
    ⟨⊥, Ideal.isPrime_bot⟩
  have hsp := specializes_fromSpecStalk w P
  refine ⟨_, hsp, fun he => ?_⟩
  have hE : ((exceptionalIdeal (Kollar.pointIdeal ho)).support :
      Set (blowUp (Kollar.pointIdeal ho))) = blowUpToBase (Kollar.pointIdeal ho) ⁻¹' {o} := by
    rw [← compl_inj_iff, ← MMP.Resolution.Kollar.preimage_compl_eq_compl_support_exceptionalIdeal]
    rfl
  have hmem : (blowUp (Kollar.pointIdeal ho)).fromSpecStalk w P ∈
      (exceptionalIdeal (Kollar.pointIdeal ho)).support := by
    change _ ∈ ((exceptionalIdeal (Kollar.pointIdeal ho)).support :
      Set (blowUp (Kollar.pointIdeal ho)))
    rw [hE]; exact he
  rw [mem_support_iff_stalk_le_primeOfSpecializes _ hsp, primeOfSpecializes_fromSpecStalk, hspan,
    Ideal.span_le, Set.singleton_subset_iff] at hmem
  exact ha0 hmem

/-! ### Preimages under closed maps with connected fibres -/

/-- Under a continuous closed map whose fibres over a closed preconnected set `S` are connected,
the preimage of `S` is preconnected. -/
private theorem isPreconnected_preimage_of_isClosedMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (hcl : IsClosedMap f) {S : Set Y}
    (hS : IsClosed S) (hSc : _root_.IsPreconnected S)
    (hfib : ∀ y ∈ S, _root_.IsConnected (f ⁻¹' {y})) : _root_.IsPreconnected (f ⁻¹' S) := by
  have hT : IsClosed (f ⁻¹' S) := hS.preimage hf
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hT]
  intro u v hu hv huv huvd
  have hfibuv : ∀ y ∈ S, f ⁻¹' {y} ⊆ u ∨ f ⁻¹' {y} ⊆ v := by
    intro y hy
    refine (isPreconnected_iff_subset_of_disjoint_closed.mp (hfib y hy).2) u v hu hv
      (fun z hz => huv (show f z ∈ S from (Set.mem_singleton_iff.mp hz) ▸ hy)) ?_
    rw [Set.disjoint_iff_inter_eq_empty.mp huvd, Set.inter_empty]
  have hA : IsClosed (f '' (f ⁻¹' S ∩ u)) := hcl _ (hT.inter hu)
  have hB : IsClosed (f '' (f ⁻¹' S ∩ v)) := hcl _ (hT.inter hv)
  have hcov : S ⊆ f '' (f ⁻¹' S ∩ u) ∪ f '' (f ⁻¹' S ∩ v) := by
    intro y hy
    obtain ⟨z, hz⟩ := (hfib y hy).nonempty
    have hzS : f z ∈ S := (Set.mem_singleton_iff.mp hz) ▸ hy
    rcases huv hzS with h | h
    · exact Or.inl ⟨z, ⟨hzS, h⟩, hz⟩
    · exact Or.inr ⟨z, ⟨hzS, h⟩, hz⟩
  have key : ∀ y ∈ S, y ∈ f '' (f ⁻¹' S ∩ u) → f ⁻¹' {y} ⊆ u := by
    rintro y hy ⟨z, ⟨-, hzu⟩, rfl⟩
    rcases hfibuv _ hy with h | h
    · exact h
    · exact absurd (Set.disjoint_left.mp huvd hzu (h rfl)) id
  have key' : ∀ y ∈ S, y ∈ f '' (f ⁻¹' S ∩ v) → f ⁻¹' {y} ⊆ v := by
    rintro y hy ⟨z, ⟨-, hzv⟩, rfl⟩
    rcases hfibuv _ hy with h | h
    · exact absurd (Set.disjoint_left.mp huvd (h rfl) hzv) id
    · exact h
  have hdisj : S ∩ (f '' (f ⁻¹' S ∩ u) ∩ f '' (f ⁻¹' S ∩ v)) = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hy hyu hyv
    obtain ⟨z, ⟨-, hzu⟩, hzy⟩ := hyu
    exact Set.disjoint_left.mp huvd hzu (key' _ hy hyv (show z ∈ f ⁻¹' {y} from hzy))
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hSc _ _ hA hB hcov hdisj with h | h
  · exact Or.inl fun z hz => key _ hz (h hz) rfl
  · exact Or.inr fun z hz => key' _ hz (h hz) rfl

/-! ### Invariants along the blowup sequence -/

/-- A smooth morphism is locally of finite type. -/
private theorem locallyOfFiniteType_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    LocallyOfFiniteType f := by
  haveI : LocallyOfFinitePresentation f := inferInstance
  infer_instance

section Invariants

variable {k : Type u} [Field k] [CharZero k] {S₀ : Scheme.{u}} (sS : S₀ ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 2 sS] (s : PointBlowupSequence S₀)

include sS in
/-- Every stage of the sequence is locally Noetherian. -/
private theorem isLocallyNoetherian_S (i : ℕ) (hi : (i : ℕ∞) ≤ s.length) :
    IsLocallyNoetherian (s.S i) := by
  haveI := SmoothOfRelativeDimension.smooth 2 sS
  haveI := smooth_π_comp sS s i hi
  exact MMP.Resolution.isLocallyNoetherian_of_smooth (s.π i hi ≫ sS)

/-- `π_{i+1}` followed by the structure morphism is `σ_i` followed by `π_i` and the structure
morphism. -/
private theorem π_succ_comp (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) ≤ s.length) :
    s.π (i + 1) hi ≫ sS = s.σ i (PointBlowupSequence.coe_lt_of_succ_le hi) ≫
      (s.π i (PointBlowupSequence.coe_lt_of_succ_le hi).le ≫ sS) :=
  Category.assoc _ _ _

include sS in
/-- Every point of `S_{i+1}` is a specialization of a point not lying over the centre `p_i`. -/
private theorem exists_specializes_σ_ne (i : ℕ) (hi : (i : ℕ∞) < s.length) (z : s.S (i + 1)) :
    ∃ a, a ⤳ z ∧ s.σ i hi a ≠ s.p i := by
  haveI := SmoothOfRelativeDimension.smooth 2 sS
  haveI := smooth_π_comp sS s i hi.le
  obtain ⟨η, hη, hne⟩ := exists_specializes_blowUpToBase_ne (s.π i hi.le ≫ sS) (s.isClosed_p i hi)
    ((s.blowupIso i hi).hom z)
  refine ⟨(s.blowupIso i hi).inv η, ?_, ?_⟩
  · have e : (s.blowupIso i hi).inv ((s.blowupIso i hi).hom z) = z := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
    have := hη.map (s.blowupIso i hi).inv.continuous
    rwa [e] at this
  · have e : (s.blowupIso i hi).hom ((s.blowupIso i hi).inv η) = η := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    unfold PointBlowupSequence.σ
    rwa [Scheme.Hom.comp_apply, e]

/-- Off the centre, `σ_i` preserves the transcendence degree. -/
private theorem trdegDim_π_succ_of_ne (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) ≤ s.length)
    (z : s.S (i + 1)) (hz : s.σ i (PointBlowupSequence.coe_lt_of_succ_le hi) z ≠ s.p i) :
    trdegDim (s.π (i + 1) hi ≫ sS) z =
      trdegDim (s.π i (PointBlowupSequence.coe_lt_of_succ_le hi).le ≫ sS)
        (s.σ i (PointBlowupSequence.coe_lt_of_succ_le hi) z) := by
  have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
  haveI := SmoothOfRelativeDimension.smooth 2 sS
  haveI := smooth_π_comp sS s i hlt.le
  haveI := locallyOfFiniteType_of_smooth (s.π i hlt.le ≫ sS)
  haveI := isIso_σ_restrict s i hlt
  rw [π_succ_comp sS s i hi]
  exact trdegDim_comp_of_isIso (s.π i hlt.le ≫ sS) (s.σ i hlt) z
    (isIso_residueFieldMap_of_isIso_restrict (s.σ i hlt)
      (U := Kollar.complPoint (s.isClosed_p i hlt)) ((mem_complPoint_iff _ _).mpr hz))

/-- On the first stage, `tr.deg_k` is that of the image in `S₀`. -/
private theorem trdegDim_π_zero (hi : ((0 : ℕ) : ℕ∞) ≤ s.length) (z : s.S 0) :
    trdegDim (s.π 0 hi ≫ sS) z = trdegDim sS (s.π 0 hi z) := by
  haveI := SmoothOfRelativeDimension.smooth 2 sS
  exact trdegDim_comp_of_isIso sS s.zeroIso.hom z inferInstance

/-- Every point of every stage has `tr.deg_k κ(z) ≤ 2`. -/
private theorem trdegDim_π_le_two :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length) (z : s.S i), trdegDim (s.π i hi ≫ sS) z ≤ 2
  | 0, hi, z => by
    rw [trdegDim_π_zero sS s hi z]
    have h := trdegDim_add_ringKrullDim_eq_two sS (s.π 0 hi z)
    have hr : 0 ≤ ringKrullDim (S₀.presheaf.stalk (s.π 0 hi z)) := ringKrullDim_nonneg_of_nontrivial
    have h2 : (((trdegDim sS (s.π 0 hi z)).toNat : ℕ) : WithBot ℕ∞) ≤ 2 := by
      rw [← h]; exact le_add_of_nonneg_right hr
    have h3 : (trdegDim sS (s.π 0 hi z)).toNat ≤ 2 := by exact_mod_cast h2
    omega
  | i + 1, hi, z => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    by_cases hz : s.σ i hlt z = s.p i
    · haveI := SmoothOfRelativeDimension.smooth 2 sS
      haveI := smooth_π_comp sS s (i + 1) hi
      haveI := locallyOfFiniteType_of_smooth (s.π (i + 1) hi ≫ sS)
      obtain ⟨a, ha, hane⟩ := exists_specializes_σ_ne sS s i hlt z
      have hne : a ≠ z := fun h => hane (h ▸ hz)
      have h1 := trdegDim_lt (s.π (i + 1) hi ≫ sS) ha hne
      rw [trdegDim_π_succ_of_ne sS s i hi a hane] at h1
      have h2 := trdegDim_π_le_two i hlt.le (s.σ i hlt a)
      omega
    · rw [trdegDim_π_succ_of_ne sS s i hi z hz]
      exact trdegDim_π_le_two i hlt.le _

include sS in
/-- The points of a curve `C ⊆ S₀` have `tr.deg_k κ(c) ≤ 1`. -/
private theorem trdegDim_le_one_of_mem (C : S₀.IdealSheafData)
    (hC : topologicalKrullDim (C.support : Set S₀) = 1) {c : S₀} (hc : c ∈ C.support) :
    trdegDim sS c ≤ 1 := by
  haveI := SmoothOfRelativeDimension.smooth 2 sS
  have h := Stacks.Chow.topologicalKrullDim_closure_singleton_eq k sS c
  have hsub : closure ({c} : Set S₀) ⊆ (C.support : Set S₀) :=
    closure_minimal (Set.singleton_subset_iff.mpr hc) C.support.isClosed
  have hle := (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
  rw [h, hC] at hle
  have h3 : (trdegDim sS c).toNat ≤ 1 := by exact_mod_cast hle
  omega

include sS in
/-- The birational transforms `C_i` lie over `C`, and the transcendence degree of a point of `C_i`
is that of its image in `S₀`. -/
private theorem transform_invariant (C : S₀.IdealSheafData)
    (hC : topologicalKrullDim (C.support : Set S₀) = 1) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length) (t : s.S i),
      t ∈ (s.transformedSubscheme C i).support →
        s.π i hi t ∈ C.support ∧ trdegDim (s.π i hi ≫ sS) t = trdegDim sS (s.π i hi t)
  | 0, hi, t, ht => by
    refine ⟨?_, trdegDim_π_zero sS s hi t⟩
    have : t ∈ ((C.comap s.zeroIso.hom).support : Set (s.S 0)) := ht
    rw [Scheme.IdealSheafData.support_comap] at this
    exact this
  | i + 1, hi, t, ht => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    haveI := isLocallyNoetherian_S sS s i hlt.le
    haveI := isLocallyNoetherian_S sS s (i + 1) hi
    have ht' : t ∈ closure (s.σ i hlt ⁻¹' ((s.transformedSubscheme C i).support : Set (s.S i)) \
        s.σ i hlt ⁻¹' {s.p i}) := by
      rw [← support_transformedSubscheme_succ s C i hlt]; exact ht
    have hFcl : IsClosed (s.σ i hlt ⁻¹' ((s.transformedSubscheme C i).support : Set (s.S i))) :=
      (s.transformedSubscheme C i).support.isClosed.preimage (s.σ i hlt).continuous
    have hσt : s.σ i hlt t ∈ (s.transformedSubscheme C i).support :=
      closure_minimal Set.diff_subset hFcl ht'
    obtain ⟨hC1, hδ1⟩ := transform_invariant C hC i hlt.le _ hσt
    have hπ : s.π (i + 1) hi t = s.π i hlt.le (s.σ i hlt t) := rfl
    refine ⟨hπ ▸ hC1, ?_⟩
    rw [hπ]
    by_cases hz : s.σ i hlt t = s.p i
    · haveI := SmoothOfRelativeDimension.smooth 2 sS
      haveI := smooth_π_comp sS s (i + 1) hi
      haveI := locallyOfFiniteType_of_smooth (s.π (i + 1) hi ≫ sS)
      haveI := smooth_π_comp sS s i hlt.le
      haveI := locallyOfFiniteType_of_smooth (s.π i hlt.le ≫ sS)
      have hp0 : trdegDim (s.π i hlt.le ≫ sS) (s.σ i hlt t) = 0 := by
        rw [hz]; exact trdegDim_eq_zero_of_isClosed _ (s.isClosed_p i hlt)
      suffices h0 : trdegDim (s.π (i + 1) hi ≫ sS) t = 0 by rw [h0, ← hδ1, hp0]
      by_contra hne
      have hpos : 1 ≤ trdegDim (s.π (i + 1) hi ≫ sS) t := by
        have := trdegDim_nonneg (s.π (i + 1) hi ≫ sS) t; omega
      rw [Set.diff_eq] at ht'
      obtain ⟨a, ⟨haF, haO⟩, hat⟩ := exists_mem_specializes_of_mem_closure_scheme hFcl
        ((s.isClosed_p i hlt).preimage (s.σ i hlt).continuous).isOpen_compl ht'
      have hane' : s.σ i hlt a ≠ s.p i := haO
      have hane : a ≠ t := fun h => hane' (h ▸ hz)
      have h1 := trdegDim_lt (s.π (i + 1) hi ≫ sS) hat hane
      rw [trdegDim_π_succ_of_ne sS s i hi a hane'] at h1
      obtain ⟨haC, haδ⟩ := transform_invariant C hC i hlt.le _ haF
      rw [haδ] at h1
      have := trdegDim_le_one_of_mem sS C hC haC
      omega
    · rw [trdegDim_π_succ_of_ne sS s i hi t hz, hδ1]

include sS in
/-- A point of the birational transform `C_i` lying over a closed point is closed. -/
private theorem isClosed_of_mem_transform (C : S₀.IdealSheafData)
    (hC : topologicalKrullDim (C.support : Set S₀) = 1) (i : ℕ) (hi : (i : ℕ∞) ≤ s.length)
    {x : S₀} (hx : IsClosed ({x} : Set S₀)) {t : s.S i}
    (ht : t ∈ (s.transformedSubscheme C i).support) (htx : s.π i hi t = x) :
    IsClosed ({t} : Set (s.S i)) := by
  haveI := SmoothOfRelativeDimension.smooth 2 sS
  haveI := smooth_π_comp sS s i hi
  haveI := locallyOfFiniteType_of_smooth (s.π i hi ≫ sS)
  obtain ⟨-, h⟩ := transform_invariant sS s C hC i hi t ht
  rw [htx, trdegDim_eq_zero_of_isClosed sS hx] at h
  exact isClosed_of_trdegDim_eq_zero _ h

include sS in
/-- Before the first blowup over `x`, the fibre over `x` has at most one point. -/
private theorem eq_of_π_eq_of_le {x : S₀} (j : ℕ)
    (hjmin : ∀ (i : ℕ) (hi : (i : ℕ∞) < s.length), i < j → s.π i hi.le (s.p i) ≠ x) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length), i ≤ j → ∀ t t' : s.S i,
      s.π i hi t = x → s.π i hi t' = x → t = t'
  | 0, hi, _, t, t', ht, ht' => by
    have hinj : Function.Injective (s.π 0 hi) := s.zeroIso.hom.homeomorph.injective
    exact hinj (ht.trans ht'.symm)
  | i + 1, hi, hij, t, t', ht, ht' => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    have h := eq_of_π_eq_of_le j hjmin i hlt.le (by omega) (s.σ i hlt t) (s.σ i hlt t') ht ht'
    haveI := isIso_σ_restrict s i hlt
    refine eq_of_apply_eq_of_isIso_restrict (s.σ i hlt)
      (U := Kollar.complPoint (s.isClosed_p i hlt)) ((mem_complPoint_iff _ _).mpr ?_) h
    intro hp
    exact hjmin i hlt (by omega) (by rw [← hp]; exact ht)

include sS in
/-- One step of the propagation: if every point of `C_i` over `x` other than `p_i` is a
specialization of a point of `C_i` not over `x`, then every point of `C_{i+1}` over `x` is. -/
private theorem exists_generization_off_fibre_succ (C : S₀.IdealSheafData)
    (hC : topologicalKrullDim (C.support : Set S₀) = 1) {x : S₀} (hx : IsClosed ({x} : Set S₀))
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) ≤ s.length)
    (H : ∀ u ∈ (s.transformedSubscheme C i).support,
      s.π i (PointBlowupSequence.coe_lt_of_succ_le hi).le u = x → u ≠ s.p i →
        ∃ g ∈ (s.transformedSubscheme C i).support,
          s.π i (PointBlowupSequence.coe_lt_of_succ_le hi).le g ≠ x ∧ g ⤳ u)
    (t : s.S (i + 1)) (ht : t ∈ (s.transformedSubscheme C (i + 1)).support)
    (htx : s.π (i + 1) hi t = x) :
    ∃ g ∈ (s.transformedSubscheme C (i + 1)).support, s.π (i + 1) hi g ≠ x ∧ g ⤳ t := by
  have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
  haveI := isLocallyNoetherian_S sS s i hlt.le
  haveI := isLocallyNoetherian_S sS s (i + 1) hi
  haveI := isIso_σ_restrict s i hlt
  have hT := support_transformedSubscheme_succ s C i hlt
  have ht' : t ∈ closure (s.σ i hlt ⁻¹' ((s.transformedSubscheme C i).support : Set (s.S i)) \
      s.σ i hlt ⁻¹' {s.p i}) := by rw [← hT]; exact ht
  have hFcl : IsClosed (s.σ i hlt ⁻¹' ((s.transformedSubscheme C i).support : Set (s.S i))) :=
    (s.transformedSubscheme C i).support.isClosed.preimage (s.σ i hlt).continuous
  have hσt : s.σ i hlt t ∈ (s.transformedSubscheme C i).support :=
    closure_minimal Set.diff_subset hFcl ht'
  have hπ : ∀ z, s.π (i + 1) hi z = s.π i hlt.le (s.σ i hlt z) := fun _ => rfl
  by_cases hz : s.σ i hlt t = s.p i
  · rw [Set.diff_eq] at ht'
    obtain ⟨a, ⟨haF, haO⟩, hat⟩ := exists_mem_specializes_of_mem_closure_scheme hFcl
      ((s.isClosed_p i hlt).preimage (s.σ i hlt).continuous).isOpen_compl ht'
    have haT : a ∈ (s.transformedSubscheme C (i + 1)).support := by
      change a ∈ ((s.transformedSubscheme C (i + 1)).support : Set (s.S (i + 1)))
      rw [hT]
      exact subset_closure ⟨haF, haO⟩
    refine ⟨a, haT, fun hax => ?_, hat⟩
    have hacl := isClosed_of_mem_transform sS s C hC (i + 1) hi hx haT hax
    have : t = a := by
      have := specializes_iff_mem_closure.mp hat
      rwa [hacl.closure_eq, Set.mem_singleton_iff] at this
    exact haO (this ▸ hz)
  · obtain ⟨g, hgT, hgx, hgu⟩ := H _ hσt (by rw [← hπ]; exact htx) hz
    have hgp : g ≠ s.p i := by
      rintro rfl
      apply hz
      have := specializes_iff_mem_closure.mp hgu
      rwa [(s.isClosed_p i hlt).closure_eq, Set.mem_singleton_iff] at this
    obtain ⟨g', hg'⟩ := exists_apply_eq_of_isIso_restrict (s.σ i hlt)
      (U := Kollar.complPoint (s.isClosed_p i hlt)) ((mem_complPoint_iff _ _).mpr hgp)
    have hg'U : s.σ i hlt g' ∈ Kollar.complPoint (s.isClosed_p i hlt) :=
      (mem_complPoint_iff _ _).mpr (hg' ▸ hgp)
    refine ⟨g', ?_, ?_, ?_⟩
    · change g' ∈ ((s.transformedSubscheme C (i + 1)).support : Set (s.S (i + 1)))
      rw [hT]
      refine subset_closure ⟨?_, ?_⟩
      · change s.σ i hlt g' ∈ ((s.transformedSubscheme C i).support : Set (s.S i))
        rw [hg']; exact hgT
      · change s.σ i hlt g' ∉ ({s.p i} : Set (s.S i))
        rw [hg']; exact hgp
    · rw [hπ, hg']; exact hgx
    · rw [specializes_iff_of_isIso_restrict (s.σ i hlt) hg'U ((mem_complPoint_iff _ _).mpr hz),
        hg']
      exact hgu

include sS in
/-- Once the sequence has blown up the point over `x`, every point of the birational transform over
`x` is a specialization of a point of the transform not over `x`. -/
private theorem exists_generization_off_fibre (C : S₀.IdealSheafData)
    (hC : topologicalKrullDim (C.support : Set S₀) = 1) {x : S₀} (hx : IsClosed ({x} : Set S₀))
    (j : ℕ) (hj : (j : ℕ∞) < s.length) (hjx : s.π j hj.le (s.p j) = x)
    (hjmin : ∀ (i : ℕ) (hi : (i : ℕ∞) < s.length), i < j → s.π i hi.le (s.p i) ≠ x)
    (i : ℕ) (hji : j < i) (hi : (i : ℕ∞) ≤ s.length) (t : s.S i)
    (ht : t ∈ (s.transformedSubscheme C i).support) (htx : s.π i hi t = x) :
    ∃ g ∈ (s.transformedSubscheme C i).support, s.π i hi g ≠ x ∧ g ⤳ t := by
  induction i, hji using Nat.le_induction with
  | base =>
    refine exists_generization_off_fibre_succ sS s C hC hx j hi ?_ t ht htx
    intro u _ hux hup
    exact absurd (eq_of_π_eq_of_le sS s j hjmin j hj.le le_rfl u (s.p j) hux hjx) hup
  | succ i hji ih =>
    refine exists_generization_off_fibre_succ sS s C hC hx i hi ?_ t ht htx
    intro u hu hux _
    exact ih (PointBlowupSequence.coe_lt_of_succ_le hi).le u hu hux

include sS in
/-- Every closed point of every stage has a proper generization. -/
private theorem exists_specializes_ne_of_isClosed :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length) (q : s.S i), IsClosed ({q} : Set (s.S i)) →
      ∃ a, a ⤳ q ∧ a ≠ q
  | 0, hi, q, hq => by
    haveI := SmoothOfRelativeDimension.smooth 2 sS
    have hq' : IsClosed ({s.zeroIso.hom q} : Set S₀) := by
      rw [← Set.image_singleton]; exact s.zeroIso.hom.homeomorph.isClosedMap _ hq
    have h := trdegDim_add_ringKrullDim_eq_two sS (s.zeroIso.hom q)
    rw [trdegDim_eq_zero_of_isClosed sS hq', ringKrullDim_stalk_eq_coheight] at h
    have hc : Order.coheight (s.zeroIso.hom q) ≠ 0 := by
      intro h0; rw [h0] at h; norm_num at h
    obtain ⟨b, hb⟩ := not_isMax_iff.mp (Order.coheight_eq_zero.not.mp hc)
    have hbs : b ⤳ s.zeroIso.hom q := Scheme.le_iff_specializes.mp hb.le
    refine ⟨s.zeroIso.inv b, ?_, ?_⟩
    · have e : s.zeroIso.inv (s.zeroIso.hom q) = q := by
        rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
      have := hbs.map s.zeroIso.inv.continuous
      rwa [e] at this
    · intro h
      apply hb.ne'
      rw [← h, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
  | i + 1, hi, q, hq => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    haveI := isLocallyNoetherian_S sS s i hlt.le
    haveI := isProper_σ s i hlt
    haveI := isIso_σ_restrict s i hlt
    by_cases hz : s.σ i hlt q = s.p i
    · obtain ⟨a, ha, hane⟩ := exists_specializes_σ_ne sS s i hlt q
      exact ⟨a, ha, fun h => hane (h ▸ hz)⟩
    · have hσq : IsClosed ({s.σ i hlt q} : Set (s.S i)) := by
        rw [← Set.image_singleton]; exact (s.σ i hlt).isClosedMap _ hq
      obtain ⟨b, hb, hbne⟩ := exists_specializes_ne_of_isClosed i hlt.le _ hσq
      have hbp : b ≠ s.p i := by
        rintro rfl
        apply hz
        have := specializes_iff_mem_closure.mp hb
        rwa [(s.isClosed_p i hlt).closure_eq, Set.mem_singleton_iff] at this
      obtain ⟨b', hb'⟩ := exists_apply_eq_of_isIso_restrict (s.σ i hlt)
        (U := Kollar.complPoint (s.isClosed_p i hlt)) ((mem_complPoint_iff _ _).mpr hbp)
      refine ⟨b', ?_, fun h => hbne (by rw [← hb', h])⟩
      rw [specializes_iff_of_isIso_restrict (s.σ i hlt)
        ((mem_complPoint_iff _ _).mpr (hb' ▸ hbp)) ((mem_complPoint_iff _ _).mpr hz), hb']
      exact hb

include sS in
/-- The fibre of `σ_i` over its centre is connected. -/
private theorem isConnected_preimage_σ_singleton (i : ℕ) (hi : (i : ℕ∞) < s.length) :
    _root_.IsConnected (s.σ i hi ⁻¹' {s.p i}) := by
  haveI := SmoothOfRelativeDimension.smooth 2 sS
  haveI := smooth_π_comp sS s i hi.le
  set I := Kollar.pointIdeal (s.isClosed_p i hi)
  have hsupp : (I.support : Set (s.S i)) = {s.p i} := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hirr : IsIrreducible (I.support : Set (s.S i)) := by
    rw [hsupp]; exact isIrreducible_singleton
  have hcodim : 1 ≤ codimension
      (⟨I.support, hirr, I.support.isClosed⟩ : TopologicalSpace.IrreducibleCloseds (s.S i)) := by
    have heq : (⟨I.support, hirr, I.support.isClosed⟩ :
        TopologicalSpace.IrreducibleCloseds (s.S i)) =
        TopologicalSpace.IrreducibleCloseds.closureSingleton (s.p i) := by
      ext1
      change (I.support : Set (s.S i)) = closure {s.p i}
      rw [hsupp, (s.isClosed_p i hi).closure_eq]
    rw [heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
    obtain ⟨a, ha, hane⟩ :=
      exists_specializes_ne_of_isClosed sS s i hi.le (s.p i) (s.isClosed_p i hi)
    have hlt : s.p i < a := MMP.Intersection.lt_of_specializes_of_ne ha (Ne.symm hane)
    rw [ENat.one_le_iff_ne_zero, ne_eq, Order.coheight_eq_zero]
    exact fun hmax => hmax.not_lt hlt
  have hsb := isSmoothBlowup_vanishingIdeal_singleton (s.π i hi.le ≫ sS) (s.isClosed_p i hi)
  obtain ⟨z, hz⟩ : ∃ z : I.subscheme, I.subschemeι z = s.p i := by
    have : s.p i ∈ Set.range I.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, hsupp]; rfl
    exact this
  have hconn := MMP.Resolution.isConnected_preimage_exceptionalSubschemeMap
    (s.π i hi.le ≫ sS) I hsb hirr hcodim z
  have huniv : (Stacks.AlgebraicGeometry.exceptionalSubschemeMap I) ⁻¹' {z} = Set.univ := by
    refine Set.eq_univ_of_forall fun e => ?_
    apply I.subschemeι.isEmbedding.injective
    have : I.subschemeι ((Stacks.AlgebraicGeometry.exceptionalSubschemeMap I) e) ∈
        (I.support : Set (s.S i)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨_, rfl⟩
    rw [hsupp] at this
    rw [this, hz]
  rw [huniv] at hconn
  have hE : ((exceptionalIdeal I).support : Set (blowUp I)) = blowUpToBase I ⁻¹' {s.p i} := by
    rw [← compl_inj_iff, ← MMP.Resolution.Kollar.preimage_compl_eq_compl_support_exceptionalIdeal]
    rfl
  have hEc : _root_.IsConnected (blowUpToBase I ⁻¹' {s.p i}) := by
    rw [← hE, ← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
    exact hconn.image _ (Scheme.Hom.continuous _).continuousOn
  have := (s.blowupIso i hi).hom.homeomorph.isConnected_preimage.mpr hEc
  exact this

include sS in
/-- The fibre of every stage over a closed point is preconnected. -/
private theorem isPreconnected_preimage_π_singleton {x : S₀} (hx : IsClosed ({x} : Set S₀)) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length), _root_.IsPreconnected ((s.π i hi).base ⁻¹' {x})
  | 0, hi => by
    refine Set.Subsingleton.isPreconnected fun t ht t' ht' => ?_
    exact s.zeroIso.hom.homeomorph.injective (ht.trans ht'.symm)
  | i + 1, hi => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    haveI := isLocallyNoetherian_S sS s i hlt.le
    haveI := isProper_σ s i hlt
    haveI := isIso_σ_restrict s i hlt
    have hpre : (s.π (i + 1) hi).base ⁻¹' {x} =
        s.σ i hlt ⁻¹' ((s.π i hlt.le).base ⁻¹' {x}) := rfl
    rw [hpre]
    refine isPreconnected_preimage_of_isClosedMap (s.σ i hlt).continuous
      (s.σ i hlt).isClosedMap (hx.preimage (s.π i hlt.le).base.hom.continuous)
      (isPreconnected_preimage_π_singleton hx i hlt.le) ?_
    intro y _
    by_cases hyp : y = s.p i
    · subst hyp
      exact isConnected_preimage_σ_singleton sS s i hlt
    · obtain ⟨q, hq⟩ := exists_apply_eq_of_isIso_restrict (s.σ i hlt)
        (U := Kollar.complPoint (s.isClosed_p i hlt)) ((mem_complPoint_iff _ _).mpr hyp)
      have : s.σ i hlt ⁻¹' {y} = {q} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun hz => eq_of_apply_eq_of_isIso_restrict (s.σ i hlt)
          (U := Kollar.complPoint (s.isClosed_p i hlt))
          ((mem_complPoint_iff _ _).mpr (hz ▸ hyp)) (hz.trans hq.symm), fun hz => hz ▸ hq⟩
      rw [this]
      exact isConnected_singleton

end Invariants

/-! ### Primes of a local ring at a point of a simple normal crossing divisor -/

section LocalPrimes

/-- A strictly monotone integer function bounded by `b` bounds the coheight: chains above `x` have
length at most `b - f x`. -/
private theorem coheight_le_of_strictMono {α : Type*} [Preorder α] (f : α → ℤ) (hf : StrictMono f)
    {b : ℤ} (hb : ∀ y, f y ≤ b) : ∀ (n : ℕ) (x : α), b - f x ≤ n → Order.coheight x ≤ n
  | 0, x, hx => by
    rw [Order.coheight_le_coe_iff]
    intro y hy
    have := hf hy
    have := hb y
    omega
  | n + 1, x, hx => by
    rw [Order.coheight_le_coe_iff]
    intro y hy
    have := hf hy
    have h := coheight_le_of_strictMono f hf hb n y (by omega)
    exact lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self n)

variable {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g]

/-- If `tr.deg_k κ(y) ≤ 2` everywhere, then `dim 𝒪_{X,z} + tr.deg_k κ(z) ≤ 2`. -/
private theorem coheight_le_of_trdegDim_le_two (hb : ∀ y, trdegDim g y ≤ 2) (z : X) (n : ℕ)
    (hn : 2 - trdegDim g z ≤ n) : Order.coheight z ≤ n :=
  coheight_le_of_strictMono (trdegDim g) (fun a b hab => trdegDim_lt g
    (Scheme.le_iff_specializes.mp hab.le) (fun h => hab.ne h.symm)) hb n z hn

/-- At a closed point `l` where a closed subscheme `D` has simple normal crossings with respect to
coordinates `w`, the prime of a proper generization `z ∈ D` of `l` is one of the coordinate primes
`(w_j)`, provided `tr.deg_k κ(y) ≤ 2` everywhere. -/
private theorem exists_primeOfSpecializes_eq_span [IsLocallyNoetherian X]
    (hb : ∀ y, trdegDim g y ≤ 2) {l : X} (hl : IsClosed ({l} : Set X)) {D : X.IdealSheafData}
    {d : ℕ} {U : X.Opens} (hlU : l ∈ U) (w : Fin d → Γ(X, U)) (m : Fin d → ℕ)
    (hrsp : MMP.Mori.IsRegularSystemOfParameters fun i => (X.presheaf.germ U l hlU).hom (w i))
    (hst : IdealSheafData.stalk D l = Ideal.span {(X.presheaf.germ U l hlU).hom (∏ i, w i ^ m i)})
    {z : X} (hz : z ⤳ l) (hzl : z ≠ l) (hzD : z ∈ D.support) :
    ∃ j, MMP.Intersection.primeOfSpecializes hz =
      Ideal.span {(X.presheaf.germ U l hlU).hom (w j)} := by
  set P := MMP.Intersection.primeOfSpecializes hz
  have hDP := (mem_support_iff_stalk_le_primeOfSpecializes D hz).mp hzD
  rw [hst, Ideal.span_le, Set.singleton_subset_iff, map_prod] at hDP
  simp only [map_pow] at hDP
  obtain ⟨j, -, hj⟩ := MMP.Resolution.exists_mem_of_prod_pow_mem hDP
  refine ⟨j, ?_⟩
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hrsp
  haveI : IsDomain (X.presheaf.stalk l) := IsRegularLocalRing.isDomain _
  haveI hprime := MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hrsp j
  have hne0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hrsp j
  have hle : Ideal.span {(X.presheaf.germ U l hlU).hom (w j)} ≤ P :=
    (Ideal.span_singleton_le_iff_mem _).mpr hj
  -- `ht P = dim 𝒪_{X,z} ≤ 1`
  have hδl := trdegDim_eq_zero_of_isClosed g hl
  have hδz := trdegDim_lt g hz hzl
  have hcoh : Order.coheight z ≤ 1 := coheight_le_of_trdegDim_le_two g hb z 1 (by omega)
  have hhtP : P.height ≤ 1 := by
    let := (X.presheaf.stalkSpecializes hz).hom.toAlgebra
    have := MMP.Intersection.isLocalization_stalkSpecializes hz
    have e := IsLocalization.AtPrime.ringKrullDim_eq_height P (X.presheaf.stalk z)
    rw [ringKrullDim_stalk_eq_coheight] at e
    have e' : Order.coheight z = P.height := by exact_mod_cast e
    exact e' ▸ hcoh
  by_contra hne
  have hlt : Ideal.span {(X.presheaf.germ U l hlU).hom (w j)} < P :=
    lt_of_le_of_ne hle (Ne.symm hne)
  have h0 : (⊥ : Ideal (X.presheaf.stalk l)) < Ideal.span {(X.presheaf.germ U l hlU).hom (w j)} :=
    bot_lt_iff_ne_bot.mpr (by rwa [ne_eq, Ideal.span_singleton_eq_bot])
  have h1 := Ideal.height_strict_mono_of_isPrime h0
  have h2 := Ideal.height_strict_mono_of_isPrime hlt
  rw [Ideal.height_bot] at h1
  have : (2 : ℕ∞) ≤ P.height := by
    have := Order.add_one_le_of_lt h1
    have := Order.add_one_le_of_lt h2
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ _ := by gcongr
      _ ≤ _ := this
  exact absurd (this.trans hhtP) (by norm_num)

end LocalPrimes

section Geometry

variable {k : Type u} [Field k] [CharZero k] {S₀ : Scheme.{u}} (sS : S₀ ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 2 sS]
    (C : S₀.IdealSheafData) [IsReduced C.subscheme]
    (x : S₀) (s : PointBlowupSequence S₀) (n : ℕ) (hn : s.length = n)

/-- In a space `X`, a closed subset `F` that is noetherian as a subspace has only finitely many
maximal irreducible subsets: they are the images of the irreducible components of `F`. -/
private theorem finite_setOf_maximal_isIrreducible {X : Type*} [TopologicalSpace X] {F : Set X}
    (hF : IsClosed F) [TopologicalSpace.NoetherianSpace F] :
    {E : Set X | Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ F) E}.Finite := by
  classical
  have hfin := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := F)).image
    (fun C => (Subtype.val '' C : Set X))
  refine hfin.subset fun E hE' => ?_
  have hE : Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ F) E := hE'
  have hclosed : ∀ z ∈ (Subtype.val '' ·) '' irreducibleComponents F, IsClosed z := by
    rintro _ ⟨C, hC, rfl⟩
    exact hF.isClosedMap_subtype_val _ (isClosed_of_mem_irreducibleComponents C hC)
  have hcov : E ⊆ ⋃₀ ((Subtype.val '' ·) '' irreducibleComponents F) := by
    intro e he
    have heF := hE.prop.2 he
    obtain ⟨C, hC, hmem⟩ : ∃ C ∈ irreducibleComponents F, (⟨e, heF⟩ : F) ∈ C :=
      ⟨irreducibleComponent _, irreducibleComponent_mem_irreducibleComponents _,
        mem_irreducibleComponent⟩
    exact ⟨_, ⟨C, hC, rfl⟩, ⟨_, hmem, rfl⟩⟩
  obtain ⟨z, hz, hEz⟩ := (isIrreducible_iff_sUnion_isClosed.mp hE.prop.1) hfin.toFinset
    (by simpa using hclosed) (by simpa using hcov)
  simp only [Set.Finite.mem_toFinset] at hz
  obtain ⟨C, hC, rfl⟩ := hz
  have hirr : IsIrreducible (Subtype.val '' C : Set X) :=
    hC.1.image _ continuous_subtype_val.continuousOn
  exact ⟨C, hC, (hE.eq_of_le ⟨hirr, by rintro _ ⟨y, _, rfl⟩; exact y.2⟩ hEz).symm⟩

/-- Over a locally noetherian base, every stage of a point blowup sequence is locally noetherian
and its map to the base is proper. -/
private theorem isLocallyNoetherian_and_isProper_π {S₀ : Scheme.{u}} [IsLocallyNoetherian S₀]
    (s : PointBlowupSequence S₀) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length), IsLocallyNoetherian (s.S i) ∧ IsProper (s.π i hi)
  | 0, _ => by
    have : IsLocallyNoetherian (s.S 0) := isLocallyNoetherian_of_isOpenImmersion s.zeroIso.hom
    exact ⟨this, by simp only [PointBlowupSequence.π]; infer_instance⟩
  | i + 1, hi => by
    obtain ⟨h1, h2⟩ :=
      isLocallyNoetherian_and_isProper_π s i (PointBlowupSequence.coe_lt_of_succ_le hi).le
    have := isProper_σ s i (PointBlowupSequence.coe_lt_of_succ_le hi)
    have : IsLocallyNoetherian (s.S (i + 1)) :=
      LocallyOfFiniteType.isLocallyNoetherian (s.σ i (PointBlowupSequence.coe_lt_of_succ_le hi))
    exact ⟨this, by simp only [PointBlowupSequence.π]; infer_instance⟩

/-- The fibre of a quasi-compact morphism out of a locally noetherian scheme is a noetherian
space. -/
private theorem noetherianSpace_preimage_singleton {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [QuasiCompact f] (y : Y) :
    TopologicalSpace.NoetherianSpace (f.base ⁻¹' {y} : Set X) := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  have hc : IsCompact (f.base ⁻¹' (U : Set Y)) :=
    QuasiCompact.isCompact_preimage _ U.2 hU.isCompact
  haveI : CompactSpace (f ⁻¹ᵁ U).toScheme := isCompact_iff_compactSpace.mp hc
  haveI : AlgebraicGeometry.IsNoetherian (f ⁻¹ᵁ U).toScheme := ⟨⟩
  haveI : TopologicalSpace.NoetherianSpace ((f ⁻¹ᵁ U : X.Opens) : Set X) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (f ⁻¹ᵁ U).toScheme)
  refine TopologicalSpace.NoetherianSpace.of_subset (W := ((f ⁻¹ᵁ U : X.Opens) : Set X)) ?_
  intro z hz
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
  change f.base z ∈ U
  rw [hz]; exact hyU

/-- There are finitely many exceptional curves over `x`. -/
private theorem finite_exceptionalCurves [IsLocallyNoetherian S₀]
    (hx : IsClosed ({x} : Set S₀)) :
    Set.Finite {E : Set (s.S n) |
      Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) E} := by
  obtain ⟨h1, h2⟩ := isLocallyNoetherian_and_isProper_π s n hn.ge
  haveI := noetherianSpace_preimage_singleton (s.π n hn.ge) x
  exact finite_setOf_maximal_isIrreducible (hx.preimage (s.π n hn.ge).base.hom.continuous)

/-- A finite family of nonempty closed sets with preconnected union, joined by any relation that
holds between distinct members that meet, forms a preconnected graph. -/
private theorem preconnected_fromRel_of_isPreconnected_iUnion {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Finite ι] (V : ι → Set X) (hcl : ∀ i, IsClosed (V i))
    (hne : ∀ i, (V i).Nonempty) (hF : IsPreconnected (⋃ i, V i))
    (R : ι → ι → Prop) (hR : ∀ i j, i ≠ j → (V i ∩ V j).Nonempty → R i j) :
    (SimpleGraph.fromRel R).Preconnected := by
  classical
  intro r
  by_contra! hcon
  obtain ⟨t, ht⟩ := hcon
  set A : Set ι := {i | (SimpleGraph.fromRel R).Reachable r i}
  have hadj : ∀ i j, i ∈ A → j ∉ A → V i ∩ V j = ∅ := by
    intro i j hi hj
    by_contra h
    have hij : i ≠ j := by rintro rfl; exact hj hi
    exact hj (hi.trans (SimpleGraph.Adj.reachable
      (SimpleGraph.fromRel_adj _ _ _ |>.mpr
        ⟨hij, Or.inl (hR i j hij (Set.nonempty_iff_ne_empty.mpr h))⟩)))
  have hU : IsClosed (⋃ i ∈ A, V i) := (Set.toFinite A).isClosed_biUnion fun i _ => hcl i
  have hW : IsClosed (⋃ i ∈ Aᶜ, V i) := (Set.toFinite Aᶜ).isClosed_biUnion fun i _ => hcl i
  have hcov : (⋃ i, V i) ⊆ (⋃ i ∈ A, V i) ∪ ⋃ i ∈ Aᶜ, V i := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    by_cases h : i ∈ A
    · exact Or.inl (Set.mem_biUnion h hi)
    · exact Or.inr (Set.mem_biUnion h hi)
  have hdisj : (⋃ i, V i) ∩ ((⋃ i ∈ A, V i) ∩ ⋃ i ∈ Aᶜ, V i) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false, not_and]
    rintro - ⟨i, hi, hzi⟩ ⟨j, hj, hzj⟩
    exact (Set.eq_empty_iff_forall_notMem.mp (hadj i j hi hj)) z ⟨hzi, hzj⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hF) _ _ hU hW hcov hdisj with h | h
  · obtain ⟨z, hz⟩ := hne t
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (h (Set.mem_iUnion.mpr ⟨t, hz⟩))
    exact (Set.eq_empty_iff_forall_notMem.mp (hadj i t hi ht)) z ⟨hzi, hz⟩
  · obtain ⟨z, hz⟩ := hne r
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (h (Set.mem_iUnion.mpr ⟨r, hz⟩))
    exact (Set.eq_empty_iff_forall_notMem.mp (hadj r i (SimpleGraph.Reachable.refl r) hi)) z
      ⟨hz, hzi⟩

/-- Every point of a set `F` lies in a maximal irreducible subset of `F`. -/
private theorem exists_maximal_isIrreducible_mem {X : Type*} [TopologicalSpace X] {F : Set X}
    {e : X} (he : e ∈ F) : ∃ E, Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ F) E ∧ e ∈ E := by
  set C : Set F := irreducibleComponent ⟨e, he⟩
  have hC := irreducibleComponent_mem_irreducibleComponents (⟨e, he⟩ : F)
  refine ⟨Subtype.val '' C, ⟨⟨hC.1.image _ continuous_subtype_val.continuousOn, by
    rintro _ ⟨y, _, rfl⟩; exact y.2⟩, fun Z hZ hle => ?_⟩, ⟨_, mem_irreducibleComponent, rfl⟩⟩
  have hZ' : IsIrreducible (Subtype.val ⁻¹' Z : Set F) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨z, hz⟩ := hZ.1.nonempty
      exact ⟨⟨z, hZ.2 hz⟩, hz⟩
    · rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
      obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hu
      obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hv
      obtain ⟨z, hz, hzU, hzW⟩ := hZ.1.2 U W hU hW ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
      exact ⟨⟨z, hZ.2 hz⟩, hz, hzU, hzW⟩
  have := hC.2 hZ' fun y hy => hle ⟨y, hy, rfl⟩
  intro z hz
  exact ⟨⟨z, hZ.2 hz⟩, this hz, rfl⟩

/-- A maximal irreducible subset of a closed set is closed. -/
private theorem isClosed_of_maximal_isIrreducible {X : Type*} [TopologicalSpace X] {F E : Set X}
    (hF : IsClosed F) (hE : Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ F) E) : IsClosed E := by
  have : closure E ⊆ E :=
    hE.2 ⟨hE.1.1.closure, closure_minimal hE.1.2 hF⟩ subset_closure
  exact closure_subset_iff_isClosed.mp this

/-- A nonempty closed subset of a fibre of a proper morphism contains a point whose residue field
is a finite, hence nonzero degree, extension of the residue field below. -/
private theorem exists_mem_residueFieldDegree_ne_zero_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] {Z : Set X} (hZ : IsClosed Z) {y : Y} (hZy : Z ⊆ f.base ⁻¹' {y})
    (hne : Z.Nonempty) : ∃ q ∈ Z, MMP.Mori.residueFieldDegree f q ≠ 0 := by
  have hc : IsCompact Z :=
    (f.isProperMap.isCompact_preimage isCompact_singleton).of_isClosed_subset hZ hZy
  haveI : CompactSpace Z := isCompact_iff_compactSpace.mp hc
  haveI : Nonempty Z := hne.to_subtype
  obtain ⟨⟨q, hq⟩, -, hqcl⟩ := (isClosed_univ (X := Z)).exists_closed_singleton
    Set.univ_nonempty
  have hq' : IsClosed ({q} : Set X) := by
    have := hZ.isClosedMap_subtype_val _ hqcl
    rwa [Set.image_singleton] at this
  refine ⟨q, hq, ?_⟩
  have h : IsClosed ({f.asFiber q} : Set (f.fiber (f q))) := by
    have : (f.fiberι (f q)).base ⁻¹' {q} = {f.asFiber q} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hz
        apply (f.fiberι (f q)).isEmbedding.injective
        rw [hz]; simp
      · rintro rfl; simp
    rw [← this]
    exact hq'.preimage (f.fiberι (f q)).continuous
  have hfin := (isClosed_asFiber_iff_finite_residueField f q).mp h
  letI := (f.residueFieldMap q).hom.toAlgebra
  exact Module.finrank_pos.ne'

include sS in
/-- The exceptional curves over `x`, joined when they meet, form a connected graph. -/
private theorem preconnected_exceptionalCurves [IsLocallyNoetherian S₀]
    (hx : IsClosed ({x} : Set S₀)) :
    (SimpleGraph.fromRel (V := {E : Set (s.S n) //
      Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) E})
      fun E E' => (E.1 ∩ E'.1).Nonempty).Preconnected := by
  have hfin := finite_exceptionalCurves x s n hn hx
  haveI : Finite {E : Set (s.S n) //
      Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) E} := hfin.to_subtype
  have hFcl : IsClosed ((s.π n hn.ge).base ⁻¹' {x}) :=
    hx.preimage (s.π n hn.ge).base.hom.continuous
  have hU : (⋃ E : {E : Set (s.S n) //
      Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) E}, E.1) =
      (s.π n hn.ge).base ⁻¹' {x} := by
    refine Set.Subset.antisymm (Set.iUnion_subset fun E => E.2.1.2) fun e he => ?_
    obtain ⟨E, hE, heE⟩ := exists_maximal_isIrreducible_mem he
    exact Set.mem_iUnion.mpr ⟨⟨E, hE⟩, heE⟩
  refine preconnected_fromRel_of_isPreconnected_iUnion (fun E => E.1)
    (fun E => isClosed_of_maximal_isIrreducible hFcl E.2) (fun E => E.2.1.1.nonempty)
    (by rw [hU]; exact isPreconnected_preimage_π_singleton sS s hx n hn.ge) _ fun _ _ _ hint => hint

include sS in
/-- The strict transform of `C` meets the fibre over `x` in finitely many points. -/
private theorem finite_branchPoints
    (hC : topologicalKrullDim (C.support : Set S₀) = 1)
    (hx : IsClosed ({x} : Set S₀)) (hxC : x ∈ C.support) :
    {l : s.S n | l ∈ (s.transformedSubscheme C n).support ∧ (s.π n hn.ge).base l = x}.Finite := by
  haveI := SmoothOfRelativeDimension.smooth 2 sS
  haveI : IsLocallyNoetherian S₀ := MMP.Resolution.isLocallyNoetherian_of_smooth sS
  obtain ⟨h1, h2⟩ := isLocallyNoetherian_and_isProper_π s n hn.ge
  set B := {l : s.S n | l ∈ (s.transformedSubscheme C n).support ∧ (s.π n hn.ge).base l = x}
  have hBcl : IsClosed B :=
    (s.transformedSubscheme C n).support.isClosed.inter
      (hx.preimage (s.π n hn.ge).base.hom.continuous)
  haveI := noetherianSpace_preimage_singleton (s.π n hn.ge) x
  haveI : TopologicalSpace.NoetherianSpace B :=
    TopologicalSpace.NoetherianSpace.of_subset (W := (s.π n hn.ge).base ⁻¹' {x})
      fun l hl => hl.2
  have hM := finite_setOf_maximal_isIrreducible hBcl
  have hZfin : ∀ Z ∈ {E : Set (s.S n) | Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ B) E},
      Z.Finite := by
    intro Z hZ
    have hZ' : Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ B) Z := hZ
    have hZcl := isClosed_of_maximal_isIrreducible hBcl hZ'
    have hgen := hZ'.1.1.isGenericPoint_genericPoint_closure
    rw [hZcl.closure_eq] at hgen
    have hηB : hZ'.1.1.genericPoint ∈ B := hZ'.1.2 hgen.mem
    have hηcl := isClosed_of_mem_transform sS s C hC n hn.ge hx hηB.1 hηB.2
    rw [← hgen.def, hηcl.closure_eq]
    exact Set.finite_singleton _
  refine (hM.sUnion hZfin).subset fun l hl => ?_
  obtain ⟨Z, hZ, hlZ⟩ := exists_maximal_isIrreducible_mem hl
  exact ⟨Z, hZ, hlZ⟩

include sS in
/-- By simple normal crossings, a point of the strict transform of `C` over `x` lies on at most
one exceptional curve. -/
private theorem eq_of_mem_of_mem_exceptionalCurve
    (hC : topologicalKrullDim (C.support : Set S₀) = 1)
    (hx : IsClosed ({x} : Set S₀)) (hxC : x ∈ C.support)
    (hblow : ∃ (i : ℕ) (hi : (i : ℕ∞) < s.length), (s.π i hi.le).base (s.p i) = x)
    (hsnc : ∀ q : s.S n, (s.π n hn.ge).base q = x →
      HasSNCAt (Scheme.IdealSheafData.vanishingIdeal (C.comap (s.π n hn.ge)).support) q)
    {l : s.S n} (hl : l ∈ (s.transformedSubscheme C n).support) (hlx : (s.π n hn.ge).base l = x)
    {E E' : Set (s.S n)}
    (hE : Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) E)
    (hE' : Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) E')
    (hlE : l ∈ E) (hlE' : l ∈ E') : E = E' := by
  classical
  by_contra hEE
  haveI := SmoothOfRelativeDimension.smooth 2 sS
  haveI := smooth_π_comp sS s n hn.ge
  haveI := locallyOfFiniteType_of_smooth (s.π n hn.ge ≫ sS)
  haveI := isLocallyNoetherian_S sS s n hn.ge
  have hFcl : IsClosed ((s.π n hn.ge).base ⁻¹' {x}) :=
    hx.preimage (s.π n hn.ge).base.hom.continuous
  have hlcl := isClosed_of_mem_transform sS s C hC n hn.ge hx hl hlx
  -- the generic points of `E` and `E'`
  have gen : ∀ {Z : Set (s.S n)},
      Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) Z →
        ∃ η, closure {η} = Z := fun hZ => ⟨hZ.1.1.genericPoint, by
      have h := hZ.1.1.isGenericPoint_genericPoint_closure
      rwa [(isClosed_of_maximal_isIrreducible hFcl hZ).closure_eq] at h⟩
  obtain ⟨η, hη⟩ := gen hE
  obtain ⟨η', hη'⟩ := gen hE'
  have hηl : η ⤳ l := specializes_iff_mem_closure.mpr (hη ▸ hlE)
  have hη'l : η' ⤳ l := specializes_iff_mem_closure.mpr (hη' ▸ hlE')
  have hηx : (s.π n hn.ge) η = x := hE.1.2 (hη ▸ subset_closure rfl)
  have hη'x : (s.π n hn.ge) η' = x := hE'.1.2 (hη' ▸ subset_closure rfl)
  have hηne : η ≠ l := by
    rintro rfl
    apply hEE
    have hEl : E = {η} := by rw [← hη, hlcl.closure_eq]
    exact hE.eq_of_le hE'.1 (by rw [hEl]; exact Set.singleton_subset_iff.mpr hlE')
  have hη'ne : η' ≠ l := by
    rintro rfl
    apply hEE
    have hEl : E' = {η'} := by rw [← hη', hlcl.closure_eq]
    exact (hE'.eq_of_le hE.1 (by rw [hEl]; exact Set.singleton_subset_iff.mpr hlE)).symm
  have hηη' : η ≠ η' := by
    rintro rfl
    exact hEE (hη.symm.trans hη')
  -- a generization of `l` on the transform, off the fibre
  let j := Nat.find hblow
  obtain ⟨hj, hjx⟩ := Nat.find_spec hblow
  have hjmin : ∀ (i : ℕ) (hi : (i : ℕ∞) < s.length), i < j → s.π i hi.le (s.p i) ≠ x :=
    fun i hi hij h => Nat.find_min hblow hij ⟨hi, h⟩
  have hjn : j < n := by
    have := lt_of_lt_of_eq hj hn; exact_mod_cast this
  obtain ⟨γ, hγT, hγx, hγl⟩ :=
    exists_generization_off_fibre sS s C hC hx j hj hjx hjmin n hjn hn.ge l hl hlx
  have hγne : γ ≠ l := fun h => hγx (h ▸ hlx)
  have hγη : γ ≠ η := fun h => hγx (h ▸ hηx)
  have hγη' : γ ≠ η' := fun h => hγx (h ▸ hη'x)
  have hγC := (transform_invariant sS s C hC n hn.ge γ hγT).1
  -- the three generizations lie in the total transform
  have hmemD : ∀ z, (s.π n hn.ge) z ∈ C.support →
      z ∈ (Scheme.IdealSheafData.vanishingIdeal (C.comap (s.π n hn.ge)).support).support := by
    intro z hz
    change z ∈ ((Scheme.IdealSheafData.vanishingIdeal (C.comap (s.π n hn.ge)).support).support :
      Set (s.S n))
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.IdealSheafData.support_comap]
    exact hz
  -- simple normal crossings at `l`
  obtain ⟨d, U, hlU, w, m, hrsp, hstalk⟩ := hsnc l hlx
  have hb := trdegDim_π_le_two sS s n hn.ge
  obtain ⟨j₁, h₁⟩ := exists_primeOfSpecializes_eq_span (s.π n hn.ge ≫ sS) hb hlcl hlU w m hrsp
    (hstalk l hlU) hηl hηne (hmemD η (hηx ▸ hxC))
  obtain ⟨j₂, h₂⟩ := exists_primeOfSpecializes_eq_span (s.π n hn.ge ≫ sS) hb hlcl hlU w m hrsp
    (hstalk l hlU) hη'l hη'ne (hmemD η' (hη'x ▸ hxC))
  obtain ⟨j₃, h₃⟩ := exists_primeOfSpecializes_eq_span (s.π n hn.ge ≫ sS) hb hlcl hlU w m hrsp
    (hstalk l hlU) hγl hγne (hmemD γ hγC)
  have hinj : ∀ {z z' : s.S n} (hz : z ⤳ l) (hz' : z' ⤳ l),
      MMP.Intersection.primeOfSpecializes hz = MMP.Intersection.primeOfSpecializes hz' →
        z = z' := fun hz hz' he =>
    ((MMP.Intersection.specializes_of_primeOfSpecializes_le hz hz' he.le).antisymm
      (MMP.Intersection.specializes_of_primeOfSpecializes_le hz' hz he.ge)).eq
  have h12 : j₁ ≠ j₂ := fun h => hηη' (hinj hηl hη'l (by rw [h₁, h₂, h]))
  have h13 : j₁ ≠ j₃ := fun h => hγη (hinj hγl hηl (by rw [h₁, h₃, h])).symm.symm
  have h23 : j₂ ≠ j₃ := fun h => hγη' (hinj hγl hη'l (by rw [h₂, h₃, h])).symm.symm
  -- `d = dim 𝒪_{S_n,l} ≤ 2`
  have hd : d ≤ 2 := by
    have h := hrsp.2
    rw [ringKrullDim_stalk_eq_coheight] at h
    have hδl := trdegDim_eq_zero_of_isClosed (s.π n hn.ge ≫ sS) hlcl
    have hc := coheight_le_of_trdegDim_le_two (s.π n hn.ge ≫ sS) hb l 2 (by omega)
    have h' : Order.coheight l = (d : ℕ∞) := by exact_mod_cast h
    rw [h'] at hc
    exact_mod_cast hc
  have := j₁.isLt
  have := j₂.isLt
  have := j₃.isLt
  have h12' : j₁.val ≠ j₂.val := fun h => h12 (Fin.ext h)
  have h13' : j₁.val ≠ j₃.val := fun h => h13 (Fin.ext h)
  have h23' : j₂.val ≠ j₃.val := fun h => h23 (Fin.ext h)
  omega

include sS in
/-- Every branch of `C` over `x` lies on exactly one exceptional curve, so the branch sums over
the exceptional curves add up to the total branch sum. -/
private theorem sum_branchSum_eq
    [Fintype {E : Set (s.S n) //
      Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) E}]
    (hC : topologicalKrullDim (C.support : Set S₀) = 1)
    (hx : IsClosed ({x} : Set S₀)) (hxC : x ∈ C.support)
    (hblow : ∃ (i : ℕ) (hi : (i : ℕ∞) < s.length), (s.π i hi.le).base (s.p i) = x)
    (hsnc : ∀ q : s.S n, (s.π n hn.ge).base q = x →
      HasSNCAt (Scheme.IdealSheafData.vanishingIdeal (C.comap (s.π n hn.ge)).support) q)
    (a : s.S n → ℚ) :
    ∑ E : {E : Set (s.S n) //
        Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) E},
      ∑ᶠ (l : s.S n) (_ : l ∈ (s.transformedSubscheme C n).support)
        (_ : (s.π n hn.ge).base l = x) (_ : l ∈ E.1),
          (MMP.Mori.residueFieldDegree (s.π n hn.ge) l : ℚ) * a l =
    ∑ᶠ (l : s.S n) (_ : l ∈ (s.transformedSubscheme C n).support)
      (_ : (s.π n hn.ge).base l = x),
        (MMP.Mori.residueFieldDegree (s.π n hn.ge) l : ℚ) * a l := by
  classical
  set w : s.S n → ℚ := fun l => (MMP.Mori.residueFieldDegree (s.π n hn.ge) l : ℚ) * a l
  have hL := finite_branchPoints sS C x s n hn hC hx hxC
  set L := hL.toFinset
  have hmem : ∀ l, l ∈ L ↔ l ∈ (s.transformedSubscheme C n).support ∧
      (s.π n hn.ge).base l = x := fun l => hL.mem_toFinset
  simp only [finsum_eq_if]
  rw [finsum_eq_sum_of_support_subset _ (s := L) (fun l hl => by
    simp only [Function.mem_support, ne_eq] at hl
    split_ifs at hl with h1 h2
    · exact (hmem l).mpr ⟨h1, h2⟩
    all_goals exact absurd rfl hl)]
  have hE : ∀ E : {E : Set (s.S n) //
      Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) E},
      (∑ᶠ l, if l ∈ (s.transformedSubscheme C n).support then
        (if (s.π n hn.ge).base l = x then (if l ∈ E.1 then w l else 0) else 0) else 0) =
      ∑ l ∈ L, if l ∈ E.1 then w l else 0 := by
    intro E
    rw [finsum_eq_sum_of_support_subset _ (s := L) (fun l hl => by
      simp only [Function.mem_support, ne_eq] at hl
      split_ifs at hl with h1 h2
      · exact (hmem l).mpr ⟨h1, h2⟩
      all_goals exact absurd rfl hl)]
    refine Finset.sum_congr rfl fun l hl => ?_
    obtain ⟨h1, h2⟩ := (hmem l).mp hl
    simp [h1, h2]
  rw [Finset.sum_congr rfl fun E _ => hE E, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  obtain ⟨h1, h2⟩ := (hmem l).mp hl
  obtain ⟨E₀, hE₀, hlE₀⟩ := exists_maximal_isIrreducible_mem (F := (s.π n hn.ge).base ⁻¹' {x})
    (e := l) h2
  rw [Finset.sum_eq_single ⟨E₀, hE₀⟩ (fun E _ hne => ?_) (by simp)]
  · simp [hlE₀, h1, h2, w]
  · rw [if_neg]
    intro hlE
    exact hne (Subtype.ext (eq_of_mem_of_mem_exceptionalCurve sS C x s n hn hC hx hxC hblow
      hsnc h1 h2 E.2 hE₀ hlE hlE₀))

end Geometry

/-- **Balanced branch coefficients on the exceptional curves of a point-blowup sequence.**
Let `S₀` be a smooth surface over a field `k` of characteristic zero, `C ⊆ S₀` a reduced curve
and `x ∈ C` a closed point. Let `s` be a sequence of point blowups of finite length `n`, with
`π : S_n → S₀`, which blows up a point over `x` and whose reduced total transform
`π⁻¹(C)_red` has simple normal crossings at every point over `x`. Let `a` be rational weights
on the points `λ` of the birational transform `C_n` over `x` with `∑_λ [κ(λ) : κ(x)] a_λ = 0`.
Then there are coefficients `c E E' q`, antisymmetric in `E, E'`, such that for every
exceptional curve `E` (irreducible component of `π⁻¹(x)`)
`∑_{E' ≠ E} ∑_{q ∈ E ∩ E'} [κ(q) : κ(x)] c E E' q + ∑_{λ ∈ E} [κ(λ) : κ(x)] a_λ = 0`. -/
@[mmp "lem_mmp_conductor_plane_curve_balanced_flow"]
public theorem exists_balanced_flow_of_sum_residueFieldDegree_mul_eq_zero
    {k : Type u} [Field k] [CharZero k] {S₀ : Scheme.{u}} (sS : S₀ ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 2 sS]
    (C : S₀.IdealSheafData) [IsReduced C.subscheme]
    (hC : topologicalKrullDim (C.support : Set S₀) = 1)
    (x : S₀) (hx : IsClosed ({x} : Set S₀)) (hxC : x ∈ C.support)
    (s : PointBlowupSequence S₀) (n : ℕ) (hn : s.length = n)
    (hblow : ∃ (i : ℕ) (hi : (i : ℕ∞) < s.length), (s.π i hi.le).base (s.p i) = x)
    (hsnc : ∀ q : s.S n, (s.π n hn.ge).base q = x →
      HasSNCAt (Scheme.IdealSheafData.vanishingIdeal (C.comap (s.π n hn.ge)).support) q)
    (a : s.S n → ℚ)
    (ha : ∑ᶠ (l : s.S n) (_ : l ∈ (s.transformedSubscheme C n).support)
      (_ : (s.π n hn.ge).base l = x),
        (Mori.residueFieldDegree (s.π n hn.ge) l : ℚ) * a l = 0) :
    ∃ c : Set (s.S n) → Set (s.S n) → s.S n → ℚ,
      (∀ E E' q, c E' E q = -c E E' q) ∧
      ∀ E : Set (s.S n),
        Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) E →
        (∑ᶠ (E' : Set (s.S n))
            (_ : Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) E')
            (_ : E' ≠ E) (q : s.S n) (_ : q ∈ E ∩ E'),
              (Mori.residueFieldDegree (s.π n hn.ge) q : ℚ) * c E E' q) +
          ∑ᶠ (l : s.S n) (_ : l ∈ (s.transformedSubscheme C n).support)
            (_ : (s.π n hn.ge).base l = x) (_ : l ∈ E),
              (Mori.residueFieldDegree (s.π n hn.ge) l : ℚ) * a l = 0 := by
  classical
  haveI := SmoothOfRelativeDimension.smooth 2 sS
  haveI : IsLocallyNoetherian S₀ := LocallyOfFiniteType.isLocallyNoetherian sS
  haveI := (isLocallyNoetherian_and_isProper_π s n hn.ge).2
  letI : Fintype {E : Set (s.S n) //
      Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (s.π n hn.ge).base ⁻¹' {x}) E} :=
    (finite_exceptionalCurves x s n hn hx).fintype
  have hFcl : IsClosed ((s.π n hn.ge).base ⁻¹' {x}) :=
    hx.preimage (s.π n hn.ge).base.hom.continuous
  obtain ⟨f, hfa, hf0, hfb⟩ := exists_flow (preconnected_exceptionalCurves sS x s n hn hx) _
    ((sum_branchSum_eq sS C x s n hn hC hx hxC hblow hsnc a).trans ha)
  obtain ⟨c, hca, hc⟩ := exists_pointCoeff_of_flow f hfa
    (fun E E' h => hf0 E E' fun hadj => by
      rcases (SimpleGraph.fromRel_adj _ _ _).mp hadj with ⟨-, h' | h'⟩
      · exact h'.ne_empty h
      · exact h'.ne_empty (Set.inter_comm E.1 E'.1 ▸ h))
    (fun q => (MMP.Mori.residueFieldDegree (s.π n hn.ge) q : ℚ)) fun E E' hE hE' hne =>
      let ⟨q, hq, hd⟩ := exists_mem_residueFieldDegree_ne_zero_of_isProper (s.π n hn.ge)
        ((isClosed_of_maximal_isIrreducible hFcl hE).inter
          (isClosed_of_maximal_isIrreducible hFcl hE'))
        (Set.inter_subset_left.trans hE.1.2) hne
      ⟨q, hq, Nat.cast_ne_zero.mpr hd⟩
  exact ⟨c, hca, fun E hE => by rw [hc E hE]; exact hfb ⟨E, hE⟩⟩

end Resolution

namespace Fourfold

open TopologicalSpace MMP MMP.Mori
open scoped MMP.SubschemeOver
open Stacks.Intersection.ExteriorProductProjections
  (topologicalKrullDim_closure_of_relativeDimension_eq
    relativeDimension_eq_of_topologicalKrullDim_closure)

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A sum over the generic points of a set, which is at most one point, commutes with scaling. -/
private theorem finsum_isGenericPoint_mul {X : Scheme.{0}} (T : Set X) (P : X → Prop) (d : X → ℚ)
    (k : ℚ) :
    ∑ᶠ (z : X) (_ : IsGenericPoint z T) (_ : P z), d z * k =
      (∑ᶠ (z : X) (_ : IsGenericPoint z T) (_ : P z), d z) * k := by
  classical
  by_cases h : ∃ z, IsGenericPoint z T ∧ P z
  · obtain ⟨z, hz, hP⟩ := h
    have key : ∀ g : X → ℚ, ∑ᶠ (y : X) (_ : IsGenericPoint y T) (_ : P y), g y = g z := by
      intro g
      rw [finsum_eq_single _ z]
      · simp only [finsum_eq_if, if_pos hz, if_pos hP]
      · intro y hy
        have : ¬ IsGenericPoint y T := fun hy' => hy (hy'.eq hz)
        simp only [finsum_eq_if, if_neg this]
    rw [key, key]
  · push Not at h
    have key : ∀ g : X → ℚ, ∑ᶠ (y : X) (_ : IsGenericPoint y T) (_ : P y), g y = 0 := by
      intro g
      refine finsum_eq_zero_of_forall_eq_zero fun y => ?_
      by_cases hy : IsGenericPoint y T
      · simp only [finsum_eq_if, if_pos hy, if_neg (h y hy)]
      · simp only [finsum_eq_if, if_neg hy]
    rw [key, key, zero_mul]

/-- Evaluating a linear form on a linear combination. -/
private theorem apply_linearCombination_eq_finsum {α M : Type*} [AddCommMonoid M] [Module ℚ M]
    (D : α →₀ ℚ) (g : α → M) (φ : M →ₗ[ℚ] ℚ) :
    φ (Finsupp.linearCombination ℚ g D) = ∑ᶠ a, D a * φ (g a) := by
  rw [Finsupp.linearCombination_apply, map_finsuppSum,
    finsum_eq_sum_of_support_subset _ (s := D.support) ?_]
  · simp [Finsupp.sum, map_smul]
  · intro a ha
    by_contra h
    exact ha (by simp [Finsupp.notMem_support_iff.mp h])

/-- The source of a resolution of a complex variety is a Noetherian scheme. -/
private theorem isNoetherian_of_isResolution {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsIntegral Y] (r : Z ⟶ Y) (hr : MMP.Intersection.IsResolution sY r) : IsNoetherian Z := by
  haveI : AlgebraicGeometry.IsVariety ℂ (r ≫ sY) := hr.2.1
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (r ≫ sY)
  haveI : CompactSpace Z := (quasiCompact_iff_compactSpace (r ≫ sY)).mp inferInstance
  exact (isNoetherian_iff Z).mpr ⟨inferInstance, inferInstance⟩

open scoped Classical in
/-- The coefficient at a point `v` of delta-dimension two of the push-forward of the prime cycle
`[x]` of a point of delta-dimension two: the residue degree of `f` at `x` if `f x = v`, and `0`
otherwise. -/
private theorem rationalCoeff_rationalProperPushforward_rationalPointCycle {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (sY : Y ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sX x = 2) (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2) :
    Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) sY 2 v
        (Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) sX sY 2 f hf
          (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) sX 2 x hx)) =
      if f.base x = v then (f.residueDegree x : ℚ) else 0 := by
  classical
  rw [Chow.rationalPointCycle, Chow.rationalCoeff_rationalProperPushforward_tmul, one_mul]
  have hterm : ∀ y : X, (Stacks.Chow.pointCycle (Stacks.Chow.fieldChowSituation ℂ) sX 2 x hx).1 y *
      (if Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction sX y =
          Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction sY
            (f.base y)
        then (f.residueDegree y : ℤ) else 0) =
      if y = x then (if f.base x = v then (f.residueDegree x : ℤ) else
        (if Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction sX x
            = Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction sY
              (f.base x) then (f.residueDegree x : ℤ) else 0)) else 0 := by
    intro y
    rw [Stacks.Chow.pointCycle_apply]
    by_cases hy : y = x
    · subst hy
      rw [if_pos rfl, if_pos rfl, one_mul]
      by_cases hfy : f.base y = v
      · rw [if_pos hfy, if_pos (by rw [hx, hfy, hv])]
      · rw [if_neg hfy]
    · rw [if_neg hy, if_neg hy, zero_mul]
  simp_rw [hterm]
  rw [finsum_eq_single _ x fun y hy => by simp [hy], finsum_eq_if, if_pos rfl]
  by_cases hfx : f.base x = v
  · rw [if_pos (show x ∈ f.base ⁻¹' {v} from hfx), if_pos hfx, if_pos hfx]
    push_cast
    rfl
  · rw [if_neg (show x ∉ f.base ⁻¹' {v} from hfx), if_neg hfx, Int.cast_zero]

open scoped Classical in
/-- The coefficient at a point `v` of delta-dimension two of the push-forward of the surface cycle
of a prime divisor `P`: the residue degree of `f` at the generic point of `P` if `P` is a surface
whose generic point maps to `v`, and `0` otherwise. -/
private theorem rationalCoeff_rationalProperPushforward_primeCycle {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (sY : Y ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX)
    (P : MMP.Mori.PrimeDivisor X) (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2) :
    Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) sY 2 v
        (Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) sX sY 2 f hf
          (if h : Stacks.Chow.relativeDimension
              (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction sX P.genericPoint = 2 then
            Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) sX 2 P.genericPoint h
          else 0)) =
      if Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction sX
          P.genericPoint = 2 ∧ f.base P.genericPoint = v then
        (f.residueDegree P.genericPoint : ℚ) else 0 := by
  by_cases h : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sX P.genericPoint = 2
  · rw [dif_pos h, rationalCoeff_rationalProperPushforward_rationalPointCycle sX sY f hf _ h v hv]
    simp only [h, true_and]
  · rw [dif_neg h, if_neg fun h' => h h'.1, map_zero, map_zero]

/-- On an integral scheme of finite type over `ℂ` of dimension four, height and coheight of a
point add up to four. -/
private theorem height_add_coheight_eq_four {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [LocallyOfFiniteType sX] (hX : topologicalKrullDim X = 4) (x : X) :
    Order.height x + Order.coheight x = 4 := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  have h1 := MMP.height_add_coheight_eq_krullDim ℂ x
  have h4 : Order.krullDim X = 4 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hX
  rw [h4] at h1
  exact WithBot.coe_injective h1

/-- Over `ℂ`, a point of delta-dimension two has height two. -/
private theorem height_eq_two_of_relativeDimension_eq_two {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sY] (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2) : Order.height v = 2 := by
  have h := topologicalKrullDim_closure_of_relativeDimension_eq ℂ sY v 2 hv
  rw [AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height] at h
  exact WithBot.coe_injective h

/-- On a fourfold of finite type over `ℂ`, a point of delta-dimension two has codimension two. -/
private theorem coheight_eq_two_of_relativeDimension_eq_two {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsIntegral Y] [LocallyOfFiniteType sY] (hY : topologicalKrullDim Y = 4) (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2) : Order.coheight v = 2 := by
  have h := height_add_coheight_eq_four sY hY v
  rw [height_eq_two_of_relativeDimension_eq_two sY v hv] at h
  generalize Order.coheight v = c at h ⊢
  induction c with
  | top => simp at h
  | coe n => norm_cast at h ⊢; omega

/-- An order embedding whose range is a lower set preserves heights. -/
private theorem height_apply_eq_of_isLowerSet {α β : Type*} [Preorder α] [Preorder β] (e : α ↪o β)
    (he : IsLowerSet (Set.range e)) (a : α) : Order.height (e a) = Order.height a := by
  apply le_antisymm _ (Order.height_le_height_apply_of_strictMono e e.strictMono a)
  let f : Set.Iic a ↪o Set.Iic (e a) :=
    { toFun := fun x => ⟨e x.1, e.monotone x.2⟩
      inj' := fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h))
      map_rel_iff' := fun {x y} => e.le_iff_le }
  have hiso : Set.Iic a ≃o Set.Iic (e a) := RelIso.ofSurjective f (by
      rintro ⟨b, hb⟩
      obtain ⟨c, rfl⟩ := he hb ⟨a, rfl⟩
      exact ⟨⟨c, e.le_iff_le.mp hb⟩, rfl⟩)
  have h1 := Order.height_eq_krullDim_Iic a
  have h2 := Order.height_eq_krullDim_Iic (e a)
  rw [Order.krullDim_eq_of_orderIso hiso] at h1
  have : (Order.height (e a) : WithBot ℕ∞) = Order.height a := h2.trans h1.symm
  exact (WithBot.coe_injective this).le

/-- An order embedding below a point `t` raises coheights by at least one. -/
private theorem coheight_add_one_le_of_forall_lt {α β : Type*} [Preorder α] [Preorder β]
    (e : α ↪o β) (t : β) (ht : ∀ x, e x < t) (a : α) :
    Order.coheight a + 1 ≤ Order.coheight (e a) := by
  let f : WithTop α → β := fun x => WithTop.recTopCoe t e x
  have hf : StrictMono f := by
    intro x y hxy
    induction x using WithTop.recTopCoe with
    | top => exact absurd hxy (by simp)
    | coe x =>
      induction y using WithTop.recTopCoe with
      | top => exact ht x
      | coe y => exact e.strictMono (WithTop.coe_lt_coe.mp hxy)
  rw [← Order.coheight_coe_withTop]
  exact Order.coheight_le_coheight_apply_of_strictMono f hf a

/-- A closed embedding of schemes is an order embedding of the specialization orders. -/
private def orderEmbeddingOfIsClosedEmbedding {X Z : Scheme.{0}} (ι : X ⟶ Z)
    (h : Topology.IsClosedEmbedding ι) : X ↪o Z where
  toFun := ι
  inj' := h.injective
  map_rel_iff' := by
    intro a b
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact h.isInducing.specializes_iff

/-- The image of a closed embedding is closed under specialization. -/
private theorem isLowerSet_range_of_isClosedEmbedding {X Z : Scheme.{0}} (ι : X ⟶ Z)
    (h : Topology.IsClosedEmbedding ι) :
    IsLowerSet (Set.range (orderEmbeddingOfIsClosedEmbedding ι h)) := by
  intro a b hba ha
  rw [Scheme.le_iff_specializes] at hba
  exact hba.mem_closed h.isClosed_range ha

/-- On the points of a scheme, a strict specialization is a strict inequality. -/
private theorem lt_of_le_of_ne_scheme {X : Scheme.{0}} {a b : X} (h : a ≤ b) (hne : a ≠ b) :
    a < b :=
  lt_of_le_not_ge h fun h' => hne (by
    rw [Scheme.le_iff_specializes] at h h'
    exact (h'.antisymm h).eq)

/-- A point in the intersection of two distinct prime divisors lies strictly below the generic
point of the first. -/
private theorem lt_genericPoint_of_mem_inter {Z : Scheme.{0}} {E E' : MMP.Mori.PrimeDivisor Z}
    (hne : E ≠ E') {z : Z} (hz : z ∈ E.support ∩ E'.support) : z < E.genericPoint := by
  have hsp : E.genericPoint ⤳ z := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hz.1
  refine lt_of_le_of_ne_scheme (Scheme.le_iff_specializes.mpr hsp) ?_
  rintro rfl
  have hsp' : E'.genericPoint ⤳ E.genericPoint := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hz.2
  by_cases heq : E.genericPoint = E'.genericPoint
  · exact hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective heq)
  · have hlt : E.genericPoint < E'.genericPoint :=
      lt_of_le_of_ne_scheme (Scheme.le_iff_specializes.mpr hsp') heq
    have := Order.coheight_add_one_le hlt
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
    exact absurd this (by decide)

/-- A point of a prime divisor `E` of codimension two in the ambient scheme, strictly below the
generic point of `E`, is the generic point of a prime divisor of `E`. -/
private theorem exists_primeDivisor_genericPoint_eq {Z : Scheme.{0}} [IsIntegral Z]
    (E : MMP.Mori.PrimeDivisor Z) {z : Z} (hzE : z < E.genericPoint)
    (hz : Order.coheight z = 2) :
    ∃ P : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme,
      E.idealSheaf.subschemeι P.genericPoint = z ∧
        Order.height P.genericPoint = Order.height z := by
  set ι := E.idealSheaf.subschemeι
  have hcl : Topology.IsClosedEmbedding ι := ι.isClosedEmbedding
  let e := orderEmbeddingOfIsClosedEmbedding ι hcl
  have hrange : ∀ y : Z, y ∈ E.support → ∃ w, ι w = y := by
    intro y hy
    rw [← Set.mem_range, Scheme.IdealSheafData.range_subschemeι]
    exact hy
  have hEmem : E.genericPoint ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hzmem : z ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
    exact Scheme.le_iff_specializes.mp hzE.le
  obtain ⟨w, rfl⟩ := hrange z hzmem
  obtain ⟨w', hw'⟩ := hrange _ hEmem
  have hgen0 : Order.coheight (genericPoint Z) = 0 :=
    Order.coheight_eq_zero.mpr fun b _ => Scheme.le_iff_specializes.mpr (genericPoint_specializes b)
  have hlt : ∀ x, e x < genericPoint Z := by
    intro x
    refine lt_of_le_of_ne_scheme (Scheme.le_iff_specializes.mpr (genericPoint_specializes _)) ?_
    intro hx
    have hmem : genericPoint Z ∈ E.support := by
      rw [← hx]
      change ι x ∈ (E.idealSheaf.support : Set Z)
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hmem
    have := (hmem.antisymm (genericPoint_specializes _)).eq
    have h1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
    rw [this, hgen0] at h1
    exact absurd h1 (by decide)
  have hup := coheight_add_one_le_of_forall_lt e (genericPoint Z) hlt w
  change _ ≤ Order.coheight (ι w) at hup
  rw [hz] at hup
  have hww' : w < w' := by
    rw [← e.lt_iff_lt]
    change ι w < ι w'
    rw [hw']; exact hzE
  have hlow := Order.coheight_add_one_le hww'
  have hw1 : Order.coheight w = 1 := by
    generalize Order.coheight w = c at hup hlow
    generalize Order.coheight w' = c' at hlow
    induction c with
    | top => simp at hup
    | coe n =>
      induction c' with
      | top => simp at hlow
      | coe m => norm_cast at hup hlow ⊢; omega
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hw1, ?_, ?_⟩
  · exact congrArg ι (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne w hw1)
  · rw [show MMP.Mori.PrimeDivisor.genericPoint _ = w from
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne w hw1]
    exact (height_apply_eq_of_isLowerSet e (isLowerSet_range_of_isClosedEmbedding ι hcl) w).symm

/-- A point of a double intersection `E ∩ E'` of prime divisors of `Z` over the generic point of a
surface `V` of `Y` has codimension two in `Z`. -/
private theorem coheight_eq_two_of_mem_inter {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsIntegral Y] (hY : topologicalKrullDim Y = 4) (r : Z ⟶ Y)
    (hr : MMP.Intersection.IsResolution sY r) (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2)
    {E E' : MMP.Mori.PrimeDivisor Z} (hne : E ≠ E') {z : Z} (hz : z ∈ E.support ∩ E'.support)
    (hzV : r.base z = v) : Order.coheight z = 2 := by
  haveI hYv : MMP.Mori.IsVariety ℂ sY := hr.1
  haveI hZv : MMP.Mori.IsVariety ℂ (r ≫ sY) := hr.2.1
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hr.1
  have hdim : topologicalKrullDim Z = topologicalKrullDim Y :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY) hr.2.2.2.2).symm
  have hle := MMP.Flips.coheight_le_coheight_map sY (r ≫ sY) hYv hZv r rfl hdim z
  rw [hzV, coheight_eq_two_of_relativeDimension_eq_two sY hY v hv] at hle
  have hlow := Order.coheight_add_one_le (lt_genericPoint_of_mem_inter hne hz)
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hlow
  generalize Order.coheight z = c at hle hlow ⊢
  induction c with
  | top => simp at hle
  | coe n => norm_cast at hle hlow ⊢; omega

/-- A point of `Z` of codimension two has dimension two. -/
private theorem height_eq_two_of_coheight_eq_two {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsIntegral Y] (hY : topologicalKrullDim Y = 4) (r : Z ⟶ Y)
    (hr : MMP.Intersection.IsResolution sY r) {z : Z} (hz : Order.coheight z = 2) :
    Order.height z = 2 := by
  haveI hYv : MMP.Mori.IsVariety ℂ sY := hr.1
  haveI hZv : MMP.Mori.IsVariety ℂ (r ≫ sY) := hr.2.1
  haveI : AlgebraicGeometry.IsVariety ℂ (r ≫ sY) := hr.2.1
  haveI : IsIntegral Z := hZv.toIsIntegral
  have hdim : topologicalKrullDim Z = topologicalKrullDim Y :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY) hr.2.2.2.2).symm
  have h := height_add_coheight_eq_four (r ≫ sY) (hdim.trans hY) z
  rw [hz] at h
  generalize Order.height z = c at h ⊢
  induction c with
  | top => simp at h
  | coe n => norm_cast at h ⊢; omega

/-- A closed immersion has residue degree one. -/
private theorem residueDegree_eq_one_of_isClosedImmersion {X Z : Scheme.{0}} (ι : X ⟶ Z)
    [IsClosedImmersion ι] (x : X) : ι.residueDegree x = 1 := by
  letI := (ι.residueFieldMap x).hom.toAlgebra
  have hb : Function.Bijective (algebraMap (Z.residueField (ι x)) (X.residueField x)) :=
    (ConcreteCategory.isIso_iff_bijective (ι.residueFieldMap x)).1
      (residueFieldMap_isIso_of_isClosedImmersion ι x)
  have := (AlgEquiv.ofBijective (Algebra.ofId (Z.residueField (ι x)) (X.residueField x))
    hb).toLinearEquiv.finrank_eq
  rw [Module.finrank_self] at this
  exact this.symm

/-- The residue degree of `E → Z → Y` at a point of a component `E` is the residue degree of
`r` at its image. -/
private theorem residueDegree_subschemeι_comp_eq_residueFieldDegree {Y Z : Scheme.{0}}
    (r : Z ⟶ Y) (E : MMP.Mori.PrimeDivisor Z) (w : E.idealSheaf.subscheme) :
    (E.idealSheaf.subschemeι ≫ r).residueDegree w =
      residueFieldDegree r (E.idealSheaf.subschemeι w) := by
  rw [Stacks.Chow.residueDegree_comp,
    residueDegree_eq_one_of_isClosedImmersion E.idealSheaf.subschemeι, mul_one]
  rfl

/-- A sum over the generic points of a set with a generic point `z₀` is the value at `z₀`. -/
private theorem finsum_isGenericPoint_eq {X : Scheme.{0}} {T : Set X} {z₀ : X}
    (h₀ : IsGenericPoint z₀ T) (P : X → Prop) (d : X → ℚ) :
    ∑ᶠ (z : X) (_ : IsGenericPoint z T) (_ : P z), d z = ∑ᶠ (_ : P z₀), d z₀ := by
  classical
  rw [finsum_eq_single _ z₀]
  · rw [finsum_eq_if, if_pos h₀]
  · intro z hz
    rw [finsum_eq_if, if_neg fun h => hz (h.eq h₀)]

/-- The height of a point of a closed subscheme is its height in the ambient scheme. -/
private theorem height_subschemeι {Z : Scheme.{0}} (I : Z.IdealSheafData) (w : I.subscheme) :
    Order.height (I.subschemeι w) = Order.height w :=
  height_apply_eq_of_isLowerSet (orderEmbeddingOfIsClosedEmbedding _ I.subschemeι.isClosedEmbedding)
    (isLowerSet_range_of_isClosedEmbedding _ _) w

/-- At most one prime divisor of `E` has the surface of a given double surface as closure. -/
private theorem subsingleton_setOf_carrier_eq {Z : Scheme.{0}} {B : Divisor Z}
    (E : MMP.Mori.PrimeDivisor Z) (σ : DoubleSurface B) :
    {P : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme |
      σ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint}}.Subsingleton := by
  intro P hP Q hQ
  have h : closure {E.idealSheaf.subschemeι P.genericPoint} =
      closure {E.idealSheaf.subschemeι Q.genericPoint} := (hP : _).symm.trans hQ
  have hQ' : IsGenericPoint (E.idealSheaf.subschemeι Q.genericPoint)
      (closure {E.idealSheaf.subschemeι P.genericPoint}) := by
    rw [h]; exact isGenericPoint_closure
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (E.idealSheaf.subschemeι.isClosedEmbedding.injective (isGenericPoint_closure.eq hQ'))

open scoped Classical in
/-- For one double surface `σ` of `E`, the prime divisors `P` of `E` equal to `σ` contribute,
weighted by their degree over `V`, exactly the degree of `σ` over `V`. -/
private theorem finsum_primeDivisor_eq_finsum_isGenericPoint {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] (hY : topologicalKrullDim Y = 4)
    [Z.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))] (r : Z ⟶ Y)
    (hr : MMP.Intersection.IsResolution sY r) (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2) {B : Divisor Z}
    (E : MMP.Mori.PrimeDivisor Z) (σ : DoubleSurface B) (hσE : σ.fst = E) :
    (∑ᶠ P : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme,
      if σ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint} then
        (if Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
              (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = 2 ∧
            (E.idealSheaf.subschemeι ≫ r) P.genericPoint = v then
          ((E.idealSheaf.subschemeι ≫ r).residueDegree P.genericPoint : ℚ)
        else 0) else 0) =
      ∑ᶠ (z : Z) (_ : IsGenericPoint z σ.carrier) (_ : r.base z = v),
        (residueFieldDegree r z : ℚ) := by
  set ι := E.idealSheaf.subschemeι
  have hgen_inter : ∀ z, IsGenericPoint z σ.carrier → r.base z = v →
      Order.coheight z = 2 := fun z hz hzV =>
    coheight_eq_two_of_mem_inter sY hY r hr v hv σ.fst_ne_snd (σ.carrier_subset hz.mem) hzV
  by_cases hex : ∃ P₀ : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme,
      σ.carrier = closure {ι P₀.genericPoint}
  · obtain ⟨P₀, hP₀⟩ := hex
    have hz₀ : IsGenericPoint (ι P₀.genericPoint) σ.carrier := by
      rw [hP₀]; exact isGenericPoint_closure
    rw [finsum_isGenericPoint_eq hz₀, finsum_eq_single _ P₀, if_pos hP₀, finsum_eq_if]
    · by_cases hrz : r.base (ι P₀.genericPoint) = v
      · have hc := hgen_inter _ hz₀ hrz
        have hh := height_eq_two_of_coheight_eq_two sY hY r hr hc
        rw [height_subschemeι] at hh
        have hdim : Stacks.Chow.relativeDimension
            (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P₀.genericPoint = 2 := by
          refine relativeDimension_eq_of_topologicalKrullDim_closure ℂ _ _ 2 ?_
          rw [AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height, hh]
          rfl
        rw [if_pos ⟨hdim, hrz⟩, if_pos hrz,
          residueDegree_subschemeι_comp_eq_residueFieldDegree r E P₀.genericPoint]
      · rw [if_neg fun h => hrz h.2, if_neg hrz]
    · intro P hP
      rw [if_neg fun (h : σ.carrier = _) => hP (subsingleton_setOf_carrier_eq E σ h hP₀)]
  · push Not at hex
    rw [finsum_eq_zero_of_forall_eq_zero fun P => if_neg (hex P)]
    symm
    apply finsum_eq_zero_of_forall_eq_zero; intro z
    rw [finsum_eq_if]
    split_ifs with hz
    swap; · rfl
    rw [finsum_eq_if]
    split_ifs with hzV
    swap; · rfl
    exfalso
    have hc := hgen_inter z hz hzV
    have hlt : z < E.genericPoint := hσE ▸ lt_genericPoint_of_mem_inter σ.fst_ne_snd
      (σ.carrier_subset hz.mem)
    haveI : IsIntegral Z := (show MMP.Mori.IsVariety ℂ (r ≫ sY) from hr.2.1).toIsIntegral
    obtain ⟨P, hP, -⟩ := exists_primeDivisor_genericPoint_eq E hlt hc
    exact hex P (by rw [hP]; exact hz.symm)

open scoped Classical in
/-- Reindexing the prime divisors `P` of a component `E` by the double surfaces `S ⊆ E ∩ E'`
they are: the degree-weighted sum over `P` of the coefficients of `Z_E(c)` is the
degree-weighted sum of `c` over the double surfaces of `E` dominating `V`. -/
private theorem finsum_surfaceCoefficientCoeff_mul_eq {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] (hY : topologicalKrullDim Y = 4)
    [Z.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))] (r : Z ⟶ Y)
    (hr : MMP.Intersection.IsResolution sY r) (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2) {B : Divisor Z}
    [Finite (DoubleSurface B)] (E : MMP.Mori.PrimeDivisor Z) (c : DoubleSurface B → ℚ) :
    (∑ᶠ P : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme,
      surfaceCoefficientCoeff c E P *
        if Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
              (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = 2 ∧
            (E.idealSheaf.subschemeι ≫ r) P.genericPoint = v then
          ((E.idealSheaf.subschemeι ≫ r).residueDegree P.genericPoint : ℚ)
        else 0) =
      ∑ᶠ (σ : DoubleSurface B) (_ : σ.fst = E) (z : Z) (_ : IsGenericPoint z σ.carrier)
        (_ : r.base z = v), (residueFieldDegree r z : ℚ) * c σ := by
  letI := Fintype.ofFinite (DoubleSurface B)
  set g : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme → ℚ := fun P =>
    if Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = 2 ∧
        (E.idealSheaf.subschemeι ≫ r) P.genericPoint = v then
      ((E.idealSheaf.subschemeι ≫ r).residueDegree P.genericPoint : ℚ)
    else 0 with hg
  have hcoeff : ∀ P, surfaceCoefficientCoeff c E P * g P = ∑ σ : DoubleSurface B,
      if σ.fst = E ∧ σ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint} then
        c σ * g P else 0 := by
    intro P
    rw [surfaceCoefficientCoeff, finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [finsum_eq_if]
    split_ifs <;> simp
  change ∑ᶠ P, surfaceCoefficientCoeff c E P * g P = _
  simp_rw [hcoeff]
  rw [finsum_sum_comm, finsum_eq_sum_of_fintype]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hσ : σ.fst = E
    · rw [finsum_eq_if, if_pos hσ, finsum_isGenericPoint_mul,
        ← finsum_primeDivisor_eq_finsum_isGenericPoint sY hY r hr v hv E σ hσ, finsum_mul]
      · refine finsum_congr fun P => ?_
        simp only [hσ, true_and, hg]
        split_ifs <;> ring
    · rw [finsum_eq_if, if_neg hσ]
      exact finsum_eq_zero_of_forall_eq_zero fun P => if_neg fun h => hσ h.1
  · intro σ _
    refine (subsingleton_setOf_carrier_eq E σ).finite.subset fun P hP => ?_
    by_contra h
    exact hP (if_neg fun h' => h h'.2)

/-- On an exceptional component `E` over `V = closure {v}`, the coefficient along `v` of
`(r|_E)_* Z_E(c)` is the degree-weighted sum of `c` over the double surfaces `S ⊆ E ∩ E'`
dominating `V`. Here `Z_E(c) = ∑_P c_P [P]` is the rational surface cycle of the divisor
`surfaceCoefficientDivisor c E` on `E`, a prime divisor `P` contributing its prime cycle `[ξ_P]`
when it has delta-dimension two (on a complex scheme this is `MMP.Chow.divisorCycle`), and
`(r|_E)_*` is Stacks' proper push-forward of rational cycles. -/
public theorem rationalCoeff_rationalProperPushforward_surfaceCoefficientDivisor_eq_finsum
    {Y Z : Scheme.{0}} [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    [IsIntegral Y] (hY : topologicalKrullDim Y = 4) [Z.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))] (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] [IsProper r]
    (hr : MMP.Intersection.IsResolution (Y ↘ Spec (.of ℂ)) r) (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Y ↘ Spec (.of ℂ)) v = 2) {B : Divisor Z}
    (E : MMP.Mori.PrimeDivisor Z) (c : DoubleSurface B → ℚ) :
    Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) 2 v
        (Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ)
          (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) 2
          (E.idealSheaf.subschemeι ≫ r) (comp_over _ _)
          (Finsupp.linearCombination ℚ (fun P : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme =>
            if h : Stacks.Chow.relativeDimension
                (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = 2 then
              Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ)
                (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) 2 P.genericPoint h
            else 0) (surfaceCoefficientDivisor c E))) =
      ∑ᶠ (σ : DoubleSurface B) (_ : σ.fst = E) (z : Z) (_ : IsGenericPoint z σ.carrier)
        (_ : r.base z = v), (residueFieldDegree r z : ℚ) * c σ := by
  haveI := isNoetherian_of_isResolution (Y ↘ Spec (.of ℂ)) r hr
  haveI : Finite (DoubleSurface B) := DoubleSurface.finite
  rw [← LinearMap.comp_apply (Chow.rationalCoeff _ _ _ v), apply_linearCombination_eq_finsum]
  have hco : ∀ P, surfaceCoefficientDivisor c E P = surfaceCoefficientCoeff c E P :=
    coeff_surfaceCoefficientDivisor c E
  simp_rw [LinearMap.comp_apply, rationalCoeff_rationalProperPushforward_primeCycle _
    (Y ↘ Spec (.of ℂ)) _ _ _ v hv, hco]
  exact finsum_surfaceCoefficientCoeff_mul_eq (Y ↘ Spec (.of ℂ)) hY r hr v hv E c

/-- A prime divisor mapping onto `V` maps its generic point to that of `V`. -/
private theorem map_genericPoint_eq_of_image_eq {Y Z : Scheme.{0}} (r : Z ⟶ Y)
    (v : Y) (D : MMP.Mori.PrimeDivisor Z)
    (h : r.base '' D.support = (closure {v} : Set Y)) :
    r.base D.genericPoint = v := by
  have hcl : IsClosed (closure {v} : Set Y) := isClosed_closure
  have hD' : D.genericPoint ∈ D.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hgen : IsGenericPoint (r.base D.genericPoint) (closure {v} : Set Y) := by
    refine (Set.Subset.antisymm ?_ ?_)
    · exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr (h ▸ ⟨_, hD', rfl⟩))
    · rw [← h, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact (image_closure_subset_closure_image r.base.hom.continuous).trans
        (by rw [Set.image_singleton])
  exact hgen.eq (isGenericPoint_closure)

/-- A prime divisor of `Z` not contained in the exceptional set of `r` does not map onto a
surface of the fourfold `Y`. -/
private theorem image_ne_of_notMem_exceptionalSet {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsIntegral Y] [LocallyOfFiniteType sY] (hY : topologicalKrullDim Y = 4) (r : Z ⟶ Y)
    (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2) (D : MMP.Mori.PrimeDivisor Z)
    (hD : D.genericPoint ∉ exceptionalSet r) :
    r.base '' D.support ≠ (closure {v} : Set Y) := by
  intro h
  have hD' : D.genericPoint ∉ MMP.Flips.exceptionalSet r := by
    haveI : IsIso (r ∣_ biregularLocus r) := isBiregular_biregularLocus r
    refine fun h' => h' ⟨r ⁻¹ᵁ biregularLocus r,
      not_not.mp (mt MMP.Mori.mem_exceptionalSet.mpr hD), ?_⟩
    rw [← morphismRestrict_ι]
    infer_instance
  have hc := MMP.Flips.coheight_map_of_notMem_exceptionalSet hD'
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
    map_genericPoint_eq_of_image_eq r v D h, coheight_eq_two_of_relativeDimension_eq_two sY hY v hv] at hc
  exact absurd hc (by decide)

/-- A proper birational morphism onto a normal variety is an isomorphism over the points of
codimension at most one: an exceptional point maps to a point of coheight at least two. -/
private theorem two_le_coheight_map_of_mem_exceptionalSet {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsLocallyNoetherian Y] [IsNormal Y] (r : Z ⟶ Y) (hr : MMP.Intersection.IsResolution sY r)
    {x : Z} (hx : x ∈ exceptionalSet r) : 2 ≤ Order.coheight (r.base x) := by
  haveI hYv : MMP.Mori.IsVariety ℂ sY := hr.1
  haveI hZv : MMP.Mori.IsVariety ℂ (r ≫ sY) := hr.2.1
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.2.2.2.1
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hr.2.2.2.2
  obtain ⟨-, hex, -⟩ :=
    MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq ℂ hZv hYv r rfl hb
  have hpos : 0 < topologicalKrullDim (r ⁻¹' {r x}) := by
    have : x ∈ (MMP.Mori.exceptionalSet r : Set Z) := hx
    rwa [hex] at this
  set y := r.base x with hy
  let e := r.fiberHomeo y
  rw [← (e.isHomeomorph).topologicalKrullDim_eq] at hpos
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints,
    Order.krullDim_pos_iff] at hpos
  obtain ⟨a, b, hab⟩ := hpos
  have hI : Topology.IsInducing (fun t => (e t).1) :=
    Topology.IsInducing.subtypeVal.comp e.isInducing
  set w := (e b).1
  set w' := (e a).1
  have hw : r.base w = y := (e b).2
  have hw' : r.base w' = y := (e a).2
  have hlt : w' < w := by
    rw [lt_iff_le_not_ge] at hab ⊢
    exact ⟨hI.specializes_iff.mpr hab.1, fun h => hab.2 (hI.specializes_iff.mp h)⟩
  have hdim : topologicalKrullDim Z = topologicalKrullDim Y :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY) hr.2.2.2.2).symm
  have hle : ∀ t : Z, Order.coheight t ≤ Order.coheight (r.base t) := fun t =>
    MMP.Flips.coheight_le_coheight_map sY (r ≫ sY) hYv hZv r rfl hdim t
  by_contra hcon
  push Not at hcon
  have h1 : Order.coheight w' ≤ 1 := (hle w').trans (hw' ▸ Order.le_of_lt_succ hcon)
  have hwfin : Order.coheight w < ⊤ :=
    (hle w).trans_lt (hw ▸ hcon.trans_le le_top)
  have h2 : Order.coheight w < Order.coheight w' := Order.coheight_strictAnti hlt hwfin
  have h0 : Order.coheight w = 0 := ENat.lt_one_iff_eq_zero.mp (h2.trans_le h1)
  have hmax : IsMax w := Order.coheight_eq_zero.mp h0
  have hgw : w = genericPoint Z :=
    (Specializes.antisymm (hmax (genericPoint_specializes w)) (genericPoint_specializes w)).eq
  have hyg : y = genericPoint Y := by
    have hm : genericPoint Z ∈ r ⁻¹' {genericPoint Y} := by
      rw [preimage_genericPoint r hb]; rfl
    rw [← hw, hgw]; exact hm
  have hmaxY : IsMax (genericPoint Y) := fun z _ => genericPoint_specializes z
  have h3 : Order.coheight w' ≤ 0 := by
    have := hle w'
    rwa [hw', hyg, Order.coheight_eq_zero.mpr hmaxY] at this
  exact absurd (h2.trans_le h3) (by simp)

/-- A component meeting a component over `V` in a surface dominating `V`, and contained in the
exceptional set of `r`, lies over `V`. -/
private theorem image_eq_of_mem_exceptionalSet
    {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : topologicalKrullDim Y = 4) (r : Z ⟶ Y)
    (hr : MMP.Intersection.IsResolution sY r) {B : Divisor Z} (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2)
    (σ : DoubleSurface B)
    (hdom : (∃ z : Z, IsGenericPoint z σ.carrier ∧ r.base z = v))
    (hex : σ.snd.genericPoint ∈ exceptionalSet r) :
    r.base '' σ.snd.support = (closure {v} : Set Y) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hr.1
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.2.2.2.1
  obtain ⟨z, hz, hzV⟩ := hdom
  have hzs : z ∈ σ.snd.support := (σ.carrier_subset hz.mem).2
  have hsp : σ.snd.genericPoint ⤳ z := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hzs
  have hsp' : r.base σ.snd.genericPoint ⤳ v :=
    hzV ▸ hsp.map r.base.hom.continuous
  have h2 := two_le_coheight_map_of_mem_exceptionalSet sY r hr hex
  have hV2 := coheight_eq_two_of_relativeDimension_eq_two sY hY v hv
  have heq : r.base σ.snd.genericPoint = v := by
    by_contra hne
    have hlt : v < r.base σ.snd.genericPoint :=
      lt_of_le_not_ge (show v ≤ r.base σ.snd.genericPoint from hsp')
        fun h => hne (hsp'.antisymm h).eq
    have := Order.coheight_add_one_le hlt
    rw [hV2] at this
    have h3 : (2 : ℕ∞) + 1 ≤ 2 :=
      (show (2 : ℕ∞) + 1 ≤ Order.coheight (r.base σ.snd.genericPoint) + 1 by gcongr).trans this
    exact absurd h3 (by decide)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    ← r.isClosedMap.closure_image_eq_of_continuous r.base.hom.continuous, Set.image_singleton,
    heq]

/-- The other component of a double surface over `V` dominating `V` lies over `V` exactly when it
is exceptional. -/
private theorem notMem_exceptionalSet_iff_image_ne
    {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : topologicalKrullDim Y = 4) (r : Z ⟶ Y)
    (hr : MMP.Intersection.IsResolution sY r) {B : Divisor Z} (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2)
    (σ : DoubleSurface B)
    (hdom : (∃ z : Z, IsGenericPoint z σ.carrier ∧ r.base z = v)) :
    σ.snd.genericPoint ∉ exceptionalSet r ↔
      r.base '' σ.snd.support ≠ (closure {v} : Set Y) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hr.1
  refine ⟨image_ne_of_notMem_exceptionalSet sY hY r v hv σ.snd, fun h hex => h ?_⟩
  exact image_eq_of_mem_exceptionalSet sY hY r hr v hv σ hdom hex

/-- In a Noetherian space, a point in the closure of `S` lies in an irreducible closed set `T` in
which `T ∩ S` is dense. -/
private theorem exists_isIrreducible_subset_closure_inter {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] (S : Set X) {z : X} (hz : z ∈ closure S) :
    ∃ T : Set X, IsIrreducible T ∧ IsClosed T ∧ z ∈ T ∧ T ⊆ closure (T ∩ S) := by
  suffices H : ∀ C : Closeds X, ∀ S : Set X, closure S = C → ∀ z ∈ closure S,
      ∃ T : Set X, IsIrreducible T ∧ IsClosed T ∧ z ∈ T ∧ T ⊆ closure (T ∩ S) from
    H ⟨closure S, isClosed_closure⟩ S rfl z hz
  intro C
  induction C using WellFoundedLT.induction with
  | _ C IH =>
  intro S hSC z hz
  by_cases hirr : IsIrreducible (C : Set X)
  · refine ⟨C, hirr, C.isClosed, hSC ▸ hz, ?_⟩
    rw [← hSC, Set.inter_eq_right.mpr subset_closure]
  · have hne : (C : Set X).Nonempty := ⟨z, hSC ▸ hz⟩
    have hnpre : ¬ IsPreirreducible (C : Set X) := fun h => hirr ⟨hne, h⟩
    rw [isPreirreducible_iff_isClosed_union_isClosed] at hnpre
    push Not at hnpre
    obtain ⟨C₁, C₂, h₁, h₂, hcov, hn₁, hn₂⟩ := hnpre
    have hS : S = (S ∩ C₁) ∪ (S ∩ C₂) := by
      ext x
      refine ⟨fun hx => ?_, fun hx => hx.elim (·.1) (·.1)⟩
      rcases hcov (hSC ▸ subset_closure hx : x ∈ (C : Set X)) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    have hlt : ∀ {C' : Set X}, IsClosed C' → ¬ (C : Set X) ⊆ C' →
        (⟨closure (S ∩ C'), isClosed_closure⟩ : Closeds X) < C := by
      intro C' hC' hnC'
      refine lt_of_le_of_ne (fun x hx => ?_) fun h => hnC' ?_
      · change x ∈ (C : Set X)
        rw [← hSC]; exact closure_mono Set.inter_subset_left hx
      · rw [← h]
        exact (closure_mono Set.inter_subset_right).trans hC'.closure_subset
    rw [hS, closure_union] at hz
    rcases hz with hz | hz
    · obtain ⟨T, hT, hTc, hzT, hTS⟩ := IH _ (hlt h₁ hn₁) (S ∩ C₁) rfl z hz
      exact ⟨T, hT, hTc, hzT, hTS.trans (closure_mono fun x hx => ⟨hx.1, hx.2.1⟩)⟩
    · obtain ⟨T, hT, hTc, hzT, hTS⟩ := IH _ (hlt h₂ hn₂) (S ∩ C₂) rfl z hz
      exact ⟨T, hT, hTc, hzT, hTS.trans (closure_mono fun x hx => ⟨hx.1, hx.2.1⟩)⟩

/-- The residue field extension of `f` at a point `ξ` whose closure has the dimension of the
closure of its image is finite. -/
private theorem finite_residueFieldMap {Y Z : Scheme.{0}} (q : Y ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType q] (f : Z ⟶ Y) [LocallyOfFiniteType f] (ξ : Z)
    (h : topologicalKrullDim (closure {ξ} : Set Z) = topologicalKrullDim (closure {f ξ} : Set Y)) :
    (f.residueFieldMap ξ).hom.Finite := by
  let : Algebra ℂ (Z.residueField ξ) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (f ≫ q).appTop ≫ Z.Γevaluation ξ).hom.toAlgebra
  let : Algebra ℂ (Y.residueField (f ξ)) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ q.appTop ≫ Y.Γevaluation (f ξ)).hom.toAlgebra
  let : Algebra (Y.residueField (f ξ)) (Z.residueField ξ) := (f.residueFieldMap ξ).hom.toAlgebra
  have : IsScalarTower ℂ (Y.residueField (f ξ)) (Z.residueField ξ) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (f ≫ q).appTop ≫ Z.Γevaluation ξ).hom =
      ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ q.appTop ≫ Y.Γevaluation (f ξ) ≫
        f.residueFieldMap ξ).hom
    rw [Scheme.Γevaluation_naturality, Scheme.Hom.comp_appTop]
    simp only [Category.assoc]
  rw [topologicalKrullDim_closure_singleton_eq_trdeg ℂ Z (f ≫ q) ξ,
    topologicalKrullDim_closure_singleton_eq_trdeg ℂ Y q (f ξ), WithBot.coe_inj] at h
  have : Algebra.EssFiniteType ℂ (Y.residueField (f ξ)) := residueField_essFiniteType ℂ q (f ξ)
  have hzero := MMP.Mori.trdeg_eq_zero_of_toENat_trdeg_eq ℂ
    (trdeg_lt_aleph0 ℂ (Y.residueField (f ξ))) h
  have : Algebra.EssFiniteType (Y.residueField (f ξ)) (Z.residueField ξ) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f ξ)
  have : Algebra.IsAlgebraic (Y.residueField (f ξ)) (Z.residueField ξ) :=
    trdeg_eq_zero_iff.mp hzero
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- A surface of `Z` over the generic point of `V` has nonzero degree over `V`. -/
private theorem residueFieldDegree_ne_zero {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsIntegral Y] (hY : topologicalKrullDim Y = 4) (r : Z ⟶ Y)
    (hr : MMP.Intersection.IsResolution sY r) (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2) {z : Z}
    (hz : Order.coheight z = 2) (hzV : r.base z = v) :
    residueFieldDegree r z ≠ 0 := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hr.1
  haveI : AlgebraicGeometry.IsVariety ℂ (r ≫ sY) := hr.2.1
  haveI : LocallyOfFiniteType r := locallyOfFiniteType_of_comp r sY
  have h1 : topologicalKrullDim (closure {z} : Set Z) = 2 := by
    rw [AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height,
      height_eq_two_of_coheight_eq_two sY hY r hr hz]
    rfl
  have h2 : topologicalKrullDim (closure {r.base z} : Set Y) = 2 := by
    rw [hzV]
    exact topologicalKrullDim_closure_of_relativeDimension_eq ℂ sY v 2 hv
  have hfin := finite_residueFieldMap sY r z (h1.trans h2.symm)
  letI := (r.residueFieldMap z).hom.toAlgebra
  haveI : Module.Finite (Y.residueField (r z)) (Z.residueField z) := hfin
  exact Module.finrank_pos.ne'

/-- A point of codimension one of `Z` over the generic point of `V` is the generic point of a
component of `B` lying over `V`. -/
private theorem exists_mem_support_genericPoint_eq {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    (Q : Divisor Y) (r : Z ⟶ Y) (hr : MMP.Intersection.IsResolution sY r) (B : Divisor Z)
    (hBsupp : (B.supp : Set Z) = r.base ⁻¹' (Q.supp : Set Y) ∪ exceptionalSet r)
    (v : Y) (hVQ : v ∈ Q.supp) {w : Z}
    (hw : Order.coheight w = 1) (hwV : r.base w = v) :
    ∃ D : MMP.Mori.PrimeDivisor Z, D ∈ B.support ∧
      r.base '' D.support = (closure {v} : Set Y) ∧ D.genericPoint = w := by
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.2.2.2.1
  have hwB : w ∈ (B.supp : Set Z) := by
    rw [hBsupp]
    left
    change r.base w ∈ (Q.supp : Set Y)
    rw [hwV]
    exact hVQ
  obtain ⟨E, hE, hwE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hwB
  have hsp : E.genericPoint ⤳ w := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hwE
  have hEw : E.genericPoint = w := by
    by_contra hne
    have hlt : w < E.genericPoint :=
      lt_of_le_of_ne_scheme (Scheme.le_iff_specializes.mpr hsp) (Ne.symm hne)
    have := Order.coheight_add_one_le hlt
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hw] at this
    exact absurd this (by decide)
  refine ⟨E, Finsupp.mem_support_iff.mpr hE, ?_, hEw⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    ← r.isClosedMap.closure_image_eq_of_continuous r.base.hom.continuous, Set.image_singleton,
    show AlgebraicGeometry.PrimeDivisor.genericPoint E = w from hEw, hwV]

/-- For an snc divisor, a connected component of the intersection of two distinct components is
irreducible: the intersection is regular, hence normal. -/
private theorem isIrreducible_carrier {Z : Scheme.{0}} {S : Scheme.{0}} (sZ : Z ⟶ S)
    [IsLocallyNoetherian Z] [NoetherianSpace Z] {B : Divisor Z}
    (hBsnc : DivisorWithCoeffs.IsSNC sZ B) (σ : DoubleSurface B) : IsIrreducible σ.carrier := by
  set D : Z.IdealSheafData := σ.fst.idealSheaf ⊔ σ.snd.idealSheaf
  have hDsupp : (D.support : Set Z) = σ.fst.support ∩ σ.snd.support := by
    rw [Scheme.IdealSheafData.support_sup]; rfl
  have : IsLocallyNoetherian D.subscheme := isLocallyNoetherian_of_isClosedImmersion D.subschemeι
  have : NoetherianSpace D.subscheme :=
    D.subschemeι.isClosedEmbedding.isEmbedding.noetherianSpace
  have hsup : ∀ y : Z, IdealSheafData.stalk D y = IdealSheafData.stalk σ.fst.idealSheaf y ⊔
      IdealSheafData.stalk σ.snd.idealSheaf y := by
    intro y
    have : D = ⨆ b : Bool, cond b σ.fst.idealSheaf σ.snd.idealSheaf := by
      rw [iSup_bool_eq]; rfl
    rw [this, MMP.Resolution.stalk_iSup, iSup_bool_eq]
    rfl
  have : IsNormal D.subscheme := by
    rw [isNormal_iff_stalk_normal]
    intro z
    have hz : D.subschemeι z ∈ (D.support : Set Z) := by
      rw [← D.range_subschemeι]; exact ⟨z, rfl⟩
    rw [hDsupp] at hz
    obtain ⟨n, w, j, hw, -, hI⟩ := hBsnc.2 (D.subschemeι z)
    have := isRegularLocalRing_of_isRegularSystemOfParameters hw
    have hstalk : IdealSheafData.stalk D (D.subschemeι z) =
        Ideal.span (w '' ((({j ⟨σ.fst, σ.fst_mem, hz.1⟩, j ⟨σ.snd, σ.snd_mem, hz.2⟩} :
          Finset (Fin n)) : Set (Fin n)))) := by
      rw [hsup, hI ⟨σ.fst, σ.fst_mem, hz.1⟩, hI ⟨σ.snd, σ.snd_mem, hz.2⟩, Finset.coe_insert,
        Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton, Ideal.span_insert]
    have := isRegularLocalRing_stalk_subscheme_of_isRegularLocalRing_quotient D z (by
      rw [hstalk]
      exact MMP.Resolution.isRegularLocalRing_quotient_span_image w hw _)
    exact ⟨IsRegularLocalRing.isDomain _, isIntegrallyClosed_of_isRegularLocalRing _⟩
  obtain ⟨y, hy, hσ⟩ := σ.isComponent
  rw [← hσ]
  have hrange : Set.range D.subschemeι = (D.support : Set Z) := by
    rw [← D.range_subschemeι]
  rw [← hDsupp] at hy ⊢
  obtain ⟨z, rfl⟩ : y ∈ Set.range D.subschemeι := hrange ▸ hy
  have hemb := D.subschemeι.isClosedEmbedding.isEmbedding
  have heq : connectedComponentIn (D.support : Set Z) (D.subschemeι z) =
      D.subschemeι '' connectedComponent z := by
    apply subset_antisymm
    · set C := connectedComponentIn (D.support : Set Z) (D.subschemeι z)
      have hC : C ⊆ Set.range D.subschemeι := hrange ▸ connectedComponentIn_subset _ _
      have hCim : D.subschemeι '' (D.subschemeι ⁻¹' C) = C := Set.image_preimage_eq_of_subset hC
      have hpc : _root_.IsPreconnected (D.subschemeι ⁻¹' C) := by
        rw [← hemb.isInducing.isPreconnected_image, hCim]
        exact isPreconnected_connectedComponentIn
      have := hpc.subset_connectedComponent (show z ∈ D.subschemeι ⁻¹' C from
        mem_connectedComponentIn hy)
      rw [← hCim]
      exact Set.image_mono this
    · refine (isPreconnected_connectedComponent.image _
        D.subschemeι.continuous.continuousOn).subset_connectedComponentIn
        ⟨z, mem_connectedComponent, rfl⟩ ?_
      rintro _ ⟨w, -, rfl⟩
      exact hrange ▸ ⟨w, rfl⟩
  rw [heq]
  exact (isIrreducible_connectedComponent_of_isNormal D.subscheme z).image _
    D.subschemeι.continuous.continuousOn

/-- A point of `Z` lying over a point of `Y` of delta-dimension two is not the generic point. -/
private theorem coheight_ne_zero_of_base_eq {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsIntegral Y] [IsLocallyNoetherian Y] (hY : topologicalKrullDim Y = 4) (r : Z ⟶ Y)
    (hr : MMP.Intersection.IsResolution sY r) (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2) {w : Z} (hw : r.base w = v) : Order.coheight w ≠ 0 := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hr.1
  haveI hZv : MMP.Mori.IsVariety ℂ (r ≫ sY) := hr.2.1
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.2.2.2.1
  intro h0
  have hgw : w = genericPoint Z := (Specializes.antisymm
    (Order.coheight_eq_zero.mp h0 (genericPoint_specializes w)) (genericPoint_specializes w)).eq
  have hm : genericPoint Z ∈ r ⁻¹' {genericPoint Y} := by
    rw [preimage_genericPoint r
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hr.2.2.2.2)]
    rfl
  have h2 := coheight_eq_two_of_relativeDimension_eq_two sY hY v hv
  rw [← hw, hgw, show r.base (genericPoint Z) = genericPoint Y from hm,
    Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z] at h2
  exact absurd h2 (by decide)

/-- Connectedness of the generic fibre: the components of `B` over `V`, joined when a double
surface between them dominating `V` has nonzero total degree, form a preconnected graph. -/
public theorem preconnected_components_over
    {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : topologicalKrullDim Y = 4) (Q : Divisor Y) (r : Z ⟶ Y)
    (hr : MMP.Intersection.IsResolution sY r) (B : Divisor Z)
    (hBsnc : DivisorWithCoeffs.IsSNC (r ≫ sY) B)
    (hBsupp : (B.supp : Set Z) = r.base ⁻¹' (Q.supp : Set Y) ∪ exceptionalSet r)
    (v : Y)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      sY v = 2) (hVQ : v ∈ Q.supp) :
    (SimpleGraph.fromRel fun E E' : {E : MMP.Mori.PrimeDivisor Z //
        E ∈ B.support ∧ r.base '' E.support = (closure {v} : Set Y)} =>
      ∑ᶠ (σ : DoubleSurface B) (_ : σ.fst = E.1) (_ : σ.snd = E'.1) (z : Z)
        (_ : IsGenericPoint z σ.carrier) (_ : r.base z = v),
          (residueFieldDegree r z : ℚ) ≠ 0).Preconnected := by
  classical
  haveI hYv : MMP.Mori.IsVariety ℂ sY := hr.1
  haveI hZv : MMP.Mori.IsVariety ℂ (r ≫ sY) := hr.2.1
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hr.1
  haveI : AlgebraicGeometry.IsVariety ℂ (r ≫ sY) := hr.2.1
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI := isNoetherian_of_isResolution sY r hr
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.2.2.2.1
  haveI : Finite (DoubleSurface B) := DoubleSurface.finite
  have hdim : topologicalKrullDim Z = topologicalKrullDim Y :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY) hr.2.2.2.2).symm
  set η := v with hη
  set F : Set Z := r.base ⁻¹' {η} with hF
  have hFconn : _root_.IsPreconnected F :=
    ((MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism (r ≫ sY) sY hZv
      ⟨hYv, inferInstance⟩ r hr.2.2.2.2).2 η).isPreconnected
  have hcoh_le : ∀ x ∈ F, Order.coheight x ≤ 2 := fun x hx => by
    have := MMP.Flips.coheight_le_coheight_map sY (r ≫ sY) hYv hZv r rfl hdim x
    rwa [show r.base x = η from hx, coheight_eq_two_of_relativeDimension_eq_two sY hY v hv] at this
  set 𝓔 := {E : MMP.Mori.PrimeDivisor Z //
    E ∈ B.support ∧ r.base '' E.support = (closure {v} : Set Y)}
  haveI : Finite 𝓔 := Finite.of_injective (fun E : 𝓔 => (⟨E.1, E.2.1⟩ : B.support))
    (fun x y h => Subtype.ext (congrArg (Subtype.val : B.support → _) h))
  have hmemF : ∀ E : 𝓔, E.1.genericPoint ∈ F := fun E =>
    map_genericPoint_eq_of_image_eq r v E.1 E.2.2
  have hgpmem : ∀ D : MMP.Mori.PrimeDivisor Z, D.genericPoint ∈ D.support := by
    intro D
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  -- the points of `F` of codimension at most one are generic points of components over `V`
  have hlow : ∀ w ∈ F, Order.coheight w ≤ 1 → ∃ E : 𝓔, E.1.genericPoint = w := by
    intro w hw hw1
    have hw0 := coheight_ne_zero_of_base_eq sY hY r hr v hv hw
    have hw1' : Order.coheight w = 1 := by
      generalize Order.coheight w = c at hw0 hw1 ⊢
      induction c with
      | top => simp at hw1
      | coe n => norm_cast at hw0 hw1 ⊢; omega
    obtain ⟨D, hD, hDV, hDw⟩ :=
      exists_mem_support_genericPoint_eq sY Q r hr B hBsupp v hVQ hw1' hw
    exact ⟨⟨D, hD, hDV⟩, hDw⟩
  -- the fibre over `η` is covered by the components over `V`
  have hcover : ∀ u : 𝓔, F ⊆ ⋃ E : 𝓔, E.1.support := by
    intro u z hzF
    by_contra hz
    simp only [Set.mem_iUnion, not_exists] at hz
    have hgen : ∀ w ∈ F, w ⤳ z → w = z := by
      intro w hwF hwz
      by_contra hne
      have hlt : z < w := lt_of_le_of_ne_scheme (Scheme.le_iff_specializes.mpr hwz) (Ne.symm hne)
      have h1 := Order.coheight_add_one_le hlt
      have h2 := hcoh_le z hzF
      have hw1 : Order.coheight w ≤ 1 := by
        generalize Order.coheight w = a at h1
        generalize Order.coheight z = b at h1 h2
        induction a with
        | top => simp at h1; simp [h1] at h2
        | coe n =>
          induction b with
          | top => simp at h2
          | coe m => norm_cast at h1 h2 ⊢; omega
      obtain ⟨E, hE⟩ := hlow w hwF hw1
      apply hz E
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure,
        show AlgebraicGeometry.PrimeDivisor.genericPoint E.1 = w from hE]
      exact hwz
    have hz2 : 2 ≤ Order.coheight z := by
      by_contra h
      push Not at h
      obtain ⟨E, hE⟩ := hlow z hzF (Order.le_of_lt_succ h)
      exact hz E (hE ▸ hgpmem E.1)
    have hspec : ∀ s ∈ F, z ⤳ s → s = z := by
      intro s hsF hzs
      by_contra hne
      have hlt : s < z := lt_of_le_of_ne_scheme (Scheme.le_iff_specializes.mpr hzs) hne
      have h1 := Order.coheight_add_one_le hlt
      have h2 := hcoh_le s hsF
      have h3 : (2 : ℕ∞) + 1 ≤ Order.coheight z + 1 := by gcongr
      have : (2 : ℕ∞) + 1 ≤ 2 := h3.trans (h1.trans h2)
      exact absurd this (by decide)
    have hnotcl : z ∉ closure (F \ {z}) := by
      intro hcl
      obtain ⟨T, hT, hTc, hzT, hTS⟩ := exists_isIrreducible_subset_closure_inter (F \ {z}) hcl
      have hgT := hT.isGenericPoint_genericPoint_closure
      rw [hTc.closure_eq] at hgT
      have htz : hT.genericPoint ⤳ z := hgT.specializes hzT
      obtain ⟨s, hsT, hsF, hsz⟩ : (T ∩ (F \ {z})).Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        have := hTS hzT
        rwa [hempty, closure_empty] at this
      have hts : hT.genericPoint ⤳ s := hgT.specializes hsT
      have htF : hT.genericPoint ∈ F := by
        have h1 : r.base hT.genericPoint ⤳ η :=
          (show r.base s = η from hsF) ▸ hts.map r.base.hom.continuous
        have hTF : T ⊆ r.base ⁻¹' closure {η} :=
          hTS.trans (closure_minimal (fun x hx => subset_closure hx.2.1)
            (isClosed_closure.preimage r.base.hom.continuous))
        have h2 : η ⤳ r.base hT.genericPoint :=
          specializes_iff_mem_closure.mpr (hTF hgT.mem)
        exact (h1.antisymm h2).eq
      exact hsz (hspec s hsF (hgen _ htF htz ▸ hts))
    obtain ⟨x, hxF, hxz, hxcl⟩ := isPreconnected_closed_iff.mp hFconn (closure {z})
      (closure (F \ {z})) isClosed_closure isClosed_closure
      (fun x hx => by
        by_cases h : x = z
        · subst h
          exact Or.inl (subset_closure rfl)
        · exact Or.inr (subset_closure ⟨hx, h⟩))
      ⟨z, hzF, subset_closure rfl⟩
      ⟨u.1.genericPoint, hmemF u, subset_closure ⟨hmemF u, fun h =>
        hz u ((Set.mem_singleton_iff.mp h) ▸ hgpmem u.1)⟩⟩
    have hx := hspec x hxF (specializes_iff_mem_closure.mpr hxz)
    exact hnotcl (hx ▸ hxcl)
  intro u u'
  by_contra huv
  let G := SimpleGraph.fromRel fun E E' : 𝓔 =>
      ∑ᶠ (σ : DoubleSurface B) (_ : σ.fst = E.1) (_ : σ.snd = E'.1) (z : Z)
        (_ : IsGenericPoint z σ.carrier) (_ : r.base z = η),
          (residueFieldDegree r z : ℚ) ≠ 0
  change ¬ G.Reachable u u' at huv
  let A : Set 𝓔 := {w | G.Reachable u w}
  have hKA : IsClosed (⋃ E ∈ A, E.1.support) :=
    (Set.toFinite A).isClosed_biUnion fun E _ => E.1.idealSheaf.support.isClosed
  have hKA' : IsClosed (⋃ E ∈ Aᶜ, E.1.support) :=
    (Set.toFinite Aᶜ).isClosed_biUnion fun E _ => E.1.idealSheaf.support.isClosed
  obtain ⟨z, hzF, hzA, hzA'⟩ := isPreconnected_closed_iff.mp hFconn _ _ hKA hKA'
    (by
      intro x hx
      obtain ⟨E, hE⟩ := Set.mem_iUnion.mp (hcover u hx)
      by_cases h : E ∈ A
      · left; exact Set.mem_biUnion h hE
      · right; exact Set.mem_biUnion h hE)
    ⟨u.1.genericPoint, hmemF u,
      Set.mem_biUnion (show u ∈ A from SimpleGraph.Reachable.refl u) (hgpmem u.1)⟩
    ⟨u'.1.genericPoint, hmemF u', Set.mem_biUnion (show u' ∈ Aᶜ from huv) (hgpmem u'.1)⟩
  obtain ⟨E, hEA, hzE⟩ := Set.mem_iUnion₂.mp hzA
  obtain ⟨E', hE'A, hzE'⟩ := Set.mem_iUnion₂.mp hzA'
  have hne : E ≠ E' := fun h => hE'A (h ▸ hEA)
  have hne' : E.1 ≠ E'.1 := fun h => hne (Subtype.ext h)
  apply hE'A
  refine SimpleGraph.Reachable.trans hEA (SimpleGraph.Adj.reachable ?_)
  rw [SimpleGraph.fromRel_adj]
  refine ⟨hne, Or.inl ?_⟩
  -- the double surface of `(E, E')` through `z`
  have hzEE' : ({z} : Set Z) ⊆ E.1.support ∩ E'.1.support :=
    Set.singleton_subset_iff.mpr ⟨hzE, hzE'⟩
  set σ := DoubleSurface.through E.2.1 E'.2.1 hne' (Set.singleton_nonempty z) hzEE'
  have hzσ : z ∈ σ.carrier := DoubleSurface.subset_through E.2.1 E'.2.1 hne'
    (Set.singleton_nonempty z) hzEE' isPreconnected_singleton (Set.mem_singleton z)
  have hirr := isIrreducible_carrier (r ≫ sY) hBsnc σ
  have hclσ : IsClosed σ.carrier := by
    have hcl : IsClosed (E.1.support ∩ E'.1.support) :=
      E.1.idealSheaf.support.isClosed.inter E'.1.idealSheaf.support.isClosed
    rw [σ.carrier_eq_connectedComponentIn hzσ]
    change IsClosed (connectedComponentIn (E.1.support ∩ E'.1.support) z)
    rw [connectedComponentIn_eq_image (hzEE' (Set.mem_singleton z))]
    exact hcl.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  have hgz' : IsGenericPoint hirr.genericPoint σ.carrier := by
    have := hirr.isGenericPoint_genericPoint_closure
    rwa [hclσ.closure_eq] at this
  have hz'z : hirr.genericPoint ⤳ z := hgz'.specializes hzσ
  have hz'mem : hirr.genericPoint ∈ E.1.support ∩ E'.1.support := σ.carrier_subset hgz'.mem
  have hz'V : r.base hirr.genericPoint = η := by
    have h1 : r.base hirr.genericPoint ⤳ η :=
      (show r.base z = η from hzF) ▸ hz'z.map r.base.hom.continuous
    have h2 : η ⤳ r.base hirr.genericPoint := by
      have : r.base hirr.genericPoint ∈ (closure {v} : Set Y) :=
        E.2.2 ▸ ⟨hirr.genericPoint, hz'mem.1, rfl⟩
      rw [← (isGenericPoint_closure).def] at this
      exact specializes_iff_mem_closure.mpr this
    exact (h1.antisymm h2).eq
  have hc2 := coheight_eq_two_of_mem_inter sY hY r hr v hv hne' hz'mem hz'V
  have hdeg := residueFieldDegree_ne_zero sY hY r hr v hv hc2 hz'V
  have hterm : (∑ᶠ (_ : σ.fst = E.1) (_ : σ.snd = E'.1) (x : Z) (_ : IsGenericPoint x σ.carrier)
      (_ : r.base x = v), (residueFieldDegree r x : ℚ)) =
      residueFieldDegree r hirr.genericPoint := by
    rw [finsum_eq_if, if_pos (show σ.fst = E.1 from rfl), finsum_eq_if,
      if_pos (show σ.snd = E'.1 from rfl), finsum_isGenericPoint_eq hgz',
      finsum_eq_if, if_pos hz'V]
  have hnonneg : ∀ τ : DoubleSurface B, 0 ≤ ∑ᶠ (_ : τ.fst = E.1) (_ : τ.snd = E'.1) (x : Z)
      (_ : IsGenericPoint x τ.carrier) (_ : r.base x = v),
        (residueFieldDegree r x : ℚ) := fun τ =>
    finsum_nonneg fun _ => finsum_nonneg fun _ => finsum_nonneg fun _ =>
      finsum_nonneg fun _ => finsum_nonneg fun _ => Nat.cast_nonneg _
  have hle := single_le_finsum σ (Set.toFinite _) hnonneg
  rw [hterm] at hle
  exact (lt_of_lt_of_le (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdeg)) hle).ne'

/-- **Balancing along a surface over which `Supp Q` passes.** Let `Y` be a normal complex
fourfold, `Q` a divisor on `Y`, `r : Z ⟶ Y` a projective resolution and `B` an snc divisor with
support `r⁻¹(Supp Q) ∪ Ex(r)`, and let `V` be a surface of `Y` with generic point in `Supp Q`.
Let `a` be an oriented coefficient system on the double surfaces of `B` whose branch legs over `V`
have degree-weighted sum `∑ [κ(S) : κ(V)] a_S = 0`. Then there is an oriented system `c`, equal
to `a` off the double surfaces of two components over `V`, such that `(r|_E)_* Z_E(c)` has
coefficient `0` along `V` for every component `E` of `B` with `r(E) = V`, and every corrected
double surface maps into `V`, hence into dimension at most one under any `p` with
`dim p(V) ≤ 1`. -/
public theorem exists_orientedSurfaceCoefficients_rationalPushforward_coeff_eq_zero_of_mem_supp
    {Y Z : Scheme.{0}} [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : topologicalKrullDim Y = 4) (Q : Divisor Y)
    [Z.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))] (r : Z ⟶ Y)
    [r.IsOver (Spec (.of ℂ))] [IsProper r] (hr : MMP.Intersection.IsResolution (Y ↘ Spec (.of ℂ)) r)
    (B : Divisor Z)
    (hBsnc : DivisorWithCoeffs.IsSNC (r ≫ Y ↘ Spec (.of ℂ)) B)
    (hBsupp : (B.supp : Set Z) = r.base ⁻¹' (Q.supp : Set Y) ∪ exceptionalSet r)
    (v : Y) (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Y ↘ Spec (.of ℂ)) v = 2) (hVQ : v ∈ Q.supp)
    (a : DoubleSurface B → ℚ) (ha : a ∈ orientedSurfaceCoefficients B)
    (hsum : ∑ᶠ (σ : DoubleSurface B) (_ : σ.fst.genericPoint ∉ exceptionalSet r)
        (_ : r.base '' σ.snd.support = (closure {v} : Set Y)) (z : Z)
        (_ : IsGenericPoint z σ.carrier) (_ : r.base z = v),
          (residueFieldDegree r z : ℚ) * a σ = 0) :
    ∃ c ∈ orientedSurfaceCoefficients B,
      (∀ σ : DoubleSurface B, c σ ≠ a σ →
        r.base '' σ.fst.support = (closure {v} : Set Y) ∧
          r.base '' σ.snd.support = (closure {v} : Set Y)) ∧
      (∀ E ∈ B.support, r.base '' E.support = (closure {v} : Set Y) →
        Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) 2 v
            (Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ)
              (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) 2
              (E.idealSheaf.subschemeι ≫ r) (comp_over _ _)
              (Finsupp.linearCombination ℚ
                (fun P : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme =>
                  if h : Stacks.Chow.relativeDimension
                      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                      (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = 2 then
                    Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ)
                      (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) 2 P.genericPoint h
                  else 0) (surfaceCoefficientDivisor c E))) = 0) ∧
      ∀ σ : DoubleSurface B, c σ ≠ a σ →
        r.base '' σ.carrier ⊆ (closure {v} : Set Y) ∧
          ∀ {X : Scheme.{0}} (p : Y ⟶ X),
            topologicalKrullDim (p.base '' (closure {v} : Set Y)) ≤ 1 →
            topologicalKrullDim ((r ≫ p).base '' σ.carrier) ≤ 1 := by
  classical
  set sY : Y ⟶ Spec (.of ℂ) := Y ↘ Spec (.of ℂ) with hsY
  haveI := isNoetherian_of_isResolution sY r hr
  haveI : Finite (DoubleSurface B) := DoubleSurface.finite
  letI := Fintype.ofFinite (DoubleSurface B)
  -- the total degree over `V` of a double surface
  set w : DoubleSurface B → ℚ := fun σ => ∑ᶠ (z : Z) (_ : IsGenericPoint z σ.carrier)
    (_ : r.base z = v), (residueFieldDegree r z : ℚ) with hw
  have hwmul : ∀ σ k, ∑ᶠ (z : Z) (_ : IsGenericPoint z σ.carrier)
      (_ : r.base z = v), (residueFieldDegree r z : ℚ) * k = w σ * k :=
    fun σ k => finsum_isGenericPoint_mul _ _ _ k
  have hwdom : ∀ σ, w σ ≠ 0 →
      ∃ z : Z, IsGenericPoint z σ.carrier ∧ r.base z = v := by
    intro σ hσ
    by_contra hne
    push Not at hne
    refine hσ (finsum_eq_zero_of_forall_eq_zero fun z => ?_)
    by_cases hz : IsGenericPoint z σ.carrier
    · simp only [finsum_eq_if, if_pos hz, if_neg (hne z hz)]
    · simp only [finsum_eq_if, if_neg hz]
  let e : DoubleSurface B ≃ DoubleSurface B :=
    ⟨DoubleSurface.swap, DoubleSurface.swap, DoubleSurface.swap_swap, DoubleSurface.swap_swap⟩
  have he : ∀ σ, e σ = σ.swap := fun _ => rfl
  set OV : MMP.Mori.PrimeDivisor Z → Prop :=
    fun E => r.base '' E.support = (closure {v} : Set Y) with hOV
  let 𝓔 := {E : MMP.Mori.PrimeDivisor Z // E ∈ B.support ∧ OV E}
  haveI : Finite 𝓔 := Finite.of_injective (fun E : 𝓔 => (⟨E.1, E.2.1⟩ : B.support))
    (fun x y h => Subtype.ext (congrArg (Subtype.val : B.support → _) h))
  letI := Fintype.ofFinite 𝓔
  -- fibrewise decomposition of a sum over double surfaces
  have hfib : ∀ (π : DoubleSurface B → MMP.Mori.PrimeDivisor Z) (_ : ∀ σ, π σ ∈ B.support)
      (P : DoubleSurface B → Prop) [DecidablePred P] (g : DoubleSurface B → ℚ),
      ∑ E : 𝓔, ∑ σ, (if π σ = E.1 ∧ P σ then g σ else 0) =
        ∑ σ, if OV (π σ) ∧ P σ then g σ else 0 := by
    intro π hπ P _ g
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases h : OV (π σ)
    · rw [Fintype.sum_eq_single ⟨π σ, hπ σ, h⟩]
      · simp only [true_and, h]
      · intro E hE
        rw [if_neg]
        rintro ⟨h1, -⟩
        exact hE (Subtype.ext h1.symm)
    · rw [if_neg (fun h' => h h'.1)]
      refine Finset.sum_eq_zero fun E _ => if_neg ?_
      rintro ⟨h1, -⟩
      exact h (h1 ▸ E.2.2)
  -- the total degree of the double surfaces between two components over `V`
  let N : 𝓔 → 𝓔 → ℚ := fun E E' => ∑ σ, if σ.fst = E.1 ∧ σ.snd = E'.1 then w σ else 0
  have hN : ∀ E E', N E' E = N E E' := by
    intro E E'
    refine Fintype.sum_equiv e _ _ fun σ => ?_
    simp only [he, DoubleSurface.swap_fst,
      DoubleSurface.swap_snd, and_comm]
    rfl
  have hNeq : ∀ E E' : 𝓔, (∑ᶠ (σ : DoubleSurface B) (_ : σ.fst = E.1) (_ : σ.snd = E'.1),
      w σ) = N E E' := by
    intro E E'
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [finsum_eq_if, ite_and]
  have hconn := preconnected_components_over sY hY Q r hr B hBsnc hBsupp v hv hVQ
  -- the demand at a component over `V`: its branch legs
  let b : 𝓔 → ℚ := fun E => ∑ σ, if σ.fst = E.1 ∧ ¬ OV σ.snd then w σ * a σ else 0
  have hb : ∑ E, b E = 0 := by
    show ∑ E : 𝓔, ∑ σ, (if σ.fst = E.1 ∧ ¬ OV σ.snd then w σ * a σ else 0) = 0
    refine (hfib (fun σ => σ.fst) (fun σ => σ.fst_mem) (fun σ => ¬ OV σ.snd)
      (fun σ => w σ * a σ)).trans ?_
    have hsum' : ∑ σ : DoubleSurface B, (if σ.fst.genericPoint ∉ exceptionalSet r ∧ OV σ.snd
        then w σ * a σ else 0) = 0 := by
      refine Eq.trans ?_ hsum
      rw [finsum_eq_sum_of_fintype]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp only [hwmul]
      simp only [finsum_eq_if, ite_and]
      rfl
    refine Eq.trans ?_ (neg_eq_zero.mpr hsum')
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv e _ _ fun σ => ?_
    simp only [he, DoubleSurface.swap_fst,
      DoubleSurface.swap_snd]
    rw [show w σ.swap = w σ from rfl, ha σ]
    by_cases hw0 : w σ = 0
    · simp [hw0]
    by_cases h1 : OV σ.fst
    · have key := notMem_exceptionalSet_iff_image_ne sY hY r hr v hv σ (hwdom σ hw0)
      by_cases h2 : OV σ.snd
      · have h3 : ¬ σ.snd.genericPoint ∉ exceptionalSet r := fun h => key.mp h h2
        simp [h1, h2, h3]
      · have h3 : σ.snd.genericPoint ∉ exceptionalSet r := key.mpr h2
        simp [h1, h2, h3]
    · simp [h1]
  obtain ⟨f, hfanti, hfadj, hfdiv⟩ := exists_flow hconn b hb
  -- the corrected system
  let c : DoubleSurface B → ℚ := fun σ =>
    if h : OV σ.fst ∧ OV σ.snd then
      f ⟨σ.fst, σ.fst_mem, h.1⟩ ⟨σ.snd, σ.snd_mem, h.2⟩ /
        N ⟨σ.fst, σ.fst_mem, h.1⟩ ⟨σ.snd, σ.snd_mem, h.2⟩
    else a σ
  have hc : ∀ σ (E E' : 𝓔), σ.fst = E.1 → σ.snd = E'.1 → c σ = f E E' / N E E' := by
    rintro σ ⟨E, hE⟩ ⟨E', hE'⟩ h1 h2
    simp only at h1 h2
    subst h1 h2
    exact dif_pos ⟨hE.2, hE'.2⟩
  have hca : ∀ σ, c σ ≠ a σ → OV σ.fst ∧ OV σ.snd := by
    intro σ h
    by_contra h'
    exact h (dif_neg h')
  refine ⟨c, ?_, hca, ?_, ?_⟩
  · intro σ
    by_cases h : OV σ.fst ∧ OV σ.snd
    · rw [hc σ ⟨σ.fst, σ.fst_mem, h.1⟩ ⟨σ.snd, σ.snd_mem, h.2⟩ rfl rfl,
        hc σ.swap ⟨σ.snd, σ.snd_mem, h.2⟩ ⟨σ.fst, σ.fst_mem, h.1⟩ rfl rfl, hfanti, hN, neg_div]
    · have h' : ¬ (OV σ.swap.fst ∧ OV σ.swap.snd) := fun h' => h ⟨h'.2, h'.1⟩
      rw [show c σ.swap = a σ.swap from dif_neg h', show c σ = a σ from dif_neg h, ha σ]
  · intro E hE hEV
    rw [rationalCoeff_rationalProperPushforward_surfaceCoefficientDivisor_eq_finsum hY r hr v hv E
      c]
    set E₀ : 𝓔 := ⟨E, hE, hEV⟩
    rw [← hfdiv E₀]
    have hsplit : ∀ σ : DoubleSurface B, (∑ᶠ (_ : σ.fst = E) (z : Z)
        (_ : IsGenericPoint z σ.carrier) (_ : r.base z = v),
          (residueFieldDegree r z : ℚ) * c σ) =
        (if σ.fst = E₀.1 ∧ OV σ.snd then w σ * c σ else 0) +
          (if σ.fst = E₀.1 ∧ ¬ OV σ.snd then w σ * a σ else 0) := by
      intro σ
      rw [finsum_eq_if, hwmul]
      by_cases h1 : σ.fst = E
      · by_cases h2 : OV σ.snd
        · simp [E₀, h1, h2]
        · have : c σ = a σ := dif_neg fun h => h2 h.2
          simp [E₀, h1, h2, this]
      · simp [E₀, h1]
    rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun σ _ => hsplit σ,
      Finset.sum_add_distrib]
    congr 1
    rw [show (∑ x, if x.fst = E₀.1 ∧ OV x.snd then w x * c x else 0) =
        ∑ x, if OV x.snd ∧ x.fst = E₀.1 then w x * c x else 0 from
      Finset.sum_congr rfl fun x _ => by
        by_cases h1 : x.fst = E₀.1 <;> by_cases h2 : OV x.snd <;> simp [h1, h2]]
    refine Eq.trans (hfib (fun σ => σ.snd) (fun σ => σ.snd_mem) (fun σ => σ.fst = E₀.1)
      (fun x => w x * c x)).symm ?_
    refine Finset.sum_congr rfl fun E' _ => ?_
    have hterm : ∀ σ : DoubleSurface B, (if σ.snd = E'.1 ∧ σ.fst = E₀.1 then w σ * c σ else 0) =
        (if σ.fst = E₀.1 ∧ σ.snd = E'.1 then w σ else 0) * (f E₀ E' / N E₀ E') := by
      intro σ
      by_cases h : σ.fst = E₀.1 ∧ σ.snd = E'.1
      · rw [if_pos ⟨h.2, h.1⟩, if_pos h, hc σ E₀ E' h.1 h.2]
      · rw [if_neg fun h' => h ⟨h'.2, h'.1⟩, if_neg h, zero_mul]
    rw [Finset.sum_congr rfl fun σ _ => hterm σ, ← Finset.sum_mul]
    change N E₀ E' * (f E₀ E' / N E₀ E') = f E₀ E'
    by_cases hN0 : N E₀ E' = 0
    · rw [hN0, zero_mul, eq_comm]
      refine hfadj _ _ fun hadj => ?_
      rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with h | h
      · exact h ((hNeq _ _).trans hN0)
      · exact h ((hNeq _ _).trans ((hN _ _).trans hN0))
    · field_simp
  · intro σ hσ
    have h := hca σ hσ
    have hsub : r.base '' σ.carrier ⊆ (closure {v} : Set Y) :=
      h.1 ▸ Set.image_mono fun x hx => (σ.carrier_subset hx).1
    refine ⟨hsub, fun {X} p hp => ?_⟩
    have hsub' : (r ≫ p).base '' σ.carrier ⊆ p.base '' (closure {v} : Set Y) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
      exact Set.image_mono hsub
    exact (Topology.IsEmbedding.inclusion hsub').isInducing.topologicalKrullDim_le.trans hp

/-- **Generic balancing along a conductor surface.** Let `Y` be a normal complex fourfold, `Q` a
reduced effective divisor on `Y`, `r : Z ⟶ Y` a projective resolution and `B` the reduced snc
divisor with support `r⁻¹(Supp Q) ∪ Ex(r)`. Let `V` be a surface of `Y` whose generic point lies
in the smooth locus of `Y` and in `Supp Q`, at which `Supp Q` is not normal, and suppose the base
change of `r` to `Spec 𝒪_{Y,η_V}` is a finite sequence of point blowups starting with the closed
point. Let `a` be an oriented coefficient system on the double surfaces of `B` with
`∑ [κ(S) : κ(V)] a_S = 0`, the sum over the branch legs `S ⊆ Q'ⱼ ∩ E` (`Q'ⱼ` not exceptional,
`r(E) = V`) whose generic point maps to `η_V`. Then there is an oriented system `c`, equal to `a`
off the double surfaces of two components over `V`, such that `(r|_E)_* Z_E(c)` has coefficient
`0` along `V` for every component `E` of `B` with `r(E) = V`; every corrected double surface
maps into `V`, hence into dimension at most one under any `p` with `dim p(V) ≤ 1`. -/
@[mmp "lem_mmp_conductor_generic_surface_verticality"]
public theorem exists_orientedSurfaceCoefficients_rationalPushforward_coeff_eq_zero
    {Y Z : Scheme.{0}} [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : topologicalKrullDim Y = 4)
    (Q : Divisor Y) (hQ : MMP.Intersection.IsReducedEffective Q)
    [Z.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))] (r : Z ⟶ Y)
    [r.IsOver (Spec (.of ℂ))] [IsProper r] (hr : MMP.Intersection.IsResolution (Y ↘ Spec (.of ℂ)) r)
    (B : Divisor Z) (hB : MMP.Intersection.IsReducedEffective B)
    (hBsnc : DivisorWithCoeffs.IsSNC (r ≫ Y ↘ Spec (.of ℂ)) B)
    (hBsupp : (B.supp : Set Z) = r.base ⁻¹' (Q.supp : Set Y) ∪ exceptionalSet r)
    (v : Y) (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Y ↘ Spec (.of ℂ)) v = 2)
    (hVsmooth : v ∈ smoothLocus (Y ↘ Spec (.of ℂ)))
    (hVQ : v ∈ Q.supp)
    (hVcond : ∃ t : Q.suppScheme, Q.suppIdeal.subschemeι t = v ∧
      ¬ (IsDomain (Q.suppScheme.presheaf.stalk t) ∧
        IsIntegrallyClosed (Q.suppScheme.presheaf.stalk t)))
    (hgen : ∃ (s : MMP.Resolution.PointBlowupSequence
        (Spec (Y.presheaf.stalk v))) (n : ℕ) (hn : s.length = n)
      (e : s.S n ≅ Limits.pullback r (Y.fromSpecStalk v)),
        e.hom ≫ Limits.pullback.snd _ _ = s.π n hn.ge ∧
        ∃ h0 : ((0 : ℕ) : ℕ∞) < s.length,
          (s.π 0 h0.le).base (s.p 0) =
            IsLocalRing.closedPoint (Y.presheaf.stalk v))
    (a : DoubleSurface B → ℚ) (ha : a ∈ orientedSurfaceCoefficients B)
    (hsum : ∑ᶠ (σ : DoubleSurface B) (_ : σ.fst.genericPoint ∉ exceptionalSet r)
        (_ : r.base '' σ.snd.support = (closure {v} : Set Y)) (z : Z)
        (_ : IsGenericPoint z σ.carrier) (_ : r.base z = v),
          (residueFieldDegree r z : ℚ) * a σ = 0) :
    ∃ c ∈ orientedSurfaceCoefficients B,
      (∀ σ : DoubleSurface B, c σ ≠ a σ →
        r.base '' σ.fst.support = (closure {v} : Set Y) ∧
          r.base '' σ.snd.support = (closure {v} : Set Y)) ∧
      (∀ E ∈ B.support, r.base '' E.support = (closure {v} : Set Y) →
        Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) 2 v
            (Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ)
              (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) 2
              (E.idealSheaf.subschemeι ≫ r) (comp_over _ _)
              (Finsupp.linearCombination ℚ
                (fun P : MMP.Mori.PrimeDivisor E.idealSheaf.subscheme =>
                  if h : Stacks.Chow.relativeDimension
                      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                      (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = 2 then
                    Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ)
                      (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) 2 P.genericPoint h
                  else 0) (surfaceCoefficientDivisor c E))) = 0) ∧
      ∀ σ : DoubleSurface B, c σ ≠ a σ →
        r.base '' σ.carrier ⊆ (closure {v} : Set Y) ∧
          ∀ {X : Scheme.{0}} (p : Y ⟶ X),
            topologicalKrullDim (p.base '' (closure {v} : Set Y)) ≤ 1 →
            topologicalKrullDim ((r ≫ p).base '' σ.carrier) ≤ 1 :=
  exists_orientedSurfaceCoefficients_rationalPushforward_coeff_eq_zero_of_mem_supp hY Q r hr B
    hBsnc hBsupp v hv hVQ a ha hsum

end Fourfold

end MMP
