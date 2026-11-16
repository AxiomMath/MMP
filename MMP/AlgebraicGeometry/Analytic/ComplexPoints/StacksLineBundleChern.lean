module

public import MMP.AlgebraicGeometry.Chow.CycleClassFirstChern
public import MMP.AlgebraicGeometry.Analytic.BlowupFibre.Euler
public import MMP.AlgebraicTopology.ComplexVectorBundle.EulerClass

/-!
# The Euler class of the line bundle of an invertible module is its first Chern class

Let `X` be a scheme over `ℂ` and `𝓝` an invertible `𝒪_X`-module, with dual `𝓝^∨` and line
bundle `𝐕(𝓝^∨) → X`, whose points over `x` are the elements of the fibre `𝓝(x)`. The
topological first Chern class `c₁ᵗᵒᵖ(𝓝^∨) = 0^* u ∈ H²(X(ℂ); R)` of `𝐕(𝓝^∨)`, the pull-back of
its Thom class along the zero section (`MMP.Modules.topFirstChernClass`), is the first Chern class
`c₁(𝓝) ∈ H²(X^an; ℤ)` of `𝓝` (`MMP.Analytic.algebraicFirstChernClass`), with coefficients
changed to `R` and pulled back along `X(ℂ) ≅ X^an` (`MMP.Modules.topFirstChernClass_dual`).

The proof compares the two topological line bundles over `X(ℂ) ≅ X^an`. For a chart `(V, λ)` of
`𝓝^∨` (`λ` a basis of `Γ(V, 𝓝^∨)`) and a local generator `a` of `𝓝` on `W`, the function
`λ(a)` on `V ∩ W` is a unit (`MMP.Modules.pairExt_ne_zero`): `a` trivializes `𝓝` on `W`, so the
dual functional `μ` of `a` has `μ(a) = 1`, and `μ = h λ` near every point. The ratio
`v ↦ λ(v) / λ(a)(x)` of the `λ`-coordinate of a vector `v` over `x` is then a fibrewise linear
isomorphism from `𝐕(𝓝^∨)(ℂ)` to the topological line bundle of `𝓝`, read in the trivialization
of the generator `a` chosen at `x`; it is continuous, since changing the chart multiplies both
`λ(v)` and `λ(a)` by the transition function of `𝓝^∨`, and changing the generator multiplies
`λ(a)` by that of `𝓝`. A fibrewise linear bundle map carries Euler classes to Euler classes
(`MMP.Topology.cast_eulerClass_eq_map`), and the Euler class of a complex line bundle is its first
Chern class (`MMP.Analytic.ComplexLineBundle.congrIndex_eulerClass_eq_firstChernClass`).

## Main definitions

* `MMP.Modules.complexPointsHom X`: the homeomorphism `X(ℂ) ≅ X^an`, as a map of spaces.
* `MMP.Modules.pairExt N c s`: the function `λ(a)` on `(V ∩ W)(ℂ)`, extended by `0`.

## Main results

* `MMP.Modules.topFirstChernClass_dual`: `c₁ᵗᵒᵖ(𝓝^∨) = c₁(𝓝)` in `H²(X(ℂ); R)`.
* `MMP.Modules.toCohomology_pullback_thomClass_dual`: for a section `σ` of `𝐕(𝓝^∨)`, the
  localized class `σ^* u`, with its supports forgotten, is `c₁(𝓝)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], Thm. 12.5 and §14.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Opposite Bundle

namespace MMP.Modules

open UnderlyingSpace MMP.Analytic MMP.Analytic.InvertibleModule

/-! ### The pairing of the dual with a module -/

section Pairing

open Stacks.SheafOfModules

variable {X : Scheme.{0}} (N : X.Modules)

/-- The pairing of `𝓝^∨` with `𝓝` commutes with restriction. -/
theorem pairing_sectionRes {U V : X.Opens} (h : V ≤ U) (lam : Γ(Scheme.Modules.dual N, U))
    (m : Γ(N, U)) :
    Scheme.Modules.pairing N (sectionRes (Scheme.Modules.dual N) h lam) (sectionRes N h m) =
      X.presheaf.map (homOfLE h).op (Scheme.Modules.pairing N lam m) :=
  internalHom_app_restrict X.presheaf N.val
    (SheafOfModules.unit (TensorSheafification.structureSheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))).val U lam
    (op (Over.mk (homOfLE h))) m

/-- The pairing of `𝓝^∨` with `𝓝` is linear in the functional. -/
theorem pairing_smul_left {U : X.Opens} (a : Γ(X, U)) (lam : Γ(Scheme.Modules.dual N, U))
    (m : Γ(N, U)) :
    Scheme.Modules.pairing N (a • lam) m = a * Scheme.Modules.pairing N lam m := by
  have h : Scheme.Modules.pairing N (a • lam) m =
      X.presheaf.map (𝟙 (op U)) a * Scheme.Modules.pairing N lam m := rfl
  rw [h, X.presheaf.map_id]
  rfl

variable {N}

/-- For a local generator `a` of `𝓝` on `W` and an open `V ⊆ W`, the isomorphism
`𝒪_X(V) ≅ 𝓝(V)`, `c ↦ c a|_V`. -/
def generatorEquiv (s : Generator N) {V : X.Opens} (h : V ≤ s.W) : Γ(X, V) ≃ₗ[Γ(X, V)] Γ(N, V) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, V) Γ(N, V) (sectionRes N h s.a))
    (s.bijective V h)

/-- `generatorEquiv s h` sends `c` to `c • a|_V`. -/
lemma generatorEquiv_apply (s : Generator N) {V : X.Opens} (h : V ≤ s.W) (c : Γ(X, V)) :
    generatorEquiv s h c = c • sectionRes N h s.a :=
  rfl

/-- The trivialization of `𝓝` over `W` given by a local generator `a`: `c a|_V ↦ c`. -/
def generatorTrivialization (s : Generator N) :
    Stacks.SheafDescent.Trivialization X.presheaf N.val s.W where
  θ V h := (generatorEquiv s (leOfHom h)).symm
  θ_naturality {V V'} h h' m := by
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    have hc : (generatorEquiv s (leOfHom h)).symm m • sectionRes N (leOfHom h) s.a = m :=
      (generatorEquiv s (leOfHom h)).apply_symm_apply m
    conv_lhs => rw [← hc]
    change sectionRes N (leOfHom h') _ = _
    rw [sectionRes_smul, sectionRes_sectionRes]
    rfl

/-- The functional `μ ∈ Γ(W, 𝓝^∨)` dual to a local generator `a`: `μ(c a) = c`. -/
def generatorDual (s : Generator N) : Γ(Scheme.Modules.dual N, s.W) :=
  Scheme.Modules.trivializationDual (generatorTrivialization s)

/-- The dual functional of a local generator takes the value `1` on it. -/
lemma pairing_generatorDual (s : Generator N) :
    Scheme.Modules.pairing N (generatorDual s) s.a = 1 := by
  change (generatorEquiv s le_rfl).symm s.a = 1
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  rw [generatorEquiv_apply, one_smul]
  exact (PresheafOfModules.map_id_apply N.val (op s.W) s.a).symm

end Pairing

/-! ### The pairing of a chart of `𝓝^∨` with a local generator of `𝓝` -/

section Values

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (N : X.Modules)
  [(Scheme.Modules.dual N).IsQuasicoherent]

/-- The function `λ(a) ∈ Γ(V ∩ W, 𝒪_X)` of a chart `(V, λ)` of `𝓝^∨` and a local generator `a`
of `𝓝` on `W`. -/
def chartPairing (c : Chart (Scheme.Modules.dual N) 1) (s : Generator N) : Γ(X, c.1.1 ⊓ s.W) :=
  Scheme.Modules.pairing N (sectionRes (Scheme.Modules.dual N) inf_le_left (c.2 0))
    (sectionRes N inf_le_right s.a)

/-- The values `λ(a)(x)` at the points `x ∈ (V ∩ W)(ℂ)` (and `0` elsewhere). -/
def pairExt (c : Chart (Scheme.Modules.dual N) 1) (s : Generator N) :
    UnderlyingSpace ℂ X → ℂ :=
  UnderlyingSpace.evalExt (c.1.1 ⊓ s.W) (chartPairing N c s)

variable {N}

omit [X.Over (Spec (.of ℂ))] [(Scheme.Modules.dual N).IsQuasicoherent] in
/-- The restriction of `λ(a)` to an open `U ⊆ V ∩ W` is `λ|_U (a|_U)`. -/
lemma pairing_sectionRes_chart (c : Chart (Scheme.Modules.dual N) 1) (s : Generator N)
    {U : X.Opens} (hU : U ≤ c.1.1 ⊓ s.W) :
    Scheme.Modules.pairing N (sectionRes (Scheme.Modules.dual N) (hU.trans inf_le_left) (c.2 0))
        (sectionRes N (hU.trans inf_le_right) s.a) =
      X.presheaf.map (homOfLE hU).op (chartPairing N c s) := by
  rw [← sectionRes_sectionRes (L := Scheme.Modules.dual N) inf_le_left hU,
    ← sectionRes_sectionRes (L := N) inf_le_right hU, pairing_sectionRes]
  rfl

omit [(Scheme.Modules.dual N).IsQuasicoherent] in
/-- `λ(a)(x)`, computed on any open `U ⊆ V ∩ W` around `x`. -/
lemma pairExt_eq_eval (c : Chart (Scheme.Modules.dual N) 1) (s : Generator N) {U : X.Opens}
    (hU : U ≤ c.1.1 ⊓ s.W) (x : UnderlyingSpace ℂ X) (hx : ⊤ ≤ x.toHom ⁻¹ᵁ U) :
    pairExt N c s x = eval x hx (Scheme.Modules.pairing N
      (sectionRes (Scheme.Modules.dual N) (hU.trans inf_le_left) (c.2 0))
      (sectionRes N (hU.trans inf_le_right) s.a)) := by
  rw [pairing_sectionRes_chart c s hU, eval_restrict]
  exact UnderlyingSpace.evalExt_of_le _ _

/-- Evaluation at a point is multiplicative. -/
lemma eval_mul_eq {U : X.Opens} (p : UnderlyingSpace ℂ X) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U)
    (f g : Γ(X, U)) : eval p hp (f * g) = eval p hp f * eval p hp g := by
  simp only [UnderlyingSpace.eval, map_mul]

/-- **`λ(a)` does not vanish on `(V ∩ W)(ℂ)`**: on a basic open `D(f) ⊆ V ∩ W` around `x`, the
dual functional `μ` of `a` is `h λ`, and `1 = μ(a) = h λ(a)`. -/
lemma pairExt_ne_zero (c : Chart (Scheme.Modules.dual N) 1) (s : Generator N)
    (x : UnderlyingSpace ℂ X) (hx : ⊤ ≤ x.toHom ⁻¹ᵁ (c.1.1 ⊓ s.W)) : pairExt N c s x ≠ 0 := by
  have hz := (top_le_preimage_iff x _).1 hx
  obtain ⟨f, hf, hzf⟩ := (isAffineOpen_affineOpens c.1).exists_basicOpen_le ⟨_, hz.2⟩ hz.1
  have hD : X.basicOpen f ≤ c.1.1 ⊓ s.W := le_inf (X.basicOpen_le f) hf
  have hxD : ⊤ ≤ x.toHom ⁻¹ᵁ X.basicOpen f := (top_le_preimage_iff x _).2 hzf
  set b := basisBasicOpen (isAffineOpen_affineOpens c.1) c.2 f
  set μ := sectionRes (Scheme.Modules.dual N) hf (generatorDual s)
  have hμ : b.repr μ 0 • b 0 = μ := by
    simpa only [Fin.sum_univ_one] using b.sum_repr μ
  have hb : b 0 = sectionRes (Scheme.Modules.dual N) (hD.trans inf_le_left) (c.2 0) :=
    basisBasicOpen_apply _ _ _ _
  have h1 : Scheme.Modules.pairing N μ (sectionRes N hf s.a) = 1 := by
    rw [pairing_sectionRes, pairing_generatorDual, map_one]
  rw [← hμ, hb, pairing_smul_left] at h1
  have h2 := congrArg (eval x hxD) h1
  rw [eval_mul_eq] at h2
  intro h0
  rw [pairExt_eq_eval c s hD x hxD] at h0
  have h0' : eval x hxD (Scheme.Modules.pairing N
      (sectionRes (Scheme.Modules.dual N) (hD.trans inf_le_left) (c.2 0))
      (sectionRes N hf s.a)) = 0 := h0
  rw [h0', mul_zero] at h2
  simp only [UnderlyingSpace.eval, map_one] at h2
  exact zero_ne_one h2

/-- **Changing the chart** multiplies `λ(a)` by the transition function of `𝓝^∨`. -/
lemma pairExt_chart (c c' : Chart (Scheme.Modules.dual N) 1) (s : Generator N)
    (x : UnderlyingSpace ℂ X) (hx : ⊤ ≤ x.toHom ⁻¹ᵁ (c.1.1 ⊓ (c'.1.1 ⊓ s.W))) :
    pairExt N c' s x = transition c c' x 0 0 * pairExt N c s x := by
  have hz := (top_le_preimage_iff x _).1 hx
  obtain ⟨f, hf, hzf⟩ := (isAffineOpen_affineOpens c.1).exists_basicOpen_le ⟨_, hz.2⟩ hz.1
  have ha : X.basicOpen f ≤ c'.1.1 := hf.trans inf_le_left
  have hD : X.basicOpen f ≤ c.1.1 ⊓ s.W := le_inf (X.basicOpen_le f) (hf.trans inf_le_right)
  have hxD : ⊤ ≤ x.toHom ⁻¹ᵁ X.basicOpen f := (top_le_preimage_iff x _).2 hzf
  have hT := restrict_eq_sum_transitionSection c c' f ha 0
  rw [Fin.sum_univ_one] at hT
  rw [transition_eq_of_basicOpen c c' f ha x hxD, Matrix.of_apply, pairExt_eq_eval c' s hf x hxD,
    pairExt_eq_eval c s hD x hxD, ← eval_mul_eq]
  congr 1
  change Scheme.Modules.pairing N
    ((Scheme.Modules.dual N).presheaf.map (homOfLE ha).op (c'.2 0)) _ = _
  rw [hT, pairing_smul_left]
  rfl

omit [X.Over (Spec (.of ℂ))] [(Scheme.Modules.dual N).IsQuasicoherent] in
/-- The restriction of `a = g a'` to an open `U ⊆ W ∩ W'`. -/
lemma sectionRes_generator_eq (s s' : Generator N) {U : X.Opens} (hV : U ≤ s.W ⊓ s'.W) :
    sectionRes N (hV.trans inf_le_left) s.a =
      X.presheaf.map (homOfLE hV).op (InvertibleModule.transitionSection s s') •
        sectionRes N (hV.trans inf_le_right) s'.a := by
  have e := congrArg (sectionRes N hV) (InvertibleModule.transitionSection_smul s s')
  rw [sectionRes_smul, sectionRes_sectionRes, sectionRes_sectionRes] at e
  exact e.symm

omit [(Scheme.Modules.dual N).IsQuasicoherent] in
/-- **Changing the generator** multiplies `λ(a)` by the transition function of `𝓝`. -/
lemma pairExt_generator (c : Chart (Scheme.Modules.dual N) 1) (s s' : Generator N)
    (x : UnderlyingSpace ℂ X) (hx : ⊤ ≤ x.toHom ⁻¹ᵁ (c.1.1 ⊓ (s.W ⊓ s'.W)))
    (hW : ⊤ ≤ x.toHom ⁻¹ᵁ (s.W ⊓ s'.W)) :
    pairExt N c s x =
      UnderlyingSpace.eval x hW (InvertibleModule.transitionSection s s') * pairExt N c s' x := by
  have hU : c.1.1 ⊓ (s.W ⊓ s'.W) ≤ c.1.1 ⊓ s.W := inf_le_inf_left _ inf_le_left
  have hU' : c.1.1 ⊓ (s.W ⊓ s'.W) ≤ c.1.1 ⊓ s'.W := inf_le_inf_left _ inf_le_right
  have hV : c.1.1 ⊓ (s.W ⊓ s'.W) ≤ s.W ⊓ s'.W := inf_le_right
  rw [pairExt_eq_eval c s hU x hx, pairExt_eq_eval c s' hU' x hx, ← eval_restrict hV x hx,
    ← eval_mul_eq]
  congr 1
  rw [← Scheme.Modules.pairing_smul_right, ← sectionRes_generator_eq s s' hV]

end Values

/-! ### The comparison of the two line bundles -/

section Comparison

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (N : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]

/-- The point of `X^an` over a point of `X(ℂ)`. -/
abbrev anPoint (x : UnderlyingSpace ℂ X) : ComplexPoints (X ↘ Spec (.of ℂ)) :=
  ComplexPoints.homeomorphUnderlyingSpace.symm x

/-- The local generator of `𝓝` chosen at the point of `X^an` over `x` by the topological line
bundle of `𝓝`. -/
abbrev genAt (x : UnderlyingSpace ℂ X) : Generator N :=
  (lineBundleCore N).indexAt (anPoint x)

omit [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] in
/-- A point of `X(ℂ)` whose point of `X^an` lies in the chart `W(ℂ)` lies in `W`. -/
lemma top_le_of_mem_chart {W : X.Opens} (x : UnderlyingSpace ℂ X)
    (h : anPoint x ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) W) :
    ⊤ ≤ x.toHom ⁻¹ᵁ W := by
  have := ComplexPoints.top_le_preimage_of_mem_chart ⟨_, h⟩
  have e : ComplexPoints.toUnderlyingSpace (anPoint x) = x :=
    ComplexPoints.homeomorphUnderlyingSpace.apply_symm_apply x
  rw [e] at this
  exact this

/-- A point lies in the open of the generator chosen at it. -/
lemma top_le_genAt (x : UnderlyingSpace ℂ X) : ⊤ ≤ x.toHom ⁻¹ᵁ (genAt N x).W :=
  top_le_of_mem_chart x ((lineBundleCore N).mem_baseSet_at (anPoint x))

/-- A point lies in the chart of `𝓝^∨` and in the open of the generator of `𝓝` chosen at it. -/
lemma top_le_chartAt_genAt (x : UnderlyingSpace ℂ X) :
    ⊤ ≤ x.toHom ⁻¹ᵁ ((chartAt (Scheme.Modules.dual N) 1 x).1.1 ⊓ (genAt N x).W) :=
  fun _ hz ↦ ⟨mem_chartBase_chartAt (Scheme.Modules.dual N) 1 x hz, top_le_genAt N x hz⟩

/-- The value `λ(a)(x) ≠ 0` for the chart `(V, λ)` and the generator `a` chosen at `x`. -/
def ratioDen (x : UnderlyingSpace ℂ X) : ℂ :=
  pairExt N (chartAt (Scheme.Modules.dual N) 1 x) (genAt N x) x

/-- The value `ratioDen N x` is nonzero. -/
lemma ratioDen_ne_zero (x : UnderlyingSpace ℂ X) : ratioDen N x ≠ 0 :=
  pairExt_ne_zero _ _ x (top_le_chartAt_genAt N x)

/-- The coordinate `v ↦ λ(v) / λ(a)(x)` of a vector `v` over `x` with respect to the generator `a`
chosen at `x`, as a continuous linear isomorphism `𝐕(𝓝^∨)_x(ℂ) ≅ ℂ`. -/
def fibreRatioEquiv (x : UnderlyingSpace ℂ X) : Fibre (Scheme.Modules.dual N) 1 x ≃L[ℂ] ℂ :=
  ((chartTrivialization (chartAt (Scheme.Modules.dual N) 1 x)).continuousLinearEquivAt ℂ x
      (mem_chartBase_chartAt (Scheme.Modules.dual N) 1 x)).trans
    ((ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).trans
      (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ (inv_ne_zero (ratioDen_ne_zero N x)))))

/-- `fibreRatioEquiv N x` sends `v` to its chart coordinate divided by `ratioDen N x`. -/
lemma fibreRatioEquiv_apply (x : UnderlyingSpace ℂ X) (v : Fibre (Scheme.Modules.dual N) 1 x) :
    fibreRatioEquiv N x v = coord (chartAt (Scheme.Modules.dual N) 1 x) v.1 0 * (ratioDen N x)⁻¹ :=
  rfl

/-- The comparison map `Σ x, 𝐕(𝓝^∨)_x(ℂ) → Σ y, 𝓝^top_y` of the topological bundle of
`𝐕(𝓝^∨)` with the topological line bundle of `𝓝`, over `X(ℂ) ≅ X^an`. -/
def lineBundleMap (p : TotalSpace (Fin 1 → ℂ) (Fibre (Scheme.Modules.dual N) 1)) :
    TotalSpace ℂ (topologicalLineBundle N) :=
  ⟨anPoint p.proj, fibreRatioEquiv N p.proj p.2⟩

omit [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] in
/-- Evaluation at equal points agrees. -/
lemma eval_congr_point {U : X.Opens} {p q : UnderlyingSpace ℂ X} (hpq : p = q)
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U) (hq : ⊤ ≤ q.toHom ⁻¹ᵁ U) (g : Γ(X, U)) :
    UnderlyingSpace.eval p hp g = UnderlyingSpace.eval q hq g := by
  subst hpq
  rfl

/-- The comparison map is continuous: in the trivialization of the generator `a₀` chosen at
`x₀` and the chart `(V₀, λ₀)` at `x₀`, it is `v ↦ λ₀(v) / λ₀(a₀)(x)` near `x₀`. -/
theorem continuous_lineBundleMap : Continuous (lineBundleMap N) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(ComplexPoints.homeomorphUnderlyingSpace.symm.continuous.comp
    (continuous_totalSpace_proj _ 1)).continuousAt, ?_⟩
  set x₀ := p₀.proj
  set s₀ := genAt N x₀
  set c₀ := chartAt (Scheme.Modules.dual N) 1 x₀
  have hx₀ : ⊤ ≤ x₀.toHom ⁻¹ᵁ (c₀.1.1 ⊓ s₀.W) := top_le_chartAt_genAt N x₀
  set S : Set (UnderlyingSpace ℂ X) := {x | ⊤ ≤ x.toHom ⁻¹ᵁ (c₀.1.1 ⊓ s₀.W)}
  have hS : IsOpen S := isOpen_setOf_le_preimage _
  have hN : ∀ᶠ p in nhds p₀, p.proj ∈ S :=
    (continuous_totalSpace_proj _ 1).continuousAt.preimage_mem_nhds (hS.mem_nhds hx₀)
  set G : TotalSpace (Fin 1 → ℂ) (Fibre (Scheme.Modules.dual N) 1) → ℂ :=
    fun p ↦ coord c₀ p.2.1 0 / pairExt N c₀ s₀ p.proj
  have hG : ContinuousAt G p₀ := by
    refine ContinuousAt.div ?_ (ContinuousAt.comp (g := pairExt N c₀ s₀)
      ((UnderlyingSpace.continuousOn_evalExt _ _).continuousAt (hS.mem_nhds hx₀))
      (continuous_totalSpace_proj _ 1).continuousAt) (pairExt_ne_zero c₀ s₀ x₀ hx₀)
    have h1 : ContinuousAt (fun p ↦ (chartTrivialization c₀ p).2) p₀ :=
      continuous_snd.continuousAt.comp ((chartTrivialization c₀).continuousOn.continuousAt
        ((chartTrivialization c₀).open_source.mem_nhds
          (mem_chartBase_chartAt (Scheme.Modules.dual N) 1 x₀)))
    exact (continuous_apply 0).continuousAt.comp h1
  refine hG.congr ?_
  filter_upwards [hN] with p hp
  set x := p.proj
  change coord c₀ p.2.1 0 / pairExt N c₀ s₀ x =
    ((lineBundleCore N).localTriv ((lineBundleCore N).indexAt (anPoint x₀)) (lineBundleMap N p)).2
  rw [VectorBundleCore.localTriv_apply]
  change _ = InvertibleModule.evalExt _ (InvertibleModule.transitionSection (genAt N x) s₀)
    (anPoint x) * fibreRatioEquiv N x p.2
  set cx := chartAt (Scheme.Modules.dual N) 1 x
  set sx := genAt N x
  have hcx : x ∈ chartBase cx := mem_chartBase_chartAt (Scheme.Modules.dual N) 1 x
  have hsx : ⊤ ≤ x.toHom ⁻¹ᵁ sx.W := top_le_genAt N x
  have hxx : ⊤ ≤ x.toHom ⁻¹ᵁ (sx.W ⊓ s₀.W) := fun z hz ↦ ⟨hsx hz, (hp hz).2⟩
  have hmem : anPoint x ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (sx.W ⊓ s₀.W) :=
    le_antisymm le_top hxx
  have hτ : InvertibleModule.evalExt _ (InvertibleModule.transitionSection sx s₀) (anPoint x) =
      UnderlyingSpace.eval x hxx (InvertibleModule.transitionSection sx s₀) := by
    rw [InvertibleModule.evalExt_of_mem _ hmem, ComplexPoints.eval_eq]
    exact eval_congr_point (ComplexPoints.homeomorphUnderlyingSpace.apply_symm_apply x) _ _ _
  have hP3 := pairExt_generator cx sx s₀ x (fun _ hz ↦ ⟨hcx hz, hxx hz⟩) hxx
  have hP2 := pairExt_chart cx c₀ s₀ x (fun _ hz ↦ ⟨hcx hz, hp hz⟩)
  have hpc : mapFun (proj (Scheme.Modules.dual N)) p.2.1 ∈ chartBase cx ∩ chartBase c₀ := by
    rw [p.2.2]
    exact ⟨hcx, fun _ hz ↦ (hp hz).1⟩
  have hco : coord c₀ p.2.1 0 = transition cx c₀ x 0 0 * coord cx p.2.1 0 := by
    rw [coord_eq_transition_mulVec cx c₀ p.2.1 (top_le_preimage_proj_inf hpc), p.2.2]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
    rfl
  have hne₀ := pairExt_ne_zero c₀ s₀ x hp
  have hnex := pairExt_ne_zero cx s₀ x (fun _ hz ↦ ⟨hcx hz, (hp hz).2⟩)
  have hden := ratioDen_ne_zero N x
  rw [hP2] at hne₀
  change pairExt N cx sx x ≠ 0 at hden
  rw [hP3] at hden
  rw [hτ, fibreRatioEquiv_apply, hco, hP2]
  change _ = _ * (_ * (pairExt N cx sx x)⁻¹)
  rw [hP3]
  have hT : transition cx c₀ x 0 0 ≠ 0 := left_ne_zero_of_mul hne₀
  have hτ0 := left_ne_zero_of_mul hden
  field_simp
  rfl

end Comparison

/-! ### Change of coefficients -/

section Coefficients

open SingularChain SingularCochain

variable (R : Type) [CommRing R]

/-- The change of coefficients `H^n(Y, A; ℤ) → H^n(Y, A; R)`, `[φ] ↦ [φ]`. -/
def relMapCoeff {Y : TopCat.{0}} (A : Set Y) (n : ℕ) :
    relativeSingularCohomology ℤ (ModuleCat.of ℤ ℤ) Y A n →ₛₗ[Int.castRingHom R]
      relativeSingularCohomology R (ModuleCat.of R R) Y A n :=
  ((relativeSingularCohomologyEquiv R A n).symm.toLinearMap.comp
    (singularCohomology.relCohomologyMap (Int.castRingHom R) A n)).comp
      (relativeSingularCohomologyEquiv ℤ A n).toLinearMap

/-- On cocycles modulo coboundaries, the change of coefficients is `[φ] ↦ [φ]`. -/
theorem relativeSingularCohomologyEquiv_relMapCoeff {Y : TopCat.{0}} (A : Set Y) (n : ℕ)
    (x : relativeSingularCohomology ℤ (ModuleCat.of ℤ ℤ) Y A n) :
    relativeSingularCohomologyEquiv R A n (relMapCoeff R A n x) =
      singularCohomology.relCohomologyMap (Int.castRingHom R) A n
        (relativeSingularCohomologyEquiv ℤ A n x) := by
  simp only [relMapCoeff, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply]

/-- The change of coefficients commutes with the maps induced by maps of pairs. -/
theorem relMapCoeff_map {Y' Y : TopCat.{0}} (g : Y' ⟶ Y) {A' : Set Y'} {A : Set Y}
    (h : A' ⊆ g ⁻¹' A) (n : ℕ) (x : relativeSingularCohomology ℤ (ModuleCat.of ℤ ℤ) Y A n) :
    relMapCoeff R A' n ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) g h n).hom x) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) g h n).hom (relMapCoeff R A n x) := by
  apply (relativeSingularCohomologyEquiv R A' n).injective
  rw [relativeSingularCohomologyEquiv_map, relativeSingularCohomologyEquiv_relMapCoeff,
    relativeSingularCohomologyEquiv_relMapCoeff, relativeSingularCohomologyEquiv_map]
  generalize relativeSingularCohomologyEquiv ℤ A n x = y
  induction y using Submodule.Quotient.induction_on with | H φ => rfl

variable {B : Type} [TopologicalSpace B]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : B → Type} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [_root_.VectorBundle ℂ F E]

/-- The change of coefficients carries the integral Thom class to the Thom class over `R`. -/
theorem relMapCoeff_thomClass :
    relMapCoeff R _ _ (ThomClass.thomClass ℤ F E) = ThomClass.thomClass R F E := by
  refine ThomClass.eq_thomClass F E fun x ψ v hv ↦ ?_
  have h := ThomClass.isThomClass_thomClass (R := ℤ) F E x ψ v hv
  rw [relativeSingularCohomologyEquiv_relMapCoeff]
  revert h
  generalize relativeSingularCohomologyEquiv ℤ _ _ (ThomClass.thomClass ℤ F E) = y
  induction y using Submodule.Quotient.induction_on with | H φ => ?_
  intro h
  rw [relEval_mk, eval_single_one] at h
  have h1 : (Int.castRingHom R) (φ.1 (ThomClass.fibreSimplex F x ψ v)) = 1 := by
    rw [h, map_one]
  exact (eval_single_one _ _).trans h1

/-- The change of coefficients carries the integral Euler class to the Euler class over `R`. -/
theorem relMapCoeff_eulerClass :
    relMapCoeff R _ _ (MMP.Topology.eulerClass ℤ F E) = MMP.Topology.eulerClass R F E :=
  (relMapCoeff_map R _ _ _ _).trans
    (congrArg (relativeSingularCohomology.map R (ModuleCat.of R R)
      (MMP.Topology.bundleZeroSection F E) _ _).hom (relMapCoeff_thomClass R))

/-- Transporting along an equality of degrees commutes with the change of coefficients. -/
lemma cast_relMapCoeff {Y : TopCat.{0}} {A : Set Y} {n m : ℕ} (h : n = m)
    (x : relativeSingularCohomology ℤ (ModuleCat.of ℤ ℤ) Y A (n : ℤ)) :
    cast (congrArg (fun k : ℕ ↦ (relativeSingularCohomology R (ModuleCat.of R R) Y A (k : ℤ) :
        Type)) h) (relMapCoeff R A n x) =
      relMapCoeff R A m (cast (congrArg (fun k : ℕ ↦ (relativeSingularCohomology ℤ
        (ModuleCat.of ℤ ℤ) Y A (k : ℤ) : Type)) h) x) := by
  subst h
  rfl

variable {R} in
/-- Moving a class to an equal degree is a cast. -/
lemma congrIndex_eq_cast {Y : TopCat.{0}} {S : Set Y} {n m : ℕ} (h : n = m)
    (hk : (n : ℤ) = (m : ℤ)) (x : relativeSingularCohomology R (ModuleCat.of R R) Y S (n : ℤ)) :
    cohomologyWithSupports.congrIndex R Y rfl hk x =
      cast (congrArg (fun k : ℕ ↦ (relativeSingularCohomology R (ModuleCat.of R R) Y S (k : ℤ) :
        Type)) h) x := by
  subst h
  rfl

/-- A cast is the composite of two casts. -/
lemma cast_eq_cast_cast {α β γ : Type} (h : α = γ) (h₁ : α = β) (h₂ : β = γ) (x : α) :
    cast h x = cast h₂ (cast h₁ x) := by
  subst h₁
  subst h₂
  rfl

end Coefficients

/-! ### The Euler class of `𝐕(𝓝^∨)` is the first Chern class of `𝓝` -/

section Chern

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]

/-- The homeomorphism `X(ℂ) ≅ X^an`, as a map of spaces. -/
abbrev complexPointsHom :
    TopCat.of (UnderlyingSpace ℂ X) ⟶ Analytification.space (X ↘ Spec (.of ℂ)) :=
  TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩

variable {X} (R : Type) [CommRing R] (N : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]

/-- **The Euler class of the line bundle of an invertible module is its first Chern class.** For
an invertible module `𝓝` on a scheme over `ℂ`, the pull-back along the zero section of the Thom
class of `𝐕(𝓝^∨)` is the first Chern class of `𝓝`, with coefficients in `R`, pulled back along
`X(ℂ) ≅ X^an`. -/
theorem topFirstChernClass_dual :
    topFirstChernClass R (Scheme.Modules.dual N) =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (complexPointsHom X) univ 2).hom
        (singularCohomology.mapCoeff (Int.castRingHom R) 2 (algebraicFirstChernClass N)) := by
  rw [topFirstChernClass, ← cast_eulerClass_eq_map_thomClass R (Scheme.Modules.dual N) 1]
  have hF : Module.finrank ℂ (Fin 1 → ℂ) = Module.finrank ℂ ℂ := by
    rw [Module.finrank_fin_fun, Module.finrank_self]
  have hn2 : 2 * Module.finrank ℂ ℂ = 2 * 1 := by rw [Module.finrank_self]
  let g : C(UnderlyingSpace ℂ X, ComplexPoints (X ↘ Spec (.of ℂ))) :=
    ⟨anPoint, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩
  let Φ : TopCat.of (TotalSpace (Fin 1 → ℂ) (Fibre (Scheme.Modules.dual N) 1)) ⟶
      TopCat.of (TotalSpace ℂ (topologicalLineBundle N)) :=
    TopCat.ofHom ⟨lineBundleMap N, continuous_lineBundleMap N⟩
  refine (cast_eq_cast_cast _ (congrArg (fun k : ℕ ↦ (relativeSingularCohomology R
      (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (univᶜ) (k : ℤ) : Type))
      (congrArg (2 * ·) hF)) (congrArg (fun k : ℕ ↦ (relativeSingularCohomology R
      (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (univᶜ) (k : ℤ) : Type)) hn2)
      _).trans ?_
  refine (congrArg (cast (congrArg (fun k : ℕ ↦ (relativeSingularCohomology R
      (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (univᶜ) (k : ℤ) : Type)) hn2))
      (MMP.Topology.cast_eulerClass_eq_map (R := R) (Φ := Φ) (g := g)
        (φ := fun x ↦ fibreRatioEquiv N x) (fun x v ↦ rfl) hF)).trans ?_
  refine (MMP.Topology.cast_map_relativeSingularCohomology _ _ hn2 _).trans ?_
  rw [← relMapCoeff_eulerClass, cast_relMapCoeff R hn2]
  have hc : cast (congrArg (fun k : ℕ ↦ (relativeSingularCohomology ℤ (ModuleCat.of ℤ ℤ)
      (TopCat.of (ComplexPoints (X ↘ Spec (.of ℂ)))) (univᶜ) (k : ℤ) : Type)) hn2)
      (MMP.Topology.eulerClass ℤ ℂ (topologicalLineBundle N)) =
      firstChernClass (topologicalLineBundle N) :=
    (congrIndex_eq_cast hn2 (by rw [hn2]) _).symm.trans
      (ComplexLineBundle.congrIndex_eulerClass_eq_firstChernClass
        (E := topologicalLineBundle N))
  rw [hc]
  rfl

/-- **The localized class of a section of `𝐕(𝓝^∨)` is the first Chern class of `𝓝`**: for a
section `σ` of the line bundle `𝐕(𝓝^∨)` of an invertible module `𝓝` on a scheme over `ℂ`, the
image in `H²(X(ℂ); R)` of `σ^* u ∈ H²(X(ℂ), X(ℂ) - Z(σ)(ℂ); R)` is `c₁(𝓝)`, pulled back along
`X(ℂ) ≅ X^an`. -/
theorem toCohomology_pullback_thomClass_dual {σ : X ⟶ totalSpace (Scheme.Modules.dual N)}
    [σ.IsOver (Spec (.of ℂ))] (hσ : σ ≫ proj (Scheme.Modules.dual N) = 𝟙 X) :
    (cohomologyWithSupports.toCohomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X))
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (zeroSection (Scheme.Modules.dual N))))
          ((2 * 1 : ℕ) : ℤ)).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
        (range (UnderlyingSpace.map (K := ℂ) (zeroSection (Scheme.Modules.dual N))))
          ((2 * 1 : ℕ) : ℤ)).hom
        (thomClass R (Scheme.Modules.dual N) 1)) =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (complexPointsHom X) univ 2).hom
        (singularCohomology.mapCoeff (Int.castRingHom R) 2 (algebraicFirstChernClass N)) :=
  (toCohomology_pullback_thomClass R hσ).trans (topFirstChernClass_dual R N)

end Chern

end MMP.Modules
