module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.PullbackMap.ChartFormPullback
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.PullbackMap.RootQuotient
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Place.IntegralRoots
public import MMP.AlgebraicGeometry.Morphisms.SmoothLocalRings

/-!
# The pull-back `θ ↦ g^*θ / z` at a prime divisor of the cover

Let `θ` be a section over `W` of the fractional logarithmic complex
`C^p = 𝒪_V(-M) · Ω^p_V(log D)(-S)`, with rational form `ρ`, and `g : V' ⟶ V` a dominant morphism
of normal integral schemes smooth over a perfect field, with `z^N = g^*ψ`, `N M = Bn + div ψ`,
`0 ≤ Bn`, `D = S + Supp Bn`. At a prime divisor `E'` of `V'` with `g(η_{E'}) = x ∈ W`, the rational
`p`-form `z⁻¹ g^*ρ` lies in the wedges of the regular lattice of `𝒪_{V',E'}`, and, when `x` is the
generic point of a component of `S`, in the maximal ideal times the wedges of the logarithmic
lattice.

Near `x`, `ρ = ∑ᵢ gᵢ ∑_K c_{i,K} β_K` with `gᵢ ∈ 𝒪_V(-M)`, `c_{i,K}` in the ideal of `S` and
`β_K` wedges of logarithmic chart forms of `D` at `x`. The factor `z⁻¹ g^*gᵢ` is integral at `E'`
since its `N`-th power is the pull-back of `gᵢ^N / ψ ∈ 𝒪_{V,x}`; the pull-backs of the chart forms
are logarithmic. If a component `F` of `D` passes through `x`, then either `F` is a component of
`S` and the `c_{i,K}` vanish at `x`, or `Bn_F ≥ 1` and `gᵢ^N / ψ` vanishes at `x`: in both cases
the coefficients lie in the maximal ideal of `𝒪_{V',E'}`, which cancels the logarithmic poles. If
`x` is the generic point of a component of `S`, the `c_{i,K}` vanish at `x`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_forall_openFormsMap_ratForm_eq`: the rational
  form of a section of `C^p`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_ratForm_eq_sum`: its expansion in a chart.
* `MMP.FourfoldProofs.FractionalLogComplexProof.smul_mapExteriorPower_eq_sum`: the pull-back of the
  expansion.
* `MMP.FourfoldProofs.FractionalLogComplexProof.mem_lattices_of_cover`: the lattices of `z⁻¹ g^*ρ`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.67
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

/-- **The pull-back of a combination of wedges.** For a tower `k → K → L` and
`ρ = ∑ᵢ Gᵢ ∑_K C_{i,K} ∧_l χ_{κ K l}` in `⋀^p Ω_{K/k}`,
`z⁻¹ · ρ|_L = ∑_{i,K} (z⁻¹ Gᵢ) C_{i,K} ∧_l χ_{κ K l}|_L`. -/
theorem smul_mapExteriorPower_eq_sum {k K L : Type u} [CommRing k] [CommRing K] [CommRing L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] {m n p : ℕ} {ι : Type*}
    [Fintype ι] (G : Fin m → K) (C : Fin m → ι → K) (χ : Fin n → Ω[K⁄k])
    (κ : ι → Fin p → Fin n) (z : L) :
    z • KaehlerDifferential.mapExteriorPower k K L p
        (∑ i, G i • ∑ q, C i q • exteriorPower.ιMulti K p (χ ∘ κ q)) =
      ∑ iq : Fin m × ι, (z * algebraMap K L (G iq.1) * algebraMap K L (C iq.1 iq.2)) •
        exteriorPower.ιMulti L p
          ((KaehlerDifferential.map k k K L ∘ χ) ∘ κ iq.2) := by
  rw [Fintype.sum_prod_type, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul, map_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [LinearMap.map_smul, KaehlerDifferential.mapExteriorPower_ιMulti,
    ← algebraMap_smul L (C i q), ← algebraMap_smul L (G i), smul_smul, smul_smul, mul_assoc]
  rfl

/-- **The rational form at a point, in a chart.** Near `x ∈ W`, the rational form `ρ` of a
section of `C^p` is `∑ᵢ gᵢ ∑_K c_{i,K} β_K`, with `gᵢ` satisfying the divisorial condition on an
affine `W₃ ∋ x`, `c_{i,K}` in the ideal of `S`, and `β_K` wedges of chart forms of `D` on an
affine `WD ∋ x`, indexed by components `j i` of `D` through `x`. -/
theorem exists_ratForm_eq_sum {k : Type u} [Field k] (n : ℕ) {V : Scheme.{u}}
    (π : V ⟶ Spec (.of k)) [SmoothOfRelativeDimension n π] [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π)
    (S M : MMP.Mori.Divisor V) [Nonempty (cU D)] (p : ℕ) (W : V.Opens)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W)))
    (hθ : Cond n π D hD S M p W θ)
    (ρ : letI := MMP.Mori.functionFieldAlgebra π; ⋀[V.functionField]^p Ω[V.functionField⁄k])
    (hρ : letI := MMP.Mori.functionFieldAlgebra π
      ∀ (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W)
        [Nonempty (O : (cU D).toScheme.Opens)],
        openFormsMap (cU D) π p (ratForm ((cU D).ι ≫ π) p O
          ((((cU D).ι ≫ π).relativeDifferentialForms (p : ℤ)).presheaf.map
            (homOfLE hO).op θ)) = ρ)
    {x : V} (hx : x ∈ W) :
    ∃ (W₃ : V.affineOpens) (hx₃ : x ∈ (W₃ : V.Opens))
      (WD : V.affineOpens) (hxD : x ∈ (WD : V.Opens)) (t : Fin n → Γ(V, WD)) (r : ℕ)
      (j : Fin r → MMP.Mori.PrimeDivisor V), (∀ i, j i ∈ D.support ∧ x ∈ (j i).support) ∧
    ∃ (m : ℕ) (gi : Fin m → Γ(V, (W₃ : V.Opens) ⊓ cU' D M))
      (c : Fin m → {K : Finset (Fin n) // K.card = p} → Γ(V, W₃)),
      (∀ i, DivCond (D := D) (M := M) (W₃ : V.Opens) (gi i)) ∧
      (∀ i K, c i K ∈ S.suppIdeal.ideal W₃) ∧
      haveI : Nonempty (WD : V.Opens) := ⟨⟨x, hxD⟩⟩
      haveI : Nonempty (W₃ : V.Opens) := ⟨⟨x, hx₃⟩⟩
      haveI := nonempty_inf_cU' D M (W := (W₃ : V.Opens)) ⟨⟨x, hx₃⟩⟩
      letI := MMP.Mori.functionFieldAlgebra π
      ρ = ∑ i, V.germToFunctionField _ (gi i) • ∑ K, V.germToFunctionField W₃ (c i K) •
        exteriorPower.ιMulti V.functionField p
          ((chartForm π WD t r) ∘ fun l => K.1.orderEmbOfFin K.2 l) := by
  obtain ⟨W₃, hx₃, h₃W, WD, hxD, t, r, hr, j, h₃D, hjx, m, gi, c, hgi, hc, hexp⟩ :=
    exists_ratForm_expansion n π D hD S M p W θ hθ hx
  refine ⟨W₃, hx₃, WD, hxD, t, r, j, hjx, m, gi, c, hgi, hc, ?_⟩
  have : Nonempty (W₃ : V.Opens) := ⟨⟨x, hx₃⟩⟩
  have hη₃ : genericPoint V ∈ (W₃ : V.Opens) ⊓ cU' D M :=
    ⟨((genericPoint_spec V).mem_open_set_iff (W₃ : V.Opens).isOpen).2 ⟨x, trivial, hx₃⟩,
      genericPoint_mem_cU' D M⟩
  have hηU : genericPoint V ∈ cU D := fun h => hη₃.2 (Or.inl h)
  obtain ⟨_, ⟨O₀, hO₀, rfl⟩, hzO, hOle⟩ :=
    (cU D).toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (show (⟨genericPoint V, hηU⟩ : (cU D).toScheme) ∈ OO D M W₃ from hη₃) (OO D M W₃).isOpen
  let O : (cU D).toScheme.affineOpens := ⟨O₀, hO₀⟩
  have : Nonempty (O : (cU D).toScheme.Opens) := ⟨⟨_, hzO⟩⟩
  have hO : (O : (cU D).toScheme.Opens) ≤ OO D M W := fun w hw =>
    ⟨h₃W (hOle hw).1, (hOle hw).2⟩
  exact (hρ O hO).symm.trans (hexp O hO fun w hw => (hOle hw).1)

/-- **The rational form of a form on `U ∩ W ∩ U'`** does not depend on the affine open. -/
theorem exists_forall_openFormsMap_ratForm_eq {k : Type u} [Field k] {V : Scheme.{u}}
    (π : V ⟶ Spec (.of k)) [IsIntegral V] (D M : MMP.Mori.Divisor V) [Nonempty (cU D)]
    (p : ℕ) (W : V.Opens)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W)))
    (O₀ : (cU D).toScheme.affineOpens) (hO₀ : (O₀ : (cU D).toScheme.Opens) ≤ OO D M W)
    [Nonempty (O₀ : (cU D).toScheme.Opens)] :
    ∃ ρ : (letI := MMP.Mori.functionFieldAlgebra π; ⋀[V.functionField]^p Ω[V.functionField⁄k]),
      letI := MMP.Mori.functionFieldAlgebra π
      ∀ (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W)
        [Nonempty (O : (cU D).toScheme.Opens)],
        openFormsMap (cU D) π p (ratForm ((cU D).ι ≫ π) p O
          ((((cU D).ι ≫ π).relativeDifferentialForms (p : ℤ)).presheaf.map
            (homOfLE hO).op θ)) = ρ := by
  refine ⟨openFormsMap (cU D) π p (ratForm ((cU D).ι ≫ π) p O₀
    ((((cU D).ι ≫ π).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO₀).op θ)),
    fun O hO _ => ?_⟩
  rw [ratForm_eq_of_le ((cU D).ι ≫ π) p θ hO hO₀]

/-- **The integral factor `z⁻¹ g^*g₁`.** If `z^N = g^*ψ` and `g₁` satisfies the divisorial
condition near `x = g(y)`, then `z⁻¹ g^*g₁` lies in `𝒪_{V',y}`, and in its maximal ideal when
some component `F` of `Bn` passes through `x`. -/
theorem exists_stalk_eq_inv_mul_germ {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] (n : ℕ) {T : Scheme.{u}} (f : V ⟶ T)
    [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n f)
    (M : MMP.Mori.Divisor V) (uu : Γ(V, cU' D M)) (hMC : M.IsCartier) (Bn : MMP.Mori.Divisor V)
    {N : ℕ} (hN : 0 < N) (ψ : (MMP.Mori.RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ)
    (hu : (MMP.Mori.toRationalFunctionsPresheaf V).app (op (cU' D M)) uu = ratRes (cU' D M) ψ)
    (hBn : ∀ E, 0 ≤ Bn E) (hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support) {x : V} {W₃ : V.Opens}
    (hx : x ∈ W₃) (g₁ : Γ(V, W₃ ⊓ cU' D M)) (hg₁ : DivCond (D := D) (M := M) W₃ g₁)
    {V' : Scheme.{u}} (g : V' ⟶ V) [IsDominant g] [IsIntegral V'] [IsNormal V'] {y : V'}
    (hxy : g y = x) (z : V'.functionField)
    (hz : z ^ N = AlgebraicGeometry.functionFieldMap g
      (MMP.Mori.rationalFunctionsEquivFunctionField V ψ)) :
    letI := MMP.Mori.functionFieldMapAlgebra g
    haveI := nonempty_inf_cU' D M (W := W₃) ⟨⟨x, hx⟩⟩
    ∃ a : V'.presheaf.stalk y,
      algebraMap _ V'.functionField a =
        z⁻¹ * algebraMap V.functionField V'.functionField (V.germToFunctionField _ g₁) ∧
      ∀ F : MMP.Mori.PrimeDivisor V, x ∈ F.support → Bn F ≠ 0 →
        a ∈ maximalIdeal (V'.presheaf.stalk y) := by
  let := MMP.Mori.functionFieldMapAlgebra g
  have := nonempty_inf_cU' D M (W := W₃) ⟨⟨x, hx⟩⟩
  have hψ0 : MMP.Mori.rationalFunctionsEquivFunctionField V ψ ≠ 0 :=
    (ψ.isUnit.map (MMP.Mori.rationalFunctionsEquivFunctionField V)).ne_zero
  obtain ⟨h, hh, hhm⟩ := exists_stalk_mul_eq_pow n f D hD M uu hMC Bn N ψ hψ hu hBn hBD hx g₁ hg₁
  have hlam : (z⁻¹ * algebraMap V.functionField V'.functionField
      (V.germToFunctionField _ g₁)) ^ N = AlgebraicGeometry.functionFieldMap g
        (algebraMap (V.presheaf.stalk x) V.functionField h) := by
    have e1 : algebraMap (V.presheaf.stalk x) V.functionField h =
        V.germToFunctionField _ g₁ ^ N * (MMP.Mori.rationalFunctionsEquivFunctionField V ψ)⁻¹ := by
      rw [← hh, mul_inv_cancel_right₀ hψ0]
    rw [e1, map_mul, map_inv₀, ← hz, mul_pow, inv_pow, map_pow, mul_comm]
    rfl
  obtain ⟨a, ha, ham⟩ := exists_stalk_eq_of_pow_eq_functionFieldMap g hxy hN.ne' hlam
  exact ⟨a, ha, fun F hxF hF => ham (hhm F hxF hF)⟩

/-- **The pulled-back chart forms are logarithmic** at `y` with `g y = x`, and regular from
index `r` on. -/
theorem map_chartForm_mem_lattices {k : Type u} [Field k] {V V' : Scheme.{u}} [IsIntegral V]
    [IsIntegral V'] (π : V ⟶ Spec (.of k)) (g : V' ⟶ V) [IsDominant g] {n : ℕ}
    (WD : V.affineOpens) [Nonempty (WD : V.Opens)] (t : Fin n → Γ(V, WD)) (r : ℕ) {y : V'} {x : V}
    (hxy : g y = x) (hxD : x ∈ (WD : V.Opens)) :
    letI := MMP.Mori.functionFieldAlgebra π
    letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
    letI := MMP.Mori.functionFieldMapAlgebra g
    haveI := MMP.Mori.isScalarTower_functionFieldMap π g
    letI := MMP.Mori.stalkAlgebra (g ≫ π) y
    haveI := MMP.Mori.isScalarTower_stalk_functionField (g ≫ π) y
    (∀ l, KaehlerDifferential.map k k V.functionField V'.functionField (chartForm π WD t r l) ∈
        logLattice k (V'.presheaf.stalk y)) ∧
      ∀ l : Fin n, r ≤ l →
        KaehlerDifferential.map k k V.functionField V'.functionField (chartForm π WD t r l) ∈
          regLattice k (V'.presheaf.stalk y) := by
  let := MMP.Mori.functionFieldAlgebra π
  let := MMP.Mori.functionFieldAlgebra (g ≫ π)
  let := MMP.Mori.functionFieldMapAlgebra g
  have := MMP.Mori.isScalarTower_functionFieldMap π g
  let := MMP.Mori.stalkAlgebra (g ≫ π) y
  have := MMP.Mori.isScalarTower_stalk_functionField (g ≫ π) y
  refine ⟨fun l => ?_, fun l hl => ?_⟩
  · rw [map_chartForm_eq π g WD t r l hxy hxD]
    split_ifs
    · exact inv_smul_D_mem_logLattice _
    · simpa using D_mem_logLattice _
  · rw [map_chartForm_eq π g WD t r l hxy hxD, ite_eq_right (not_lt.2 hl), one_smul]
    exact D_mem_regLattice _

/-- If `D = S + Supp Bn`, a component of `D` that is not a component of `S` is one of `Bn`. -/
theorem ne_zero_of_mem_support_of_notMem {V : Scheme.{u}} {D S Bn : MMP.Mori.Divisor V}
    (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1) {F : MMP.Mori.PrimeDivisor V}
    (hFD : F ∈ D.support) (hFS : F ∉ S.support) : Bn F ≠ 0 := by
  intro hB0
  have := hSB F
  rw [Finsupp.notMem_support_iff.1 hFS, ite_eq_left hB0, add_zero] at this
  exact Finsupp.mem_support_iff.1 hFD this

/-- A function in the ideal of `S` pulls back into the maximal ideal of `𝒪_{V',y}` when `g y`
lies on `S`. -/
theorem placeHom_germ_mem_maximalIdeal {V V' : Scheme.{u}} (S : MMP.Mori.Divisor V)
    (g : V' ⟶ V) {y : V'} {x : V} (hxy : g y = x) {W : V.affineOpens} (hx : x ∈ (W : V.Opens))
    (hxS : x ∈ (S.supp : Set V)) {c : Γ(V, W)} (hc : c ∈ S.suppIdeal.ideal W) :
    (placeHom g hxy).hom (V.presheaf.germ (W : V.Opens) x hx c) ∈
      maximalIdeal (V'.presheaf.stalk y) := by
  have hxI : x ∈ S.suppIdeal.support := by
    rwa [← SetLike.mem_coe, MMP.Mori.DivisorWithCoeffs.coe_support_suppIdeal]
  exact map_nonunit (placeHom g hxy).hom _ (germ_mem_maximalIdeal_of_mem_ideal hx hxI hc)

/-- **The pull-back `z⁻¹ g^*ρ` at a prime divisor of the cover.** It lies in the `p`-th wedges
of the regular lattice of `𝒪_{V',E'}`, and, if `g(η_{E'})` is the generic point of a component
of `S`, in the maximal ideal times the `p`-th wedges of the logarithmic lattice. -/
theorem mem_lattices_of_cover {k : Type u} [Field k] [PerfectField k] (n : ℕ) {V : Scheme.{u}}
    (π : V ⟶ Spec (.of k)) [SmoothOfRelativeDimension n π] [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S Bn : MMP.Mori.Divisor V)
    (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1) (N : ℕ) (hN : 0 < N)
    (hBn : ∀ E, 0 ≤ Bn E) (hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support) (M : MMP.Mori.Divisor V)
    (uu : Γ(V, cU' D M)) (hMC : M.IsCartier) (ψ : (MMP.Mori.RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ)
    (hu : (MMP.Mori.toRationalFunctionsPresheaf V).app (op (cU' D M)) uu = ratRes (cU' D M) ψ)
    [Nonempty (cU D)] {V' : Scheme.{u}} (g : V' ⟶ V) [IsDominant g] [IsIntegral V']
    [SmoothOfRelativeDimension n (g ≫ π)] [IsLocallyNoetherian V'] [IsNormal V']
    (z : V'.functionField)
    (hz : z ^ N = AlgebraicGeometry.functionFieldMap g
      (MMP.Mori.rationalFunctionsEquivFunctionField V ψ))
    (p : ℕ) (W : V.Opens)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W)))
    (hθ : Cond n π D hD S M p W θ)
    (ρ : letI := MMP.Mori.functionFieldAlgebra π; ⋀[V.functionField]^p Ω[V.functionField⁄k])
    (hρ : letI := MMP.Mori.functionFieldAlgebra π
      ∀ (O : (cU D).toScheme.affineOpens) (hO : (O : (cU D).toScheme.Opens) ≤ OO D M W)
        [Nonempty (O : (cU D).toScheme.Opens)],
        openFormsMap (cU D) π p (ratForm ((cU D).ι ≫ π) p O
          ((((cU D).ι ≫ π).relativeDifferentialForms (p : ℤ)).presheaf.map
            (homOfLE hO).op θ)) = ρ)
    (E' : MMP.Mori.PrimeDivisor V') (hE' : g E'.genericPoint ∈ W) :
    letI := MMP.Mori.functionFieldAlgebra π
    letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
    letI := MMP.Mori.functionFieldMapAlgebra g
    haveI := MMP.Mori.isScalarTower_functionFieldMap π g
    letI := MMP.Mori.stalkAlgebra (g ≫ π) E'.genericPoint
    haveI := MMP.Mori.isScalarTower_stalk_functionField (g ≫ π) E'.genericPoint
    z⁻¹ • KaehlerDifferential.mapExteriorPower k V.functionField V'.functionField p ρ ∈
        wedgeSpan E'.localRing (regLattice k E'.localRing) p ∧
      ((∃ E ∈ S.support, g E'.genericPoint = E.genericPoint) →
        z⁻¹ • KaehlerDifferential.mapExteriorPower k V.functionField V'.functionField p ρ ∈
          maximalIdeal E'.localRing • wedgeSpan E'.localRing (logLattice k E'.localRing) p) := by
  classical
  let := MMP.Mori.functionFieldAlgebra π
  let := MMP.Mori.functionFieldAlgebra (g ≫ π)
  let := MMP.Mori.functionFieldMapAlgebra g
  have := MMP.Mori.isScalarTower_functionFieldMap π g
  set y := E'.genericPoint
  let := MMP.Mori.stalkAlgebra (g ≫ π) y
  have := MMP.Mori.isScalarTower_stalk_functionField (g ≫ π) y
  set x := g y with hxy
  obtain ⟨W₃, hx₃, WD, hxD, t, r, j, hjx, m, gi, c, hgi, hc, hρe⟩ :=
    exists_ratForm_eq_sum n π D hD S M p W θ hθ ρ hρ hE'
  obtain ⟨_, _⟩ : Nonempty (WD : V.Opens) ∧ Nonempty (W₃ : V.Opens) := ⟨⟨⟨x, hxD⟩⟩, ⟨⟨x, hx₃⟩⟩⟩
  choose a ha ham using fun i => exists_stalk_eq_inv_mul_germ n π D hD M uu hMC Bn hN ψ hψ hu
    hBn hBD hx₃ (gi i) (hgi i) g hxy.symm z hz
  let Cc : Fin m → {K : Finset (Fin n) // K.card = p} → V'.presheaf.stalk y := fun i K =>
    (placeHom g hxy.symm).hom (V.presheaf.germ (W₃ : V.Opens) x hx₃ (c i K))
  let τ : Fin n → Ω[V'.functionField⁄k] := fun l =>
    KaehlerDifferential.map k k V.functionField V'.functionField (chartForm π WD t r l)
  obtain ⟨hlog, hreg⟩ := map_chartForm_mem_lattices π g WD t r hxy.symm hxD
  have hβ : z⁻¹ • KaehlerDifferential.mapExteriorPower k V.functionField V'.functionField p ρ =
      ∑ q ∈ (Finset.univ : Finset (Fin m × {K : Finset (Fin n) // K.card = p})),
        algebraMap (V'.presheaf.stalk y) V'.functionField (a q.1 * Cc q.1 q.2) •
          exteriorPower.ιMulti V'.functionField p
            (τ ∘ fun l => q.2.1.orderEmbOfFin q.2.2 l) := by
    rw [hρe, smul_mapExteriorPower_eq_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, ha, algebraMap_placeHom, Scheme.algebraMap_germ_eq_germToFunctionField]
    rfl
  have := E'.isDiscreteValuationRing_localRing
  obtain ⟨hfs, hfree, hfin⟩ := formallySmooth_free_finite_stalk (g ≫ π) (m := n) y
  have : Smooth (g ≫ π) := SmoothOfRelativeDimension.smooth n _
  have := essFiniteType_stalkAlgebra (g ≫ π) y
  have hlat := mem_lattices_of_eq_sum k (R := V'.presheaf.stalk y) (L := V'.functionField)
    (ι := Fin m × {K : Finset (Fin n) // K.card = p}) τ hlog hreg Finset.univ
    (fun q => a q.1 * Cc q.1 q.2) (fun q l => q.2.1.orderEmbOfFin q.2.2 l) hβ
  refine ⟨?_, fun ⟨E, hES, hEx⟩ => ?_⟩
  · rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · exact hlat.2.1 hr0
    · obtain ⟨hFD, hxF⟩ := hjx ⟨0, hr0⟩
      exact (hlat.2.2 fun q _ => if hFS : j ⟨0, hr0⟩ ∈ S.support then
        Ideal.mul_mem_left _ _ (placeHom_germ_mem_maximalIdeal S g hxy.symm hx₃
          (MMP.Mori.DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.1 hFS) hxF)
          (hc q.1 q.2))
      else Ideal.mul_mem_right _ _ (ham q.1 _ hxF (ne_zero_of_mem_support_of_notMem hSB hFD hFS))).2
  · have hxE : x ∈ E.support := by
      rw [hEx, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    exact (hlat.2.2 fun q _ => Ideal.mul_mem_left _ _ (placeHom_germ_mem_maximalIdeal S g
      hxy.symm hx₃ (MMP.Mori.DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.1 hES)
        hxE) (hc q.1 q.2))).1

end MMP.FourfoldProofs.FractionalLogComplexProof
