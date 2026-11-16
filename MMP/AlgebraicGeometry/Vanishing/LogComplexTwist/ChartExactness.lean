module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.ChartLocalData
public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.ChartModel

/-!
# Residue charts of the twist inclusion of the fractional logarithmic complex

Let `K` be a model of the fractional logarithmic complex `C^• = 𝒪_V(-M) · Ω^•_V(log D)` (with
`S = 0`, `D = Supp Bn`, `N M = Bn + div ψ`) and `K'` a model of its twist
`𝒪_V(-M - E) · Ω^•_V(log D)` by a component `E` of `D` with `Bn(E) ≠ 0`, and `φ : K' ⟶ K` the
inclusion. Near every point of `E` the sections of `K` and `K'` are encoded as forms
`g₀ (α + θ ∧ β)` and `g₀ t (α' + θ ∧ β')` on a chart, with residue data along `E` of residue
`λ = Bn(E)/N ≠ 0` (`MMP.LcBpf.TwistChart`); off `E` the twist does not change the sheaves. So `φ`
is relatively locally exact.

## Main results

* `MMP.LcBpf.exists_twistChart`: a residue chart near a point of `E`.
* `MMP.LcBpf.exists_surjective_of_notMem`: off `E`, `φ` is onto on sections near every point.
* `MMP.LcBpf.relLocallyExact_of_isTwistInclusion`: `φ` is relatively locally exact.

## References

* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.LcBpf

open MMP.Mori MMP.FourfoldProofs.FractionalLogComplexProof TwistChartForms

section Twist

variable {d : ℕ} {V : Scheme.{0}} {π : V ⟶ Spec (CommRingCat.of ℂ)}
  [SmoothOfRelativeDimension d π] [IsLocallyNoetherian V] [IsNormal V] [IsIntegral V]
  {D : Divisor V} {hD : D.IsRelativeSNC d π} {M M' : Divisor V} {hM : cU' D M' = cU' D M}
  {N : ℕ} {u : Γ(V, cU' D M)} {E : MMP.Mori.PrimeDivisor V}
  {K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
  {F : ℕ → V.Modules}
  {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
  {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W))}
  (hK : IsCModel d π D hD 0 M N u K F e ι)
  {N' : ℕ} {u' : Γ(V, cU' D M')}
  {K' : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
  {F' : ℕ → V.Modules}
  {e' : ∀ p, K'.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F' p)}
  {ι' : ∀ (p : ℕ) (W : V.Opens), (F' p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M' W))}
  (hK' : IsCModel d π D hD 0 M' N' u' K' F' e' ι')
  {φ : K' ⟶ K} (hφ : IsTwistInclusion π D M M' hM e e' ι ι' φ)

/-- The encoding of the sections of `K'` over `W` as forms on `U ∩ W ∩ U'`, through `K`'s open. -/
noncomputable def encK' (W : V.Opens) (q : ℕ) :
    (K'.X q).val.obj (op W) →+ (TB ((cU D).ι ≫ π)).Total (op (OO D M W)) :=
  AddMonoidHom.mk'
    (fun z => (TB ((cU D).ι ≫ π)).totalRestrict (homOfLE (OO_le_twist hM W)).op (encK hK' W q z))
    fun z z' => by rw [map_add, map_add]

omit [IsIntegral V] in
include hφ in
/-- The encoding in `K` of the image under `φ` of a section of `K'` is its encoding `encK'`. -/
theorem encK_φ (W : V.Opens) (q : ℕ) (x' : (K'.X q).val.obj (op W)) :
    encK hK W q ((φ.f q).val.app (op W) x') = encK' (hM := hM) hK' W q x' := by
  change (TB ((cU D).ι ≫ π)).incl (q : ℤ) (ι q W ((e q).hom.val.app (op W)
    ((φ.f q).val.app (op W) x'))) = (TB ((cU D).ι ≫ π)).totalRestrict _
      ((TB ((cU D).ι ≫ π)).incl (q : ℤ) (ι' q W ((e' q).hom.val.app (op W) x')))
  rw [hφ q W x', incl_map π D]

variable {pt : V} {W₀ : V.Opens} (L : LocalData d π D M M' hM N u E pt W₀)

omit [IsIntegral V] in
/-- The sections of `K'`, through `K`'s open, are `g₀ m ∑_K a_K θ_K`. -/
theorem encK'_eq {q : ℕ} {z : (K'.X q).val.obj (op (L.W : V.Opens))}
    {a : {K : Finset (Fin d) // K.card = q} → Γ(V, L.W)}
    (h : encK hK' L.W q z = sm ((cU D).ι ≫ π) (OO D M' L.W)
      ((cU D).ι.app ((L.W : V.Opens) ⊓ cU' D M') L.g₁) *
        (letI := chartAlgebra (f := π) (D := D) M' (W := L.W);
          ChartAlgebra.combo (θO L.c M' L.hWc) q a)) :
    encK' (hM := hM) hK' L.W q z = sm ((cU D).ι ≫ π) (OO D M L.W)
      ((cU D).ι.app ((L.W : V.Opens) ⊓ cU' D M) L.g₀) *
        (letI := chartAlgebra (f := π) (D := D) M (W := L.W);
          L.m • ChartAlgebra.combo (θO L.c M L.hWc) q a) := by
  change (TB ((cU D).ι ≫ π)).totalRestrict _ (encK hK' L.W q z) = _
  rw [h, Stacks.GradedAlgebra.totalRestrict_mul, totalRestrict_sm_twist hM,
    totalRestrict_combo_twist L.c hM L.hWc, L.rel, map_mul, map_mul, chartAlgebra_smul, mul_assoc]
  rfl

/-- `combo θ q` commutes with scalar multiplication of the coefficient family. -/
theorem ChartAlgebra.combo_smul {R Λ : Type*} [CommRing R] [Ring Λ] [Algebra R Λ] {n : ℕ}
    (θ : Fin n → Λ) (q : ℕ) (r : R) (a : {K : Finset (Fin n) // K.card = q} → R) :
    ChartAlgebra.combo θ q (r • a) = r • ChartAlgebra.combo θ q a := by
  simp only [ChartAlgebra.combo, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

variable [Nonempty (cU D)]

include hK hK' hφ in
/-- **The residue chart near a point of `E`.** -/
theorem nonempty_twistChart_of_localData (hptE : pt ∈ E.support) :
    Nonempty (TwistChart φ (L.W : V.Opens)) := by
  classical
  obtain ⟨i₀, w, -, hw, hmw, ξ, cO, hcO, hξ, lam, lamInv, hlam, hdlam, hres⟩ := L.onE hptE
  let _ := chartAlgebra (f := π) (D := D) M (W := L.W)
  obtain ⟨ξ', hξ', μ, hξeq⟩ := hres
  have hsq := θO_mul_self L.c M L.hWc
  have hac := θO_anticomm L.c M L.hWc
  have hind : ∀ (q : ℕ) (a : {K : Finset (Fin d) // K.card = q} → Γ(V, L.W)),
      ChartAlgebra.combo (θO L.c M L.hWc) q a = 0 → a = 0 := fun q a ha =>
    eq_zero_of_combo_eq_zero L.c M L.hWc hD L.hpt q a ha
  obtain ⟨wi, hwi⟩ := hw.exists_left_inv
  have hsmt : ∀ x : (TB ((cU D).ι ≫ π)).Total (op (OO D M L.W)),
      L.m • x = tW L.c L.hWc (Fin.castLE L.c.hr i₀) • (w • x) := fun x => by
    rw [hmw, mul_comm, mul_smul]
  have hwwi : ∀ x : (TB ((cU D).ι ≫ π)).Total (op (OO D M L.W)), w • wi • x = x := fun x => by
    rw [smul_smul, mul_comm, hwi, one_smul]
  have hlift : ∀ (q : ℕ) (x : (TB ((cU D).ι ≫ π)).Total (op (OO D M L.W))),
      x ∈ ChartAlgebra.F (R := Γ(V, L.W)) (θO L.c M L.hWc) q → ∃ z,
        encK' (hM := hM) hK' L.W q z = sm ((cU D).ι ≫ π) (OO D M L.W)
          ((cU D).ι.app ((L.W : V.Opens) ⊓ cU' D M) L.g₀) *
            tW L.c L.hWc (Fin.castLE L.c.hr i₀) • x := fun q x hx => by
    obtain ⟨a, rfl⟩ := (ChartAlgebra.mem_F_iff (θ := θO L.c M L.hWc)).1 hx
    obtain ⟨y, hy⟩ := exists_incl_ι_eq_sm_mul_combo hK' L.c L.hWc L.g₁ L.div₁ q (wi • a)
    refine ⟨(e' q).inv.val.app (op (L.W : V.Opens)) y, ?_⟩
    rw [encK'_eq hK' L (by rw [encK_apply, e_inv_hom, hy]), hsmt, ChartAlgebra.combo_smul,
      hwwi]
  refine ⟨{
    R := Γ(V, L.W)
    Λ := (TB ((cU D).ι ≫ π)).Total (op (OO D M L.W))
    instAlgebra := chartAlgebra (f := π) (D := D) M (W := L.W)
    H := ChartAlgebra.toResidueData hsq hac hind (Fin.castLE L.c.hr i₀)
      (tW L.c L.hWc (Fin.castLE L.c.hr i₀)) (fun q => Δ ((cU D).ι ≫ π) (OO D M L.W) q)
      (Dr (f := π) (D := D) M) (fun q a K hK => Δ_smul_θK L.c M L.hWc q a K hK)
      (exists_Dr_eq L.c M L.hWc i₀.2) (θO_mul_Dr L.c M L.hWc _) ξ' hξ' μ lam lamInv hlam
      hdlam
    G := sm ((cU D).ι ≫ π) (OO D M L.W) ((cU D).ι.app ((L.W : V.Opens) ⊓ cU' D M) L.g₀)
    E := fun q => encK hK L.W q
    E' := fun q => encK' (hM := hM) hK' L.W q
    E_injective := fun q => encK_injective hK L.W q
    E_φ := fun q x' => encK_φ hK hK' hφ L.W q x'
    G_cancel := fun a b h => sm_cancel L.unit₀ h
    rep_zero := fun x => ?_
    rep_succ := fun q x => ?_
    twist_rep := fun q z => ?_
    twist_lift_zero := fun a ha => ?_
    twist_lift_succ := fun q a ha b hb => ?_
    lift := fun q b hb => ?_
    d_rep := fun q y z hyz => ?_ }⟩
  · obtain ⟨a, ha⟩ := exists_encK_eq hK L.c L.hWc L.g₀ L.unit₀ L.gen₀ 0 x
    refine ⟨_, ?_, ha⟩
    change _ ∈ ChartAlgebra.L (θO L.c M L.hWc) (Fin.castLE L.c.hr i₀) 0
    rw [← ChartAlgebra.F_zero_eq_L]
    exact (ChartAlgebra.mem_F_iff (θ := θO L.c M L.hWc)).2 ⟨a, rfl⟩
  · obtain ⟨a, ha⟩ := exists_encK_eq hK L.c L.hWc L.g₀ L.unit₀ L.gen₀ (q + 1) x
    obtain ⟨α, hα, β, hβ, hαβ⟩ := ChartAlgebra.exists_eq_add_θ_mul hac (Fin.castLE L.c.hr i₀)
      ((ChartAlgebra.mem_F_iff (θ := θO L.c M L.hWc)).2 ⟨a, rfl⟩)
    exact ⟨α, hα, β, hβ, ha.trans (by rw [hαβ]; rfl)⟩
  · obtain ⟨a, ha⟩ := exists_encK_eq hK' L.c L.hWc L.g₁ L.unit₁ L.gen₁ (q + 1) z
    obtain ⟨α, hα, β, hβ, hαβ⟩ := ChartAlgebra.exists_eq_add_θ_mul hac (Fin.castLE L.c.hr i₀)
      (Submodule.smul_mem _ w ((ChartAlgebra.mem_F_iff (θ := θO L.c M L.hWc)).2 ⟨a, rfl⟩))
    refine ⟨α, hα, β, hβ, ?_⟩
    change encK' (hM := hM) hK' L.W (q + 1) z = _
    rw [encK'_eq hK' L ha, hsmt, hαβ]
    rfl
  · exact hlift 0 a (ChartAlgebra.L_le_F _ _ _ ha)
  · exact hlift (q + 1) _ (ChartAlgebra.add_θ_mul_mem_F hac ha hb)
  · obtain ⟨a, rfl⟩ := (ChartAlgebra.mem_F_iff (θ := θO L.c M L.hWc)).1
      (ChartAlgebra.L_le_F _ _ _ hb)
    exact exists_encK_eq_lift hK L.c L.hWc L.g₀ L.div₀ q a
  · obtain ⟨a, ha⟩ := exists_encK_eq hK L.c L.hWc L.g₀ L.unit₀ L.gen₀ q y
    have hz : z = ChartAlgebra.combo (θO L.c M L.hWc) q a := sm_cancel L.unit₀ (hyz.symm.trans ha)
    have hzF : z ∈ ChartAlgebra.F (R := Γ(V, L.W)) (θO L.c M L.hWc) q :=
      hz ▸ (ChartAlgebra.mem_F_iff (θ := θO L.c M L.hWc)).2 ⟨a, rfl⟩
    obtain ⟨hzm, hzq⟩ := mem_monSet_of_mem_F L.c M L.hWc hzF
    have key := incl_eq_sm_mul_nabla M N hcO hξ _ _ hzm hzq hyz
      (hK.2.2.2.2.2 q L.W y)
    change encK hK L.W (q + 1) ((K.d q (q + 1)).val.app (op (L.W : V.Opens)) y) =
      _ * ((lam • θO L.c M L.hWc (Fin.castLE L.c.hr i₀) + ξ' +
        (tW L.c L.hWc (Fin.castLE L.c.hr i₀) * μ) • θO L.c M L.hWc (Fin.castLE L.c.hr i₀)) * z +
        Δ ((cU D).ι ≫ π) (OO D M L.W) q z)
    rw [← hξeq]
    exact key

include hK hK' hφ in
/-- **Off `E` the twist inclusion is onto on the sections over `W`.** -/
theorem exists_eq_map_of_localData (hptE : pt ∉ E.support) (q : ℕ)
    (x : (K.X q).val.obj (op (L.W : V.Opens))) :
    ∃ x', x = (φ.f q).val.app (op (L.W : V.Opens)) x' := by
  let _ := chartAlgebra (f := π) (D := D) M (W := L.W)
  obtain ⟨a, ha⟩ := exists_encK_eq hK L.c L.hWc L.g₀ L.unit₀ L.gen₀ q x
  obtain ⟨mi, hmi⟩ := (L.offE hptE).exists_left_inv
  obtain ⟨y, hy⟩ := exists_incl_ι_eq_sm_mul_combo hK' L.c L.hWc L.g₁ L.div₁ q (mi • a)
  refine ⟨(e' q).inv.val.app (op (L.W : V.Opens)) y, encK_injective hK L.W q ?_⟩
  rw [encK_φ hK hK' hφ, encK'_eq hK' L (by rw [encK_apply, e_inv_hom, hy]),
    ChartAlgebra.combo_smul, smul_smul, mul_comm, hmi, one_smul, ha]

end Twist

section Main

variable (d : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension d π] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [CompactSpace V]
  (D : Divisor V) (hD : D.IsRelativeSNC d π) (M Bn : Divisor V)
  (hSB : ∀ E, D E = (0 : Divisor V) E + if Bn E = 0 then 0 else 1) (N : ℕ) (hN : 0 < N)
  (hBn : ∀ E, 0 ≤ Bn E) (ψ : (RationalFunctions V)ˣ)
  (hψ : (N : ℤ) • M = Bn + principalDivisor ψ) (u : Γ(V, cU' D M))
  (hu : (toRationalFunctionsPresheaf V).app (op (cU' D M)) u = ratRes (cU' D M) ψ)
  {K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
  {F : ℕ → V.Modules}
  (e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p))
  (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W)))
  (hK : IsCModel d π D hD 0 M N u K F e ι)
  (E : MMP.Mori.PrimeDivisor V) (hBE : Bn E ≠ 0)
  {M' : Divisor V} (hM' : M' = M + Finsupp.single E 1) (hM : cU' D M' = cU' D M)
  {N' : ℕ} {u' : Γ(V, cU' D M')}
  {K' : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
  {F' : ℕ → V.Modules}
  (e' : ∀ p, K'.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F' p))
  (ι' : ∀ (p : ℕ) (W : V.Opens), (F' p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M' W)))
  (hK' : IsCModel d π D hD 0 M' N' u' K' F' e' ι')
  (φ : K' ⟶ K) (hφ : IsTwistInclusion π D M M' hM e e' ι ι' φ)

include hD hSB hN hBn hψ hu hK hBE hM' hK' hφ in
/-- **A residue chart near a point of `E`.** Every open `W` containing a point `pt` of `E`
contains an open `V₀ ∋ pt` carrying a `TwistChart φ V₀`. -/
theorem exists_twistChart (W : V.Opens) (pt : V) (hpt : pt ∈ W) (hptE : pt ∈ E.support) :
    ∃ (V₀ : V.Opens) (_ : V₀ ≤ W), pt ∈ V₀ ∧ Nonempty (TwistChart φ V₀) := by
  have : Nonempty (cU D) := by
    obtain ⟨Z⟩ : Nonempty (irreducibleComponents V) :=
      ⟨⟨irreducibleComponent pt, irreducibleComponent_mem_irreducibleComponents pt⟩⟩
    exact ⟨⟨_, (cU'_le_cU D M) (componentGenericPoint_mem_cU' D M Z)⟩⟩
  obtain ⟨L⟩ := nonempty_localData (hM := hM) (N := N) (u := u) hD Bn hSB hN hBn ψ hψ hu hBE hM'
    pt W hpt
  exact ⟨L.W, L.hW₀, L.hpt, nonempty_twistChart_of_localData hK hK' hφ L hptE⟩

include hD hSB hN hBn hψ hu hK hBE hM' hK' hφ in
/-- **Off `E` the twist inclusion is onto on sections**, near every point. -/
theorem exists_surjective_of_notMem (W : V.Opens) (pt : V) (hpt : pt ∈ W)
    (hptE : pt ∉ E.support) :
    ∃ (V₀ : V.Opens) (_ : V₀ ≤ W), pt ∈ V₀ ∧
      ∀ (q : ℕ) (x : (K.X q).val.obj (op V₀)), ∃ x', x = (φ.f q).val.app (op V₀) x' := by
  have : Nonempty (cU D) := by
    obtain ⟨Z⟩ : Nonempty (irreducibleComponents V) :=
      ⟨⟨irreducibleComponent pt, irreducibleComponent_mem_irreducibleComponents pt⟩⟩
    exact ⟨⟨_, (cU'_le_cU D M) (componentGenericPoint_mem_cU' D M Z)⟩⟩
  obtain ⟨L⟩ := nonempty_localData (hM := hM) (N := N) (u := u) hD Bn hSB hN hBn ψ hψ hu hBE hM'
    pt W hpt
  exact ⟨L.W, L.hW₀, L.hpt, fun q x => exists_eq_map_of_localData hK hK' hφ L hptE q x⟩

end Main

/-- **The one-step twist inclusion is relatively locally exact.** For a model `K` of the
fractional logarithmic complex `𝒪_V(-M) · Ω^•_V(log D)` (`S = 0`, `D = Supp Bn`,
`N M = Bn + div ψ`), a component `E` of `D` with `Bn(E) ≠ 0`, a model `K'` of its twist by `-E`,
and the inclusion `φ : K' ⟶ K`, every section `x` of `K^p` whose differential comes from `K'` is,
near every point, `d y + φ x'`. -/
theorem relLocallyExact_of_isTwistInclusion (d : ℕ) {V : Scheme.{0}}
    (π : V ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension d π] [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (D : Divisor V) (hD : D.IsRelativeSNC d π) (M Bn : Divisor V)
    (hSB : ∀ E, D E = (0 : Divisor V) E + if Bn E = 0 then 0 else 1) (N : ℕ) (hN : 0 < N)
    (hBn : ∀ E, 0 ≤ Bn E) (ψ : (RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + principalDivisor ψ) (u : Γ(V, cU' D M))
    (hu : (toRationalFunctionsPresheaf V).app (op (cU' D M)) u = ratRes (cU' D M) ψ)
    {K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
    {F : ℕ → V.Modules}
    (e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p))
    (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W)))
    (hK : IsCModel d π D hD 0 M N u K F e ι)
    (E : MMP.Mori.PrimeDivisor V) (hBE : Bn E ≠ 0)
    (hM : cU' D (M + Finsupp.single E 1) = cU' D M)
    {K' : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
    {F' : ℕ → V.Modules}
    (e' : ∀ p, K'.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F' p))
    (ι' : ∀ (p : ℕ) (W : V.Opens), (F' p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D (M + Finsupp.single E 1) W)))
    (hK' : IsCModel d π D hD 0 (M + Finsupp.single E 1) N
      (V.presheaf.map (homOfLE hM.le).op u) K' F' e' ι')
    (φ : K' ⟶ K) (hφ : IsTwistInclusion π D M (M + Finsupp.single E 1) hM e e' ι ι' φ) :
    RelLocallyExact φ :=
  relLocallyExact_of_twistCharts φ fun W pt hpt => by
    by_cases hptE : pt ∈ E.support
    · obtain ⟨V₀, hV₀, hpt₀, hC⟩ := exists_twistChart d π D hD M Bn hSB N hN hBn ψ hψ u hu e ι hK
        E hBE rfl hM e' ι' hK' φ hφ W pt hpt hptE
      exact ⟨V₀, hV₀, hpt₀, Or.inl hC⟩
    · obtain ⟨V₀, hV₀, hpt₀, hC⟩ := exists_surjective_of_notMem d π D hD M Bn hSB N hN hBn ψ hψ
        u hu e ι hK E hBE rfl hM e' ι' hK' φ hφ W pt hpt hptE
      exact ⟨V₀, hV₀, hpt₀, Or.inr hC⟩

end MMP.LcBpf
