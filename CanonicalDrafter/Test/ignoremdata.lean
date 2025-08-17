import Mathlib

-- because mdata, exprs that are definitionally equal will fail == comparison. this test makes sure the definitional equality is being tested by the havedraft logic.

theorem line_differentiable_at_measurable_set
    {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
    {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (f : E → F) (v : E) (hf : Continuous f) :
    MeasurableSet {x | LineDifferentiableAt 𝕜 f x v} := by
  borelize 𝕜
  sorry

open PrimeSpectrum

-- Theorem statement producing the given tactic state
theorem comap_homeomorph_of_surj_nilradical
  {R : Type u_3} {S : Type u_4}
  [CommRing R] [CommRing S]
  (f : R →+* S)
  (H : ∀ (x : S), ∃ n > 0, x ^ n ∈ f.range)
  (hker : RingHom.ker f ≤ nilradical R) :
  IsHomeomorph (⇑(comap f) : PrimeSpectrum S → PrimeSpectrum R) := by
have h1 : Function.Injective (comap f) := by sorry
sorry
