# Aristotle Task Index

This file indexes the Lean statement bank in
`Jacobian/WorkPackets/StatementBank.lean`.

Claude should treat each queue below as a source of small Aristotle jobs. Before
submitting, Claude should copy the relevant declarations into a narrower target
file and ask Aristotle to work only on that file.

The Aristotle account is shared with other projects; job IDs from
`aristotle list` may belong to FourColor or other unrelated work. Record every
JacobianChallenge submission in `aristotle_jobs.jsonl` so future ticks can
identify our jobs without inspecting tarballs.

## Live Status (2026-05-07, /loop tick — backend live, queue light)

- **b782c387-5718-4565-a3e8-ed049d6c4c26** (submitted): `Jacobian/HolomorphicForms/SectionTopologyRecon.lean` — Recon: survey Mathlib v4.28.0 API for topology-of-uniform-convergence on ContMDiffSection (step (a) of the Riemann-Roch plan from 72ac3a75)
- **5dfd5106-8e6b-45b4-92a6-b4265d3a5704** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — TOP-DOWN survey on `holomorphicOneForm_montel` — Montel's theorem for holomorphic 1-forms on compact Riemann surface. High-risk gap-narrowing on the Riemann-Roch / FD chain.
- **848a0c88-6c27-423d-865b-38b35390b7a0** (submitted): `Jacobian/HolomorphicForms/SectionTopologyConstructionRecon.lean` — NEW recon file: how to construct the Banach data on `ContMDiffSection` for compact X. Companion to `holomorphicOneForm_normedSpace_uniformOnCompact` obligation.
- **90750074-0d26-4f60-b32e-a79942e56111** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOP-DOWN refinement on `holomorphicOneForm_onePointCx_subsingleton` — the Liouville core of genus-zero classification (no global holomorphic 1-form on ℂℙ¹). Anti-hack #1 critical path.
- **dc8af381-8277-44ab-95f4-6e62dba5faee** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — Discharge `exists_compact_periodFundamentalDomain` using the existing `IsZLattice ℝ` instance + Mathlib ZSpan API. Reduction 3→2 sorries in this file.
- **6992e390-050b-49fb-bb21-5fde3ccb0449** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — TOPDOWN reduction: discharge `holomorphicOneForm_locallyCompact_of_compactRiemannSurface` sorry-free using `holomorphicOneForm_montel B` (still-sorry but named) — translation invariance on a normed space. Reduction 3→2 sorries in CompactRiemannSurface.lean.
- **d493c66b-a666-4b4d-a245-67db26ff4346** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOP-DOWN refinement on `holomorphicOneForm_onePointCx_toFun_eq_zero` — chart-coefficient extraction sorry exposed by 90750074. The Liouville analytic content is now discharged; this is the chart-pullback API gap.
- **63158306-c2f9-4f3e-a2e9-1b385e59fe48** (submitted): `Jacobian/HolomorphicForms/SectionFiberNorm.lean` — NEW file: Step 1 of `848a0c88` Banach-data construction recon — define `ContMDiffSection.fiberNorm` and prove its continuity. Building block for the eventual `holomorphicOneForm_normedSpace_uniformOnCompact` discharge.
- **1f7d4399-438b-4d8a-b128-dc290bde3a48** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOPDOWN on the now-narrower finite leaf `holomorphicOneForm_onePointCx_toFun_finite_eq_zero` (Liouville application via identity-chart pullback + EntireZero black-box).
- **f1786fa8-bbaa-4cdd-9683-b9dfbdf01797** (submitted): `Jacobian/HolomorphicForms/SectionSupNorm.lean` — NEW file: Step 2 of `848a0c88` Banach-data construction recon — define `ContMDiffSection.supNorm` and prove 5 sup-norm properties (zero, eq_zero_iff, add_le, smul_le, neg). 40-60 LOC per recon §5 Step 2.
- **51fd0fce-fb19-45e7-9ef1-efbf65de7ac9** (submitted): `Jacobian/HolomorphicForms/SectionMetric.lean` — NEW file: Step 3 of `848a0c88` Banach-data construction recon — define `ContMDiffSection.dist` and prove 4 MetricSpace axioms + dist_eq. ~20-50 LOC per recon §5 Step 3.
- **8585f085-371e-4c86-b276-adadf70f6392** (submitted): `Jacobian/HolomorphicForms/SectionComplete.lean` — NEW file: Step 4 of `848a0c88` Banach-data construction recon — completeness via embedding HolomorphicOneForm ℂ X into C(X, ℂ) + closedness. Hardest step, 80-150 LOC.
- **7e2bc288-bedc-4149-b0d8-28bcadf78ade** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — TOPDOWN refinement of 3 sorries (analyticPullback_contMDiff/_id_apply/_comp_apply). Acceptable outcomes: full proofs, companion-spec split, or survey docstring.
- **4d56b249-931f-46e3-8ace-50d28a74ac78** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — TOPDOWN refinement of 3 sorries (analyticPushforward_contMDiff/_id_apply/_comp_apply). Mirror of PullbackBasis packet 7e2bc288.
- **bbe527bb-28a6-4d6e-a32a-cf5f8d8df6e3** (submitted): `Jacobian/TraceDegree/AnalyticDegree.lean` — Discharge analyticPushforward_analyticPullback (anti-hack #4) via the recommended companion opaque _spec from prior survey 10e5bfbb.
- **d1d10391-67c2-4bfc-ad21-5514a1052a55** (submitted): `Jacobian/ComplexTorus/ULiftTransport.lean` — Discharge 2 sorries (complexTorusULift_contMDiff_up/_down). Both should be straightforward via the transported chart structure (chart-target map is identity).
- **d967438b-5455-49c9-a8ab-08bf2e0482e8** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — TOPDOWN of 3 sorries: pathIntegralFunctional_self, analyticOfCurve_contMDiff, pathIntegralFunctional_separates_points (Abel's theorem).
- **c5101910-f51a-4aab-8abf-d801b239642a** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — TOPDOWN of 2 sorries: periodSubgroup_isZLattice (integrality), periodSubgroup_spans_real (Riemann bilinear nondegeneracy).
- **c7feba63-8103-4859-846f-053274534d9d** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — TOPDOWN refinement of holomorphicOneForm_montel (only — _normedSpace handled by 8585f085 chain).
- **b3280ab0-41c9-46fd-82be-4eb17e7c0748** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOPDOWN refinement of 4 sorries: 2 Liouville-core leaves (chart-extraction blocker) + 2 uniformization items.
- **d8fd495f-b92d-4c09-898b-ce7614ecfaa7** (submitted): `Jacobian/ComplexTorus/ULiftTransport.lean` — Single-sorry packet on complexTorusULift_contMDiff_up only.
- **b4029f72-c3d9-4629-a961-e5ade014ea84** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on analyticPullback_id_apply only.
- **c910ac80-7262-443d-88c1-bb55817ac27e** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on analyticPullback_contMDiff only.
- **2bd5f151-4bab-4023-ae9e-dc614099864a** (submitted): `Jacobian/ComplexTorus/ULiftTransport.lean` — Single-sorry packet on complexTorusULift_contMDiff_down only.
- **27c56154-66ff-4c22-a86b-e112054f19de** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on analyticPullback_comp_apply only.
- **f280ecc6-c477-48f1-9128-3d8b7eeb0012** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Single-sorry packet on analyticPushforward_contMDiff only.
- **271cc21e-7540-4a49-978e-a51cad18978c** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Single-sorry packet on analyticPushforward_id_apply only.
- **6c796045-b207-4290-9d5c-5b02499ca57e** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Single-sorry packet on analyticPushforward_comp_apply only.
- **3d5f379e-568b-4e13-8f51-c9529fdc1f36** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Single-sorry packet on pathIntegralFunctional_self only.
- **c6c4c612-3d0a-4b8f-a792-9ee8ff6eb80f** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Single-sorry packet on analyticOfCurve_contMDiff only.
- **4f76ac75-4b03-44bf-9c4d-e473bcbb86b8** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Single-sorry packet on pathIntegralFunctional_separates_points (Abel's theorem).
- **99825c13-b58a-420b-b25c-ff202a2a5e70** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on the new analyticPullback_comp_spec (Claude's split target).
- **2aab5e91-890a-447f-9729-f4872a50e23e** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on the improved analyticPullback_id_spec (= ContinuousAddMonoidHom.id _).
- **a3b5ae84-236d-4b40-a64a-259b3f8a7752** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Replacement packet on the new pathIntegralFunctional_self_spec.
- **777f976c-0e8e-4078-a345-68f015c9d7aa** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Replacement packet on the new analyticPushforward_contMDiff_spec.
- **3264c622-6675-4b18-94f3-9ec50f130185** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Replacement packet on analyticOfCurve_contMDiff_spec.
- **7f273ec8-537c-4bc9-a159-3098725b12f7** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Replacement packet on pathIntegralFunctional_separates_points_spec (Abel's theorem deep content).
- **09a7e39c-5748-4c12-a2a0-55b2039d52c7** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Replacement packet on analyticPushforward_id_spec.
- **90fc4a81-0f3c-4a7f-a09a-34f8e16b532b** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Replacement packet on analyticPushforward_comp_spec.
- **f914a263-801f-4dbc-8671-bc6d67a763bf** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — contMDiff_continuousAddMonoidHom_complexTorus general lemma.
- **c69fcd88-2cb2-4710-bef0-200e1a2cd351** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — analyticPullback_id_spec respecting basisDualPullback structure.
- **369f3f7b-4879-4ef1-9994-d46784537914** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — analyticPullback_contMDiff via complex-torus smoothness lemma.
- **16277f52-39bc-4f28-9860-8d771687c3ad** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — quotientMk_contMDiff_spec via charted-space machinery.
- **65001239-6493-4b88-8f4d-e21c6373addd** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — analyticPushforward_id_eq deeper split.
- **654d5071-ee04-446c-a69e-0d584517149e** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — pathIntegralFunctional_contMDiff_spec gap analysis.
- **7f3ec297-cad6-409f-bc0d-f4c0dc196fd2** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — analyticPullback_mk_eq + basisDualPullback_comp paired packet.
- **e3dcd529-c13e-4409-8236-3c4fd5474c11** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — analyticPushforward_mk_spec descent compatibility.
- **0a5f74a8-0259-4d37-b6f3-1690c29cac19** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — PeriodFunctional sorry (long-blocked).
- **03715a4d-0570-47fe-b3a7-bae31ecca811** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — GenusZeroClassification sorry (long-blocked).
- **05100f76-7d7d-4798-bb7c-c35c7ee7cabb** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_id (NEW from local _id_spec split).
- **b7799fc9-ad77-40de-9b32-42f2d735ac82** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id (NEW from local _id_eq split).
- **6b2f47f1-c0fe-4313-a950-57525866b53e** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — pathIntegralFunctional_separates_points_spec (Abel anti-hack #2) — orphan packet.
- **403c9581-217e-4df5-a9b7-656409a0d9dd** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (after Claude's bundle refactor closed _mk_eq).
- **5f052643-eee1-47d4-bce2-a3717c488d8d** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp_spec — orphan packet (covariant trace-lift composition).
- **e19361c4-97c0-44bb-a8e4-1036aadfee16** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — GenusZeroClassification sorry (Aristotle's pick, not chart-blocked).
- **bbca4cae-6ca6-4d1a-90b6-6bab64f6b71e** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — Second PeriodFunctional sorry (whichever 0a5f74a8 didn't pick).
- **58eb31f0-9b8c-411d-9087-0ff130a58ec8** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — Step 5: holomorphicOneForm_normedSpace_uniformOnCompact assembly (after 8585f085 lands).
- **360a05bf-5522-4d96-8e44-fb68e19ad707** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — Specifically L320: analyticGenus ℂ X = analyticGenus ℂ (OnePoint ℂ).
- **fbfe1498-210b-4931-a093-788d14de2cb0** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — Specifically L591: Nonempty (X ≃ₜ Metric.sphere ...) sphere homeomorphism.
- **e7250841-96e4-4d65-9be5-81dcaf1ae393** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_montel_subseq_tendsto (NEW from Montel TOPDOWN split): analytic core — Cauchy estimates + Arzelà–Ascoli + Weierstrass.
- **ba57741f-3fef-4160-b252-1af4ea559094** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id_apply_at (NEW from subagent TOPDOWN split).
- **dc58e548-c453-4335-a57c-e739df284174** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp_spec_apply_at (NEW from subagent TOPDOWN split).
- **de8822fb-8ae9-4c26-a026-213c17802e28** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_fiberNorm_continuous (NEW from 58eb31f0 split).
- **bed365ae-8a56-49fd-a9c8-432d36d0e7de** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_supNorm_completeSpace (NEW from 58eb31f0 split).
- **20995679-1911-4bcf-b0e9-12b6b6bc29a3** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_montel_subseq_isCauchy (NEW from Montel TOPDOWN split).
- **8a8ea66d-a01e-4317-a3ea-0ce135ae485c** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_closedBall_totallyBounded (NEW from 20995679 split).
- **706bf2e2-1e99-48ee-8926-1eb995019743** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_supNorm_cauchySeq_tendsto (NEW from a8db8a8f split).
- **76c01cf9-02c3-4a37-9a60-f983a96bdf3e** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_onePointCx_toFun_finite_eq_zero (Liouville finite leaf — 1:1 coverage).
- **c2a57d71-73b5-4669-8892-78e24ec878cb** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_onePointCx_toFun_infty_eq_zero (Liouville infty leaf — 1:1 coverage).
- **88effa1c-9abb-4391-99d2-a277c7e05c39** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneFormLinearEquivOfHomeoSphere (uniformization-lite — 1:1 coverage).
- **0cfa1878-064e-49dd-9d39-acba1d18adfc** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — periodVectors_linearIndependent (Riemann bilinear — 1:1 coverage).
- **ad278fcd-6c7c-476a-ba06-b5fb15989e6b** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (replacement for rejected 403c9581 — 1:1 coverage).
- **9b4998a5-7fd1-468e-91d5-ae2861eec0f6** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id_apply_at (renewed attempt after ba57741f docstring integration).
- **3b7e5dac-a8b0-4863-be44-462d2f09c961** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp_spec_apply_at (renewed attempt after dc58e548 docstring integration).
- **dc2c19e1-76ba-4fab-ba91-3a996a15add6** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_entire (NEW from 76c01cf9 split).
- **659de1fb-a95c-4d0d-8cd9-99925f04f931** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_tendsto_zero (NEW from 76c01cf9 split).
- **af6e2c7a-1412-4823-96fb-eade7b78c3ca** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — subsingleton_holomorphicOneForm_of_homeo_sphere (NEW from 88effa1c split).
- **e227f244-521b-4105-9744-25d6d25338f3** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — symplectic_basis_of_cycles (NEW from 0cfa1878 split).
- **0de5af2a-87b1-4fff-8721-c2e5136654d6** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — period_vectors_linearIndependent_of_symplectic (NEW from 0cfa1878 split).
- **a0bddfd5-c8f6-476a-ae89-47571f269525** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (renewed after ad278fcd docstring integration).
- **921772f5-cea4-429c-a2c9-3d7bd55f13b6** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — h1_basis_of_compact_riemann_surface (NEW from e227f244 split).
- **4d0d28d6-6d52-4e7e-b1ab-16afe7cf0180** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (renewed after a0bddfd5 no-op).
- **3683ef39-f83c-41e3-98ed-a1ed2dd6f2cd** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id_apply_at (renewed after 9b4998a5 deferred).
- **362e259f-b8cf-4522-a55f-de60211c801d** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp (NEW from af653549 split).
- **9c222f2d-2be3-499f-a8a6-9fe263bec7f4** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — period_vectors_linearIndependent_of_symplectic (renewed after 0de5af2a stale).
- **6f6f015d-7c0d-4cba-9182-07300e8c9be8** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — basisAnalyticPushforwardBundle_id_traceLift (NEW from a8778c20 bundle-primitive split).
- **f3a8e713-ba50-4ec6-b31b-ca49dd3e9460** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — basisAnalyticPushforwardBundle_comp_traceLift (NEW from a1ce4200 bundle-primitive split).
- **6547fde4-4483-430f-b567-5cb1f81b0c18** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisAnalyticPullbackBundle_id_dualPullback (NEW from PullbackBasis bundle-primitive split).
- **86bef3e0-0fa0-40b4-83ce-700cc19b847e** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisAnalyticPullbackBundle_comp_dualPullback (NEW from PullbackBasis bundle-primitive split).
- **632f36aa-6152-40dd-ad86-582d47e6b2db** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_fiberNorm_continuous — fresh packet for previously uncovered sorry.
- **fc057985-4072-43e4-b4a1-668153917ba7** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_supNorm_cauchySeq_tendsto — fresh packet for previously uncovered sorry.
- **6751b37c-9af7-4757-a5cc-9602ff3603d9** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_closedBall_totallyBounded — fresh packet for previously uncovered sorry.
- **2a5eea2c-0ce6-4316-b857-a77068d82713** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_entire — fresh packet for previously uncovered sorry.
- **47166a51-62ae-40a6-a4a1-5086a7a4614e** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_tendsto_zero — fresh packet for previously uncovered sorry.
- **50ed9388-fdd1-4456-9c83-387c8f83ab3d** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_onePointCx_toFun_infty_eq_zero — Liouville-infty leaf, fresh packet.
- **edca80d7-307a-490a-a343-fa6e4c4b92f7** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — subsingleton_holomorphicOneForm_of_homeo_sphere — uniformization-lite, fresh packet.
- **4f698084-46b4-4a5d-970f-368a0225c3f4** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — genus_zero_homeomorph_onePointCx — uniformization core. Codex also racing this in worktree.
- **303edecd-6419-49e5-8994-0200b5f66fe7** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — periodSubgroup_isZLattice — discreteness of basis-aligned period subgroup. TOPDOWN plan in docstring.
- **263e138e-1e3c-4281-80e3-66618f709eae** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — h1_free_of_compact_surface — fresh packet for previously uncovered sorry (NEW from 921772f5 split).
- **c17e5dd9-80d5-4312-b8f0-673890bdc881** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — analyticGenus_eq_topologicalGenus — submitted on cap-recovery.
- **7ceff781-61d0-4e33-8ce4-7edbac690bb3** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — pathIntegralFunctional_separates_points_spec — submitted on cap-recovery.
- **56e6ac87-4c37-4c7a-b5b5-8d3ef369b0d6** (submitted): `Jacobian/Blueprint/Sec05/RiemannHurwitzDeg1.lean` — 2 sorries — placeholder-refinement framing: refine local SurfaceMap to bundle ramification_satisfies_riemann_hurwitz invariant.
- **db7d56a1-84a9-4ad1-82ad-7ae2fa13a102** (submitted): `Jacobian/StageA/EdgeWordTietze.lean` — 1 sorry (handleSwap_grouping_inductive_step). Refine local handleSwap_strictly_decreases_mu (True := trivial placeholder) into real content.
- **31175f0a-6e6a-4b9a-9e1a-5b1287c8d9e2** (submitted): `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` — ID 4: singular simplex integration
- **c2cf69e5-b4a5-44b6-972a-8db7a66cebce** (submitted): `Jacobian/Periods/Polygon4gCellular.lean` — prove polygon4g_succ_hurewicz_iso_freeZ
- **421a90df-fb9a-46d0-82e3-25d40c3b418a** (submitted): `Jacobian/TraceDegree/PiecewiseC1Instance.lean` — prove instPiecewiseC1PathRegularity
- **0006f3e9-5842-40e9-b8fd-e77d39667a57** (submitted): `Jacobian/TraceDegree/TraceDefinition.lean` — prove localInverseAt_holomorphic
- **7bd649ad-2b68-43fb-9cc7-a119925825e9** (submitted): `Jacobian/TraceDegree/TraceDefinition.lean` — prove localTraceAtRegularValue_holomorphic
- **b4654c4b-01ec-4fe7-bbcf-9c976473ea72** (submitted): `Jacobian/TraceDegree/TraceDefinition.lean` — prove trace_pullback_at_regular_value
- **0050e6c0-3326-4d75-9c21-58f79bdccfce** (submitted): `Jacobian/Blueprint/Sec02/MontelCompactness.lean` — prove montel_pointwise_extraction
- **1259f3fa-872c-4ae5-8c0a-634e23cac4d9** (submitted): `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` — prove chartLift_contDiffOn_assumption
- **3fec87fa-3619-4acc-87d5-a82ae74293e5** (submitted): `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` — prove chartedFormPullback_continuous_assumption
- **1b11a60f-19e5-455d-beb7-a5baadc0ac3c** (submitted): `Jacobian/HolomorphicForms/CMfldBumpStub.lean` — prove cMfldBump_apply_self
- **da91941b-89cc-46b4-86a9-156dcc2d8624** (submitted): `Jacobian/HolomorphicForms/CMfldBumpStub.lean` — prove cMfldBump_eq_one_near
- **1a50bfc4-e90d-4c9d-8891-3e0994b48b7e** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — prove holomorphicOneForm_arzela_ascoli_refine23
- **eb62762d-9750-4cf4-a8cd-1d2a6c361dd6** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — prove holomorphicOneForm_supNorm_cauchySeq_tendsto_via_steps
- **d0717941-5047-454b-8fd5-68382a67e40d** (submitted): `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` — prove closedForm_pathIntegral_primitive_exists

## Live Status (2026-05-04, R10 dispatch end-to-end on

- **b782c387-5718-4565-a3e8-ed049d6c4c26** (submitted): `Jacobian/HolomorphicForms/SectionTopologyRecon.lean` — Recon: survey Mathlib v4.28.0 API for topology-of-uniform-convergence on ContMDiffSection (step (a) of the Riemann-Roch plan from 72ac3a75)
- **5dfd5106-8e6b-45b4-92a6-b4265d3a5704** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — TOP-DOWN survey on `holomorphicOneForm_montel` — Montel's theorem for holomorphic 1-forms on compact Riemann surface. High-risk gap-narrowing on the Riemann-Roch / FD chain.
- **848a0c88-6c27-423d-865b-38b35390b7a0** (submitted): `Jacobian/HolomorphicForms/SectionTopologyConstructionRecon.lean` — NEW recon file: how to construct the Banach data on `ContMDiffSection` for compact X. Companion to `holomorphicOneForm_normedSpace_uniformOnCompact` obligation.
- **90750074-0d26-4f60-b32e-a79942e56111** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOP-DOWN refinement on `holomorphicOneForm_onePointCx_subsingleton` — the Liouville core of genus-zero classification (no global holomorphic 1-form on ℂℙ¹). Anti-hack #1 critical path.
- **dc8af381-8277-44ab-95f4-6e62dba5faee** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — Discharge `exists_compact_periodFundamentalDomain` using the existing `IsZLattice ℝ` instance + Mathlib ZSpan API. Reduction 3→2 sorries in this file.
- **6992e390-050b-49fb-bb21-5fde3ccb0449** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — TOPDOWN reduction: discharge `holomorphicOneForm_locallyCompact_of_compactRiemannSurface` sorry-free using `holomorphicOneForm_montel B` (still-sorry but named) — translation invariance on a normed space. Reduction 3→2 sorries in CompactRiemannSurface.lean.
- **d493c66b-a666-4b4d-a245-67db26ff4346** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOP-DOWN refinement on `holomorphicOneForm_onePointCx_toFun_eq_zero` — chart-coefficient extraction sorry exposed by 90750074. The Liouville analytic content is now discharged; this is the chart-pullback API gap.
- **63158306-c2f9-4f3e-a2e9-1b385e59fe48** (submitted): `Jacobian/HolomorphicForms/SectionFiberNorm.lean` — NEW file: Step 1 of `848a0c88` Banach-data construction recon — define `ContMDiffSection.fiberNorm` and prove its continuity. Building block for the eventual `holomorphicOneForm_normedSpace_uniformOnCompact` discharge.
- **1f7d4399-438b-4d8a-b128-dc290bde3a48** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOPDOWN on the now-narrower finite leaf `holomorphicOneForm_onePointCx_toFun_finite_eq_zero` (Liouville application via identity-chart pullback + EntireZero black-box).
- **f1786fa8-bbaa-4cdd-9683-b9dfbdf01797** (submitted): `Jacobian/HolomorphicForms/SectionSupNorm.lean` — NEW file: Step 2 of `848a0c88` Banach-data construction recon — define `ContMDiffSection.supNorm` and prove 5 sup-norm properties (zero, eq_zero_iff, add_le, smul_le, neg). 40-60 LOC per recon §5 Step 2.
- **51fd0fce-fb19-45e7-9ef1-efbf65de7ac9** (submitted): `Jacobian/HolomorphicForms/SectionMetric.lean` — NEW file: Step 3 of `848a0c88` Banach-data construction recon — define `ContMDiffSection.dist` and prove 4 MetricSpace axioms + dist_eq. ~20-50 LOC per recon §5 Step 3.
- **8585f085-371e-4c86-b276-adadf70f6392** (submitted): `Jacobian/HolomorphicForms/SectionComplete.lean` — NEW file: Step 4 of `848a0c88` Banach-data construction recon — completeness via embedding HolomorphicOneForm ℂ X into C(X, ℂ) + closedness. Hardest step, 80-150 LOC.
- **7e2bc288-bedc-4149-b0d8-28bcadf78ade** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — TOPDOWN refinement of 3 sorries (analyticPullback_contMDiff/_id_apply/_comp_apply). Acceptable outcomes: full proofs, companion-spec split, or survey docstring.
- **4d56b249-931f-46e3-8ace-50d28a74ac78** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — TOPDOWN refinement of 3 sorries (analyticPushforward_contMDiff/_id_apply/_comp_apply). Mirror of PullbackBasis packet 7e2bc288.
- **bbe527bb-28a6-4d6e-a32a-cf5f8d8df6e3** (submitted): `Jacobian/TraceDegree/AnalyticDegree.lean` — Discharge analyticPushforward_analyticPullback (anti-hack #4) via the recommended companion opaque _spec from prior survey 10e5bfbb.
- **d1d10391-67c2-4bfc-ad21-5514a1052a55** (submitted): `Jacobian/ComplexTorus/ULiftTransport.lean` — Discharge 2 sorries (complexTorusULift_contMDiff_up/_down). Both should be straightforward via the transported chart structure (chart-target map is identity).
- **d967438b-5455-49c9-a8ab-08bf2e0482e8** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — TOPDOWN of 3 sorries: pathIntegralFunctional_self, analyticOfCurve_contMDiff, pathIntegralFunctional_separates_points (Abel's theorem).
- **c5101910-f51a-4aab-8abf-d801b239642a** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — TOPDOWN of 2 sorries: periodSubgroup_isZLattice (integrality), periodSubgroup_spans_real (Riemann bilinear nondegeneracy).
- **c7feba63-8103-4859-846f-053274534d9d** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — TOPDOWN refinement of holomorphicOneForm_montel (only — _normedSpace handled by 8585f085 chain).
- **b3280ab0-41c9-46fd-82be-4eb17e7c0748** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOPDOWN refinement of 4 sorries: 2 Liouville-core leaves (chart-extraction blocker) + 2 uniformization items.
- **d8fd495f-b92d-4c09-898b-ce7614ecfaa7** (submitted): `Jacobian/ComplexTorus/ULiftTransport.lean` — Single-sorry packet on complexTorusULift_contMDiff_up only.
- **b4029f72-c3d9-4629-a961-e5ade014ea84** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on analyticPullback_id_apply only.
- **c910ac80-7262-443d-88c1-bb55817ac27e** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on analyticPullback_contMDiff only.
- **2bd5f151-4bab-4023-ae9e-dc614099864a** (submitted): `Jacobian/ComplexTorus/ULiftTransport.lean` — Single-sorry packet on complexTorusULift_contMDiff_down only.
- **27c56154-66ff-4c22-a86b-e112054f19de** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on analyticPullback_comp_apply only.
- **f280ecc6-c477-48f1-9128-3d8b7eeb0012** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Single-sorry packet on analyticPushforward_contMDiff only.
- **271cc21e-7540-4a49-978e-a51cad18978c** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Single-sorry packet on analyticPushforward_id_apply only.
- **6c796045-b207-4290-9d5c-5b02499ca57e** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Single-sorry packet on analyticPushforward_comp_apply only.
- **3d5f379e-568b-4e13-8f51-c9529fdc1f36** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Single-sorry packet on pathIntegralFunctional_self only.
- **c6c4c612-3d0a-4b8f-a792-9ee8ff6eb80f** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Single-sorry packet on analyticOfCurve_contMDiff only.
- **4f76ac75-4b03-44bf-9c4d-e473bcbb86b8** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Single-sorry packet on pathIntegralFunctional_separates_points (Abel's theorem).
- **99825c13-b58a-420b-b25c-ff202a2a5e70** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on the new analyticPullback_comp_spec (Claude's split target).
- **2aab5e91-890a-447f-9729-f4872a50e23e** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on the improved analyticPullback_id_spec (= ContinuousAddMonoidHom.id _).
- **a3b5ae84-236d-4b40-a64a-259b3f8a7752** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Replacement packet on the new pathIntegralFunctional_self_spec.
- **777f976c-0e8e-4078-a345-68f015c9d7aa** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Replacement packet on the new analyticPushforward_contMDiff_spec.
- **3264c622-6675-4b18-94f3-9ec50f130185** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Replacement packet on analyticOfCurve_contMDiff_spec.
- **7f273ec8-537c-4bc9-a159-3098725b12f7** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Replacement packet on pathIntegralFunctional_separates_points_spec (Abel's theorem deep content).
- **09a7e39c-5748-4c12-a2a0-55b2039d52c7** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Replacement packet on analyticPushforward_id_spec.
- **90fc4a81-0f3c-4a7f-a09a-34f8e16b532b** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Replacement packet on analyticPushforward_comp_spec.
- **f914a263-801f-4dbc-8671-bc6d67a763bf** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — contMDiff_continuousAddMonoidHom_complexTorus general lemma.
- **c69fcd88-2cb2-4710-bef0-200e1a2cd351** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — analyticPullback_id_spec respecting basisDualPullback structure.
- **369f3f7b-4879-4ef1-9994-d46784537914** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — analyticPullback_contMDiff via complex-torus smoothness lemma.
- **16277f52-39bc-4f28-9860-8d771687c3ad** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — quotientMk_contMDiff_spec via charted-space machinery.
- **65001239-6493-4b88-8f4d-e21c6373addd** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — analyticPushforward_id_eq deeper split.
- **654d5071-ee04-446c-a69e-0d584517149e** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — pathIntegralFunctional_contMDiff_spec gap analysis.
- **7f3ec297-cad6-409f-bc0d-f4c0dc196fd2** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — analyticPullback_mk_eq + basisDualPullback_comp paired packet.
- **e3dcd529-c13e-4409-8236-3c4fd5474c11** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — analyticPushforward_mk_spec descent compatibility.
- **0a5f74a8-0259-4d37-b6f3-1690c29cac19** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — PeriodFunctional sorry (long-blocked).
- **03715a4d-0570-47fe-b3a7-bae31ecca811** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — GenusZeroClassification sorry (long-blocked).
- **05100f76-7d7d-4798-bb7c-c35c7ee7cabb** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_id (NEW from local _id_spec split).
- **b7799fc9-ad77-40de-9b32-42f2d735ac82** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id (NEW from local _id_eq split).
- **6b2f47f1-c0fe-4313-a950-57525866b53e** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — pathIntegralFunctional_separates_points_spec (Abel anti-hack #2) — orphan packet.
- **403c9581-217e-4df5-a9b7-656409a0d9dd** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (after Claude's bundle refactor closed _mk_eq).
- **5f052643-eee1-47d4-bce2-a3717c488d8d** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp_spec — orphan packet (covariant trace-lift composition).
- **e19361c4-97c0-44bb-a8e4-1036aadfee16** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — GenusZeroClassification sorry (Aristotle's pick, not chart-blocked).
- **bbca4cae-6ca6-4d1a-90b6-6bab64f6b71e** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — Second PeriodFunctional sorry (whichever 0a5f74a8 didn't pick).
- **58eb31f0-9b8c-411d-9087-0ff130a58ec8** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — Step 5: holomorphicOneForm_normedSpace_uniformOnCompact assembly (after 8585f085 lands).
- **360a05bf-5522-4d96-8e44-fb68e19ad707** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — Specifically L320: analyticGenus ℂ X = analyticGenus ℂ (OnePoint ℂ).
- **fbfe1498-210b-4931-a093-788d14de2cb0** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — Specifically L591: Nonempty (X ≃ₜ Metric.sphere ...) sphere homeomorphism.
- **e7250841-96e4-4d65-9be5-81dcaf1ae393** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_montel_subseq_tendsto (NEW from Montel TOPDOWN split): analytic core — Cauchy estimates + Arzelà–Ascoli + Weierstrass.
- **ba57741f-3fef-4160-b252-1af4ea559094** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id_apply_at (NEW from subagent TOPDOWN split).
- **dc58e548-c453-4335-a57c-e739df284174** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp_spec_apply_at (NEW from subagent TOPDOWN split).
- **de8822fb-8ae9-4c26-a026-213c17802e28** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_fiberNorm_continuous (NEW from 58eb31f0 split).
- **bed365ae-8a56-49fd-a9c8-432d36d0e7de** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_supNorm_completeSpace (NEW from 58eb31f0 split).
- **20995679-1911-4bcf-b0e9-12b6b6bc29a3** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_montel_subseq_isCauchy (NEW from Montel TOPDOWN split).
- **8a8ea66d-a01e-4317-a3ea-0ce135ae485c** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_closedBall_totallyBounded (NEW from 20995679 split).
- **706bf2e2-1e99-48ee-8926-1eb995019743** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_supNorm_cauchySeq_tendsto (NEW from a8db8a8f split).
- **76c01cf9-02c3-4a37-9a60-f983a96bdf3e** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_onePointCx_toFun_finite_eq_zero (Liouville finite leaf — 1:1 coverage).
- **c2a57d71-73b5-4669-8892-78e24ec878cb** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_onePointCx_toFun_infty_eq_zero (Liouville infty leaf — 1:1 coverage).
- **88effa1c-9abb-4391-99d2-a277c7e05c39** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneFormLinearEquivOfHomeoSphere (uniformization-lite — 1:1 coverage).
- **0cfa1878-064e-49dd-9d39-acba1d18adfc** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — periodVectors_linearIndependent (Riemann bilinear — 1:1 coverage).
- **ad278fcd-6c7c-476a-ba06-b5fb15989e6b** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (replacement for rejected 403c9581 — 1:1 coverage).
- **9b4998a5-7fd1-468e-91d5-ae2861eec0f6** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id_apply_at (renewed attempt after ba57741f docstring integration).
- **3b7e5dac-a8b0-4863-be44-462d2f09c961** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp_spec_apply_at (renewed attempt after dc58e548 docstring integration).
- **dc2c19e1-76ba-4fab-ba91-3a996a15add6** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_entire (NEW from 76c01cf9 split).
- **659de1fb-a95c-4d0d-8cd9-99925f04f931** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_tendsto_zero (NEW from 76c01cf9 split).
- **af6e2c7a-1412-4823-96fb-eade7b78c3ca** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — subsingleton_holomorphicOneForm_of_homeo_sphere (NEW from 88effa1c split).
- **e227f244-521b-4105-9744-25d6d25338f3** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — symplectic_basis_of_cycles (NEW from 0cfa1878 split).
- **0de5af2a-87b1-4fff-8721-c2e5136654d6** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — period_vectors_linearIndependent_of_symplectic (NEW from 0cfa1878 split).
- **a0bddfd5-c8f6-476a-ae89-47571f269525** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (renewed after ad278fcd docstring integration).
- **921772f5-cea4-429c-a2c9-3d7bd55f13b6** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — h1_basis_of_compact_riemann_surface (NEW from e227f244 split).
- **4d0d28d6-6d52-4e7e-b1ab-16afe7cf0180** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (renewed after a0bddfd5 no-op).
- **3683ef39-f83c-41e3-98ed-a1ed2dd6f2cd** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id_apply_at (renewed after 9b4998a5 deferred).
- **362e259f-b8cf-4522-a55f-de60211c801d** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp (NEW from af653549 split).
- **9c222f2d-2be3-499f-a8a6-9fe263bec7f4** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — period_vectors_linearIndependent_of_symplectic (renewed after 0de5af2a stale).
- **6f6f015d-7c0d-4cba-9182-07300e8c9be8** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — basisAnalyticPushforwardBundle_id_traceLift (NEW from a8778c20 bundle-primitive split).
- **f3a8e713-ba50-4ec6-b31b-ca49dd3e9460** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — basisAnalyticPushforwardBundle_comp_traceLift (NEW from a1ce4200 bundle-primitive split).
- **6547fde4-4483-430f-b567-5cb1f81b0c18** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisAnalyticPullbackBundle_id_dualPullback (NEW from PullbackBasis bundle-primitive split).
- **86bef3e0-0fa0-40b4-83ce-700cc19b847e** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisAnalyticPullbackBundle_comp_dualPullback (NEW from PullbackBasis bundle-primitive split).
- **632f36aa-6152-40dd-ad86-582d47e6b2db** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_fiberNorm_continuous — fresh packet for previously uncovered sorry.
- **fc057985-4072-43e4-b4a1-668153917ba7** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_supNorm_cauchySeq_tendsto — fresh packet for previously uncovered sorry.
- **6751b37c-9af7-4757-a5cc-9602ff3603d9** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_closedBall_totallyBounded — fresh packet for previously uncovered sorry.
- **2a5eea2c-0ce6-4316-b857-a77068d82713** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_entire — fresh packet for previously uncovered sorry.
- **47166a51-62ae-40a6-a4a1-5086a7a4614e** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_tendsto_zero — fresh packet for previously uncovered sorry.
- **50ed9388-fdd1-4456-9c83-387c8f83ab3d** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_onePointCx_toFun_infty_eq_zero — Liouville-infty leaf, fresh packet.
- **edca80d7-307a-490a-a343-fa6e4c4b92f7** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — subsingleton_holomorphicOneForm_of_homeo_sphere — uniformization-lite, fresh packet.
- **4f698084-46b4-4a5d-970f-368a0225c3f4** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — genus_zero_homeomorph_onePointCx — uniformization core. Codex also racing this in worktree.
- **303edecd-6419-49e5-8994-0200b5f66fe7** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — periodSubgroup_isZLattice — discreteness of basis-aligned period subgroup. TOPDOWN plan in docstring.
- **263e138e-1e3c-4281-80e3-66618f709eae** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — h1_free_of_compact_surface — fresh packet for previously uncovered sorry (NEW from 921772f5 split).
- **c17e5dd9-80d5-4312-b8f0-673890bdc881** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — analyticGenus_eq_topologicalGenus — submitted on cap-recovery.
- **7ceff781-61d0-4e33-8ce4-7edbac690bb3** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — pathIntegralFunctional_separates_points_spec — submitted on cap-recovery.
- **56e6ac87-4c37-4c7a-b5b5-8d3ef369b0d6** (submitted): `Jacobian/Blueprint/Sec05/RiemannHurwitzDeg1.lean` — 2 sorries — placeholder-refinement framing: refine local SurfaceMap to bundle ramification_satisfies_riemann_hurwitz invariant.
- **db7d56a1-84a9-4ad1-82ad-7ae2fa13a102** (submitted): `Jacobian/StageA/EdgeWordTietze.lean` — 1 sorry (handleSwap_grouping_inductive_step). Refine local handleSwap_strictly_decreases_mu (True := trivial placeholder) into real content.
- **31175f0a-6e6a-4b9a-9e1a-5b1287c8d9e2** (submitted): `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` — ID 4: singular simplex integration
- **c2cf69e5-b4a5-44b6-972a-8db7a66cebce** (submitted): `Jacobian/Periods/Polygon4gCellular.lean` — prove polygon4g_succ_hurewicz_iso_freeZ
- **421a90df-fb9a-46d0-82e3-25d40c3b418a** (submitted): `Jacobian/TraceDegree/PiecewiseC1Instance.lean` — prove instPiecewiseC1PathRegularity
- **0006f3e9-5842-40e9-b8fd-e77d39667a57** (submitted): `Jacobian/TraceDegree/TraceDefinition.lean` — prove localInverseAt_holomorphic
- **7bd649ad-2b68-43fb-9cc7-a119925825e9** (submitted): `Jacobian/TraceDegree/TraceDefinition.lean` — prove localTraceAtRegularValue_holomorphic
- **b4654c4b-01ec-4fe7-bbcf-9c976473ea72** (submitted): `Jacobian/TraceDegree/TraceDefinition.lean` — prove trace_pullback_at_regular_value
- **0050e6c0-3326-4d75-9c21-58f79bdccfce** (submitted): `Jacobian/Blueprint/Sec02/MontelCompactness.lean` — prove montel_pointwise_extraction
- **1259f3fa-872c-4ae5-8c0a-634e23cac4d9** (submitted): `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` — prove chartLift_contDiffOn_assumption
- **3fec87fa-3619-4acc-87d5-a82ae74293e5** (submitted): `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` — prove chartedFormPullback_continuous_assumption
- **1b11a60f-19e5-455d-beb7-a5baadc0ac3c** (submitted): `Jacobian/HolomorphicForms/CMfldBumpStub.lean` — prove cMfldBump_apply_self
- **da91941b-89cc-46b4-86a9-156dcc2d8624** (submitted): `Jacobian/HolomorphicForms/CMfldBumpStub.lean` — prove cMfldBump_eq_one_near
- **1a50bfc4-e90d-4c9d-8891-3e0994b48b7e** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — prove holomorphicOneForm_arzela_ascoli_refine23
- **eb62762d-9750-4cf4-a8cd-1d2a6c361dd6** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — prove holomorphicOneForm_supNorm_cauchySeq_tendsto_via_steps
- **d0717941-5047-454b-8fd5-68382a67e40d** (submitted): `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` — prove closedForm_pathIntegral_primitive_exists

## Curve-analysis frontier delegation packets (2026-05-05, queued; Aristotle blocked)

Stepwise refinement (per `ref/TOPDOWN.md`) is being driven locally
while the Aristotle queue is unavailable. The packets below are the
*Aristotle-shaped split* of each frontier sorry in the curve-analysis
pass — each packet targets one new helper file with a tightly scoped
named obligation, prefers direct tactics, and includes the Mathlib
gap that blocks final discharge.

When Aristotle is back, dispatch in the order given (lower numbers
first; sibling jobs can go in parallel because their write scopes are
disjoint).

### Packet C1 — `polygon4g_singularH1_basis` (Polygon4gCellular)

**Source sorry:** `hurewicz_singularH1_iso_polygon4g`
(`Jacobian/Periods/Polygon4gCellular.lean:135`).

Top-down split into three named obligations (each in its own file):

| Sub-job | Target file | Statement | Mathlib gap |
|---|---|---|---|
| C1a | `Jacobian/Periods/Polygon4gFundamentalGroupAb.lean` | `polygon4g_succ_fundamentalGroup_abelianization_freeZ` — `π₁(Σ_g)^{ab} ≃ ℤ^{2(g+1)}` | Surface group presentation absent |
| C1b | `Jacobian/Periods/HurewiczNatTrans.lean` | `hurewicz_iso_natural` — `H₁(X,ℤ) ≃ π₁(X)^{ab}` for path-connected `X` | Hurewicz natural transformation absent |
| C1c | `Jacobian/Periods/Polygon4gCellular.lean` | `hurewicz_singularH1_iso_polygon4g` — sorry-free assembly composing C1a∘C1b⁻¹ | — |

Each sub-job's allowed write scope is exactly the named file; forbidden
files always include `Jacobian/Challenge.lean`.

### Packet C2 — `singularH1_iso_of_homotopyEquiv_via_prism` (SingularH1Homotopy)

**Source sorry:** `singularH1_iso_of_homotopyEquiv_via_prism`
(`Jacobian/Periods/SingularH1Homotopy.lean:208`).

Already split top-down into named leaves (`SingularChainPrism`,
`singularChain_homotopy_chainHomotopy`, etc.); the residual sorry is the
*assembly through Mathlib's homology functor*. Sub-split:

| Sub-job | Target file | Statement | Mathlib gap |
|---|---|---|---|
| C2a | `Jacobian/Periods/SingularH1FunctorMap.lean` | `singularH1Functor_map` — `C(X,Y) → singularH1 X →ₗ[ℤ] singularH1 Y` honestly via the singular-chain functor | Need to compose `singularChainComplexFunctor` with `Hₙ` extraction |
| C2b | `Jacobian/Periods/SingularH1FunctorMapId.lean` | `singularH1Functor_map_id` — identity functoriality | — (follows from C2a) |
| C2c | `Jacobian/Periods/SingularH1FunctorMapComp.lean` | `singularH1Functor_map_comp` — composition functoriality | — |
| C2d | `Jacobian/Periods/SingularH1FunctorMapHomotopy.lean` | homotopic maps induce equal `H₁` (via prism leaves already in `SingularH1Homotopy.lean`) | descent of chain-homotopy to homology |
| C2e | `Jacobian/Periods/SingularH1Homotopy.lean` | `singularH1_iso_of_homotopyEquiv_via_prism` — sorry-free `LinearEquiv` from C2a/b/c/d | — |

### Packet C3 — `IntegralOneCycle_finite_of_cellular`, `_free_of_cellular` (CellularHomologyRS)

**Source sorries:** `Jacobian/Periods/CellularHomologyRS.lean:114, 136`.

| Sub-job | Target file | Statement | Mathlib gap |
|---|---|---|---|
| C3a | `Jacobian/Periods/CellularChainComplex.lean` | `cellularChainComplex` — finite ℤ-chain complex from `FiniteCWStructure` | cellular chain complex on a topological space |
| C3b | `Jacobian/Periods/CellularSingularComparison.lean` | `cellular_eq_singular_homology` — Hatcher Theorem 2.35 | comparison theorem |
| C3c | `Jacobian/Periods/IntegralOneCycleFreeFromPolygon.lean` | `IntegralOneCycle_free_of_cellular` via the polygonal model (route 1) — uses C1c | needs Packet C1 first |
| C3d | `Jacobian/Periods/IntegralOneCycleFinite.lean` | `IntegralOneCycle_finite_of_cellular` via C3b | — |

C3c blocks on C1; C3a/b are independent.

### Packet C4 — `pathIntegralViaCover_pullbackFormsBundledLM` (PullbackNaturality, path level)

**Source sorry:** `Jacobian/Periods/PullbackNaturality.lean:239`.

This is a chain-rule calculation for path integrals, no Stokes. The
existing file already discharges the Path-API special cases
(refl/trans/symm/zero/add/smul/neg/comp). The remaining base case is
chart-level naturality.

| Sub-job | Target file | Statement |
|---|---|---|
| C4a | `Jacobian/Periods/ChartedFormPullbackNaturality.lean` | `chartedFormPullback_pullback_naturality` — at chart level, `pathIntegralInChart c (f^*η) γᵢ = pathIntegralInChart (c ∘ f, ⟨…⟩) η (γᵢ.map hf.continuous)` |
| C4b | `Jacobian/Periods/PathIntegralViaCoverWithPullbackNaturality.lean` | the `_With` variant on a fixed cover-and-partition |
| C4c | `Jacobian/Periods/PullbackNaturality.lean` | un-`With` lift: discharges line 239 from C4b via the existing Classical.choose wrapper |

### Packet C5 — `periodPairing_pullbackFormsBundledLM` (PullbackNaturality, cycle level)

**Source sorry:** `Jacobian/Periods/PullbackNaturality.lean:139`.

Cycle-level Stokes / descent. Blocks on C4 + concretisation of
`opaque periodPairing`.

| Sub-job | Target file | Statement | Mathlib gap |
|---|---|---|---|
| C5a | `Jacobian/Periods/PeriodPairingChainLevel.lean` | `chainFormPairing` and `periodPairing_eq_chainFormPairing_descent` | concretise `periodPairing` |
| C5b | `Jacobian/Periods/CyclePushforwardChainCompat.lean` | `cyclePushforward` agrees with chain-level pushforward | — (functoriality bookkeeping) |
| C5c | `Jacobian/Periods/PullbackNaturality.lean` | line-139 sorry-free assembly from C4c + C5a + C5b | — |

### Packet C6 — `basisAnalyticPullbackBundle_*_dualPullback` (PullbackBasis HEq diamond)

**Source sorries:** `Jacobian/TraceDegree/PullbackBasis.lean:180, 269`.

Structural fix only. The opaque `basisAnalyticPullbackBundle` is
realised by `Classical.choice` from the zero-valued `Inhabited`
witness, so cross-instance identities cannot be proved without a
concrete construction. The fix is to replace the opaque bundle with
a definition built from a concrete `pullbackFormsMap`.

| Sub-job | Target file | Statement | Mathlib gap |
|---|---|---|---|
| C6a | `Jacobian/HolomorphicForms/PullbackFormsMapConcrete.lean` | `pullbackFormsMap` — concrete `H⁰(Y, Ω¹) →ₗ[ℂ] H⁰(X, Ω¹)` | concrete pullback of holomorphic 1-forms |
| C6b | `Jacobian/TraceDegree/BasisAnalyticPullbackConcrete.lean` | replacement for `opaque basisAnalyticPullbackBundle` built from C6a | — |
| C6c | `Jacobian/TraceDegree/PullbackBasis.lean` | discharge lines 180 and 269 via C6b's defining equations | — |

C6 is sibling to the analogous `PushforwardBasis` blocker
(`pushforwardTraceLift_comp_spec_apply_at`); a real Mathlib
`pullbackFormsMap` would unblock both.

### Packet C7 — `period_congruence_distinct_implies_genus_zero` (AnalyticOfCurveBasis)

**Source sorry:** `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean:264`.

The file's docstring (lines 187–232) already proposes a 3-way split:

| Sub-job | Target file | Statement | Mathlib gap |
|---|---|---|---|
| C7a | `Jacobian/AbelJacobi/AbelTheoremExistence.lean` | `abelJacobi_image_zero_implies_principal` — Abel's theorem (existence) | divisor theory + Pic⁰ |
| C7b | `Jacobian/AbelJacobi/RiemannHurwitzDegOne.lean` | `degree_one_meromorphic_implies_genus_zero` — Riemann-Hurwitz at degree 1 | degree of holomorphic maps + genus-0 classification |
| C7c | `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` | line-264 sorry-free assembly from C7a + C7b + `analyticGenus_eq_topologicalGenus` | — |

Per the file's note this split is "worth executing once the divisor
theory layer or even a placeholder `Divisor X` / `IsPrincipal d` API
exists in the project." Until then, either keep the consolidated form
or commit to introducing the placeholder API in C7a's file.

### Packet C8 — RR/Serre cluster (24 sorries / 11 files)

These are all pieces of classical Riemann-Roch / residue / Serre
duality. The cluster sorries break down as follows; each is its own
Aristotle packet (one file → one or two declarations) and each is
blocked on the same upstream Mathlib gap (divisor / line-bundle /
Čech cohomology / residue machinery).

| Sub-job | File | Decls | Bottom-up content |
|---|---|---|---|
| C8a | `Jacobian/HolomorphicForms/Serre/ResidueMap.lean` | `residueMap_left_inv`, `residueMap_right_inv` | residue ↔ integration map iso |
| C8b | `Jacobian/HolomorphicForms/Serre/RiemannRochHighFromSerre.lean` | (2 decls) | Serre-duality → RR high-degree |
| C8c | `Jacobian/HolomorphicForms/Serre/RiemannRochUmbrellaPieces.lean` | (1 decl) | RR umbrella |
| C8d | `Jacobian/HolomorphicForms/RiemannRoch.lean` | `genusZero_exists_nonconstant_mem_L_point`, `_poleDivisor_eq_point_…` | RR `ℓ(P)=2` for genus 0 |
| C8e | `Jacobian/HolomorphicForms/RiemannRochLowDegree.lean` | (1 decl) | RR low-degree case |
| C8f | `Jacobian/HolomorphicForms/EulerCharLineBundle.lean` | (2 decls) | Euler char of a line bundle |
| C8g | `Jacobian/HolomorphicForms/MeromorphicDegree.lean` | (2 decls) | degree of a meromorphic function |
| C8h | `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` | (2 decls) | de Rham → Dolbeault comparison |
| C8i | `Jacobian/HolomorphicForms/ChartCoeffExtractionRecon.lean` | (1 decl) | smoothness of chart coefficient extraction |
| C8j | `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` | (3 decls) | RS-level glue |
| C8k | `Jacobian/HolomorphicForms/GenusZeroClassification.lean` | (6 decls) | genus-0 ⇒ `≅ ℂℙ¹` |

Total surface area: 24 sorries / 11 files. Most files are 1–2
sorries each (only `GenusZeroClassification` exceeds with 6).

Each C8x packet's split-into-helpers will be filled in as the cluster
is iterated; the splits live in the target file's docstring rather
than this index.

### Iteration cadence (while Aristotle is blocked)

`ref/TOPDOWN.md` defines a "round" as one stepwise refinement that
either reduces the sorry count *or* keeps it constant while replacing
one big sorry by smaller, better-named children. The local schedule
is:

* **C1** — 10 rounds of refinement on Polygon4gCellular before moving on.
* **C2** — 10 rounds on SingularH1Homotopy.
* **C3** — 10 rounds on CellularHomologyRS (both leaves).
* **C4 / C5** — 10 rounds each on PullbackNaturality (path / cycle).
* **C6** — 10 rounds on PullbackBasis (HEq diamond).
* **C7** — 10 rounds on AnalyticOfCurveBasis.
* **C8** — 10 rounds on the RR/Serre cluster (rotating across files).

Each round must end with a passing narrow `lake build` of the touched
module(s).

---

## Live Status (2026-05-02, roadmap-driven saturation tick)

- **b782c387-5718-4565-a3e8-ed049d6c4c26** (submitted): `Jacobian/HolomorphicForms/SectionTopologyRecon.lean` — Recon: survey Mathlib v4.28.0 API for topology-of-uniform-convergence on ContMDiffSection (step (a) of the Riemann-Roch plan from 72ac3a75)
- **5dfd5106-8e6b-45b4-92a6-b4265d3a5704** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — TOP-DOWN survey on `holomorphicOneForm_montel` — Montel's theorem for holomorphic 1-forms on compact Riemann surface. High-risk gap-narrowing on the Riemann-Roch / FD chain.
- **848a0c88-6c27-423d-865b-38b35390b7a0** (submitted): `Jacobian/HolomorphicForms/SectionTopologyConstructionRecon.lean` — NEW recon file: how to construct the Banach data on `ContMDiffSection` for compact X. Companion to `holomorphicOneForm_normedSpace_uniformOnCompact` obligation.
- **90750074-0d26-4f60-b32e-a79942e56111** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOP-DOWN refinement on `holomorphicOneForm_onePointCx_subsingleton` — the Liouville core of genus-zero classification (no global holomorphic 1-form on ℂℙ¹). Anti-hack #1 critical path.
- **dc8af381-8277-44ab-95f4-6e62dba5faee** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — Discharge `exists_compact_periodFundamentalDomain` using the existing `IsZLattice ℝ` instance + Mathlib ZSpan API. Reduction 3→2 sorries in this file.
- **6992e390-050b-49fb-bb21-5fde3ccb0449** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — TOPDOWN reduction: discharge `holomorphicOneForm_locallyCompact_of_compactRiemannSurface` sorry-free using `holomorphicOneForm_montel B` (still-sorry but named) — translation invariance on a normed space. Reduction 3→2 sorries in CompactRiemannSurface.lean.
- **d493c66b-a666-4b4d-a245-67db26ff4346** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOP-DOWN refinement on `holomorphicOneForm_onePointCx_toFun_eq_zero` — chart-coefficient extraction sorry exposed by 90750074. The Liouville analytic content is now discharged; this is the chart-pullback API gap.
- **63158306-c2f9-4f3e-a2e9-1b385e59fe48** (submitted): `Jacobian/HolomorphicForms/SectionFiberNorm.lean` — NEW file: Step 1 of `848a0c88` Banach-data construction recon — define `ContMDiffSection.fiberNorm` and prove its continuity. Building block for the eventual `holomorphicOneForm_normedSpace_uniformOnCompact` discharge.
- **1f7d4399-438b-4d8a-b128-dc290bde3a48** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOPDOWN on the now-narrower finite leaf `holomorphicOneForm_onePointCx_toFun_finite_eq_zero` (Liouville application via identity-chart pullback + EntireZero black-box).
- **f1786fa8-bbaa-4cdd-9683-b9dfbdf01797** (submitted): `Jacobian/HolomorphicForms/SectionSupNorm.lean` — NEW file: Step 2 of `848a0c88` Banach-data construction recon — define `ContMDiffSection.supNorm` and prove 5 sup-norm properties (zero, eq_zero_iff, add_le, smul_le, neg). 40-60 LOC per recon §5 Step 2.
- **51fd0fce-fb19-45e7-9ef1-efbf65de7ac9** (submitted): `Jacobian/HolomorphicForms/SectionMetric.lean` — NEW file: Step 3 of `848a0c88` Banach-data construction recon — define `ContMDiffSection.dist` and prove 4 MetricSpace axioms + dist_eq. ~20-50 LOC per recon §5 Step 3.
- **8585f085-371e-4c86-b276-adadf70f6392** (submitted): `Jacobian/HolomorphicForms/SectionComplete.lean` — NEW file: Step 4 of `848a0c88` Banach-data construction recon — completeness via embedding HolomorphicOneForm ℂ X into C(X, ℂ) + closedness. Hardest step, 80-150 LOC.
- **7e2bc288-bedc-4149-b0d8-28bcadf78ade** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — TOPDOWN refinement of 3 sorries (analyticPullback_contMDiff/_id_apply/_comp_apply). Acceptable outcomes: full proofs, companion-spec split, or survey docstring.
- **4d56b249-931f-46e3-8ace-50d28a74ac78** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — TOPDOWN refinement of 3 sorries (analyticPushforward_contMDiff/_id_apply/_comp_apply). Mirror of PullbackBasis packet 7e2bc288.
- **bbe527bb-28a6-4d6e-a32a-cf5f8d8df6e3** (submitted): `Jacobian/TraceDegree/AnalyticDegree.lean` — Discharge analyticPushforward_analyticPullback (anti-hack #4) via the recommended companion opaque _spec from prior survey 10e5bfbb.
- **d1d10391-67c2-4bfc-ad21-5514a1052a55** (submitted): `Jacobian/ComplexTorus/ULiftTransport.lean` — Discharge 2 sorries (complexTorusULift_contMDiff_up/_down). Both should be straightforward via the transported chart structure (chart-target map is identity).
- **d967438b-5455-49c9-a8ab-08bf2e0482e8** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — TOPDOWN of 3 sorries: pathIntegralFunctional_self, analyticOfCurve_contMDiff, pathIntegralFunctional_separates_points (Abel's theorem).
- **c5101910-f51a-4aab-8abf-d801b239642a** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — TOPDOWN of 2 sorries: periodSubgroup_isZLattice (integrality), periodSubgroup_spans_real (Riemann bilinear nondegeneracy).
- **c7feba63-8103-4859-846f-053274534d9d** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — TOPDOWN refinement of holomorphicOneForm_montel (only — _normedSpace handled by 8585f085 chain).
- **b3280ab0-41c9-46fd-82be-4eb17e7c0748** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOPDOWN refinement of 4 sorries: 2 Liouville-core leaves (chart-extraction blocker) + 2 uniformization items.
- **d8fd495f-b92d-4c09-898b-ce7614ecfaa7** (submitted): `Jacobian/ComplexTorus/ULiftTransport.lean` — Single-sorry packet on complexTorusULift_contMDiff_up only.
- **b4029f72-c3d9-4629-a961-e5ade014ea84** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on analyticPullback_id_apply only.
- **c910ac80-7262-443d-88c1-bb55817ac27e** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on analyticPullback_contMDiff only.
- **2bd5f151-4bab-4023-ae9e-dc614099864a** (submitted): `Jacobian/ComplexTorus/ULiftTransport.lean` — Single-sorry packet on complexTorusULift_contMDiff_down only.
- **27c56154-66ff-4c22-a86b-e112054f19de** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on analyticPullback_comp_apply only.
- **f280ecc6-c477-48f1-9128-3d8b7eeb0012** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Single-sorry packet on analyticPushforward_contMDiff only.
- **271cc21e-7540-4a49-978e-a51cad18978c** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Single-sorry packet on analyticPushforward_id_apply only.
- **6c796045-b207-4290-9d5c-5b02499ca57e** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Single-sorry packet on analyticPushforward_comp_apply only.
- **3d5f379e-568b-4e13-8f51-c9529fdc1f36** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Single-sorry packet on pathIntegralFunctional_self only.
- **c6c4c612-3d0a-4b8f-a792-9ee8ff6eb80f** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Single-sorry packet on analyticOfCurve_contMDiff only.
- **4f76ac75-4b03-44bf-9c4d-e473bcbb86b8** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Single-sorry packet on pathIntegralFunctional_separates_points (Abel's theorem).
- **99825c13-b58a-420b-b25c-ff202a2a5e70** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on the new analyticPullback_comp_spec (Claude's split target).
- **2aab5e91-890a-447f-9729-f4872a50e23e** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on the improved analyticPullback_id_spec (= ContinuousAddMonoidHom.id _).
- **a3b5ae84-236d-4b40-a64a-259b3f8a7752** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Replacement packet on the new pathIntegralFunctional_self_spec.
- **777f976c-0e8e-4078-a345-68f015c9d7aa** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Replacement packet on the new analyticPushforward_contMDiff_spec.
- **3264c622-6675-4b18-94f3-9ec50f130185** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Replacement packet on analyticOfCurve_contMDiff_spec.
- **7f273ec8-537c-4bc9-a159-3098725b12f7** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Replacement packet on pathIntegralFunctional_separates_points_spec (Abel's theorem deep content).
- **09a7e39c-5748-4c12-a2a0-55b2039d52c7** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Replacement packet on analyticPushforward_id_spec.
- **90fc4a81-0f3c-4a7f-a09a-34f8e16b532b** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Replacement packet on analyticPushforward_comp_spec.
- **f914a263-801f-4dbc-8671-bc6d67a763bf** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — contMDiff_continuousAddMonoidHom_complexTorus general lemma.
- **c69fcd88-2cb2-4710-bef0-200e1a2cd351** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — analyticPullback_id_spec respecting basisDualPullback structure.
- **369f3f7b-4879-4ef1-9994-d46784537914** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — analyticPullback_contMDiff via complex-torus smoothness lemma.
- **16277f52-39bc-4f28-9860-8d771687c3ad** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — quotientMk_contMDiff_spec via charted-space machinery.
- **65001239-6493-4b88-8f4d-e21c6373addd** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — analyticPushforward_id_eq deeper split.
- **654d5071-ee04-446c-a69e-0d584517149e** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — pathIntegralFunctional_contMDiff_spec gap analysis.
- **7f3ec297-cad6-409f-bc0d-f4c0dc196fd2** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — analyticPullback_mk_eq + basisDualPullback_comp paired packet.
- **e3dcd529-c13e-4409-8236-3c4fd5474c11** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — analyticPushforward_mk_spec descent compatibility.
- **0a5f74a8-0259-4d37-b6f3-1690c29cac19** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — PeriodFunctional sorry (long-blocked).
- **03715a4d-0570-47fe-b3a7-bae31ecca811** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — GenusZeroClassification sorry (long-blocked).
- **05100f76-7d7d-4798-bb7c-c35c7ee7cabb** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_id (NEW from local _id_spec split).
- **b7799fc9-ad77-40de-9b32-42f2d735ac82** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id (NEW from local _id_eq split).
- **6b2f47f1-c0fe-4313-a950-57525866b53e** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — pathIntegralFunctional_separates_points_spec (Abel anti-hack #2) — orphan packet.
- **403c9581-217e-4df5-a9b7-656409a0d9dd** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (after Claude's bundle refactor closed _mk_eq).
- **5f052643-eee1-47d4-bce2-a3717c488d8d** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp_spec — orphan packet (covariant trace-lift composition).
- **e19361c4-97c0-44bb-a8e4-1036aadfee16** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — GenusZeroClassification sorry (Aristotle's pick, not chart-blocked).
- **bbca4cae-6ca6-4d1a-90b6-6bab64f6b71e** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — Second PeriodFunctional sorry (whichever 0a5f74a8 didn't pick).
- **58eb31f0-9b8c-411d-9087-0ff130a58ec8** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — Step 5: holomorphicOneForm_normedSpace_uniformOnCompact assembly (after 8585f085 lands).
- **360a05bf-5522-4d96-8e44-fb68e19ad707** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — Specifically L320: analyticGenus ℂ X = analyticGenus ℂ (OnePoint ℂ).
- **fbfe1498-210b-4931-a093-788d14de2cb0** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — Specifically L591: Nonempty (X ≃ₜ Metric.sphere ...) sphere homeomorphism.
- **e7250841-96e4-4d65-9be5-81dcaf1ae393** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_montel_subseq_tendsto (NEW from Montel TOPDOWN split): analytic core — Cauchy estimates + Arzelà–Ascoli + Weierstrass.
- **ba57741f-3fef-4160-b252-1af4ea559094** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id_apply_at (NEW from subagent TOPDOWN split).
- **dc58e548-c453-4335-a57c-e739df284174** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp_spec_apply_at (NEW from subagent TOPDOWN split).
- **de8822fb-8ae9-4c26-a026-213c17802e28** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_fiberNorm_continuous (NEW from 58eb31f0 split).
- **bed365ae-8a56-49fd-a9c8-432d36d0e7de** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_supNorm_completeSpace (NEW from 58eb31f0 split).
- **20995679-1911-4bcf-b0e9-12b6b6bc29a3** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_montel_subseq_isCauchy (NEW from Montel TOPDOWN split).
- **8a8ea66d-a01e-4317-a3ea-0ce135ae485c** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_closedBall_totallyBounded (NEW from 20995679 split).
- **706bf2e2-1e99-48ee-8926-1eb995019743** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_supNorm_cauchySeq_tendsto (NEW from a8db8a8f split).
- **76c01cf9-02c3-4a37-9a60-f983a96bdf3e** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_onePointCx_toFun_finite_eq_zero (Liouville finite leaf — 1:1 coverage).
- **c2a57d71-73b5-4669-8892-78e24ec878cb** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_onePointCx_toFun_infty_eq_zero (Liouville infty leaf — 1:1 coverage).
- **88effa1c-9abb-4391-99d2-a277c7e05c39** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneFormLinearEquivOfHomeoSphere (uniformization-lite — 1:1 coverage).
- **0cfa1878-064e-49dd-9d39-acba1d18adfc** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — periodVectors_linearIndependent (Riemann bilinear — 1:1 coverage).
- **ad278fcd-6c7c-476a-ba06-b5fb15989e6b** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (replacement for rejected 403c9581 — 1:1 coverage).
- **9b4998a5-7fd1-468e-91d5-ae2861eec0f6** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id_apply_at (renewed attempt after ba57741f docstring integration).
- **3b7e5dac-a8b0-4863-be44-462d2f09c961** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp_spec_apply_at (renewed attempt after dc58e548 docstring integration).
- **dc2c19e1-76ba-4fab-ba91-3a996a15add6** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_entire (NEW from 76c01cf9 split).
- **659de1fb-a95c-4d0d-8cd9-99925f04f931** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_tendsto_zero (NEW from 76c01cf9 split).
- **af6e2c7a-1412-4823-96fb-eade7b78c3ca** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — subsingleton_holomorphicOneForm_of_homeo_sphere (NEW from 88effa1c split).
- **e227f244-521b-4105-9744-25d6d25338f3** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — symplectic_basis_of_cycles (NEW from 0cfa1878 split).
- **0de5af2a-87b1-4fff-8721-c2e5136654d6** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — period_vectors_linearIndependent_of_symplectic (NEW from 0cfa1878 split).
- **a0bddfd5-c8f6-476a-ae89-47571f269525** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (renewed after ad278fcd docstring integration).
- **921772f5-cea4-429c-a2c9-3d7bd55f13b6** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — h1_basis_of_compact_riemann_surface (NEW from e227f244 split).
- **4d0d28d6-6d52-4e7e-b1ab-16afe7cf0180** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (renewed after a0bddfd5 no-op).
- **3683ef39-f83c-41e3-98ed-a1ed2dd6f2cd** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id_apply_at (renewed after 9b4998a5 deferred).
- **362e259f-b8cf-4522-a55f-de60211c801d** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp (NEW from af653549 split).
- **9c222f2d-2be3-499f-a8a6-9fe263bec7f4** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — period_vectors_linearIndependent_of_symplectic (renewed after 0de5af2a stale).
- **6f6f015d-7c0d-4cba-9182-07300e8c9be8** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — basisAnalyticPushforwardBundle_id_traceLift (NEW from a8778c20 bundle-primitive split).
- **f3a8e713-ba50-4ec6-b31b-ca49dd3e9460** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — basisAnalyticPushforwardBundle_comp_traceLift (NEW from a1ce4200 bundle-primitive split).
- **6547fde4-4483-430f-b567-5cb1f81b0c18** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisAnalyticPullbackBundle_id_dualPullback (NEW from PullbackBasis bundle-primitive split).
- **86bef3e0-0fa0-40b4-83ce-700cc19b847e** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisAnalyticPullbackBundle_comp_dualPullback (NEW from PullbackBasis bundle-primitive split).
- **632f36aa-6152-40dd-ad86-582d47e6b2db** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_fiberNorm_continuous — fresh packet for previously uncovered sorry.
- **fc057985-4072-43e4-b4a1-668153917ba7** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_supNorm_cauchySeq_tendsto — fresh packet for previously uncovered sorry.
- **6751b37c-9af7-4757-a5cc-9602ff3603d9** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_closedBall_totallyBounded — fresh packet for previously uncovered sorry.
- **2a5eea2c-0ce6-4316-b857-a77068d82713** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_entire — fresh packet for previously uncovered sorry.
- **47166a51-62ae-40a6-a4a1-5086a7a4614e** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_tendsto_zero — fresh packet for previously uncovered sorry.
- **50ed9388-fdd1-4456-9c83-387c8f83ab3d** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_onePointCx_toFun_infty_eq_zero — Liouville-infty leaf, fresh packet.
- **edca80d7-307a-490a-a343-fa6e4c4b92f7** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — subsingleton_holomorphicOneForm_of_homeo_sphere — uniformization-lite, fresh packet.
- **4f698084-46b4-4a5d-970f-368a0225c3f4** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — genus_zero_homeomorph_onePointCx — uniformization core. Codex also racing this in worktree.
- **303edecd-6419-49e5-8994-0200b5f66fe7** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — periodSubgroup_isZLattice — discreteness of basis-aligned period subgroup. TOPDOWN plan in docstring.
- **263e138e-1e3c-4281-80e3-66618f709eae** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — h1_free_of_compact_surface — fresh packet for previously uncovered sorry (NEW from 921772f5 split).
- **c17e5dd9-80d5-4312-b8f0-673890bdc881** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — analyticGenus_eq_topologicalGenus — submitted on cap-recovery.
- **7ceff781-61d0-4e33-8ce4-7edbac690bb3** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — pathIntegralFunctional_separates_points_spec — submitted on cap-recovery.
- **56e6ac87-4c37-4c7a-b5b5-8d3ef369b0d6** (submitted): `Jacobian/Blueprint/Sec05/RiemannHurwitzDeg1.lean` — 2 sorries — placeholder-refinement framing: refine local SurfaceMap to bundle ramification_satisfies_riemann_hurwitz invariant.
- **db7d56a1-84a9-4ad1-82ad-7ae2fa13a102** (submitted): `Jacobian/StageA/EdgeWordTietze.lean` — 1 sorry (handleSwap_grouping_inductive_step). Refine local handleSwap_strictly_decreases_mu (True := trivial placeholder) into real content.
- **31175f0a-6e6a-4b9a-9e1a-5b1287c8d9e2** (submitted): `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` — ID 4: singular simplex integration
- **c2cf69e5-b4a5-44b6-972a-8db7a66cebce** (submitted): `Jacobian/Periods/Polygon4gCellular.lean` — prove polygon4g_succ_hurewicz_iso_freeZ
- **421a90df-fb9a-46d0-82e3-25d40c3b418a** (submitted): `Jacobian/TraceDegree/PiecewiseC1Instance.lean` — prove instPiecewiseC1PathRegularity
- **0006f3e9-5842-40e9-b8fd-e77d39667a57** (submitted): `Jacobian/TraceDegree/TraceDefinition.lean` — prove localInverseAt_holomorphic
- **7bd649ad-2b68-43fb-9cc7-a119925825e9** (submitted): `Jacobian/TraceDegree/TraceDefinition.lean` — prove localTraceAtRegularValue_holomorphic
- **b4654c4b-01ec-4fe7-bbcf-9c976473ea72** (submitted): `Jacobian/TraceDegree/TraceDefinition.lean` — prove trace_pullback_at_regular_value
- **0050e6c0-3326-4d75-9c21-58f79bdccfce** (submitted): `Jacobian/Blueprint/Sec02/MontelCompactness.lean` — prove montel_pointwise_extraction
- **1259f3fa-872c-4ae5-8c0a-634e23cac4d9** (submitted): `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` — prove chartLift_contDiffOn_assumption
- **3fec87fa-3619-4acc-87d5-a82ae74293e5** (submitted): `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` — prove chartedFormPullback_continuous_assumption
- **1b11a60f-19e5-455d-beb7-a5baadc0ac3c** (submitted): `Jacobian/HolomorphicForms/CMfldBumpStub.lean` — prove cMfldBump_apply_self
- **da91941b-89cc-46b4-86a9-156dcc2d8624** (submitted): `Jacobian/HolomorphicForms/CMfldBumpStub.lean` — prove cMfldBump_eq_one_near
- **1a50bfc4-e90d-4c9d-8891-3e0994b48b7e** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — prove holomorphicOneForm_arzela_ascoli_refine23
- **eb62762d-9750-4cf4-a8cd-1d2a6c361dd6** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — prove holomorphicOneForm_supNorm_cauchySeq_tendsto_via_steps
- **d0717941-5047-454b-8fd5-68382a67e40d** (submitted): `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` — prove closedForm_pathIntegral_primitive_exists

## Live Status (2026-04-29 17:01 EDT, prior tick — kept for context)

- **b782c387-5718-4565-a3e8-ed049d6c4c26** (submitted): `Jacobian/HolomorphicForms/SectionTopologyRecon.lean` — Recon: survey Mathlib v4.28.0 API for topology-of-uniform-convergence on ContMDiffSection (step (a) of the Riemann-Roch plan from 72ac3a75)
- **5dfd5106-8e6b-45b4-92a6-b4265d3a5704** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — TOP-DOWN survey on `holomorphicOneForm_montel` — Montel's theorem for holomorphic 1-forms on compact Riemann surface. High-risk gap-narrowing on the Riemann-Roch / FD chain.
- **848a0c88-6c27-423d-865b-38b35390b7a0** (submitted): `Jacobian/HolomorphicForms/SectionTopologyConstructionRecon.lean` — NEW recon file: how to construct the Banach data on `ContMDiffSection` for compact X. Companion to `holomorphicOneForm_normedSpace_uniformOnCompact` obligation.
- **90750074-0d26-4f60-b32e-a79942e56111** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOP-DOWN refinement on `holomorphicOneForm_onePointCx_subsingleton` — the Liouville core of genus-zero classification (no global holomorphic 1-form on ℂℙ¹). Anti-hack #1 critical path.
- **dc8af381-8277-44ab-95f4-6e62dba5faee** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — Discharge `exists_compact_periodFundamentalDomain` using the existing `IsZLattice ℝ` instance + Mathlib ZSpan API. Reduction 3→2 sorries in this file.
- **6992e390-050b-49fb-bb21-5fde3ccb0449** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — TOPDOWN reduction: discharge `holomorphicOneForm_locallyCompact_of_compactRiemannSurface` sorry-free using `holomorphicOneForm_montel B` (still-sorry but named) — translation invariance on a normed space. Reduction 3→2 sorries in CompactRiemannSurface.lean.
- **d493c66b-a666-4b4d-a245-67db26ff4346** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOP-DOWN refinement on `holomorphicOneForm_onePointCx_toFun_eq_zero` — chart-coefficient extraction sorry exposed by 90750074. The Liouville analytic content is now discharged; this is the chart-pullback API gap.
- **63158306-c2f9-4f3e-a2e9-1b385e59fe48** (submitted): `Jacobian/HolomorphicForms/SectionFiberNorm.lean` — NEW file: Step 1 of `848a0c88` Banach-data construction recon — define `ContMDiffSection.fiberNorm` and prove its continuity. Building block for the eventual `holomorphicOneForm_normedSpace_uniformOnCompact` discharge.
- **1f7d4399-438b-4d8a-b128-dc290bde3a48** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOPDOWN on the now-narrower finite leaf `holomorphicOneForm_onePointCx_toFun_finite_eq_zero` (Liouville application via identity-chart pullback + EntireZero black-box).
- **f1786fa8-bbaa-4cdd-9683-b9dfbdf01797** (submitted): `Jacobian/HolomorphicForms/SectionSupNorm.lean` — NEW file: Step 2 of `848a0c88` Banach-data construction recon — define `ContMDiffSection.supNorm` and prove 5 sup-norm properties (zero, eq_zero_iff, add_le, smul_le, neg). 40-60 LOC per recon §5 Step 2.
- **51fd0fce-fb19-45e7-9ef1-efbf65de7ac9** (submitted): `Jacobian/HolomorphicForms/SectionMetric.lean` — NEW file: Step 3 of `848a0c88` Banach-data construction recon — define `ContMDiffSection.dist` and prove 4 MetricSpace axioms + dist_eq. ~20-50 LOC per recon §5 Step 3.
- **8585f085-371e-4c86-b276-adadf70f6392** (submitted): `Jacobian/HolomorphicForms/SectionComplete.lean` — NEW file: Step 4 of `848a0c88` Banach-data construction recon — completeness via embedding HolomorphicOneForm ℂ X into C(X, ℂ) + closedness. Hardest step, 80-150 LOC.
- **7e2bc288-bedc-4149-b0d8-28bcadf78ade** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — TOPDOWN refinement of 3 sorries (analyticPullback_contMDiff/_id_apply/_comp_apply). Acceptable outcomes: full proofs, companion-spec split, or survey docstring.
- **4d56b249-931f-46e3-8ace-50d28a74ac78** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — TOPDOWN refinement of 3 sorries (analyticPushforward_contMDiff/_id_apply/_comp_apply). Mirror of PullbackBasis packet 7e2bc288.
- **bbe527bb-28a6-4d6e-a32a-cf5f8d8df6e3** (submitted): `Jacobian/TraceDegree/AnalyticDegree.lean` — Discharge analyticPushforward_analyticPullback (anti-hack #4) via the recommended companion opaque _spec from prior survey 10e5bfbb.
- **d1d10391-67c2-4bfc-ad21-5514a1052a55** (submitted): `Jacobian/ComplexTorus/ULiftTransport.lean` — Discharge 2 sorries (complexTorusULift_contMDiff_up/_down). Both should be straightforward via the transported chart structure (chart-target map is identity).
- **d967438b-5455-49c9-a8ab-08bf2e0482e8** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — TOPDOWN of 3 sorries: pathIntegralFunctional_self, analyticOfCurve_contMDiff, pathIntegralFunctional_separates_points (Abel's theorem).
- **c5101910-f51a-4aab-8abf-d801b239642a** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — TOPDOWN of 2 sorries: periodSubgroup_isZLattice (integrality), periodSubgroup_spans_real (Riemann bilinear nondegeneracy).
- **c7feba63-8103-4859-846f-053274534d9d** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — TOPDOWN refinement of holomorphicOneForm_montel (only — _normedSpace handled by 8585f085 chain).
- **b3280ab0-41c9-46fd-82be-4eb17e7c0748** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — TOPDOWN refinement of 4 sorries: 2 Liouville-core leaves (chart-extraction blocker) + 2 uniformization items.
- **d8fd495f-b92d-4c09-898b-ce7614ecfaa7** (submitted): `Jacobian/ComplexTorus/ULiftTransport.lean` — Single-sorry packet on complexTorusULift_contMDiff_up only.
- **b4029f72-c3d9-4629-a961-e5ade014ea84** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on analyticPullback_id_apply only.
- **c910ac80-7262-443d-88c1-bb55817ac27e** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on analyticPullback_contMDiff only.
- **2bd5f151-4bab-4023-ae9e-dc614099864a** (submitted): `Jacobian/ComplexTorus/ULiftTransport.lean` — Single-sorry packet on complexTorusULift_contMDiff_down only.
- **27c56154-66ff-4c22-a86b-e112054f19de** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on analyticPullback_comp_apply only.
- **f280ecc6-c477-48f1-9128-3d8b7eeb0012** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Single-sorry packet on analyticPushforward_contMDiff only.
- **271cc21e-7540-4a49-978e-a51cad18978c** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Single-sorry packet on analyticPushforward_id_apply only.
- **6c796045-b207-4290-9d5c-5b02499ca57e** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Single-sorry packet on analyticPushforward_comp_apply only.
- **3d5f379e-568b-4e13-8f51-c9529fdc1f36** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Single-sorry packet on pathIntegralFunctional_self only.
- **c6c4c612-3d0a-4b8f-a792-9ee8ff6eb80f** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Single-sorry packet on analyticOfCurve_contMDiff only.
- **4f76ac75-4b03-44bf-9c4d-e473bcbb86b8** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Single-sorry packet on pathIntegralFunctional_separates_points (Abel's theorem).
- **99825c13-b58a-420b-b25c-ff202a2a5e70** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on the new analyticPullback_comp_spec (Claude's split target).
- **2aab5e91-890a-447f-9729-f4872a50e23e** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — Single-sorry packet on the improved analyticPullback_id_spec (= ContinuousAddMonoidHom.id _).
- **a3b5ae84-236d-4b40-a64a-259b3f8a7752** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Replacement packet on the new pathIntegralFunctional_self_spec.
- **777f976c-0e8e-4078-a345-68f015c9d7aa** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Replacement packet on the new analyticPushforward_contMDiff_spec.
- **3264c622-6675-4b18-94f3-9ec50f130185** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Replacement packet on analyticOfCurve_contMDiff_spec.
- **7f273ec8-537c-4bc9-a159-3098725b12f7** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — Replacement packet on pathIntegralFunctional_separates_points_spec (Abel's theorem deep content).
- **09a7e39c-5748-4c12-a2a0-55b2039d52c7** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Replacement packet on analyticPushforward_id_spec.
- **90fc4a81-0f3c-4a7f-a09a-34f8e16b532b** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — Replacement packet on analyticPushforward_comp_spec.
- **f914a263-801f-4dbc-8671-bc6d67a763bf** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — contMDiff_continuousAddMonoidHom_complexTorus general lemma.
- **c69fcd88-2cb2-4710-bef0-200e1a2cd351** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — analyticPullback_id_spec respecting basisDualPullback structure.
- **369f3f7b-4879-4ef1-9994-d46784537914** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — analyticPullback_contMDiff via complex-torus smoothness lemma.
- **16277f52-39bc-4f28-9860-8d771687c3ad** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — quotientMk_contMDiff_spec via charted-space machinery.
- **65001239-6493-4b88-8f4d-e21c6373addd** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — analyticPushforward_id_eq deeper split.
- **654d5071-ee04-446c-a69e-0d584517149e** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — pathIntegralFunctional_contMDiff_spec gap analysis.
- **7f3ec297-cad6-409f-bc0d-f4c0dc196fd2** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — analyticPullback_mk_eq + basisDualPullback_comp paired packet.
- **e3dcd529-c13e-4409-8236-3c4fd5474c11** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — analyticPushforward_mk_spec descent compatibility.
- **0a5f74a8-0259-4d37-b6f3-1690c29cac19** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — PeriodFunctional sorry (long-blocked).
- **03715a4d-0570-47fe-b3a7-bae31ecca811** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — GenusZeroClassification sorry (long-blocked).
- **05100f76-7d7d-4798-bb7c-c35c7ee7cabb** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_id (NEW from local _id_spec split).
- **b7799fc9-ad77-40de-9b32-42f2d735ac82** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id (NEW from local _id_eq split).
- **6b2f47f1-c0fe-4313-a950-57525866b53e** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — pathIntegralFunctional_separates_points_spec (Abel anti-hack #2) — orphan packet.
- **403c9581-217e-4df5-a9b7-656409a0d9dd** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (after Claude's bundle refactor closed _mk_eq).
- **5f052643-eee1-47d4-bce2-a3717c488d8d** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp_spec — orphan packet (covariant trace-lift composition).
- **e19361c4-97c0-44bb-a8e4-1036aadfee16** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — GenusZeroClassification sorry (Aristotle's pick, not chart-blocked).
- **bbca4cae-6ca6-4d1a-90b6-6bab64f6b71e** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — Second PeriodFunctional sorry (whichever 0a5f74a8 didn't pick).
- **58eb31f0-9b8c-411d-9087-0ff130a58ec8** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — Step 5: holomorphicOneForm_normedSpace_uniformOnCompact assembly (after 8585f085 lands).
- **360a05bf-5522-4d96-8e44-fb68e19ad707** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — Specifically L320: analyticGenus ℂ X = analyticGenus ℂ (OnePoint ℂ).
- **fbfe1498-210b-4931-a093-788d14de2cb0** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — Specifically L591: Nonempty (X ≃ₜ Metric.sphere ...) sphere homeomorphism.
- **e7250841-96e4-4d65-9be5-81dcaf1ae393** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_montel_subseq_tendsto (NEW from Montel TOPDOWN split): analytic core — Cauchy estimates + Arzelà–Ascoli + Weierstrass.
- **ba57741f-3fef-4160-b252-1af4ea559094** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id_apply_at (NEW from subagent TOPDOWN split).
- **dc58e548-c453-4335-a57c-e739df284174** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp_spec_apply_at (NEW from subagent TOPDOWN split).
- **de8822fb-8ae9-4c26-a026-213c17802e28** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_fiberNorm_continuous (NEW from 58eb31f0 split).
- **bed365ae-8a56-49fd-a9c8-432d36d0e7de** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_supNorm_completeSpace (NEW from 58eb31f0 split).
- **20995679-1911-4bcf-b0e9-12b6b6bc29a3** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_montel_subseq_isCauchy (NEW from Montel TOPDOWN split).
- **8a8ea66d-a01e-4317-a3ea-0ce135ae485c** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_closedBall_totallyBounded (NEW from 20995679 split).
- **706bf2e2-1e99-48ee-8926-1eb995019743** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_supNorm_cauchySeq_tendsto (NEW from a8db8a8f split).
- **76c01cf9-02c3-4a37-9a60-f983a96bdf3e** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_onePointCx_toFun_finite_eq_zero (Liouville finite leaf — 1:1 coverage).
- **c2a57d71-73b5-4669-8892-78e24ec878cb** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_onePointCx_toFun_infty_eq_zero (Liouville infty leaf — 1:1 coverage).
- **88effa1c-9abb-4391-99d2-a277c7e05c39** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneFormLinearEquivOfHomeoSphere (uniformization-lite — 1:1 coverage).
- **0cfa1878-064e-49dd-9d39-acba1d18adfc** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — periodVectors_linearIndependent (Riemann bilinear — 1:1 coverage).
- **ad278fcd-6c7c-476a-ba06-b5fb15989e6b** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (replacement for rejected 403c9581 — 1:1 coverage).
- **9b4998a5-7fd1-468e-91d5-ae2861eec0f6** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id_apply_at (renewed attempt after ba57741f docstring integration).
- **3b7e5dac-a8b0-4863-be44-462d2f09c961** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp_spec_apply_at (renewed attempt after dc58e548 docstring integration).
- **dc2c19e1-76ba-4fab-ba91-3a996a15add6** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_entire (NEW from 76c01cf9 split).
- **659de1fb-a95c-4d0d-8cd9-99925f04f931** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_tendsto_zero (NEW from 76c01cf9 split).
- **af6e2c7a-1412-4823-96fb-eade7b78c3ca** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — subsingleton_holomorphicOneForm_of_homeo_sphere (NEW from 88effa1c split).
- **e227f244-521b-4105-9744-25d6d25338f3** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — symplectic_basis_of_cycles (NEW from 0cfa1878 split).
- **0de5af2a-87b1-4fff-8721-c2e5136654d6** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — period_vectors_linearIndependent_of_symplectic (NEW from 0cfa1878 split).
- **a0bddfd5-c8f6-476a-ae89-47571f269525** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (renewed after ad278fcd docstring integration).
- **921772f5-cea4-429c-a2c9-3d7bd55f13b6** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — h1_basis_of_compact_riemann_surface (NEW from e227f244 split).
- **4d0d28d6-6d52-4e7e-b1ab-16afe7cf0180** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisDualPullback_comp (renewed after a0bddfd5 no-op).
- **3683ef39-f83c-41e3-98ed-a1ed2dd6f2cd** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_id_apply_at (renewed after 9b4998a5 deferred).
- **362e259f-b8cf-4522-a55f-de60211c801d** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — pushforwardTraceLift_comp (NEW from af653549 split).
- **9c222f2d-2be3-499f-a8a6-9fe263bec7f4** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — period_vectors_linearIndependent_of_symplectic (renewed after 0de5af2a stale).
- **6f6f015d-7c0d-4cba-9182-07300e8c9be8** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — basisAnalyticPushforwardBundle_id_traceLift (NEW from a8778c20 bundle-primitive split).
- **f3a8e713-ba50-4ec6-b31b-ca49dd3e9460** (submitted): `Jacobian/TraceDegree/PushforwardBasis.lean` — basisAnalyticPushforwardBundle_comp_traceLift (NEW from a1ce4200 bundle-primitive split).
- **6547fde4-4483-430f-b567-5cb1f81b0c18** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisAnalyticPullbackBundle_id_dualPullback (NEW from PullbackBasis bundle-primitive split).
- **86bef3e0-0fa0-40b4-83ce-700cc19b847e** (submitted): `Jacobian/TraceDegree/PullbackBasis.lean` — basisAnalyticPullbackBundle_comp_dualPullback (NEW from PullbackBasis bundle-primitive split).
- **632f36aa-6152-40dd-ad86-582d47e6b2db** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_fiberNorm_continuous — fresh packet for previously uncovered sorry.
- **fc057985-4072-43e4-b4a1-668153917ba7** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_supNorm_cauchySeq_tendsto — fresh packet for previously uncovered sorry.
- **6751b37c-9af7-4757-a5cc-9602ff3603d9** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — holomorphicOneForm_closedBall_totallyBounded — fresh packet for previously uncovered sorry.
- **2a5eea2c-0ce6-4316-b857-a77068d82713** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_entire — fresh packet for previously uncovered sorry.
- **47166a51-62ae-40a6-a4a1-5086a7a4614e** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_coeff_tendsto_zero — fresh packet for previously uncovered sorry.
- **50ed9388-fdd1-4456-9c83-387c8f83ab3d** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — holomorphicOneForm_onePointCx_toFun_infty_eq_zero — Liouville-infty leaf, fresh packet.
- **edca80d7-307a-490a-a343-fa6e4c4b92f7** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — subsingleton_holomorphicOneForm_of_homeo_sphere — uniformization-lite, fresh packet.
- **4f698084-46b4-4a5d-970f-368a0225c3f4** (submitted): `Jacobian/HolomorphicForms/GenusZeroClassification.lean` — genus_zero_homeomorph_onePointCx — uniformization core. Codex also racing this in worktree.
- **303edecd-6419-49e5-8994-0200b5f66fe7** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — periodSubgroup_isZLattice — discreteness of basis-aligned period subgroup. TOPDOWN plan in docstring.
- **263e138e-1e3c-4281-80e3-66618f709eae** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — h1_free_of_compact_surface — fresh packet for previously uncovered sorry (NEW from 921772f5 split).
- **c17e5dd9-80d5-4312-b8f0-673890bdc881** (submitted): `Jacobian/Periods/PeriodFunctional.lean` — analyticGenus_eq_topologicalGenus — submitted on cap-recovery.
- **7ceff781-61d0-4e33-8ce4-7edbac690bb3** (submitted): `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` — pathIntegralFunctional_separates_points_spec — submitted on cap-recovery.
- **56e6ac87-4c37-4c7a-b5b5-8d3ef369b0d6** (submitted): `Jacobian/Blueprint/Sec05/RiemannHurwitzDeg1.lean` — 2 sorries — placeholder-refinement framing: refine local SurfaceMap to bundle ramification_satisfies_riemann_hurwitz invariant.
- **db7d56a1-84a9-4ad1-82ad-7ae2fa13a102** (submitted): `Jacobian/StageA/EdgeWordTietze.lean` — 1 sorry (handleSwap_grouping_inductive_step). Refine local handleSwap_strictly_decreases_mu (True := trivial placeholder) into real content.
- **31175f0a-6e6a-4b9a-9e1a-5b1287c8d9e2** (submitted): `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` — ID 4: singular simplex integration
- **c2cf69e5-b4a5-44b6-972a-8db7a66cebce** (submitted): `Jacobian/Periods/Polygon4gCellular.lean` — prove polygon4g_succ_hurewicz_iso_freeZ
- **421a90df-fb9a-46d0-82e3-25d40c3b418a** (submitted): `Jacobian/TraceDegree/PiecewiseC1Instance.lean` — prove instPiecewiseC1PathRegularity
- **0006f3e9-5842-40e9-b8fd-e77d39667a57** (submitted): `Jacobian/TraceDegree/TraceDefinition.lean` — prove localInverseAt_holomorphic
- **7bd649ad-2b68-43fb-9cc7-a119925825e9** (submitted): `Jacobian/TraceDegree/TraceDefinition.lean` — prove localTraceAtRegularValue_holomorphic
- **b4654c4b-01ec-4fe7-bbcf-9c976473ea72** (submitted): `Jacobian/TraceDegree/TraceDefinition.lean` — prove trace_pullback_at_regular_value
- **0050e6c0-3326-4d75-9c21-58f79bdccfce** (submitted): `Jacobian/Blueprint/Sec02/MontelCompactness.lean` — prove montel_pointwise_extraction
- **1259f3fa-872c-4ae5-8c0a-634e23cac4d9** (submitted): `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` — prove chartLift_contDiffOn_assumption
- **3fec87fa-3619-4acc-87d5-a82ae74293e5** (submitted): `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` — prove chartedFormPullback_continuous_assumption
- **1b11a60f-19e5-455d-beb7-a5baadc0ac3c** (submitted): `Jacobian/HolomorphicForms/CMfldBumpStub.lean` — prove cMfldBump_apply_self
- **da91941b-89cc-46b4-86a9-156dcc2d8624** (submitted): `Jacobian/HolomorphicForms/CMfldBumpStub.lean` — prove cMfldBump_eq_one_near
- **1a50bfc4-e90d-4c9d-8891-3e0994b48b7e** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — prove holomorphicOneForm_arzela_ascoli_refine23
- **eb62762d-9750-4cf4-a8cd-1d2a6c361dd6** (submitted): `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` — prove holomorphicOneForm_supNorm_cauchySeq_tendsto_via_steps
- **d0717941-5047-454b-8fd5-68382a67e40d** (submitted): `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` — prove closedForm_pathIntegral_primitive_exists

## Layer status

- **Complex torus layer: complete (sorry-free).**
- **Queue C foundation in place.**
- **Queue D scaffolding (1 opaque, no sorries):** 11 files +
  umbrella; growing.
- **Queue E foundation:** `AnalyticJacobianGroup E X` + umbrella.
- **Queue F:** Recon document.
- **Queue G:** Recon document (`Jacobian/TraceDegree/Recon.lean`)
  inventories `mfderiv`/`ContMDiff` (PRESENT) vs `pullbackForms`/
  `traceForms`/`analyticDegree` (ABSENT); lays out chain-rule for
  pullback, fiber-sum for trace, 6 packets, flags
  `pushforward_pullback` as the strongest multiplicative anti-hack
  theorem.
- All challenge queues (A through G) have at least a recon document
  or production scaffold; Queue H's theorems live in
  `Jacobian/Challenge.lean` directly.

### Queued for next submission round (gated on current batch)

- `pullbackFormsFun_smooth` — Queue G follow-up to `0b8b1163`:
  prove the chain-rule pullback function is `ContMDiff` when `f` is.
  The substantive piece for upgrading to `HolomorphicOneForm E X`.
- `pathIntegralViaChartCorrect` linearity (zero/neg/add) — gated on
  `ee3ce016` + `fe592ee1`.
- Multi-chart `pathIntegralViaCover` definition combining
  `exists_uniform_chart_partition` (from `PathPartition`) with
  chart-local integrals. Needs Claude-owned design step first
  (subpath / affine reparam), then a clean Aristotle packet for
  the well-definedness lemmas.
- Decomposed TorusExample replacement (split into "constant
  function `_ ↦ id` is `ContMDiff`" as a standalone helper, then
  build the section on top), retrying `259b18a1`'s scope.

## Top open correctness item

`chartedForm c ω e v` should equal
`ω.toFun (c.symm e) (D(c.symm)_e v)`, but the current definition
drops the chart-derivative `D(c.symm)_e` and only evaluates the
section at `c.symm e`. Lean accepts the type only because
`TangentSpace I _ = E` trivially. Consequence: `pathIntegralInChart`
is the right integral only when chart transitions are translations
(torus case); it is wrong on a general Riemann surface. Flagged in
the `ChartedForm.lean` docstring and tracked here as the highest-
priority correctness fix. The proper version uses
`mfderiv 𝓘(ℂ, E) (chartedSpaceSelf ...) c.symm e` (or the
inverse-chart partial derivative API).
- Deferred (per the user's explicit guidance and the
  reviewer-acknowledged staging-phase tradeoff): file granularity
  consolidation, naming-convention alignment, and the
  `FullComplexLattice → Submodule + IsZLattice` design change. These
  belong to the eventual Mathlib-prep cleanup, not this phase.

## Planned packets (queued for Aristotle when queue unblocks)

The chart layer is complete; the next layer is `LieAddGroup` smoothness
of `+` and `-` on `quotient V Λ`. Decomposition into Aristotle-sized
packets below. Each packet targets one new file; allowed writes are
that file only; forbidden files always include `Jacobian/Challenge.lean`.

1. **`Jacobian/ComplexTorus/AddSmoothLocal.lean`** — `ContMDiffAt`
   of `(q1, q2) ↦ q1 + q2` at a single point. Strategy: at point
   `(q1, q2)` lift to representatives `v1, v2` via `Function.surjInv`,
   use the chart machinery (the same δ from
   `exists_pos_le_norm_of_discreteTopology` works for both factors),
   and observe that on a small ball the chart-coordinate addition is
   exactly the linear sum on `V × V → V`, then mk back. Re-uses
   `localSection_mk_locally_translate`-style reasoning; no new heavy
   API.

2. **`Jacobian/ComplexTorus/AddSmooth.lean`** — promote (1) to
   `ContMDiff (modelWithCornersSelf ℂ V).prod (modelWithCornersSelf ℂ V)
   (modelWithCornersSelf ℂ V) ⊤ (fun p => p.1 + p.2)` and from there
   to a `ContMDiffAdd` instance.

3. **`Jacobian/ComplexTorus/NegSmoothLocal.lean`** — `ContMDiffAt` of
   `q ↦ -q`. Same lift+chart pattern; in chart coordinates negation
   is `x ↦ -x` on `V`, which is `ContDiff ℂ ω`.

4. **`Jacobian/ComplexTorus/NegSmooth.lean`** — promote (3) to
   `ContMDiff` everywhere.

5. **`Jacobian/ComplexTorus/LieAddGroup.lean`** — combine the
   `ContMDiffAdd` instance from (2) and the `contMDiff_neg` from (4)
   into a `LieAddGroup (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
   (quotient V Λ)` instance. One- or two-line `where`-clause once the
   pieces are in place.

When the queue unblocks, submit (1) and (3) in parallel (disjoint
write scopes), then (2) and (4), then (5). All five fit the
"prefer simple tactics" guideline.

## General Job Template

```text
Working directory: C:\ver\JacobianChallenge
Target file: <one Lean file>
Allowed writes: only <target file>
Do not edit: Jacobian/Challenge.lean
Task: prove or implement the named declarations below.
Expected verification: lake build <module name>
If blocked: leave the theorem statement unchanged and add a short comment naming
the missing prerequisite.
```

## Queue A: Inventory

Source namespace:

```lean
JacobianChallenge.Inventory
```

Useful declarations:

- `MathlibInventory`
- `inventoryComplete`

Expected output:

- a factual inventory of existing Mathlib declarations at the pinned commit;
- exact file paths and declaration names;
- a list of missing infrastructure.

## Queue B: Complex Tori

Source namespace:

```lean
JacobianChallenge.ComplexTorus
```

Useful declarations:

- `FullComplexLattice`
- `quotient`
- `mk`
- `mk_surjective`
- `map`
- `map_mk`
- `map_id`
- `map_comp`
- `quotientChartedSpaceStatement`
- `quotientIsManifoldStatement`
- `quotientLieAddGroupStatement`

Good first Aristotle packets:

- prove quotient-map universal property lemmas;
- prove `map_mk`, `map_id`, and `map_comp`;
- replace placeholder lattice fields with existing Mathlib predicates if found;
- isolate the exact quotient-manifold theorem needed.

## Queue C: Holomorphic Forms and Genus

Source namespace:

```lean
JacobianChallenge.HolomorphicForms
```

Useful declarations:

- `HolomorphicOneForm`
- `FiniteDimensionalHolomorphicOneForms`
- `analyticGenus`
- `genus_eq_analyticGenus`
- `analyticGenus_eq_zero_iff_homeomorphic_sphere`

Expected packets:

- define holomorphic 1-forms using existing differential-form API;
- prove vector-space structure;
- state finite-dimensionality as a named theorem;
- connect analytic genus to the challenge `genus`.

## Queue D: Periods

Source namespace:

```lean
JacobianChallenge.Periods
```

Useful declarations:

- `IntegralOneCycle`
- `HolomorphicOneFormDual`
- `periodFunctional`
- `periodSubgroup`
- `periodSubgroup_isClosed`
- `periodFullComplexLattice`
- `period_homology_invariance_statement`
- `period_pairing_full_rank_statement`

Expected packets:

- define path/cycle integration;
- prove homology invariance of periods;
- prove period subgroup is closed;
- prove the full-lattice theorem.

## Queue E: Analytic Jacobian

Source namespace:

```lean
JacobianChallenge.AnalyticJacobian
```

Useful declarations:

- `AnalyticJacobian`
- `analyticJacobianEquivChallenge`
- `analyticJacobian_homeomorph_challenge`

Expected packets:

- define Jacobian from the period lattice;
- bridge to the public challenge type;
- handle universe issues deliberately.

## Queue F: Abel-Jacobi

Source namespace:

```lean
JacobianChallenge.AbelJacobi
```

Useful declarations:

- `pathIntegralFunctional`
- `analyticOfCurve`
- `analyticOfCurve_path_independent`
- `analyticOfCurve_self`
- `analyticOfCurve_contMDiff`
- `analyticOfCurve_injective`
- `challenge_ofCurve_eq_analytic`

Expected packets:

- prove path independence modulo periods;
- prove basepoint maps to zero;
- prove holomorphicity;
- prove injectivity for positive genus.

## Queue G: Trace, Degree, Pushforward, Pullback

Source namespace:

```lean
JacobianChallenge.TraceDegree
```

Useful declarations:

- `pullbackForms`
- `traceForms`
- `analyticDegree`
- `trace_pullback_forms`
- `degree_eq_analyticDegree`
- `pullbackForms_preserves_periods`
- `traceForms_preserves_periods`
- `analyticDegree_comp`
- `pushforward_pullback_from_trace`

Expected packets:

- define pullback of forms;
- define trace of forms;
- prove the trace-pullback identity;
- define degree compatibly;
- descend maps to Jacobians.

## Queue H: Anti-Hack Theorems

Source namespace:

```lean
JacobianChallenge.AntiHack
```

Useful declarations:

- `genus_zero_topological_sphere`
- `positive_genus_nontrivial_jacobian`

Expected packets:

- prove or trace dependencies for the anti-hack theorems;
- keep these theorems separate from convenience API;
- do not weaken their statements.
