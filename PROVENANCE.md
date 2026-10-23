# Provenance of the released files

For each file that comes from the runs, the table gives the SHA-256 hash of the version that ran (for the checker
files, the versions that produced the check logs; for the search programs, the versions recorded in the part
headers) and the hash of the released file. "AST identical up to docstrings" means that both files parse to the
same Python syntax tree once docstrings are removed; comments are not part of the tree. Files marked "new" were
written for the paper after the runs.

| file | SHA-256 of the version that ran | SHA-256 of this file | changes |
|---|---|---|---|
| checker/wcheck.py | 520e291eac2712c53ba3c8f8de7ad45b53c7121b37e9bc0b30bedf39899b9d2a | fb0d9a6992740243c56fc8cde9503f5708c76b62822d8f61275b37bb6e38a415 | docstrings and one comment edited (no internal note names; description of W corrected; model() marked unused); AST identical up to docstrings |
| checker/wcheck_v2.py | 9374fec55c2ebdf50193ade9c31c3e2608e6ebe77f4ec6d38a36845ae95d7e8d | 27914a130c382ab903475b51a0a04d0d3f4ffca93b7f22841f64f5f3b980d615 | docstrings and one comment edited (no internal note names; description of W corrected; model() marked unused); AST identical up to docstrings |
| checker/wcheck_presence.py | 645b0e2656b94f056bd15c941af8823023103577596819e4567954ec8fdddfac | 645b0e2656b94f056bd15c941af8823023103577596819e4567954ec8fdddfac | identical |
| checker/wcheck_presence_v2.py | 9e7cbbd33799cd943f3042474ea4f449599bcbc18652be447c93c30020c9034e | 9e7cbbd33799cd943f3042474ea4f449599bcbc18652be447c93c30020c9034e | identical |
| checker/wcheck_selftest.py | 4cf1a9d4a443909e28aa52f6f20ca91612c611ddc9c565eea08ac272740ee206 | 4cf1a9d4a443909e28aa52f6f20ca91612c611ddc9c565eea08ac272740ee206 | identical |
| checker/negtest_leaf.py | - | 40a5a41603aebdc139795645be540e95d2d35f3cced7dbfa8441ccab4f7d3163 | new |
| checker/check_headers.py | - | 73dfe6f20c3dfc890f4c084dd9e7db3e42c01b6985cee8c1907504d6f6774270 | new |
| checker/negtest_winding.py | - | 4d14a7a658cf196dd9f56a0dbc6468d5adbe8c1223899cd9b259ea301bba2e27 | new |
| checker/testcert/part31010.json | 4223c8b4fa87fbbed18a48e513db5c0a4881e607d576a499974b47552cfb42b2 | 4223c8b4fa87fbbed18a48e513db5c0a4881e607d576a499974b47552cfb42b2 | identical |
| checker/testcert/part31010.leaves.jsonl.gz | 7b7a1bbf12b08bf171f48df734554ae037157c0e847dc03671d4186cf2812047 | 7b7a1bbf12b08bf171f48df734554ae037157c0e847dc03671d4186cf2812047 | identical |
| checker/testcert/part31010.npy | 70e874b75c17dc5635ac2c9864e80790b2b7e99f275b254ac0d912cfd586452f | 70e874b75c17dc5635ac2c9864e80790b2b7e99f275b254ac0d912cfd586452f | identical |
| checker/testcert/part49490.json | 8030afd0a9d5e831a02c5f1a4a70d2c4668b67398fc8778e8053b1f5f7a7cd67 | 8030afd0a9d5e831a02c5f1a4a70d2c4668b67398fc8778e8053b1f5f7a7cd67 | identical |
| checker/testcert/part49490.leaves.jsonl.gz | 0d2b351b244d31e3824dc7a3d1062ad8ab22be920ca926127c35715ac05b26c8 | 0d2b351b244d31e3824dc7a3d1062ad8ab22be920ca926127c35715ac05b26c8 | identical |
| checker/testcert/part49490.npy | f204a17322e91ede8430fc082bcaf5810188600a9f3cdedb74916f3c70d7a125 | f204a17322e91ede8430fc082bcaf5810188600a9f3cdedb74916f3c70d7a125 | identical |
| checker/testcert/part5613.json | 5ea561f36bb331d824550ea63f362a0cd632cf7d78ea80f6b70ca56b4911be6b | 5ea561f36bb331d824550ea63f362a0cd632cf7d78ea80f6b70ca56b4911be6b | identical |
| checker/testcert/part5613.leaves.jsonl.gz | 93a97794e0945afebfdebecfa20446898438bda946c9cb3117ebb696ca739044 | 93a97794e0945afebfdebecfa20446898438bda946c9cb3117ebb696ca739044 | identical |
| checker/testcert/part5613.npy | a30efe3553f1f03e42aa0828c345ceb305cae4b39ba350b7e1e6d7d1311365cc | a30efe3553f1f03e42aa0828c345ceb305cae4b39ba350b7e1e6d7d1311365cc | identical |
| checker/testcert/part62289.json | bc7649f1635e1fe0c23bb4885355e2a6cf684dc231648fc35b9a1a747f3a1c82 | bc7649f1635e1fe0c23bb4885355e2a6cf684dc231648fc35b9a1a747f3a1c82 | identical |
| checker/testcert/part62289.leaves.jsonl.gz | 8714c20a4004829d195c04567dade6e36b84a03e1605d5b37e190537cd729958 | 8714c20a4004829d195c04567dade6e36b84a03e1605d5b37e190537cd729958 | identical |
| checker/testcert/part62289.npy | 72541dae69908589d38a01a13d51140b75723bb1a41e1a855fbbb0ec46460bce | 72541dae69908589d38a01a13d51140b75723bb1a41e1a855fbbb0ec46460bce | identical |
| data/opt_point.json | - | a9364694ac8086d009b08e9cdd0c81d9339104841a8948712cd315d7747089ef | new |
| checker/logs/check_lines.jsonl.gz | - | c90303480b7712b22091c927eef8c3b8c312ad651fe0dc3572324c9fcd05cab3 | 19772 lines (deduplicated, sorted by part and leaf range) |
| checker/logs/SUMMARY.json | d8e36dd41c43f891e57077072c5c990e590ef77fc3f4918c35fa9c4873a70d23 | d8e36dd41c43f891e57077072c5c990e590ef77fc3f4918c35fa9c4873a70d23 | identical |
| search/run5b_f80e8996.py | f80e8996a81d0ca684b977c08e81b0773e5936d03bd562dbe36e62338cb4765c | f80e8996a81d0ca684b977c08e81b0773e5936d03bd562dbe36e62338cb4765c | identical |
| search/wsearch_b837e347.py | b837e3478c973c5a2bb6d656852296ecc4fb66e4ba079d8ea54b2925dada22e7 | 6817241c7dbaae148b314e33f2e60276c63246aa9e0b610b96892214ac6035c3 | 3 sys.path line(s) relative to the file; docstring edited (internal paths or note names replaced by neutral text) |
| search/wbnb_b4042d07.py | b4042d0741a67da1f82119725a87617e95d6155d883bbf5729871032803aeff7 | e42269195e41b361fa3addcdb1042917429a19c9cd6af94bad80c85d5d199a57 | 1 sys.path line(s) relative to the file |
| search/wchord_eec210b9.py | eec210b95a8dd1ae70b898882f37f912ffbbccdde6bb90f2e396a66676d7011a | fa5f179bc1db07ab45f18a174f21ed510849677b74571bef1ca02b6ad0a9ac69 | 2 sys.path line(s) relative to the file |
| search/lbsearch_94f78046.py | 94f78046e11dc75fcf7c300b771552f98bbd7a2daf8f912fc3345bbc383253aa | 7fe586a43a9d7916565f9b7fe24c6bacf01c78ac8b152ca211cf97dfe88ddb32 | docstring edited (internal paths or note names replaced by neutral text) |
| search/wtask_5acd5ac0.py | 5acd5ac00cb5eb762228f137b8434eab689eeef410288c6920ea36fc6206f270 | 5acd5ac00cb5eb762228f137b8434eab689eeef410288c6920ea36fc6206f270 | identical |
| search/wtask_ab6507da.py | ab6507daa644b2b3c7b1fd350bf3e5d82adc354ae9b218526d155911847589f5 | ab6507daa644b2b3c7b1fd350bf3e5d82adc354ae9b218526d155911847589f5 | identical |
| search/wtask_812be2a4.py | 812be2a409d03f0c05f06d27f28f95647d877dc17193c808369eeec9434a8fa1 | 812be2a409d03f0c05f06d27f28f95647d877dc17193c808369eeec9434a8fa1 | identical |
| search/worm_ff8e285a.py | ff8e285aec65e7a635dbf8fdde5a7649694e23065aa628b9cfbf12ab52fb9a68 | ff8e285aec65e7a635dbf8fdde5a7649694e23065aa628b9cfbf12ab52fb9a68 | identical |
| search/fammin_964be377.py | 964be3777fe7eea69a34f217895564dffbb30e0a820c5f152f5c4460b3168a91 | 964be3777fe7eea69a34f217895564dffbb30e0a820c5f152f5c4460b3168a91 | identical |
| search/wfam_17da1a7b.py | 17da1a7b596fafc06ffa36c050a50e7d991dffd7f9c32807b207e99691597352 | 17da1a7b596fafc06ffa36c050a50e7d991dffd7f9c32807b207e99691597352 | identical |
| search/assemble_195ccd91.py | 195ccd91cee3456b1994e029e2790ed791e77158095cfbe0531d27e80e92866c | 195ccd91cee3456b1994e029e2790ed791e77158095cfbe0531d27e80e92866c | identical |
| search/wfam_261fc37d.py | 261fc37dc158ee70d8de04f8ec417fdb859dc4c50f1513fcf4526a157fadca53 | 289c4818b4d8705291c92a2b638631e3a42eac4eb107fdeb660e9cadd4527a78 | one comment edited (no names) |
| search/fitscale_487e12fd.py | 487e12fdf911fbd19be640d014fbba895c99cc179138763f603d8f7a19dc9f48 | 487e12fdf911fbd19be640d014fbba895c99cc179138763f603d8f7a19dc9f48 | identical |

## Lean files (`lean/`)

`lean/` holds the 11,566 files of the Lean development that was built and checked, unchanged; the data of the formal proof (`lean/data/`) comes from the archives of the supplement record. Third-party files: see `lean/PROVENANCE.md`.

## Lean files of the proof of 0.241 (`lean_k/`)

`lean_k/` holds the 86 hand-written files of the proof that the Lean kernel checks alone; the generated modules are in the supplement record. The table lists every file that differs from the version that was built and checked. Comments, docstrings and documentation were edited to remove internal names, the lakefile lists only the shipped libraries, and `README.md` and the third-party files are new in this directory. Of the generated modules, only `WormKD/Final.lean` differs from the built version, in two docstrings; compiled against the built tree, it gives the same theorems with the same axioms. Third-party files: see `lean_k/PROVENANCE.md`.

| file | SHA-256 of the version that was built | SHA-256 of this file | changes |
|---|---|---|---|
| lean_k/PROVENANCE.md | - | 22eccb627eac70fb9f8bcb66332f7731c9b81c8a6d9caef69c967ea55d9adee6 | added (third-party files and their provenance) |
| lean_k/README.md | - | 1268ef3428a2de080dbac9eab4657b19c8546d35f87551a2b1eef01b079d4d91 | new |
| lean_k/WormCore/Check.lean | e678104d4650cd0ce2496cf4193d97339301d3bfc9fd714405a726e84575e857 | 7fb4d735d489cf04aa9ef66ce6c852e4d70f43d846a603ce760a20763b332a40 | comments and docstrings |
| lean_k/WormK/Fast.lean | 1402afc4e0d0738b67fc77b4988da6127f0b4125e0789bf4245dd909add3163b | 7739805d88f34ae7b75533ec5cd33e1e7e21a918ee205f65729718817b4f7dd7 | comments and docstrings |
| lean_k/WormK/Fast2.lean | aa5daefabe76662d2748ff184aa4aa4840d8d6bac9fb874a33bfdd28f897670c | 18182cae8175850aedb999830e7bfa61189eb44353890121d3b4a366e8926f3a | comments and docstrings |
| lean_k/WormK/Fast3.lean | 6e35d4e9b707f11bd0b850fd32de982638069170c49f1cd40fbf207b6f9705d6 | f994f20950888bbedd6e8e5cf131d67535184ead2ddc66810edee79a4d9db9d9 | comments and docstrings |
| lean_k/WormK/Fast4.lean | 10e61c6a647e4f01fb93a548ca542de3a673d2c3a1b6bf2e5b1383e3146f6ed4 | 9a53ed49f7119597d2492bc365c5809d767f415be527bca13df9c6d7a75fed83 | comments and docstrings |
| lean_k/WormK/Walk3.lean | 95c4903b137da3454b7251881acfbd8a5b42149ec854d10380bdb4efd172507a | d5d27d9e240b04453f2d78c44a9011af4b7c098d4ec7d1a3a95545e65ba2b2d9 | comments and docstrings |
| lean_k/WormK/Walk4.lean | 2a51513a59cfc317e58bc2601ee8b0f4d6a6c82622905178c80b3b4011b7326e | 978b06fb863fefe42f33b07cb251c4b985637bd3a2d4033b041250c7c5117ab6 | comments and docstrings |
| lean_k/WormKC/BridgeK.lean | 41c0cd3d78005bd57fc51774ccaba5c8c51c6f25b82e0e77fc3c22334103247d | f8b2b6b0864219b713910ee0e4b774cb8fb79a70c3703d027f45621ec9c44957 | comments and docstrings |
| lean_k/WormKC/Cov.lean | 68d5242c6ec1aa4a7ac24a1c0ea8e61d2fe5835c4e7c11b05baa929d8343d2b3 | 8595e188be5c7c598c2ad87be7bf2a399360bb71e8c594c8010b8862456fef6a | comments and docstrings |
| lean_k/WormKC/Pack.lean | cafe305c25ba78c8b2587d1cf62756f2f5f53442ac3331c7373abb9679f661cd | b4e6c31c274f138641a8bc9971d01efc52ebf4ce69d4ac10cd7577b018b55f91 | comments and docstrings |
| lean_k/WormKC/Walk.lean | 097bf0ff5017d270130fcad31b6913b10a60b360512c2db4da321266b24e3447 | 13e011d94ad20f8393861f3e5db790b95e93477730c28cc9821caa80b4ca9760 | comments and docstrings |
| lean_k/WormKProof/R4.lean | 723ea58d451becd6015d76d3634b6bb06adea77224547e454ba29308ac3fe266 | e95d6db6024451c5b8181831d7b6ebf2572dda6400ef9d1cddcf67dbe034515d | comments and docstrings |
| lean_k/WormKProof/R4Prims.lean | 46d371a9d783a034337a57d4ddbaf9b8a8b61d4b3967a38ad3938433af45d5ae | a96352b71fdaed40d33921c02a0d8dea7bd6b915bb4584135e9422a82772b57c | comments and docstrings |
| lean_k/WormKProof/Walk.lean | 2f71726bf23df948ac8dc0f5d091f24a9151e4663ee0a39454277532560bdda7 | 143971011b68ebc9c78a5f0731df6efc0577784f6644728d3e0dc301644e9c2c | comments and docstrings |
| lean_k/WormKTools/MergeOut.lean | 300efc9ad6a4530c8b4d0f4a243c71ce5e1bc8b58a6f3535323a6eb1f0c2ce77 | 6f827c605808de7b9b2f91e2af9aa7a56cc45cb56d41244d9f28bbba17012403 | comments and docstrings |
| lean_k/WormSound/FinalAt.lean | 5bec7413844e03e1842a0ad4b0e3146d2b435fc8b40de16822c36faa990971b6 | 24e8e7ab80f0f0b4a453b04e45c8ab12ee55994b9f688b7e7a231d742c489f15 | comments and docstrings |
| lean_k/lakefile.toml | c526545fd7cffa73c05742043e5a89060f451b7348a31b3d29b8b782a336fb66 | 97efeede10a9809ebf7b3676b642232555f8c22241922606c85c7c24953a9d78 | rewritten to list the libraries of the shipped modules, with the same options |
| lean_k/third_party/moser-worm-improved-bounds/CITATION.cff | - | 78d96646a050bdd70d732f920b534fe2ecf4de09148a85ad07456508b2c387a3 | added (third-party files and their provenance) |
| lean_k/third_party/moser-worm-improved-bounds/LICENSE | - | e74b5d16da388425ae5bd2bb9fa384749198717dd77b7c24bb394b49c959016c | added (third-party files and their provenance) |
| lean_k/third_party/moser-worm-improved-bounds/UPSTREAM_SHA256SUMS | - | a39e0376db051237e54e52c04539ce33a8317864755fa9be095485c5d86f968b | added (third-party files and their provenance) |
| lean_k/tools/StatementCheckK2410.lean | 39ffa7c8b8191509c1590003df671ee4b438e241a3d758b0b8c7e9a1ef85da60 | ca28d780ee4fcfb8013161b7769ca46806bcaecf23fd6f06b472938e143a33e3 | comments and docstrings |
| lean_k/tools/build_dag.py | 5bcf8a7c3ae9da72f5153d03dddd89a093feb4a3d29936805655caf38bb54f83 | 8322b072d5086d611503e6f13f5e1053f3bce60dbb891e4a61c95db6f6999fe6 | comments and docstrings |
| lean_k/tools/gen_kd4.py | e75283a131fb65bc95154fa820e1649ed6a48e1d3c8c50529f7520294501cc26 | d9cce45c93733e1c6f22e8732822d5a7d7e363beeae14fec70f5ee2eeceffd9b | comments and docstrings, including the two docstrings that it writes into `WormKD/Final.lean` |
| WormKD/Final.lean | cafb4f626e9b22f5eb4f7cc43d835070769d61c5b964aed300f605027433256b | e6d7e8a394b4bbb52143a9987d08fdb96595898363037052c96ec80cad702473 | regenerated; two docstrings differ |
