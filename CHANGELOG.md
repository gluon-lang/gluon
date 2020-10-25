<a name="v0.17.2"></a>
### v0.17.2 (2020-10-25)


#### Features

*   Allow the http module to be used without a tcp listener ([c45353d2](https://github.com/gluon-lang/gluon/commit/c45353d2ceb10d98dbeca7e7dce1f658b875eb3a))
*   Format seq expressions without seq ([5c0cec2d](https://github.com/gluon-lang/gluon/commit/5c0cec2d29a0580a8e171e040f13427b282c4c1f))
*   Compile block expressions as monadic sequences ([bce59737](https://github.com/gluon-lang/gluon/commit/bce5973719cdb24849671f5b11e980e5d9cefc31), closes [#884](https://github.com/gluon-lang/gluon/issues/884))
* **std:**
  *  add Option assertions to std.test ([28e5053f](https://github.com/gluon-lang/gluon/commit/28e5053f1e56f7304d8b94eead3174ccfa4077c6))
  *  add modulo functions to int and float ([92f188ab](https://github.com/gluon-lang/gluon/commit/92f188ab24b599d0d0ef004c996f5fbefbfe1786))

#### Bug Fixes

*   Recognize raw string literals without any `#` ([4d66fbb3](https://github.com/gluon-lang/gluon/commit/4d66fbb37f5acae81c28fe3af715b8d1c04a2ab5), closes [#885](https://github.com/gluon-lang/gluon/issues/885))
*   Prevent zero-argument functions from being created in Rust ([e91ea06d](https://github.com/gluon-lang/gluon/commit/e91ea06d447fea4f9e5699ada6f38e742526ebc7), closes [#873](https://github.com/gluon-lang/gluon/issues/873))
*   Give tuple fields a span ([2a1c2c71](https://github.com/gluon-lang/gluon/commit/2a1c2c711408372eed71812696776ee93fde3c0a))
*   xor_shift_new inconsistent description ([591b64b3](https://github.com/gluon-lang/gluon/commit/591b64b359d98948ca379fd2f17e8d34982d12b2))



<a name="v0.17.1"></a>
### v0.17.1 (2020-08-15)


#### Bug Fixes

*   Disable inlining until it can be made sound ([97b63c42](https://github.com/gluon-lang/gluon/commit/97b63c42717d5080dd4ccfe5f7df26479124ef0f))
*   Inline functions that are re-exports ([bcf87838](https://github.com/gluon-lang/gluon/commit/bcf878385c09291a4b9256688a6f76818039a888))

#### Features

* **opt:**
  *  Constant fold through simple matches ([360c9d0a](https://github.com/gluon-lang/gluon/commit/360c9d0a93ffc6b624821d925303fb0441407850))
  *  Inline functions with impure arguments ([669f959d](https://github.com/gluon-lang/gluon/commit/669f959d6b21c4d8792d6d13ce109166f1d212f1))



<a name="v0.17.0"></a>
## v0.17.0 (2020-08-10)


#### Bug Fixes

*   Keep type field arguments on the same line as the name ([b1e40d37](https://github.com/gluon-lang/gluon/commit/b1e40d37f33d9d9815206d6a52cde49f47d99e16))
* **std:**
  *  fix formatting for std.monad ([df87ac30](https://github.com/gluon-lang/gluon/commit/df87ac300caa0c5d61d91d34c03b481f5ca70466))
  *  fix imports for aforementioned utility functions ([da7d3f98](https://github.com/gluon-lang/gluon/commit/da7d3f98ce1ba47b5159f2a4a7119e6d7550dee9))

#### Performance

* **vm:**
  *  Remove unnecessary check when calling closures ([9b8075e3](https://github.com/gluon-lang/gluon/commit/9b8075e36af04cf6cc0ba4241f82ff90d3eb437c))
  *  Only check for stack overflow when entering a function ([a5a22968](https://github.com/gluon-lang/gluon/commit/a5a22968104d715254ad1be5b922f8f2c2addb92))

#### Features

*   Update salsa ([a60a444f](https://github.com/gluon-lang/gluon/commit/a60a444fcf912d9ac1b3b65630c4387fceaa7a9e))
*   Report multiple kindcheck errors in the same type ([00eb1167](https://github.com/gluon-lang/gluon/commit/00eb1167b2211467ca8dddde0ffd240017f5b708))
*   Record record fields as symbols ([b3b65c75](https://github.com/gluon-lang/gluon/commit/b3b65c757d09deb683429eaa5b20357c9e87e7f2))
*   Add function arguments to all symbol queries ([1f063f9e](https://github.com/gluon-lang/gluon/commit/1f063f9e29f2fe38af0f67e5db9ccc2ffbb025e5))
*   Recover on most tokenization errors ([18692100](https://github.com/gluon-lang/gluon/commit/186921004a01b398bec2ec7330a5e7475ff8a579))
* **completion:**
  *  Provide symbol information for enum definitions ([04a5b20c](https://github.com/gluon-lang/gluon/commit/04a5b20c0bf2ac182105180da0bf017d1c409f75))
  *  Return the kind of type fields ([5f8d9d6f](https://github.com/gluon-lang/gluon/commit/5f8d9d6f2dcc74ff6c38aef0f3946fe9b220063a))
* **parser:**  Recover on unterminated string literals ([b0422366](https://github.com/gluon-lang/gluon/commit/b0422366b81e4e56bd90e40a64b22e490f911735))
* **std:**
  *  add Kleisli composition operators ([a384e046](https://github.com/gluon-lang/gluon/commit/a384e04606c145be58a0d9cd79a899f5911e264d))
  *  add utility functions to Option and Result ([bed70513](https://github.com/gluon-lang/gluon/commit/bed705135d389927c1e961f0f9248b040d22810f))



<a name="v0.16.1"></a>
### v0.16.1 (2020-07-05)


#### Bug Fixes

*   Gracefully error on concurrently loaded cyclic modules ([e6f1aa95](https://github.com/gluon-lang/gluon/commit/e6f1aa9555684b049f44f412d6f606fceda6cd7b))



<a name="v0.16.0"></a>
## v0.16.0 (2020-07-04)


#### Features

*   Make tokio an optional dependency ([c3450a99](https://github.com/gluon-lang/gluon/commit/c3450a99656f2c6298d7b937d976ac5d0e96f6c2), closes [#843](https://github.com/gluon-lang/gluon/issues/843))
*   Update to codespan_reporting 0.9 ([a6f214ce](https://github.com/gluon-lang/gluon/commit/a6f214ce120c34f37d5b2169dba593f576f24265))

#### Bug Fixes

*   Handle errors when pushing a BTreeMap ([bd8ad34f](https://github.com/gluon-lang/gluon/commit/bd8ad34fbf294729442c0c8d0e8983903b59cbdf), closes [#847](https://github.com/gluon-lang/gluon/issues/847))
*   Convert rust tuples such that they can be used polymorphically ([6c4d5731](https://github.com/gluon-lang/gluon/commit/6c4d5731cefff867f468c2982eb55df6cf69aa8f), closes [#848](https://github.com/gluon-lang/gluon/issues/848))



<a name="v0.15.1"></a>
### v0.15.1 (2020-06-20)


#### Bug Fixes

*   Allow find_type etc to work without calling global ([6e469b9a](https://github.com/gluon-lang/gluon/commit/6e469b9a311d1bdb7b5e4fc62688fc7d4d08ceea))

#### Features

*   Make the query code compatible with the language server ([14e8f1de](https://github.com/gluon-lang/gluon/commit/14e8f1ded3f4e02d6b8ab9c50dbd29b35b534996))
*   Add Default for Root/OwnedExpr ([fedb7322](https://github.com/gluon-lang/gluon/commit/fedb732270eb24e544b047e19e5a7533028a2f5b))



<a name="v0.15.0"></a>
## v0.15.0 (2020-06-06)


#### Bug Fixes

*   Allow bitoperations to be deserialized ([ed36ed9c](https://github.com/gluon-lang/gluon/commit/ed36ed9ccc5e423fd872994ffb52edda97c8965d))

#### Performance

*   Strategically inline comment productions ([78e733e7](https://github.com/gluon-lang/gluon/commit/78e733e701abe71ee10048b3de3b550bed927f43))
*   Shrink the metadata stored in the AST ([842c1080](https://github.com/gluon-lang/gluon/commit/842c1080bb73a7509384064e07a671b2c0f11fb6))
*   Use T::Generics in AliasData ([4cb575fa](https://github.com/gluon-lang/gluon/commit/4cb575fac5356bbc9a018eb6779c209a3473d3b6))
*   Shrink the symbol type in the parser ([a8fc8f39](https://github.com/gluon-lang/gluon/commit/a8fc8f39556a2997e359288ec37dfd9bd0932d7d))

#### Features

*   Accept multiple lines on incomplete repl input ([47318399](https://github.com/gluon-lang/gluon/commit/473183995ad793e48eef7d5b3b56c5cf22c325f5), closes [#830](https://github.com/gluon-lang/gluon/issues/830))



<a name="v0.14.1"></a>
### v0.14.1 (2020-04-15)


#### Bug Fixes

*   Rework how hanging lambda/parens are handled ([732f09f3](https://github.com/gluon-lang/gluon/commit/732f09f3c4c866f8b1b1be231a39604b8e2128e8))
*   Accept filenames that start with `.`/`..` as modules ([01e450bb](https://github.com/gluon-lang/gluon/commit/01e450bbc2f0737ecc80fde112174f52585c3445))
*   Don't deadlock when collecting and cloning a thread concurrently ([5886f59f](https://github.com/gluon-lang/gluon/commit/5886f59ff68cbfe029fc6a1697784d2800f42b0a))
* **check:**  Reject programs which misspecifies the number of patterns ([248387d9](https://github.com/gluon-lang/gluon/commit/248387d9c8d8121ab0f25645f79f7a47aeedfb25), closes [#807](https://github.com/gluon-lang/gluon/issues/807))
* **doc:**  Correct the style.css path ([4e629ab5](https://github.com/gluon-lang/gluon/commit/4e629ab5afb923ec0e097935f02f42717a2b51d5))
* **format:**  Improve tuple multiline formatting ([5122fe38](https://github.com/gluon-lang/gluon/commit/5122fe38f4c1360c13bf2ff483b6a7d35f2e7d2d))

#### Features

*   Add AstClone to clone arena allocated ASTs ([3ee7bd28](https://github.com/gluon-lang/gluon/commit/3ee7bd28bdc7126f5f4401e6fbe3368da94aa921))
*   Compile modules in parallel using salsa-async ([e0ab1811](https://github.com/gluon-lang/gluon/commit/e0ab18115a99115e54294b7240bb5d0360d4043a))
*   Compile modules in parallel ([57fca165](https://github.com/gluon-lang/gluon/commit/57fca165df50ff61ba87fb81d34dc4087f7ebc60))
*   Add Function::call_any ([2c06104f](https://github.com/gluon-lang/gluon/commit/2c06104fe2454f6636d811e77384945b4744a4bf))
*   Export Array from the prelude ([16eb3456](https://github.com/gluon-lang/gluon/commit/16eb3456ca864b7f6c12d7145d15a1c07fb683dc))
*   Allow serde_json::Value to be marshalled to std.json.Value ([aabdec86](https://github.com/gluon-lang/gluon/commit/aabdec86f49bda922fa01c9c1c84f32fdf2e3011))
* **check:**
  *  Avoid propagating errors on lift_io! misuse ([3dbabe53](https://github.com/gluon-lang/gluon/commit/3dbabe5355aeb6b4f61dfa8bdae95b6593f5575c))
  *  Avoid generating more errors from a type that could not be imported ([752e2bce](https://github.com/gluon-lang/gluon/commit/752e2bce68f6ef7726f0cc92a5b0e194648eb743))

#### Performance

*   Avoid some unnecessary allocations ([089bae4c](https://github.com/gluon-lang/gluon/commit/089bae4c4578d36163ec9a84ee83bbfc6e41ab04))
*   Shrink the size of Pattern ([75fb8840](https://github.com/gluon-lang/gluon/commit/75fb8840001f3e4d17ada88077b111024d673cf9))
*   Avoid hashing symbols twice ([0cfb52c8](https://github.com/gluon-lang/gluon/commit/0cfb52c871e80272a087311f230c11a5ad218c39))
*   Allocate all temporaries into the same Vec ([af945c4a](https://github.com/gluon-lang/gluon/commit/af945c4ad177839aa881d88aefa199b0c9f79aac))
* **compiler:**  Hoist a remove_alias call out from match alternatives ([c13172e2](https://github.com/gluon-lang/gluon/commit/c13172e2c9ee1fabbf267d83101458af47231436))



<a name="v0.13.1"></a>
### v0.13.1 (2019-10-29)


#### Bug Fixes

*   Don't deadlock when collecting and cloning a thread concurrently ([d7368950](https://github.com/gluon-lang/gluon/commit/d7368950d9310f383cebcbaf841382181701da00))
* **doc:**  Correct the style.css path ([2cee5cff](https://github.com/gluon-lang/gluon/commit/2cee5cffab0c1df604a45e3272e92f69624e6b41))



<a name="v0.13.0"></a>
## v0.13.0 (2019-10-27)


#### Performance

*   Only do one hash lookup when creating a Symbol ([a709c712](https://github.com/gluon-lang/gluon/commit/a709c7120ff151d368128cf7c0a89d667c91015c))
*   Shrink Type's size to 48 bytes (from 64) ([178180f8](https://github.com/gluon-lang/gluon/commit/178180f8b4555c8ae831d428fc464cb0a4179455))
*   Avoid RefCell in Fixed* structurs (-1%) ([de32dbd6](https://github.com/gluon-lang/gluon/commit/de32dbd631beb0958c7c0fcb655807fda874a2a7))
*   Avoid recursion in implicits.rs ([89eb836a](https://github.com/gluon-lang/gluon/commit/89eb836afbd2e5d43324c141fad52b761816c754))
*   Only mark types with unbound generics as HAS_GENERICS ([3d835a8a](https://github.com/gluon-lang/gluon/commit/3d835a8adaf2b3c63ef31d512780c9b6de2be5d8))
*   Avoid computing the plain name in name_eq (-3%) ([a7ac9f80](https://github.com/gluon-lang/gluon/commit/a7ac9f800d7f1ad944d81140dfe6be99d59f7943))
* **check:**
  *  Use RefCell::get_mut when possible ([12441438](https://github.com/gluon-lang/gluon/commit/1244143838ed56fcc7d257ef6f9288d38754f60d))
  *  Remove redundant operations in union ([f3d4203a](https://github.com/gluon-lang/gluon/commit/f3d4203a44074467e40240afc2cbf5547403efcc))
  *  No need to lookup the type again before querying the level ([5e4efe37](https://github.com/gluon-lang/gluon/commit/5e4efe37386f4d937fa8afa8b8d06b4aed7c738e))
  *  Remove some branches in the occurs check¨ ([03e7c3b4](https://github.com/gluon-lang/gluon/commit/03e7c3b4b22e5abd53b2af64f09849ba0ca43b32))
  *  Only initialize the variable generator when it is necessary (-3%) ([793b6580](https://github.com/gluon-lang/gluon/commit/793b658082f71f016655f7f4f3e44432814116fa))
  *  Only do one lookup/insertion on the implicit definition map ([0ea13ff1](https://github.com/gluon-lang/gluon/commit/0ea13ff1923527bbc69a5fa44ce905fe2a4c593d))
  *  Narrow down the implicit parititioning further (-10%) ([a9c965b4](https://github.com/gluon-lang/gluon/commit/a9c965b418cbff642d5c8a0c9c3c7821b610eb12))
  *  Avoid looking through metadata when checking for an implicit type ([4a3662e9](https://github.com/gluon-lang/gluon/commit/4a3662e9e108b902ed61f17d9e2da204d29e54bf))
  *  Only add implicit fields if the binding is implicit ([da861eba](https://github.com/gluon-lang/gluon/commit/da861ebad00a6f336d7fc7cbc99bf8703cd4b567), breaks [#](https://github.com/gluon-lang/gluon/issues/))
* **optimize:**  Allocate core syntax directly into arenas ([723ec4d6](https://github.com/gluon-lang/gluon/commit/723ec4d6e2026865ac3cfca29253786dc6bbee49))
* **parser:**
  *  Shrink the Token type and remove it's need to Drop ([3016f251](https://github.com/gluon-lang/gluon/commit/3016f251b35f01da81ab8ea51e2ea8f62c1ac870))
  *  Simplify tokenization iterators ([c7061c7b](https://github.com/gluon-lang/gluon/commit/c7061c7bef60b3ab3367dd06399d3bf5b8deae84))
* **vm:**
  *  Add function inlining ([5093137a](https://github.com/gluon-lang/gluon/commit/5093137a42f2b9ad757f5b712ad9a1a192b22b5e))
  *  Eliminate redundant match expressions ([945fb83d](https://github.com/gluon-lang/gluon/commit/945fb83df71a2fdca4353aedf9ff1349aa53ea01))
  *  Implement inter-module dead code elimination ([ab1b1b80](https://github.com/gluon-lang/gluon/commit/ab1b1b806fa4a99f1955ff1a2896b81cdd7b016d))
  *  Avoid tracing global values unless we are in the root gc (-7%) ([48a5313e](https://github.com/gluon-lang/gluon/commit/48a5313ebea8751a3815d2664a1ab001b399a8cb))
  *  Avoid the bounds check when fetching instructions ([c2778e7f](https://github.com/gluon-lang/gluon/commit/c2778e7fda9f424d710e9ac96f0d10051766e6f1))
  *  Faster updates to the stack frame ([2b94a3af](https://github.com/gluon-lang/gluon/commit/2b94a3af600a8bea64478384535fe378ba74a08d))
  *  Cache the frame offset for the stack (-20%) ([0469cb2e](https://github.com/gluon-lang/gluon/commit/0469cb2ef5bad94c3d52b52fd8186aa424c035e5))
  *  Copy instead of clone unrooted gc values ([a0396f40](https://github.com/gluon-lang/gluon/commit/a0396f4039641ad228b3cce2b0bfa0f443742c57))

#### Breaking Changes

*   Replace Compiler with the ThreadExt trait ([c16132eb](https://github.com/gluon-lang/gluon/commit/c16132eb2c817926aba6a89b33f63b917bb71458), breaks [#](https://github.com/gluon-lang/gluon/issues/))
* **check:**  Only add implicit fields if the binding is implicit ([da861eba](https://github.com/gluon-lang/gluon/commit/da861ebad00a6f336d7fc7cbc99bf8703cd4b567), breaks [#](https://github.com/gluon-lang/gluon/issues/))

#### Bug Fixes

*   Don't leak implicit bindings into adjacent scopes ([5681ffc5](https://github.com/gluon-lang/gluon/commit/5681ffc5c611dfbad235256f053b11525b91542c), closes [#783](https://github.com/gluon-lang/gluon/issues/783))
*   ignore formatting in std.test due to a bug ([bdccee6f](https://github.com/gluon-lang/gluon/commit/bdccee6f53411d113b9bd8dd1e89cbb5dff9ace4))
*   rerefix formatting ([31166161](https://github.com/gluon-lang/gluon/commit/31166161c78e4f38dca50daa695c0af994d70bbe))
*   refix formatting ([fcb7f0bb](https://github.com/gluon-lang/gluon/commit/fcb7f0bb56343f314b3d126b5ebfa95f572f9ee0))
*   fix formatting and apply naming suggesions ([6bb0d87c](https://github.com/gluon-lang/gluon/commit/6bb0d87cabf329f0a2585efd0e8daec4eca2c3ca))
*   Make the behaviour consistent for `Show Char` ([0ff89870](https://github.com/gluon-lang/gluon/commit/0ff89870fe064c3b8c524e862f07a5faaa85dd14))
*   Avoid infinite loops/extremely slow optimization ([dc7ec72a](https://github.com/gluon-lang/gluon/commit/dc7ec72ab053de68533f794621ea756fe66c35b0))
*   Expand macros inside macros ([5a294330](https://github.com/gluon-lang/gluon/commit/5a2943300b9010acf3913c535c983f10af4c9ec7))
*   Invalidate text properly so rexpect tests work ([92e45081](https://github.com/gluon-lang/gluon/commit/92e4508172607ae99e3de5d75a3874832682c470))
*   Don't depend on ansi_term in windows to make windows 7 work ([58e2a8b9](https://github.com/gluon-lang/gluon/commit/58e2a8b940f89abcdaaf0e0beafcc9f6bf04cabf), closes [#777](https://github.com/gluon-lang/gluon/issues/777))
*   Add tests and fix the regression with clone_userdata ([df078725](https://github.com/gluon-lang/gluon/commit/df078725965297c2920403d5ffc1c230273058d5))
*   Ensure that threads are dropped when using child threads ([b9efb513](https://github.com/gluon-lang/gluon/commit/b9efb513527c0ce51eef648f69b48e2252929365))
* **check:**  Handle aliases better in `do` ([770e52ea](https://github.com/gluon-lang/gluon/commit/770e52ea202d9fe1648b36f90cb9bab64d09b906), closes [#766](https://github.com/gluon-lang/gluon/issues/766))
* **repl:**  make the REPL respect --no-std ([e7974706](https://github.com/gluon-lang/gluon/commit/e79747067ca6538581ee4c3d2fe6631a087db53d))
* **std:**  export missing assertions in std.test ([41f4fc52](https://github.com/gluon-lang/gluon/commit/41f4fc524c00243b71a1fce01a134a2a08ce145f))
* **vm:**
  *  Don't (rust) panic in string.split_at ([50f937b3](https://github.com/gluon-lang/gluon/commit/50f937b3598adc52f8ec5eec19f6701d38c2fd38), closes [#757](https://github.com/gluon-lang/gluon/issues/757))
  *  Accept trailing comma in record macros ([f35c0b96](https://github.com/gluon-lang/gluon/commit/f35c0b96c255d209daf3b9e33362af4c5e1cdb38), closes [#770](https://github.com/gluon-lang/gluon/issues/770))

#### Features

*   Use implicit Monoids in std.foldable ([295b8c3d](https://github.com/gluon-lang/gluon/commit/295b8c3dfc3db3e4d5bd17e5b14ed4fdf4eb0362))
*   Add a mutable string type to the ST monad ([9ec946b4](https://github.com/gluon-lang/gluon/commit/9ec946b418842c6ac136406230d96e102d86b7fe))
*   Allow attributes to be specified on fields inside types ([fb35db51](https://github.com/gluon-lang/gluon/commit/fb35db5153161d1ee393ae29bc9adfc1db553458))
*   Provide std.effect.io as a mirror of std.io ([66e49b37](https://github.com/gluon-lang/gluon/commit/66e49b37196db18c36909900c46ccdc69254a7b0))
*   Replace Compiler with the ThreadExt trait ([c16132eb](https://github.com/gluon-lang/gluon/commit/c16132eb2c817926aba6a89b33f63b917bb71458), breaks [#](https://github.com/gluon-lang/gluon/issues/))
*   Use salsa for incremental compilation ([7bc82532](https://github.com/gluon-lang/gluon/commit/7bc82532f5aa7f9787d385ce97f0a769594b8064))
*   Add history hints and bracket highlight to the REPL ([10ef8cdf](https://github.com/gluon-lang/gluon/commit/10ef8cdf39baa5ad0cc7dd6817e59b8ea04f028f))
*   Use line/column numbers in lambda names ([201fdfb9](https://github.com/gluon-lang/gluon/commit/201fdfb9ed132adfca8055abae84a9ea8f00dcf8))
* **codegen:**  Map Rust's struct enums to records in Gluon. ([afb682e5](https://github.com/gluon-lang/gluon/commit/afb682e55d6115748a9861ff3086c934fe74afcf))
* **repl:**  add --no-std option to gluon.exe ([f2c1819f](https://github.com/gluon-lang/gluon/commit/f2c1819f9fc5ba3cb8d5d005b5ae61c1c74af658))
* **std:**
  *  add ordering assertions ([3efac996](https://github.com/gluon-lang/gluon/commit/3efac9963deb031e78462d00e49d090ab911cbd4))
  *  add a few functions to std.test & std.effect.error ([58e00431](https://github.com/gluon-lang/gluon/commit/58e00431a815ebdd7dae94a4d58a0c621d22aafd))
* **vm:**  Make macro errors implement PartialEq, Eq, Hash and Clone ([039825ab](https://github.com/gluon-lang/gluon/commit/039825abebc4fcd445c08574bd3cc0dd6f97a69f))



<a name="v0.12.0"></a>
## v0.12.0 (2019-07-06)


#### Bug Fixes

*   Remove Userdata and Trace impls for RwLock and Mutex ([e90f02b5](https://github.com/gluon-lang/gluon/commit/e90f02b56afd40e00b6e9fba58dd5421cd91a6d2))
*   Add missing negate function from the prelude ([0091f475](https://github.com/gluon-lang/gluon/commit/0091f475355b2bc1562dc6e257826ff71e7faf7c))
*   Refer to registered types by their full name ([a2daace6](https://github.com/gluon-lang/gluon/commit/a2daace6e914157391b8453c97ddd675b86a7165), breaks [#](https://github.com/gluon-lang/gluon/issues/))
*   Handle newtypes with a public field ([d1fef968](https://github.com/gluon-lang/gluon/commit/d1fef9688a3c8d379df0837ee18a4ff8f79c91ae), closes [#713](https://github.com/gluon-lang/gluon/issues/713))
*   Don't ICE on unapplied, aliased constructors ([2a44a0db](https://github.com/gluon-lang/gluon/commit/2a44a0db2180ec4f25550a9672b0f24a1e45ab90))
* **check:**
  *  Propagate metadata through parens ([bd767c07](https://github.com/gluon-lang/gluon/commit/bd767c07cb0506943a26c22e8d1c46e97f6f4ed3))
  *  Bring nested implicit instances into scope ([ad82bde6](https://github.com/gluon-lang/gluon/commit/ad82bde69b886f44dafcb094d9b4ef7eb87daa17))
  *  Don't lose type information in catch-all ([d2a3fbf0](https://github.com/gluon-lang/gluon/commit/d2a3fbf0e86ab605d5944f6ed3d61cad037469dd), closes [#702](https://github.com/gluon-lang/gluon/issues/702), [#703](https://github.com/gluon-lang/gluon/issues/703), [#704](https://github.com/gluon-lang/gluon/issues/704), [#705](https://github.com/gluon-lang/gluon/issues/705))
* **codegen:**  Return exactly the same type on VmType derive on enum ([375d3e9a](https://github.com/gluon-lang/gluon/commit/375d3e9a84e9f61464652eab268bac7185011be4))
* **compiler:**  Don't panic when matching a tuple against an alias ([777bd310](https://github.com/gluon-lang/gluon/commit/777bd310c69793a1453bc335af9e5ee4cd500dac), closes [#749](https://github.com/gluon-lang/gluon/issues/749))
* **std:**
  *  cleaned up statet.glu exports ([5d8864f9](https://github.com/gluon-lang/gluon/commit/5d8864f99fc25c606816bab7584f55a71e755648))
  *  export wrap_monad from transformer.glu ([0e9d7bc4](https://github.com/gluon-lang/gluon/commit/0e9d7bc43845338e966eca5115378ddc46e0803e))
* **vm:**
  *  Check if a collection is needed when creating a child thread ([86e4b9f7](https://github.com/gluon-lang/gluon/commit/86e4b9f7b4485cd57e144ec5bd3b2961a5d92183))
  *  Automatically remove the elements added to pushed data ([8cd5152b](https://github.com/gluon-lang/gluon/commit/8cd5152b5e0fef90eb663c96c99e3cbb2cdbc03a), closes [#719](https://github.com/gluon-lang/gluon/issues/719))

#### Performance

*   Use NonNull for garbage collected pointers ([9c66eded](https://github.com/gluon-lang/gluon/commit/9c66eded918d495057d31ced0096cb07835bda7d))
*   Don't recurse into already visited records to find implicits ([b50061f5](https://github.com/gluon-lang/gluon/commit/b50061f509d53105b3ca886c9cdbf6e54f2677eb))
*   Avoid recursing into non-implicit types ([c35b29e6](https://github.com/gluon-lang/gluon/commit/c35b29e65ec4791fec7ac24d2d500adc4651c1aa))
*   Use SmallVec in Partition ([d8c549bf](https://github.com/gluon-lang/gluon/commit/d8c549bff709bbf398b1a456878f0cb60a16a14e))
*   Use a scoped collections over a persistent in implicit resolution ([d13097e2](https://github.com/gluon-lang/gluon/commit/d13097e2ad91f6774299cdc09be6876eb438ecbf))
*   Memoize implicit attribute lookups (-3%) ([254af75e](https://github.com/gluon-lang/gluon/commit/254af75e544056262613a84b9cdc7907af1838e4))
*   Speedup Symbol::module ([9566a377](https://github.com/gluon-lang/gluon/commit/9566a37740dd70730bf9db510e11693e780fe5ae))
*   Avoid creating function types unnecessarily ([170f4673](https://github.com/gluon-lang/gluon/commit/170f4673a225f1e50d6e4ea84d020c563e3f1fc8))
* **compiler:**
  *  Shrink the core::Expr type to 40 bytes (from 72) ([779d1b65](https://github.com/gluon-lang/gluon/commit/779d1b65fbe61e27df49ccc3a0dc22cf98bacb56))
  *  Copy elements directly into arena ([cd2dd366](https://github.com/gluon-lang/gluon/commit/cd2dd366a4dc6a12d4a2b57144ef271355d2f765))

#### Features

*   Add gc::Mutex ([d6e12460](https://github.com/gluon-lang/gluon/commit/d6e124605c115b709ecbda34c104d20e71d281bb))
*   Automatically unroot values stored in `Gc` allocated values ([6ebc398f](https://github.com/gluon-lang/gluon/commit/6ebc398ff5e0343076b64b319c07eeb0c5ad8294), closes [#746](https://github.com/gluon-lang/gluon/issues/746))
*   Add derive for Traverseable ([844418df](https://github.com/gluon-lang/gluon/commit/844418dfc1d0cb37a4ddfdb82e79380887e9da7b))
*   Allow mutable references to be passed to gluon ([602220b5](https://github.com/gluon-lang/gluon/commit/602220b5f0af4a7b889cb7657ea491aaee85a50c))
*   Add std.env ([b561c8d6](https://github.com/gluon-lang/gluon/commit/b561c8d61dda20ca71fb03cc36ca317cc139c458))
*   Implement woobly type propagation ([a0b84525](https://github.com/gluon-lang/gluon/commit/a0b84525d8cbf7b1ba34542a9a173c0843c1bbc3))
* **codegen:**  Add the newtype attribute ([40854638](https://github.com/gluon-lang/gluon/commit/40854638263d96adcde77f9631ae0daab7bccf26))
* **completion:**
  *  Match on the symbols in type declarations ([9d28ba10](https://github.com/gluon-lang/gluon/commit/9d28ba102029e3c593f4fda9bc1acd167c445cb9))
  *  Return scoped symbols in the all_symbols query ([94a385af](https://github.com/gluon-lang/gluon/commit/94a385afd3b23bf6b54208858fd8c3736c758696))
  *  Match on the symbols in type declarations ([8fe083af](https://github.com/gluon-lang/gluon/commit/8fe083afe0a85e8a9db45b32dacd630cd87b8559))
  *  Return scoped symbols in the all_symbols query ([1ad302b0](https://github.com/gluon-lang/gluon/commit/1ad302b08a501ccb589ed97f427321d753d5ca59))
* **doc:**  Link to the github source ([da75875b](https://github.com/gluon-lang/gluon/commit/da75875bc0ee032c2b38a94982a7e08001d6a090))
* **vm:**  Allow references to be passed through ([3a92b176](https://github.com/gluon-lang/gluon/commit/3a92b1768a73ee3bf94fab22c9d10d33bd0fe50e))

#### Breaking Changes

*   Refer to registered types by their full name ([a2daace6](https://github.com/gluon-lang/gluon/commit/a2daace6e914157391b8453c97ddd675b86a7165), breaks [#](https://github.com/gluon-lang/gluon/issues/))



<a name="v0.11.2"></a>
### v0.11.2 (2019-03-26)


#### Features

* **doc:**  Don't display the full path to types in the documentation ([a669faaa](https://github.com/gluon-lang/gluon/commit/a669faaadadd388e23d36393204820d73316cbf5))

#### Bug Fixes

*   Ignore mdbook for osx builds ([7755967a](https://github.com/gluon-lang/gluon/commit/7755967ad5e3defb5a1d1b1c10ce920ec030556d))
* **check:**  The alias reduction stack must be cleared between unifying function arguments ([170072a4](https://github.com/gluon-lang/gluon/commit/170072a4734d4ec27c97c307aae7dc5b7d181dcc))
* **doc:**
  *  Correct all the remaining links in docs ([494675fe](https://github.com/gluon-lang/gluon/commit/494675fe3dbfc229c795ed3b076ce0c87c7297a1))
  *  Point breadcrumb links correctly ([2a9cca72](https://github.com/gluon-lang/gluon/commit/2a9cca7282a74bd13851a25f88f2b04d398f2dbe))
  *  Point Rust defined types to their doc location ([b170f2f3](https://github.com/gluon-lang/gluon/commit/b170f2f3a2bd9b8a33ca4eb7620ea0e7f2a26784))
  *  Don't generate dead links in the documentation ([04131b71](https://github.com/gluon-lang/gluon/commit/04131b71176bc824cee956aa431ab84063d98861))
  *  Point sibling module links correctly ([3bbf4a99](https://github.com/gluon-lang/gluon/commit/3bbf4a9927ef2060707bf8345cf028f6a03df658))



<a name="v0.11.1"></a>
### v0.11.1 (2019-02-13)


#### Bug Fixes

*   Don't build release artifacts with full debug info ([fe935835](https://github.com/gluon-lang/gluon/commit/fe9358358a30d06103e6ca51d0af41a1bdff7c60))
* **check:**  Subsume implicit functions with forall correctly ([6de5c256](https://github.com/gluon-lang/gluon/commit/6de5c256ecfa0a82ddea0f50d13e5441aefb722c))



<a name="v0.11.0"></a>
## v0.11.0 (2019-02-11)


#### Performance

*   Re-use the value buffers used in fixed structures ([40ca7bfd](https://github.com/gluon-lang/gluon/commit/40ca7bfd251aedb3391d5929a56b2d82a6e5fd66))
*   Avoid recursing when zonking a type without variables ([4a482c76](https://github.com/gluon-lang/gluon/commit/4a482c767994ecf966f87eda7d8809f8185d81b4))
*   Avoid recursing in gather_foralls ([6a38f437](https://github.com/gluon-lang/gluon/commit/6a38f4371de46c7c5f6ea7364d8f610b227129a0))
*   Optimized definition_name for the non-`:` case ([1713a442](https://github.com/gluon-lang/gluon/commit/1713a4424b2c3f54363f02f25d6dea216c148951))
*   Avoid recursing more in occurs check ([c0acb066](https://github.com/gluon-lang/gluon/commit/c0acb066b4503a407ee13f7b99a3a7111bcdfc82))
*   Use VecMap for type variable -> type lookup ([e5f086c9](https://github.com/gluon-lang/gluon/commit/e5f086c9848a3208e3f242a6e0a9889a0414621c))
*   Avoid some clones when adding implicit bindings ([86b2c9a6](https://github.com/gluon-lang/gluon/commit/86b2c9a61b5d0ef029e0c3814113d6456fd9b429))
*   Use HashTrie over RedBlackTree ([878f311a](https://github.com/gluon-lang/gluon/commit/878f311aa34509a218f6423a107c40ddb1571b4a))
*   Avoid allocating new ArcKind in Type::kind ([2911d7ef](https://github.com/gluon-lang/gluon/commit/2911d7ef9261c9dfbc0509f1756908b5e95f5ce6))
*   Properly rename type projections ([fb6f3e14](https://github.com/gluon-lang/gluon/commit/fb6f3e14c723a6653b66b695430f39e5bedff306))
*   Don't allocate individual boxes for values in Fixed{Map,Vec} ([b2532a17](https://github.com/gluon-lang/gluon/commit/b2532a17d1b1eea8af0567e22d2b43a11c5f2e4c))
*   Speedup global metadata lookup ([2c0477c7](https://github.com/gluon-lang/gluon/commit/2c0477c725bbf36029af7355ba05ea631315fd09))
*   Intern alias groups in translation ([e20a1dba](https://github.com/gluon-lang/gluon/commit/e20a1dba3c160b0390cdb34ae5dd6ff148ec639d))
*   Avoid some recursion when unpacking aliases with `AliasRef::typ` ([64edfb05](https://github.com/gluon-lang/gluon/commit/64edfb057545a71184572a0f38a881f0ef75e8d6))
*   Avoid recomputing generalization for the same type ([0732ce1a](https://github.com/gluon-lang/gluon/commit/0732ce1a35b41386d518cdc9383ee1eeef48d846))
*   Compare and hash types by the minimum necessary ([75174cdf](https://github.com/gluon-lang/gluon/commit/75174cdf2bd6535419f8f270179780c8082dd883))
*   Avoid doing two hash lookups in interning ([e3a3556c](https://github.com/gluon-lang/gluon/commit/e3a3556c8de75bf550c6542d905245e431c8b5f7))
* **base:**  Remove an indirection in aliases ([8327a035](https://github.com/gluon-lang/gluon/commit/8327a035f0b72d2662f53a294680928809408ea9))
* **check:**
  *  Re-use the allocations for variables ([d569cdc2](https://github.com/gluon-lang/gluon/commit/d569cdc2341ca7ad70f3b3bf83ae7377a3d7575f))
  *  Cuts the max memory use roughly in half on the lisp benchmark ([5b91b6d3](https://github.com/gluon-lang/gluon/commit/5b91b6d3b2e8d95e7f053c0a7de78e998d73a690))
  *  Avoid allocations for the field duplication check ([18abf71e](https://github.com/gluon-lang/gluon/commit/18abf71e0ca1e006e46ab7d8db9aa8f88bb45dfe))
  *  Partition implicit lookup more ([e80f683d](https://github.com/gluon-lang/gluon/commit/e80f683dc855a9d658f10fa91a7a3a5752a54d6a))
  *  Don't look in the global context for non-globals ([45bc2ad6](https://github.com/gluon-lang/gluon/commit/45bc2ad653d9d2e20b875d16b973069f209da0ac))
  *  Optmize occurs check ([2ce4ec07](https://github.com/gluon-lang/gluon/commit/2ce4ec07cd67904e238e82c51bffb78fd6fd30b1))
* **kindcheck:**
  *  Avoid some unnecessary kind allocations ([0afc648d](https://github.com/gluon-lang/gluon/commit/0afc648d2883895d75ec493dcae5b0dbb147ceb9))
  *  Use a HashMap for lookups and cache computed kinds ([27571ea5](https://github.com/gluon-lang/gluon/commit/27571ea5ead63810c302a1e697604e35f0da4d9b))
* **metadata:**  Use Arc to do shallow clones of Metadata (-4%) ([4faf41b0](https://github.com/gluon-lang/gluon/commit/4faf41b0245a4ce9634fdec381a48819f28f7a88))
* **parser:**
  *  Pre-allocate space for record fields ([d1f3cfec](https://github.com/gluon-lang/gluon/commit/d1f3cfecab2495d32360df666bb929894d499bb3))
  *  Shrink LALRPOP's internal symbol size by boxing ([c845f753](https://github.com/gluon-lang/gluon/commit/c845f753e8d7b7eecaf5a6c017ebdf814b7d94a5))
* **translate:**  Fix N^2 behavior in translation due to type replacements. ([14fc70fb](https://github.com/gluon-lang/gluon/commit/14fc70fb3095e6f01f4f87b4e2c961bf0fa3e5eb))

#### Features

* **check:**  Allow non-Type kinded types at the top of aliases ([126ecebb](https://github.com/gluon-lang/gluon/commit/126ecebbf0cdde4ff09ee5e9a6b3ad2ef17627f7), closes [#186](https://github.com/gluon-lang/gluon/issues/186))

#### Bug Fixes

*   Honor the compiler settings through all import!'s ([4da5b5f9](https://github.com/gluon-lang/gluon/commit/4da5b5f92f010d052aa57b08c75564c8fc97868b))
* **check:**  Take the parameters of record type fields into account when inserting forall ([b390db10](https://github.com/gluon-lang/gluon/commit/b390db109cadd5028ae76fa1f4661735d72291ae))
* **doc:**  Don't display an empty module section ([39478e07](https://github.com/gluon-lang/gluon/commit/39478e072ddc45791f3d8d53aca50534c1319bfa))
* **kindcheck:**  Force scoped type variables to have the same type in each scope ([cadbc29c](https://github.com/gluon-lang/gluon/commit/cadbc29c618c20135f84a8abcb4971d07cd8e2bf))
* **rename:**  Don't try to rename symbols if they are only defined in an earlier compilation ([56c115ed](https://github.com/gluon-lang/gluon/commit/56c115ed961dcfc1d5196f3560d4e3329e582cd9))
* **std.http:**  Don't let one slow TLS connection block the server ([68cc1286](https://github.com/gluon-lang/gluon/commit/68cc12869cdd2f84a7ac0cf3a981e9df5bd04d7b))



<a name="v0.10.1"></a>
### v0.10.1 (2019-01-27)


#### Performance

*   Use &mut to get better LLVM optimization (-2%) ([7bd988e5](https://github.com/gluon-lang/gluon/commit/7bd988e5de1be18c3b721ade509444fed990c9fc))
*   Take the type directly from the pattern during record pattern compile ([5fc9b2e8](https://github.com/gluon-lang/gluon/commit/5fc9b2e85f2a13832ecc97140ff79efc6dd10f27))
* **parser:**
  *  Avoid one branch in Tokenizer::bump (parse_prelude: -6%) ([9cf39d4b](https://github.com/gluon-lang/gluon/commit/9cf39d4b4d1fe7c0647e0e3651f5c16b9e34a23e))
  *  Shrink lalrpop's symbol size slightly ([fff12fab](https://github.com/gluon-lang/gluon/commit/fff12fab3a705a689fad616a97cd7d9b633bdc52))
* **vm:**
  *  Use more specialized functions ([cd057689](https://github.com/gluon-lang/gluon/commit/cd057689789a677fb8e6420d8c9bd6b388865abf))
  *  Add and use extend for Stack manipulation ([41c9f0f6](https://github.com/gluon-lang/gluon/commit/41c9f0f6ffa4e0191e9edcaaf58947b5c28bbf9d))
* **vm/translate:**
  *  Avoid one field lookup loop in pattern desugaring ([292edb70](https://github.com/gluon-lang/gluon/commit/292edb709c667b7bbc4accb19834d418918c4e94))
  *  Hoist a remove_alias call outside the loop ([37fe8762](https://github.com/gluon-lang/gluon/commit/37fe8762573594143adaf9378adfde07238d0d8a))
  *  Avoid doing replacement for trivial matches ([bfbab7fd](https://github.com/gluon-lang/gluon/commit/bfbab7fd452e0efb51bb55c7bc296b82bfe2d217))
  *  Use FnvMap with variable replacement ([e6c4b614](https://github.com/gluon-lang/gluon/commit/e6c4b614562078b176601b014fda4ef5cb5736c7))

#### Bug Fixes

*   Always do a gluon panic on arithemtic overflow ([82838a96](https://github.com/gluon-lang/gluon/commit/82838a962121066120f9643d67559c8287fbd0bb))
* **std.http:**  Don't return NotReady if the http stream is broken ([a93ed235](https://github.com/gluon-lang/gluon/commit/a93ed2352f5aa432f1ea6ef85660ba352b514d98))



<a name="v0.10.0"></a>
## v0.10.0 (2019-01-05)


#### Features

*   Implement extensible effects ([40185f22](https://github.com/gluon-lang/gluon/commit/40185f22650d959a62b3fd63dfd10f2bdcfd698f))
*   Recover from more parser errors and errors in imports ([693b560a](https://github.com/gluon-lang/gluon/commit/693b560a317f028de785720f6982951981353ea4))
*   Improve error recovery in let and do ([ed5670c3](https://github.com/gluon-lang/gluon/commit/ed5670c3a8de8c58425b21aa6c1bc6db19f80ecc))
*   Make std.json.de.deserialize simpler to use ([0a6b2517](https://github.com/gluon-lang/gluon/commit/0a6b2517ada461e682e21e8f5cb524f44b3f35ec), breaks [#](https://github.com/gluon-lang/gluon/issues/))
*   Add seq expressions ([f452c2e3](https://github.com/gluon-lang/gluon/commit/f452c2e36dcda24b53803f59747e6bb430fa3c43))
*   Display submodules in module documentation ([fdab790f](https://github.com/gluon-lang/gluon/commit/fdab790f0780b40a8971866fdfedd271d1c8e66a))
*   Add --open to gluon doc ([89a93c59](https://github.com/gluon-lang/gluon/commit/89a93c5939b3d4264cdd22a33ed3ff037dcc90d1))
*   Don't have format depend on the main crate ([55005236](https://github.com/gluon-lang/gluon/commit/550052367431ff4e6bbc4cf50993e059ee74104c))
*   Add std.effect.alt ([b9d65fb1](https://github.com/gluon-lang/gluon/commit/b9d65fb1eeac46a63dfce257d5c398eb785036d9))
*   Allow the prompt and color to be set from the REPL ([3aa8f7d8](https://github.com/gluon-lang/gluon/commit/3aa8f7d8c75dd697f672767ecf9a970d35f5bda5))
*   Let row polymorphic record types be parsed ([fb41cde3](https://github.com/gluon-lang/gluon/commit/fb41cde3cd2788949796c28ed10c1e9908a28e8b))
*   Use i64 as the integer type in the vm ([7ed0c1ef](https://github.com/gluon-lang/gluon/commit/7ed0c1efc4fc41c05402f86845799ac3b6c03219))
*   Add feature to switch debug status inside repl ([b48d180c](https://github.com/gluon-lang/gluon/commit/b48d180ceef214c17bc21f3096b20ffe80b367be))
*   Add general purpose debugging status ([92797784](https://github.com/gluon-lang/gluon/commit/927977849594b0daebf274df4bdaac55d93eb2d9))
* **check:**
  *  Remove the alias dependence for variants ([8c4678c7](https://github.com/gluon-lang/gluon/commit/8c4678c72fa1c5e456a261695ff58ddf090d11a0))
  *  Remove the alias dependence for variants ([16980eb4](https://github.com/gluon-lang/gluon/commit/16980eb4e1ff88537a18124260c2342f669e1eca))
* **std:**
  *  Move `when` to std.applicative ([2fd47247](https://github.com/gluon-lang/gluon/commit/2fd47247a2c790900b60d5069d37db7c52772383))
  *  Add the Reader effect ([14322f7e](https://github.com/gluon-lang/gluon/commit/14322f7e0f14225ff6f844295d1834a8a6067c80))
  *  Add the State effect ([092a0d05](https://github.com/gluon-lang/gluon/commit/092a0d05f421b0a4a4e91355b21a0486e69e230c))
  *  Add open_file_with and create_file to std.io ([5b2a031f](https://github.com/gluon-lang/gluon/commit/5b2a031fb0ede552fe2041b4fcf54980ea682b63))
  *  Add std.io.throw ([ef756280](https://github.com/gluon-lang/gluon/commit/ef75628032f4b253205a9201cc84109d76622c5a))
  *  Add Read File and Write File instances ([1b86ae44](https://github.com/gluon-lang/gluon/commit/1b86ae44587131044c4778476c8bdd4253a225b1), breaks [#](https://github.com/gluon-lang/gluon/issues/))
  *  Add std.array.is_empty ([8a65bc0f](https://github.com/gluon-lang/gluon/commit/8a65bc0fce6d4aabcb2403ba4f13150ec748b268))
  *  Add std.io.write ([571e827c](https://github.com/gluon-lang/gluon/commit/571e827cf0a5c09e99b5b154f2961dac8654bb5e))
  *  Add std.array.slice ([d5f8e190](https://github.com/gluon-lang/gluon/commit/d5f8e1902097a16dac3eb419c3cb23def5a01b78))
  *  Add std.io.read ([689a42cc](https://github.com/gluon-lang/gluon/commit/689a42cc32d0857bbc8f1942b3376cf671c709ac))
  *  Add std.disposable ([066655d1](https://github.com/gluon-lang/gluon/commit/066655d1f0099a2be4f8b7f09ee42a18cc67f306))
  *  Expose functions for overflowing/saturating arithmetic in std.int and std.byte ([ebfb68a0](https://github.com/gluon-lang/gluon/commit/ebfb68a0cb83981cf51faaa344b6598aec855df4))

#### Performance

*   Don't have generalize_type be N^2 ([16ba38a2](https://github.com/gluon-lang/gluon/commit/16ba38a208cef2668c03b3f0d4e7d3aab442e375))
*   Remove redundant HashMap ([7a07da19](https://github.com/gluon-lang/gluon/commit/7a07da197e99d212ccb45411b14a8cc015975047))
* **doc:**  Parallelize the documentation output ([f3b24712](https://github.com/gluon-lang/gluon/commit/f3b24712c18c9cb2b65d4b5c8503e98d87c88fbf))

#### Bug Fixes

*   Sort the modules in the documentation ([1193d729](https://github.com/gluon-lang/gluon/commit/1193d729d6d6db4a1e7a357da013c27801ee759f))
*   Rewrite higher ranked type inference to support ST ([b52a1471](https://github.com/gluon-lang/gluon/commit/b52a147104349c1afaaa9e2d29b1b34be7c81098))
*   Display the alias in type errors in more cases ([61a9a6fe](https://github.com/gluon-lang/gluon/commit/61a9a6fe4be2847457cc0e8e495421aad1b0a655))
*   Consistently put `then` on the same line as `if` ([6d00a89c](https://github.com/gluon-lang/gluon/commit/6d00a89ca283679d352a5bb53c89d3df04b1da05), closes [#495](https://github.com/gluon-lang/gluon/issues/495))
*   Handle implicit forall insertion better ([27be87ef](https://github.com/gluon-lang/gluon/commit/27be87ef57699c71b61bc6ea60d564182eeede6f))
*   Handle exhaustive matching on forall wrapper variants ([8789f6a3](https://github.com/gluon-lang/gluon/commit/8789f6a3ac3e71bcaadc21d1a4b59029e746f34d))
*   Handle forall before variant constructors ([8b2fcbed](https://github.com/gluon-lang/gluon/commit/8b2fcbed5293bcd8f287eafc553a7c2846a3e9dd))
*   Handle forall before variant constructors ([7e472abd](https://github.com/gluon-lang/gluon/commit/7e472abde06c169fc0ff10be6928e2e73b69b347))
*   Fix get_debug_level method to return cloned value instead of using lock ([f1c40257](https://github.com/gluon-lang/gluon/commit/f1c40257fa72d0888f0bcf273ccc0374fe741013))
*   Use fmt::Display trait to obtain to_string method ([cdc13ce4](https://github.com/gluon-lang/gluon/commit/cdc13ce4da6be0d8599e9c7105670c48780d87af))
*   Prevent printing out the contents of functions to the repl when debug status is not set ([3824695a](https://github.com/gluon-lang/gluon/commit/3824695a3ff1ec4b8cf8a0158873829c970f2d2f))
* **check:**
  *  Abort implicit checking immediately on infinite loops ([b4e859c5](https://github.com/gluon-lang/gluon/commit/b4e859c52669f3b132e6d973d277c4adaf9e1a9c))
  *  Multiple fixes with higher ranked types ([67a502f7](https://github.com/gluon-lang/gluon/commit/67a502f7cf7d06b04ab32b44dd9b06cb5f19ee66), closes [#603](https://github.com/gluon-lang/gluon/issues/603))
  *  Distionguish forall in the top of aliases ([69b0753b](https://github.com/gluon-lang/gluon/commit/69b0753b4c645b5a6f5ef6068f0c872a76786894))
  *  Avoid instantiating higher ranked types in function arguments ([2750d242](https://github.com/gluon-lang/gluon/commit/2750d242a00711fc3ba7573674aedd4350c3365f))
  *  Distionguish forall in the top of aliases ([aee2389c](https://github.com/gluon-lang/gluon/commit/aee2389c06850703b37db197925bffee825b275a))
  *  Avoid instantiating higher ranked types in function arguments ([f4fc5451](https://github.com/gluon-lang/gluon/commit/f4fc54519e38d7561d13a0318dd0c0c67e7dab4b))
* **std:**
  *  removed explicit eq parameter from elem ([b8c1c2a9](https://github.com/gluon-lang/gluon/commit/b8c1c2a9fbe9656fd64339b2f6b848c23f00c0b0))
  *  fix a couple typos in a couple std modules ([d4c1ddf0](https://github.com/gluon-lang/gluon/commit/d4c1ddf0d3706f26490604e6c9ac40264a740c6e))
* **vm:**  Forward all functions in the VmType impl of RuntimeResult ([9d6c7f45](https://github.com/gluon-lang/gluon/commit/9d6c7f45431ab1e0dfcac97846812e0e1a731138))

#### Breaking Changes

*   Make std.json.de.deserialize simpler to use ([0a6b2517](https://github.com/gluon-lang/gluon/commit/0a6b2517ada461e682e21e8f5cb524f44b3f35ec), breaks [#](https://github.com/gluon-lang/gluon/issues/))
* **std:**  Add Read File and Write File instances ([1b86ae44](https://github.com/gluon-lang/gluon/commit/1b86ae44587131044c4778476c8bdd4253a225b1), breaks [#](https://github.com/gluon-lang/gluon/issues/))



<a name="v0.9.4"></a>
### v0.9.4 (2018-10-21)


#### Bug Fixes

* **codegen:**  Fix Type::variant call for VmType derive ([48e1e11b](https://github.com/gluon-lang/gluon/commit/48e1e11b345db2e69ca98cc78a63836100148b64))



<a name="v0.9.3"></a>
### v0.9.3 (2018-10-15)


#### Features

*   Allow headers to be part of the response ([69dba621](https://github.com/gluon-lang/gluon/commit/69dba621b5c8e1d507e3fc5c476422b799a6068c))
*   Allow std.http to use https ([fb30fda2](https://github.com/gluon-lang/gluon/commit/fb30fda2624328f9893c222556fe89a5ad8c701b))
* **vm:**  Add thread.join ([514fd3b5](https://github.com/gluon-lang/gluon/commit/514fd3b5501c15f4223fb9afb8fc96c34195c7b3))

#### Bug Fixes

*   Ensure all futures on the stack gets polled ([d5862e14](https://github.com/gluon-lang/gluon/commit/d5862e1407968d3c96dee73682071caf5829acf3))
*   Don't generate warnings for VmType and Userdata derives ([5979c967](https://github.com/gluon-lang/gluon/commit/5979c9673cf603abf4bb2151960edb0dce9046a1))



<a name="v0.9.1"></a>
### v0.9.1 (2018-09-24)


#### Features

*   Allow implicit resolution if the same binding is included twice ([e62a0523](https://github.com/gluon-lang/gluon/commit/e62a052326ce5537aa155f566df85b3ef24f9f34))
*   Support non-static type parameters in VMType derive ([bdc7ecaf](https://github.com/gluon-lang/gluon/commit/bdc7ecaf22815a67fbc23a59a9c24655ca5c6258))
* **vm:**  Allow module loaders to contain state ([bee61dd8](https://github.com/gluon-lang/gluon/commit/bee61dd8882af6a0c3f471d9b883299f4e88ffa0), closes [#634](https://github.com/gluon-lang/gluon/issues/634))

#### Bug Fixes

*   Use the field order of the base record in record updates ([b60c3e12](https://github.com/gluon-lang/gluon/commit/b60c3e127b3e329d6030c6c9e4d60fba55266c50), closes [#509](https://github.com/gluon-lang/gluon/issues/509))
*   Don't error on Serialize/Deserialize derives because of missing imports ([a598fe23](https://github.com/gluon-lang/gluon/commit/a598fe23b3f4d1cc35fca27eff8795f9cb3ac264))
* **check:**  Correct the order of expected and actual hints ([beb30ae4](https://github.com/gluon-lang/gluon/commit/beb30ae4f53273b8b5fb670dd2ea52281be06a1f), closes [#627](https://github.com/gluon-lang/gluon/issues/627))
* **vm:**  Don't remove parent frames in when calling into the vm ([4a4fd3b6](https://github.com/gluon-lang/gluon/commit/4a4fd3b61af38d4ea28ebb6da3b3f51460422cf4))


<a name="v0.9.0"></a>
## v0.9.0 (2018-09-16)


#### Performance

*   Avoid allocating Strings in JSON [de]serialization ([694dd14f](https://github.com/gluon-lang/gluon/commit/694dd14fc1b02a0eef5c2e1f6a42369be20bba9f))
* **recursion:**  No need to keep state between top level bindings ([208d8b74](https://github.com/gluon-lang/gluon/commit/208d8b748ed974ccce97cd34b66ff6501cf09101))

#### Bug Fixes

*   Handle multiple doc comments and attributes between recursive let bindings ([1767019c](https://github.com/gluon-lang/gluon/commit/1767019c3fa8e88e0fc5395964901f14846cddb6))
*   Break function types with implicit arguments correctly ([2f537e66](https://github.com/gluon-lang/gluon/commit/2f537e6601626fd93b4f4ac2835098ebe56a77e6))
*   Resolve aliases that are hidden behind type variables ([b61ea5e9](https://github.com/gluon-lang/gluon/commit/b61ea5e9f51996c6cef40b8c837c27d11ff19f0c))
*   Resolve types through function aliases ([be5374ef](https://github.com/gluon-lang/gluon/commit/be5374efe466b60ad8dc0da09e11711448e5ad99))
* **check:**
  *  Always inserted implicit arguments to implicit_args ([f7ffc701](https://github.com/gluon-lang/gluon/commit/f7ffc701c1076c8044c120e1ed5dc3673fed17d9), closes [#601](https://github.com/gluon-lang/gluon/issues/601))
  *  Plug soundness holes with higher ranked types ([731a9ecd](https://github.com/gluon-lang/gluon/commit/731a9ecd609ffedf22f9b35dac139493ee233e93))
  *  Don't return non-skolemized types from lambda ([b0f283f2](https://github.com/gluon-lang/gluon/commit/b0f283f2e045a70e4ec40c04268e8b82a2f36fd6))
  *  Non-polymorphic records which are a prefix of another do not unify ([cc85aae2](https://github.com/gluon-lang/gluon/commit/cc85aae2b1b5c88d1eb3647610bcb606d9dcb221))
  *  Don't panic on partially applied aliases ([cc1e613e](https://github.com/gluon-lang/gluon/commit/cc1e613ea3bbad563fe23034a38b3a00831e48c0))
* **doc:**
  *  Correct the breadcrumbs link of nested modules ([81c17c22](https://github.com/gluon-lang/gluon/commit/81c17c22eabce7c5ce8bca7029f8bfc2d3c59a84))
  *  Don't rebuild gluon_doc when used outside of the gluon repo ([3da6c639](https://github.com/gluon-lang/gluon/commit/3da6c6393efb1fc8449cbf836570492b4e883f64))
* **format:**  Keep the brackets around implicit arguments on the same line ([03a1d9f6](https://github.com/gluon-lang/gluon/commit/03a1d9f67debdd74fd31237f544d4aadcfd462f9))
* **repl:**  Extract record fields using name_eq instead of Symbol::eq ([160c1c9c](https://github.com/gluon-lang/gluon/commit/160c1c9c0139d3302b3cae737a0554124acd4afc))
* **std:**  Don't panic if an error is found compiling a std module ([b02fa812](https://github.com/gluon-lang/gluon/commit/b02fa81224249b7b56725ea7e53311acf42ebfdd))
* **vm:**
  *  Handle out of order drops with RootedValue ([2fdc16b6](https://github.com/gluon-lang/gluon/commit/2fdc16b64571404d6fa508b191a02fb99daa9001))
  *  Restore the vm to a valid state after error has occured ([d4f4ec5e](https://github.com/gluon-lang/gluon/commit/d4f4ec5e77f383c92fa2eb2cee38034f9f494888))
  *  Set the field names of record! created records ([8e58159e](https://github.com/gluon-lang/gluon/commit/8e58159e3239c58b5bdc5d21186ae790ced9e928))
  *  Allow spawned actions to be forced multiple times ([8b27d649](https://github.com/gluon-lang/gluon/commit/8b27d649366232b3ccff5ca90e233e59d38ea171))
  *  Correctly assign record field names derive(Pushable) ([4a36d825](https://github.com/gluon-lang/gluon/commit/4a36d825fc166730a408d50cc74d086e89e3c385), closes [#591](https://github.com/gluon-lang/gluon/issues/591))

#### Breaking Changes

*   Allow Pushable to to call back into the vm ([8d100dd2](https://github.com/gluon-lang/gluon/commit/8d100dd2a5084412e01ed26d1f6a7b504d1ef074), breaks [#](https://github.com/gluon-lang/gluon/issues/))
*   Migrate tokio_core uses to tokio ([18aa1f0f](https://github.com/gluon-lang/gluon/commit/18aa1f0f08f072b3f49f097ade43a6c216e1f415), closes [#462](https://github.com/gluon-lang/gluon/issues/462), breaks [#](https://github.com/gluon-lang/gluon/issues/))
* **parser:**  Define recursive bindings with `rec` ([552c8f21](https://github.com/gluon-lang/gluon/commit/552c8f2173a385804b8dc896d7568e803d0179a5), breaks [#](https://github.com/gluon-lang/gluon/issues/))
* **vm:**
  *  Remove the unused Root and RootStr types ([996fedc1](https://github.com/gluon-lang/gluon/commit/996fedc1ecb5cc6494529d3097e8ceb76eb0f42f), breaks [#](https://github.com/gluon-lang/gluon/issues/))
  *  Move Alternative to std.alternative ([e961cc24](https://github.com/gluon-lang/gluon/commit/e961cc24f7d13296772a609c073b75576ddfc144), breaks [#](https://github.com/gluon-lang/gluon/issues/))

#### Features

*   Hint towards rec let if old 'and' bindings are used ([a879194c](https://github.com/gluon-lang/gluon/commit/a879194cc772f1f74979aa3115ab4254c9dba22e))
*   Print a hint/warning towards necessary feature gates when importing modules ([9b96e511](https://github.com/gluon-lang/gluon/commit/9b96e51162e8ae7b11dee29fbc13c3445bf589a0))
*   Prevent type errors from creating cascading errors ([7976bcd5](https://github.com/gluon-lang/gluon/commit/7976bcd5d33ee92cc72281ef13e859498c4423ed))
*   Bound derive(Getable) by 'value byte default ([597b6963](https://github.com/gluon-lang/gluon/commit/597b6963b1c032af12f18849b25e757c6b5640ac))
*   Add derive(Serialize) ([31799a94](https://github.com/gluon-lang/gluon/commit/31799a944710f78b8a0fae9472f91dd48b89ca0e))
*   Treat Pushable/Getable derives on newtypes as their inner type ([62ad61d9](https://github.com/gluon-lang/gluon/commit/62ad61d9ca85370cdd4482a0dd7d0069c62ea745))
*   Allow OpaqueValue to be converted into its inner value ([1147ab59](https://github.com/gluon-lang/gluon/commit/1147ab593f278718f950215ae82ff4d7f65949d8))
*   Add JSON serialization ([b028ab2d](https://github.com/gluon-lang/gluon/commit/b028ab2df839b6b064d129ea5fc6abd12f644b49))
*   Support the crate_name attribute in getable ([81ba45f5](https://github.com/gluon-lang/gluon/commit/81ba45f5d5193a52c31678053760257bd36b0ce1))
*   Allow Pushable to to call back into the vm ([8d100dd2](https://github.com/gluon-lang/gluon/commit/8d100dd2a5084412e01ed26d1f6a7b504d1ef074), breaks [#](https://github.com/gluon-lang/gluon/issues/))
*   Migrate tokio_core uses to tokio ([18aa1f0f](https://github.com/gluon-lang/gluon/commit/18aa1f0f08f072b3f49f097ade43a6c216e1f415), closes [#462](https://github.com/gluon-lang/gluon/issues/462), breaks [#](https://github.com/gluon-lang/gluon/issues/))
*   Implement Getable for Vec<T> ([727e279b](https://github.com/gluon-lang/gluon/commit/727e279b42079197a68cd6feb7a01feb5bb16e84))
*   Allow displaying the post-macro expansion AST ([53f5cbf9](https://github.com/gluon-lang/gluon/commit/53f5cbf96492d67ca6c62ee055889435cc797479))
*   Add derive(Show) ([d8689a73](https://github.com/gluon-lang/gluon/commit/d8689a7307a83eea383478c267d3899bd85dfd6c))
*   Add derive(Eq) ([c6da284d](https://github.com/gluon-lang/gluon/commit/c6da284d12d43a2e34c38f0027c56b1988c010f1))
* **check:**  Let non-function values be used recursively in some contexts ([c2027add](https://github.com/gluon-lang/gluon/commit/c2027add10c7b5d11f0d9444ed87ced877b98d2d))
* **codegen:**  Allow structs to generate record types using derive(VmType) ([7a9fb16c](https://github.com/gluon-lang/gluon/commit/7a9fb16ce2ed252244a56eb36692ced64881c76d))
* **doc:**
  *  Provide links to sub-directories of modules ([3ef34989](https://github.com/gluon-lang/gluon/commit/3ef34989f5cf064324bb0ec673df3afbafa0b615))
  *  Add `#[doc(hidden)]` to hide bindings in docs ([92c8bec6](https://github.com/gluon-lang/gluon/commit/92c8bec64ada939ff85bb738288d64e97ad85bf1))
  *  Update to handlebars 1.0.0-beta.4 ([78880ebf](https://github.com/gluon-lang/gluon/commit/78880ebfbeb8221fb9509dab78fed2839cf11efa), closes [#582](https://github.com/gluon-lang/gluon/issues/582))
  *  Make all types link to their definition ([34fff8d1](https://github.com/gluon-lang/gluon/commit/34fff8d1e757bcf6efa425ee436530258c622997), closes [#552](https://github.com/gluon-lang/gluon/issues/552))
* **parser:**
  *  Define recursive bindings with `rec` ([552c8f21](https://github.com/gluon-lang/gluon/commit/552c8f2173a385804b8dc896d7568e803d0179a5), breaks [#](https://github.com/gluon-lang/gluon/issues/))
  *  Add raw string literals ([9bda2804](https://github.com/gluon-lang/gluon/commit/9bda2804df2c7b7713bd871e92055b5aaaa5c7a2), closes [#276](https://github.com/gluon-lang/gluon/issues/276))
* **vm:**
  *  Remove the unused Root and RootStr types ([996fedc1](https://github.com/gluon-lang/gluon/commit/996fedc1ecb5cc6494529d3097e8ceb76eb0f42f), breaks [#](https://github.com/gluon-lang/gluon/issues/))
  *  Let Userdata be returned to Rust ([1ea24284](https://github.com/gluon-lang/gluon/commit/1ea242849de3a9689e1e79c356598a34621c0e80))
  *  Move Alternative to std.alternative ([e961cc24](https://github.com/gluon-lang/gluon/commit/e961cc24f7d13296772a609c073b75576ddfc144), breaks [#](https://github.com/gluon-lang/gluon/issues/))
  *  Let Getable return types bound to the lifetime of Variants (#587) ([010a7f71](https://github.com/gluon-lang/gluon/commit/010a7f71fe162265e64bc43f8db3832fcfbda3d1))



<a name="v0.8.1"></a>
### v0.8.1 (2018-07-01)


#### Bug Fixes

*   Reject programs which use lowercase letters for types ([bd54a83f](https://github.com/gluon-lang/gluon/commit/bd54a83f572ab25e15c2602bf05bea40f08314b0))
*   Display type fields with the parameters on the left side of = ([ef6fc9bc](https://github.com/gluon-lang/gluon/commit/ef6fc9bcea491449cf1d8d8e4815065d47188beb))
*   Handle type projection in kind check ([3b78e370](https://github.com/gluon-lang/gluon/commit/3b78e3708c98dc3a383c6f2acec792ab91e157f4))
*   Print the correct source on errors in the repl ([159eaf99](https://github.com/gluon-lang/gluon/commit/159eaf99aeaafbff43ce55557fadb8d5e843ab19), closes [#568](https://github.com/gluon-lang/gluon/issues/568))
* **check:**  Don't shadow more general variant constructors ([182c3960](https://github.com/gluon-lang/gluon/commit/182c396086e17bbc03111f445436099fa31ab5c2), closes [#548](https://github.com/gluon-lang/gluon/issues/548))
* **completion:**  Avoid panicking on env_type_of calls ([c63cf2fb](https://github.com/gluon-lang/gluon/commit/c63cf2fbe52f4cd4604ce580889a0035e43dc8f5))
* **format:**
  *  Update pretty to avoid panickingon multiline strings in debug mode ([bb4d05da](https://github.com/gluon-lang/gluon/commit/bb4d05da9e5158186dea3d81769993ffe6dc05eb))
  *  Don't panic on multiline strings ([7662f38f](https://github.com/gluon-lang/gluon/commit/7662f38f30744cbac83222fd5b855a36eb47b9ec))
* **repl:**
  *  Don't panic on solo array literals ([5bffdfa9](https://github.com/gluon-lang/gluon/commit/5bffdfa97e80f5e69bf8d58d7c3328936cfa76e8), closes [#555](https://github.com/gluon-lang/gluon/issues/555))
  *  Don't fail with a parse error on lines only containing a comment ([f5819bca](https://github.com/gluon-lang/gluon/commit/f5819bca3b7ea9013088ed798c93a53697edbee3), closes [#559](https://github.com/gluon-lang/gluon/issues/559))

#### Features

*   Allow type definitions to be declared inside types ([d47508d9](https://github.com/gluon-lang/gluon/commit/d47508d9fb610b7c25a742c619f62bb7730e1408))
*   Add debug.show ([0c962722](https://github.com/gluon-lang/gluon/commit/0c96272237567e098f2f692e5ac9350b19e39c30))



<a name="v0.8.0"></a>
## v0.8.0 (2018-06-14)


#### Performance

*   Remove Substitution::set_type ([4c751ab6](https://github.com/gluon-lang/gluon/commit/4c751ab69aed6883c44b697abda5c1bf5e42fd6a))
*   Avoid running skolemize and instantiate when there is no variables ([1a09a745](https://github.com/gluon-lang/gluon/commit/1a09a74564ce89ade1660bc7149169f8e1ff7bce))
*   Don't trim anything when just derefing symbols (~12%) ([703e0529](https://github.com/gluon-lang/gluon/commit/703e0529d82603a09180476f1795255ccc3db122))
*   Avoid cloning the name inside Symbols unnecessarily ([c1c061a0](https://github.com/gluon-lang/gluon/commit/c1c061a09e5245f2f3d1bfaa95a082564256409a))
*   Avoid allocating a new Arc for each type hole during parsing ([8ecdccf1](https://github.com/gluon-lang/gluon/commit/8ecdccf1df43481105a5ee6af3601dec89789731))
* **check:**  Partition the implicit bindings to reduce the search space ([c26c12f3](https://github.com/gluon-lang/gluon/commit/c26c12f3c3716de22e0065eb292891436e6f3c6c))
* **parser:**
  *  Avoid calling Location::shift unnecessarily ([07e00726](https://github.com/gluon-lang/gluon/commit/07e0072648938a09a3a49f6b8b03d2442e07825c))
  *  Improve performance of is_operator_char (~2%) ([3d885997](https://github.com/gluon-lang/gluon/commit/3d885997989524554523a94afe6e6d75d2334506))
  *  Reuse the same Kind allocation in the parser ([ba6e9816](https://github.com/gluon-lang/gluon/commit/ba6e9816f5478fcf968a21aa60dc85e1d81d4add))

#### Bug Fixes

*   Ensure that missing identifier gets reported despite the infix reparser errors on it ([390b2a2c](https://github.com/gluon-lang/gluon/commit/390b2a2c25cbb08daf939a25c3be7afab8a8d55b))
*   Emit the correct type Deserialize generated array types ([112fe346](https://github.com/gluon-lang/gluon/commit/112fe3463e249b3428a2802a6c6ac5c2b87e40cb), closes [#542](https://github.com/gluon-lang/gluon/issues/542))
*   Emit a span inside the actual source for eof parse errors ([3d598fbe](https://github.com/gluon-lang/gluon/commit/3d598fbefb1696e478eb7dd97686a8308e3eb4b6))
*   Resolve aliases properly in call expressions ([b6ac8b65](https://github.com/gluon-lang/gluon/commit/b6ac8b651144edf6edaae734b9e01ffdc4d00e16))
*   Ignore symbols outside of the current source for all_symbols ([b8a408a1](https://github.com/gluon-lang/gluon/commit/b8a408a1653b7b8ad3cb2387d2d3523f5c9ca624))
*   Get the http example working again ([d151ab10](https://github.com/gluon-lang/gluon/commit/d151ab10575d60c492b0cde5ec5d4e5736cf2505))
*   Print a newline between each unification error ([2241c296](https://github.com/gluon-lang/gluon/commit/2241c296889dcd278acc625cd29314dd7a8bcc9a))
*   Don't allow string references to be returned from run_expr ([b133bf08](https://github.com/gluon-lang/gluon/commit/b133bf087c14c25f125e15e589b2406e91949795))
*   Don't lose error messages from sub-modules ([5e1bbbef](https://github.com/gluon-lang/gluon/commit/5e1bbbefa24894e5ebef2445220cb9c0c3f9218b))
*   Take implicits into account in type queries on infix expressions ([8651be33](https://github.com/gluon-lang/gluon/commit/8651be33055e31517525595577c4b440f9e4ec39))
*   Insert implicit arguments when none one has not been specified ([c9a42268](https://github.com/gluon-lang/gluon/commit/c9a4226869cee0d67929da29148e2819d4c84e46))
*   Indent type signatures that are on multiple lines ([27eea994](https://github.com/gluon-lang/gluon/commit/27eea994ec8f0692125c444014f1307bf218266b))
*   Only report errors from imported modules once ([6f3bbd8f](https://github.com/gluon-lang/gluon/commit/6f3bbd8f5eebf2078cc1f221fe1e445efc30875d))
*   Provide proper line and source information for macro errors ([7e924c2c](https://github.com/gluon-lang/gluon/commit/7e924c2ca3cee12a90b11b888998de07cd448926))
*   Don't panic if let bindings has more arguments than declared type ([15bf3072](https://github.com/gluon-lang/gluon/commit/15bf3072f28b84e285864830b58595f098875a5a))
* **check:**
  *  Put variants into scope even behind aliases ([2d1ba6cb](https://github.com/gluon-lang/gluon/commit/2d1ba6cbbd4328657d4b314e3ae562d8d13efcca))
  *  Propagate the expected type through array expressions ([9f0f6571](https://github.com/gluon-lang/gluon/commit/9f0f657127c8154853f52e4ac2da6e0768975587))
  *  Don't guess at what type a record is ([a4ae10f0](https://github.com/gluon-lang/gluon/commit/a4ae10f00f8b98351726b4667330b569f3d3c0b1), closes [#510](https://github.com/gluon-lang/gluon/issues/510))
  *  Make the pattern's type the expected type ([8b075f6f](https://github.com/gluon-lang/gluon/commit/8b075f6f6e3c5db5e4a9feccce1a4dc0f9aaf735))
  *  Propagate type fields even if the type was undefined ([f79f1a7e](https://github.com/gluon-lang/gluon/commit/f79f1a7e11137a161ce0bdf5bd8dc0ad714eadec))
  *  Point to the exact field that did not exist in type patterns ([88865cd4](https://github.com/gluon-lang/gluon/commit/88865cd450f0d88a056a03ba6adedfd43dd224ae))
  *  Replace the type hole with the actual type during subsumption ([f2ae746e](https://github.com/gluon-lang/gluon/commit/f2ae746e0c413e46bcd135b8e4052cdb9a14ada5))
  *  Don't generalize tail expressions before replacing implicits.rs ([7d7bede2](https://github.com/gluon-lang/gluon/commit/7d7bede2d73a993c31e20a0d6f6c42b1105c5fbc))
  *  Don't overwrite implicit variables in renaming ([b8de950f](https://github.com/gluon-lang/gluon/commit/b8de950f6048723818234233a698abd1b7b9e274))
  *  Don't bail out if record fields are undefined ([e0863b93](https://github.com/gluon-lang/gluon/commit/e0863b934e954df65a857a5e8aec6a6b1330d8d4))
* **compiler:**  Merge pattern bindings which appear in multiple alternatives ([f8657776](https://github.com/gluon-lang/gluon/commit/f86577761a713d9735493fd6d619ecbb84e947fb))
* **completion:**
  *  Provide suggestions on whitespace inside record expressions ([17a63a04](https://github.com/gluon-lang/gluon/commit/17a63a044c71015b3f95ad91259a116981850156))
  *  Don't suggest fields that have already been used for record expressions ([7edbe92e](https://github.com/gluon-lang/gluon/commit/7edbe92e0405c879df1af5ea7a48bccc48cb8e9e))
  *  Fix almost all clippy warnings ([cd842de0](https://github.com/gluon-lang/gluon/commit/cd842de0c3e5b6e94efa1cf9a4b06fd1fd4e707d))
* **format:**
  *  Format doc comments in record expressions ([d030cd2c](https://github.com/gluon-lang/gluon/commit/d030cd2ca80e8174da7c107774a5dab1e86ee52b))
  *  Always put declared variants on separate lines ([859e0acb](https://github.com/gluon-lang/gluon/commit/859e0acb2fe10c3bf2207f784b744e02b7c2c124))
  *  Don't touch formatted files if they haven't changed ([dabc96db](https://github.com/gluon-lang/gluon/commit/dabc96db2bb67709dc833cf90b6ac262b00eec60))
* **metadata:**  Propagate metadata from function arguments ([025c73c6](https://github.com/gluon-lang/gluon/commit/025c73c63168dcbcaf114ff395998e5b6093b868))
* **rename:**  Rename implicit imports ([6a3409d1](https://github.com/gluon-lang/gluon/commit/6a3409d10f042a6fce181d3b40f31434cd281229))
* **std:**
  *  Ensure that ++ gets a fixity assigned to it ([020153f7](https://github.com/gluon-lang/gluon/commit/020153f7642d4c88556778d641403aca22224d48))
  *  Correct Show's type ([6ab92d13](https://github.com/gluon-lang/gluon/commit/6ab92d137ff3a102656a7d5fe71d573a550eb4a8))
* **vm:**
  *  Don't error on <<loop>> when using lazy values from multiple threads ([78e5f90b](https://github.com/gluon-lang/gluon/commit/78e5f90b5e96f87748bee0006a3676ac32890dee))
  *  Allow deserializing functions through RootedValue ([6f7531d6](https://github.com/gluon-lang/gluon/commit/6f7531d6413fb169ce2f49f79efb6a808954a821))
  *  Align garbage collected allocations correctly on 32-bit systems ([734bfc5e](https://github.com/gluon-lang/gluon/commit/734bfc5e435e62dc7c86855abbdf52094ffae94c))

#### Features

*   Provide metadata for type patterns ([67fcb19e](https://github.com/gluon-lang/gluon/commit/67fcb19e98eaa66e00db53ac18d3eaee54871cae))
*   Display the kind of a type when hovered over ([f407d976](https://github.com/gluon-lang/gluon/commit/f407d9768b5d595504de629c362771ad15f7f703))
*   Break apart the prelude into separate modules ([966750b2](https://github.com/gluon-lang/gluon/commit/966750b2b4cd54f2d6280558dbe1683d3d45b573), breaks [#](https://github.com/gluon-lang/gluon/issues/))
*   Allow primitive types to be exported with record! ([6700dc29](https://github.com/gluon-lang/gluon/commit/6700dc293a6afa383907b953a595d09b9d5b5cd9))
*   Detect and format tuple types as (Int, String, abc) ([8697e348](https://github.com/gluon-lang/gluon/commit/8697e3489844c2300ff49f2e2ba41cdae5a3ef44))
*   Use #[IDENTIFIER(..)] as the attribute syntax ([0300590d](https://github.com/gluon-lang/gluon/commit/0300590d98605223aae5053bac58307db3120a33), closes [#515](https://github.com/gluon-lang/gluon/issues/515), breaks [#](https://github.com/gluon-lang/gluon/issues/))
*   Improve the error message for unresolved implicits ([2bda18b3](https://github.com/gluon-lang/gluon/commit/2bda18b34d58f86a105c70acde668d4eb5519246))
*   Return an error when infix operators are used without fixity ([89c7e4a8](https://github.com/gluon-lang/gluon/commit/89c7e4a8c5d41d96104207ad6a83658716f0efa3))
*   Obey the new @infix attribute for operator fixity ([1a143b80](https://github.com/gluon-lang/gluon/commit/1a143b80a80589461088398247767f3766124020))
*   Update to lalrpop 0.15 ([4f59c4c2](https://github.com/gluon-lang/gluon/commit/4f59c4c222eb86a64b4e6290ca1d206fb4492a06))
*   Add conversion functions betwen ints and floats ([187ac79f](https://github.com/gluon-lang/gluon/commit/187ac79fe343e0edbae1b49af12cf59a3f279309))
*   Treat a pattern matched type as if it exists even on type errors ([42059db7](https://github.com/gluon-lang/gluon/commit/42059db713aeaba8e18bc2ea7c9c521b854340f2))
*   Display sibling modules on the left side of module documentation ([c18c6729](https://github.com/gluon-lang/gluon/commit/c18c672903e2edd415ff7dac0af7bd31b60baebe))
*   Use bootstrap to get some prettier documentation ([bbfee5d0](https://github.com/gluon-lang/gluon/commit/bbfee5d0577b150f2d7702db469d267636aceec1))
*   Make gluon_doc into an executable ([dd046531](https://github.com/gluon-lang/gluon/commit/dd046531f7cb37fee569070787972a2e46f8c86b))
*   Generate an index.html file with links to all documented modules ([788d2c7e](https://github.com/gluon-lang/gluon/commit/788d2c7e61f6ba4a2b8b8ca086cbc50bce4ef6d2))
*   Emit html from the documentation generator ([30565c1e](https://github.com/gluon-lang/gluon/commit/30565c1e81300efe53016ea1d93d21363f11afb9))
*   Allow configuring the import search paths when creating a vm ([87e92198](https://github.com/gluon-lang/gluon/commit/87e921987ddeeaca529e4cd22554f294db67a3bb))
*   Allow explicit bindings of implicit arguments ([79869285](https://github.com/gluon-lang/gluon/commit/79869285b4e00df3f66d196fc9cceca8c09cd37a))
*   Replace make_ functions with implicits ([2a51ece7](https://github.com/gluon-lang/gluon/commit/2a51ece70590400eb86e61f2cb5440bac4e942cd))
*   Add implicit arguments ([9eb8aafd](https://github.com/gluon-lang/gluon/commit/9eb8aafd4d7989cba627f35b4fc12a217527f513))
*   Filter out unrelated fields in some type errors ([63d2ab43](https://github.com/gluon-lang/gluon/commit/63d2ab43c6b934f7d62b53fcbd214e865b4b4275))
* **check:**
  *  Improve error message for applying to many arguments ([012bcefb](https://github.com/gluon-lang/gluon/commit/012bcefb5b8fba006c541aa62d91ecdb2e80e399), closes [#508](https://github.com/gluon-lang/gluon/issues/508))
  *  Filter UndefinedField errors ([a0ecfd20](https://github.com/gluon-lang/gluon/commit/a0ecfd202b73ce2dc0406f11f66fba2bcc209e38))
  *  Propagate metadata defined on fields in type definitions ([c413bbdb](https://github.com/gluon-lang/gluon/commit/c413bbdba9eb5ec58000e0bf04e48fff63c28a41))
* **completion:**
  *  Suggest types in record expressions ([8091a845](https://github.com/gluon-lang/gluon/commit/8091a845cba5eeaa37f05d2a87b9ee1244522a7f))
  *  Provide suggestions for the record field shorthand ([eb193aae](https://github.com/gluon-lang/gluon/commit/eb193aaef0c490256fa337229373b74ebea7e2cb))
  *  Display information about fields in record constructors ([3fd96c0e](https://github.com/gluon-lang/gluon/commit/3fd96c0e055d451690bd8b10d4836e565f2d70de))
* **doc:**  Add documentation generation ([1d199936](https://github.com/gluon-lang/gluon/commit/1d199936f64b7a35be2f12f1a2cf3e0a9581e6a4))
* **repl:**  Displayed colored errors in the repl ([4d053f32](https://github.com/gluon-lang/gluon/commit/4d053f32099ad27b0d71c3b97c0b9fcb91d93c5d))
* **std:**
  *  Add Show, Eq, Ord etc to std.array ([b76e290d](https://github.com/gluon-lang/gluon/commit/b76e290d188d884aba308ef4997ee34bd332fc2c))
  *  Add Show, Eq, Ord etc to std.stream ([e9406d33](https://github.com/gluon-lang/gluon/commit/e9406d331a57f318f4cae19a7952a34de07b670d))
  *  Add min and max functions to std.cmp ([2f3b8048](https://github.com/gluon-lang/gluon/commit/2f3b80487946753888c9eab11aea12335ad8f1ad))
  *  Export ++ as a string append function ([85a0eeaa](https://github.com/gluon-lang/gluon/commit/85a0eeaa4c7b85eb9e3a5089d75cdef0e513b908))
  *  Re-export all std.map functions as implicit functions ([64bb7899](https://github.com/gluon-lang/gluon/commit/64bb78992064aad5e9b9b6f13b9ad48c85e7ddc8), breaks [#](https://github.com/gluon-lang/gluon/issues/))
* **vm:**
  *  Display the stacktrace on gluon panics ([ebc17487](https://github.com/gluon-lang/gluon/commit/ebc17487990486fe74e9eec4b06acdd828bf3d34), closes [#528](https://github.com/gluon-lang/gluon/issues/528))
  *  Add from_str_radix to std.int ([7d0f705c](https://github.com/gluon-lang/gluon/commit/7d0f705cf2d08235f87bfef4194948069ce011c0))
  *  Add is_char_boundary and char_at on String ([3a63c26c](https://github.com/gluon-lang/gluon/commit/3a63c26ce079904ab4120052ee76ae9c7b23bd9a))
  *  Add Char <-> Int conversion functions ([620df403](https://github.com/gluon-lang/gluon/commit/620df403d09baf24d09a9a45e16fbc34d5434c67))
  *  Add the std.byte module ([ecbbc132](https://github.com/gluon-lang/gluon/commit/ecbbc132d37c4459a6e59a8a1e105f529aee0e1c))

#### Breaking Changes

*   Break apart the prelude into separate modules ([966750b2](https://github.com/gluon-lang/gluon/commit/966750b2b4cd54f2d6280558dbe1683d3d45b573), breaks [#](https://github.com/gluon-lang/gluon/issues/))
*   Use #[IDENTIFIER(..)] as the attribute syntax ([0300590d](https://github.com/gluon-lang/gluon/commit/0300590d98605223aae5053bac58307db3120a33), closes [#515](https://github.com/gluon-lang/gluon/issues/515), breaks [#](https://github.com/gluon-lang/gluon/issues/))
* **std:**  Re-export all std.map functions as implicit functions ([64bb7899](https://github.com/gluon-lang/gluon/commit/64bb78992064aad5e9b9b6f13b9ad48c85e7ddc8), breaks [#](https://github.com/gluon-lang/gluon/issues/))



<a name="0.7.1"></a>
## v0.7.1 (2018-02-04)


#### Features

*   Deploy builds using trust and cross ([372a278f](https://github.com/gluon-lang/gluon/commit/372a278f6c2cb95a7caf349a17033a6b14c4b506))
*   Export expr pretty printing function to format ([646b7c66](https://github.com/gluon-lang/gluon/commit/646b7c66d384209cb57bdddb2aa14688e287ba67))
*   Make dependencies unavailable in wasm optional ([6e666f73](https://github.com/gluon-lang/gluon/commit/6e666f73b6a4c56299abcab9d8ee99401e18d28c))
* **completion:**
  *  Make prefix filtering optional ([896e985f](https://github.com/gluon-lang/gluon/commit/896e985f813e06524be4e83220fc974633613c42))
  *  Provide signature help through completion ([df92dad7](https://github.com/gluon-lang/gluon/commit/df92dad74855877d6bd839f79b8349ffa6649674))
* **parser:**  Introduce literal pattern for match expressions ([6f4dd7f6](https://github.com/gluon-lang/gluon/commit/6f4dd7f676dad55ebde8a92aea53b4947b069a7f))

#### Bug Fixes

*   Actually return the stack size from the stack_size function ([87e4c95e](https://github.com/gluon-lang/gluon/commit/87e4c95e3c66c6f4ca905b62111ccc0aa7fcd9f0))
* **c-api:**  Mark C functions as no_mangle ([8eee8619](https://github.com/gluon-lang/gluon/commit/8eee8619cbf2cb9c717974a20cb82e4ecca88bf2))
* **check:**
  *  Don't print type mismatches betwen EmptyRow ([f2dc9ef6](https://github.com/gluon-lang/gluon/commit/f2dc9ef6d02ed1edbf6884e94320a8706cb67b48))
  *  Don't instantiate variables during unification inside aliases ([1326ca5d](https://github.com/gluon-lang/gluon/commit/1326ca5de7411783293b83bc15b15b1b74ad3b78))
* **vm:**
  *  Use check_translation in all tests ([43ca5f62](https://github.com/gluon-lang/gluon/commit/43ca5f621a59480c7efe5d536b31d463a302b9f2))
  *  Fix warning about upcoming breaking change ([3918f66c](https://github.com/gluon-lang/gluon/commit/3918f66c91e6146bcb78d1100ccaee21ebfe4299))



<a name="0.7.0"></a>
## v0.7.0 (2017-12-22)


#### Breaking Changes

*   Let the run_script functions execute IO actions ([8373f8f5](https://github.com/gluon-lang/gluon/commit/8373f8f5ac749ced0daf78340516535477c055d5), breaks [#](https://github.com/gluon-lang/gluon/issues/))

#### Bug Fixes

*   Don't crash in renaming on partial patterns ([fdea1724](https://github.com/gluon-lang/gluon/commit/fdea17242e5ed227757f3bd1c41f38e6f326407d))
*   Don't format Value::String as GcStr(<contents>) ([c8c8ba99](https://github.com/gluon-lang/gluon/commit/c8c8ba997adc0589e145b30c603b2a17627640c0))
*   Set the correct spans for renamed identifiers ([545f8911](https://github.com/gluon-lang/gluon/commit/545f89115c9f73e6e78abadd29cb4e4bd8db1082))
*   Lock the garbage collector before the interner to prevent dead locks ([794cdce1](https://github.com/gluon-lang/gluon/commit/794cdce1a0c8ec86449f440333fab10a1751f3d8))
*   Rename variables in record base expressions ([d4270a84](https://github.com/gluon-lang/gluon/commit/d4270a84da1662616f53e4c3d54d4e37498baba9))
*   Handle fields being omitted when removing intermediate records ([bfac0823](https://github.com/gluon-lang/gluon/commit/bfac08230fcbcb6e256c2ce45ecbeb2bac301cb0))
*   Correctly use traverse_with_key to get access to the keys ([abff3b90](https://github.com/gluon-lang/gluon/commit/abff3b902d6c3afcd0a73d845fdd3ebaa2bdf197))
* **base:**
  *  parameterless ice! macro. ([e5346dfa](https://github.com/gluon-lang/gluon/commit/e5346dfa1ab428cd05c8a3b70b17ca1f854008f6))
  *  Don't forget the ForAll type when calling walk_move_type ([7b78bd78](https://github.com/gluon-lang/gluon/commit/7b78bd78b4d700f53f0fcabff438d3dbe61094dc))
* **check:**
  *  Don't panic on nested patterns on parameterized types ([7e6ef364](https://github.com/gluon-lang/gluon/commit/7e6ef3649f314b018eca640e0a3cc2dde63c47e0))
  *  Remove spurious println! ([95177345](https://github.com/gluon-lang/gluon/commit/95177345c73b9d3fe04569ce6373c57e1b50cd51))
  *  Don't panic if a type is undefined in a variant ([e476b1e0](https://github.com/gluon-lang/gluon/commit/e476b1e0b8d2660d163360adbb0e6d21b04af95c))
  *  Typecheck a module even if macro expansion fails ([5f78fec0](https://github.com/gluon-lang/gluon/commit/5f78fec00c408128dc38dafffee743f57981b97b))
  *  Don't consider global variables for overload resolution ([aeade634](https://github.com/gluon-lang/gluon/commit/aeade63440239f1c5f23b44d1202ef1b865ef12a))
  *  generalize_type must not return unified variables ... ([437c5224](https://github.com/gluon-lang/gluon/commit/437c5224f9256603b2907a6e9c926392458f6602))
* **completion:**
  *  Don't print duplicate primitive modules ([0c4100db](https://github.com/gluon-lang/gluon/commit/0c4100db345f2728e4aabb4379445d854b7f57d9))
  *  Provide completion for types imported from other modules ([923f5cc7](https://github.com/gluon-lang/gluon/commit/923f5cc7f6002e249137a4d1abfd122604df0923))
  *  Complete parameterized variant type contructors ([d232cc19](https://github.com/gluon-lang/gluon/commit/d232cc1995d84310b327abfca9437e0038a5f05a))
  *  Provide pattern completion on record aliases ([43abb033](https://github.com/gluon-lang/gluon/commit/43abb0334133c52583e07c3599ef2e229576f837))
* **doc:**  Rearranged sections to make it easier for a first time user to get started and added a section on testing ([f4ed3134](https://github.com/gluon-lang/gluon/commit/f4ed3134fb0c6771abce28528dbc6b2f24239886))
* **format:**
  *  Layout successive if-else expressions on the same line ([18055c8d](https://github.com/gluon-lang/gluon/commit/18055c8dc96efdd357144bf9e7ff402cd2b61c23))
  *  Don't remove comments between expressions in blocks ([473b583e](https://github.com/gluon-lang/gluon/commit/473b583ec221b61cc57230f5c8c160a7069c0115))
  *  Don't put records already on a newline on the beginning line ([a66cafcf](https://github.com/gluon-lang/gluon/commit/a66cafcff7c45ec390b5a385e0df1e3d3eb1701a))
* **import:**  Prevent multiple threads from compiling the same module ([cb522854](https://github.com/gluon-lang/gluon/commit/cb52285403de392d7f9bf8826528594a52dc15b8))
* **parser:**
  *  Accept doc comments before `and` tokens ([90393b9d](https://github.com/gluon-lang/gluon/commit/90393b9d219e24cf6cb62b5e41f9da5281f149a1))
  *  Select the correct offside location inside parentheses ([4060aad5](https://github.com/gluon-lang/gluon/commit/4060aad5353753b3e2c31aa95f95ebd1010eb8ae))
  *  Byte literals with unexpected char ([18b34794](https://github.com/gluon-lang/gluon/commit/18b34794d60bf6ffa0c2057e352da630bc971887))
  *  Float literals with unexpected char ([ea537e13](https://github.com/gluon-lang/gluon/commit/ea537e1317508ab45fd4e49f9c761cc409ed6d16))
* **repl:**
  *  Avoid overflowing the stack when printing values ([cd1505ad](https://github.com/gluon-lang/gluon/commit/cd1505ada8aa3a214a5a81eb7559f159f18be040))
  *  Don't exit the repl if compilation errors occur in load ([3cf289f5](https://github.com/gluon-lang/gluon/commit/3cf289f5cef13ff80e5eb31f95458b651521ef29))
  *  Print out Char as the "character" instead of code point integer in the repl ([6612ceb2](https://github.com/gluon-lang/gluon/commit/6612ceb23200be85726b8d2d399d3355709f37bb), closes [#395](https://github.com/gluon-lang/gluon/issues/395))
  *  Run io expression when running files from the command line ([64ed556e](https://github.com/gluon-lang/gluon/commit/64ed556e980267a5b6476b7a3cf6c20870384163), closes [#365](https://github.com/gluon-lang/gluon/issues/365))
* **vm:**
  *  Run IO expressions with io.run_expr ([e308f1f2](https://github.com/gluon-lang/gluon/commit/e308f1f26173c645ea9f39f91f884e1db7dcdec0))
  *  Don't rely on frame_levels to clear frames after errors ([3a3205df](https://github.com/gluon-lang/gluon/commit/3a3205df97dc762ca7d9a728ff3ab496261b7472))
  *  Allow async functions to run within the io primitives ([e6f611a0](https://github.com/gluon-lang/gluon/commit/e6f611a00695a1d9069a7e85fd06bb064d9e70a2))
  *  Indent the pretty printing of Value ([5d646515](https://github.com/gluon-lang/gluon/commit/5d646515b1ee8ee1c94337e7483232d8b0b20da6))
  *  Fix deadlock caused by inconsistent lock ordering ([8024d57d](https://github.com/gluon-lang/gluon/commit/8024d57d7c6d4753f8a2b435cb5d5634e1179fc7))
  *  Deep clone partial applications properly ([d7877cac](https://github.com/gluon-lang/gluon/commit/d7877cacbb5048d1d8a4e6d8d7d4895f689d1eed))
  *  Lock all child gc's and child-threads when collecting ([5642b97a](https://github.com/gluon-lang/gluon/commit/5642b97a045119d15f8d21b8a488b536d27c0184))
  *  Handle polymorphic records created in parent threads ([8570ace5](https://github.com/gluon-lang/gluon/commit/8570ace57861866063b2dd451a44f5391ede6ebb))
  *  Don't let rustc think the Array type can't exist ([a8db3d5d](https://github.com/gluon-lang/gluon/commit/a8db3d5d1a97e76a28cd08bfff9a3af95e1a4d9d))
  *  child_threads must be traversed for all threads ([eac571b9](https://github.com/gluon-lang/gluon/commit/eac571b9d7dd8006d605124ff179fa786ce6fb65))
  *  Tuple indices start at 0, not 6 ([655e4526](https://github.com/gluon-lang/gluon/commit/655e45265fb8f37d1d687122b285c816dbbaa6f4))
  *  Don't deadlock when returning the result of `resume` ([99c8d148](https://github.com/gluon-lang/gluon/commit/99c8d14854e5f0563d9680eac4076d9d0f282b5e))

#### Features

*   Accept @ patterns in the repl ([1b6838ec](https://github.com/gluon-lang/gluon/commit/1b6838ec673c7525486225cbdd514f13e55084f1))
*   Add more character parsers to parser.glu ([a74726b9](https://github.com/gluon-lang/gluon/commit/a74726b93b84098266d7caafb60c3d76dc37328b))
*   Wrap all macro errors with a span ([20c8339a](https://github.com/gluon-lang/gluon/commit/20c8339a8a6b8dd79d2be23ea6e0bae18bd37c52))
*   Display kinds when completing types ([1dd43c14](https://github.com/gluon-lang/gluon/commit/1dd43c14cbdbdbc17a101b8712e70eb03f8e5d5e))
*   Teach import to accept a path as argument ([ed3d0b19](https://github.com/gluon-lang/gluon/commit/ed3d0b19ab9047ffa4bb4a4b3cc69b7974f98c36))
*   Let the run_script functions execute IO actions ([8373f8f5](https://github.com/gluon-lang/gluon/commit/8373f8f5ac749ced0daf78340516535477c055d5), breaks [#](https://github.com/gluon-lang/gluon/issues/))
*   Improve the error message of cyclic dependencies ([db540fd7](https://github.com/gluon-lang/gluon/commit/db540fd7be2488fadf4c71165f05a41dcbd8b395))
* **base:**
  *  Add a non-panicking version of env_type_of ([0a7aea90](https://github.com/gluon-lang/gluon/commit/0a7aea90ba4064c2eb00e828cbdd8483b9c991fc))
  *  Improve method names in MutVisitor ([1a24c084](https://github.com/gluon-lang/gluon/commit/1a24c08461567e9623236d79eb0ea7a50a5cbe0d))
  *  Add PartialEq for spans ([ded0d03b](https://github.com/gluon-lang/gluon/commit/ded0d03bee317bf53e38523314bcef3cc0ea3247))
* **check:**
  *  Typecheck do expressions ([c5afd839](https://github.com/gluon-lang/gluon/commit/c5afd839338d0e9c191237c1e2f229bc20f6838a))
  *  Run kindchecking on AstType ([5c31efe3](https://github.com/gluon-lang/gluon/commit/5c31efe3223f2c5b0d6a6127d5028cd30851129a))
  *  Let type aliases be referred via projection ([49a2a04a](https://github.com/gluon-lang/gluon/commit/49a2a04a6d6121b0debb9c8521d253a55f06a760), closes [#192](https://github.com/gluon-lang/gluon/issues/192), [#370](https://github.com/gluon-lang/gluon/issues/370))
* **completion:**
  *  Provide completion for primitive modules ([ce7100bf](https://github.com/gluon-lang/gluon/commit/ce7100bf489abf74bdffc2d596abd5fab330c841))
  *  Provide completion for the import! macro ([6e791ecb](https://github.com/gluon-lang/gluon/commit/6e791ecbbdee501f0b2e63949250b28b4f95d202))
  *  Provide completion when writing fields before another field ([e89f8df7](https://github.com/gluon-lang/gluon/commit/e89f8df783b630d8140fb29a91dfe408a462ff74))
  *  Don't suggest fields already written in a pattern ([bb371410](https://github.com/gluon-lang/gluon/commit/bb37141067ad228cb456dea48279e956628411a8))
  *  Suggest type fields inside record patterns ([a37222a4](https://github.com/gluon-lang/gluon/commit/a37222a48e4d76e7490a758d55cc81b29c852f77))
  *  Suggest what fields are available in record patterns ([6e1dca2a](https://github.com/gluon-lang/gluon/commit/6e1dca2a7519979b309e275aa02b4a598fd84d8a))
  *  Provide completion on do expressions ([e45de697](https://github.com/gluon-lang/gluon/commit/e45de697fc8f2f331c29714fcb43308180bd325c))
  *  Provide completion for type variables ([3b164a45](https://github.com/gluon-lang/gluon/commit/3b164a45a436df6bf2cb0807da7355b2d8dd78b1))
  *  Provide auto completion for types in let bindings ([e7a0c5c8](https://github.com/gluon-lang/gluon/commit/e7a0c5c885c9900e4aea277a19109373882dd343))
  *  Provide auto completion in type definitions ([79688de8](https://github.com/gluon-lang/gluon/commit/79688de853063c1bddbeb42889e04b2ede70da31))
* **format:**  Format do expressions ([71157dbd](https://github.com/gluon-lang/gluon/commit/71157dbd4e34191441c67dc0c472be4c6f0bb499))
* **parser:**
  *  Produce expressions if the `in` token is missing ([a523bec7](https://github.com/gluon-lang/gluon/commit/a523bec7470b2f5a8673c0863b4d4d004c55d6b1))
  *  Add more operator characters ([6a54edbb](https://github.com/gluon-lang/gluon/commit/6a54edbb2f7182d6d5629492cbf4c0a2d08935c3))
  *  Recover from parse errors when nothing follows =, -> ... ([d753672e](https://github.com/gluon-lang/gluon/commit/d753672ee695c1ed6a06d2012b1a04f1476c902d))
  *  Parse `do` expressions ([9a97a457](https://github.com/gluon-lang/gluon/commit/9a97a457c0cd10e12150aafc8155198fd21b118a))
* **repl:**
  *  Save and load command history ([8fd443b2](https://github.com/gluon-lang/gluon/commit/8fd443b214da4f7919fca77457f91cf8965ad67a))
  *  Have a long a short form for each repl command ([db099216](https://github.com/gluon-lang/gluon/commit/db099216d6abf5a7763196fb239d36949c015ba3))
  *  Allow module loading to be interrupted ([196e099e](https://github.com/gluon-lang/gluon/commit/196e099ec285f2de199e771af1ca187b1c1526c0))
  *  Don't shutdown the repl on Ctrl-C ([088b1a05](https://github.com/gluon-lang/gluon/commit/088b1a05cf9033c2a7e395d1b62fb13e67618abc))
* **std.list:**  Add filter and sort ([d67fc29e](https://github.com/gluon-lang/gluon/commit/d67fc29e9dccf42eea8aefd4a169fd158c79a0cc))
* **std.parser:**
  *  Add chainl/chainl1 ([449d61f8](https://github.com/gluon-lang/gluon/commit/449d61f81db5ad25f67e4bf5943477b76ce50cfa))
  *  Include the byte offset in the error message ([fc7c6762](https://github.com/gluon-lang/gluon/commit/fc7c6762bf1f2fdd57894f51102e137b06419381))
  *  Add satisfy_map ([75df8f5b](https://github.com/gluon-lang/gluon/commit/75df8f5b5e89dacfd34002462de844c5f1421b1e))
  *  Add sep_by and sep_by1 ([77f8ec0c](https://github.com/gluon-lang/gluon/commit/77f8ec0c36c204d97af39722e30b8fd7116665eb))
* **vm:**
  *  Add discriminant_value primitive ([3d65a559](https://github.com/gluon-lang/gluon/commit/3d65a5598fedc56a160de589314acc2ed8b732ac))
  *  Return type and value separately from run_expr ([6aa5c471](https://github.com/gluon-lang/gluon/commit/6aa5c471f4179bf0589fc252425bfb59e3be6438))
  *  Add a basic wrapper around the rand crate ([7210d8dd](https://github.com/gluon-lang/gluon/commit/7210d8dd12996d01965283516b9ca9196e5c6c3f))
  *  Let the record macros have non-rust identifiers for field names ([55ccbe1c](https://github.com/gluon-lang/gluon/commit/55ccbe1cea7eeaa3b5db8af9da9ab1dd7d4269e4))
  *  Let primitive modules be loaded via import! ([91bb7d3f](https://github.com/gluon-lang/gluon/commit/91bb7d3f34993f6d02d6988ddb25752e19068f78))
  *  Re-export map.empty ([577cb08b](https://github.com/gluon-lang/gluon/commit/577cb08b2fde65b27f27da9210fcc7b27de1aec8))



<a name="0.6.2"></a>
## v0.6.2 (2017-10-18)


#### Features

*   Format all files (recusively) when a directory is given ([6ce97c6f](https://github.com/gluon-lang/gluon/commit/6ce97c6fc3ef6064e32bcce40bc10f3a05bd9ba3))
*   Add a trailing comman on records that take multiple lines ([8c3aa951](https://github.com/gluon-lang/gluon/commit/8c3aa951396b5111d693b86daecdbbcacf95909a))
*   Pretty print record expressions with the `..` operator ([aeb1d75b](https://github.com/gluon-lang/gluon/commit/aeb1d75b75e6176745200817563c115b476315e9))
*   Add the '..' operator to distribute the fields of a record ([d6b03cc9](https://github.com/gluon-lang/gluon/commit/d6b03cc99c68d91ddfddd787ab562ccb515377c5))

#### Bug Fixes

*   Error on undefined variables in type bindings ([ed442110](https://github.com/gluon-lang/gluon/commit/ed4421102641f994a1474465a339b0cb34759a06))
*   Return and error on duplicate fields defined in another module ([0973b264](https://github.com/gluon-lang/gluon/commit/0973b264ee1063de82ca9d32bebf5cc20a254e6e))



<a name="v0.6.0"></a>
## v0.6.0 (2017-10-10)


#### Bug Fixes

*   format/tests/pretty_print.rs ([de858796](https://github.com/gluon-lang/gluon/commit/de8587969c759711cb041fffab8c065a251f785f))
*   Replace 'env!("OUT_DIR")' with 'env::var("OUT_DIR").unwrap()' ([366c6306](https://github.com/gluon-lang/gluon/commit/366c6306401353038b7561a0df5736bf3730bbb8))
*   Preserve comments inside types ([4a216da8](https://github.com/gluon-lang/gluon/commit/4a216da8b1084e806b843232550f0a89eaebb762))
*   Mark lines of recursive function definitions ([4d5a4b67](https://github.com/gluon-lang/gluon/commit/4d5a4b674b26f3df2acce5817a6a78eca5c0d0a1))
*   Don't crash when querying types on unit expressions ([1c36bbbd](https://github.com/gluon-lang/gluon/commit/1c36bbbd149aef1f57236b3ce114d73ea95ab21b))
*   Report completions in let patterns ([c6172991](https://github.com/gluon-lang/gluon/commit/c6172991a83eb5945f90ac7b2b98ef00ee1a552e))
*   Visit `Expr::Tuple { typ }` ([640154b2](https://github.com/gluon-lang/gluon/commit/640154b29024e09c54f812bef0e12d11cde9ea88))
*   Deserilize partial applications properly ([0efed42b](https://github.com/gluon-lang/gluon/commit/0efed42b6c90bfbf8ed1f5f165c39990e103f991))
*   Preserve parentheses in nested patterns ([d7e238da](https://github.com/gluon-lang/gluon/commit/d7e238da8dd916f5c4e430fb31694afdfb1c721c))
*   Correctly visit all core expressions when walking the tree ([0ad8ce00](https://github.com/gluon-lang/gluon/commit/0ad8ce0055fe93027c96576b505621b3766fcca4))
*   Preserve newlines between record fields properly ([8f169ad3](https://github.com/gluon-lang/gluon/commit/8f169ad351463f938cc2a801e455842291a450b6))
*   Don't lose parts of literals when formatting ([7b538496](https://github.com/gluon-lang/gluon/commit/7b5384968365f83c7a258799cde7ac2bebb4e93d))
* **check:**  Indent types in error messages correctly ([6ff9a217](https://github.com/gluon-lang/gluon/commit/6ff9a217c1fe3f27366841dc6e6492bb4a86417b))
* **completion:**
  *  Complete type constructors which are implicitly imported ([d336ad37](https://github.com/gluon-lang/gluon/commit/d336ad379cbe0221911a1769dd7d2643476e3c36))
* **format:**
  *  Indent long record pattern matches ([c2a5cf34](https://github.com/gluon-lang/gluon/commit/c2a5cf347934fe03978cf2b390fc8771c736d486))
  *  Preserve block comments in some places ([ca125bf1](https://github.com/gluon-lang/gluon/commit/ca125bf126f8ede4ccd3fb0ab8e0252deaba2a12))
  *  Preserve comments between let bindings and their bodies ([f9836f9c](https://github.com/gluon-lang/gluon/commit/f9836f9c3e9c14b82f436d0dfe5034c3bc79c48d))
* **repl:**  Evaluate IO expressions automatically in the repl ([d9e6e952](https://github.com/gluon-lang/gluon/commit/d9e6e95246ffd7ec59b00c3deee57ce465e5fe97), closes [#334](https://github.com/gluon-lang/gluon/issues/334))
* **resolve:**  Leave aliases over opque types alone ([3ac0fd61](https://github.com/gluon-lang/gluon/commit/3ac0fd6127cae059ca58e6b60635515d629fa533))

#### Features

*   Add impls of VmType, Pushable, Getable for all integer types ([0a53bd52](https://github.com/gluon-lang/gluon/commit/0a53bd52bfb99b20be7eb936246588ff501d9177))
*   Allow gluon types to be generated from rust types ([35d9b804](https://github.com/gluon-lang/gluon/commit/35d9b804365ec43a422fbcd89e124fc506c3434d))
*   Provide a way to get all* symbols of a module ([d6df46fd](https://github.com/gluon-lang/gluon/commit/d6df46fd105d0fa145a78968fdabb99cbc027341))
*   Add find_all_symbols ([0602f8d6](https://github.com/gluon-lang/gluon/commit/0602f8d62229d3aad5c0623746e661ddd2b555b6))
*   Allow doc comments on fields in types ([3e9ce940](https://github.com/gluon-lang/gluon/commit/3e9ce940a4a36906e5617d97a972b5875802bc29))
*   Vastly improve when comments are kept during formatting ([91522578](https://github.com/gluon-lang/gluon/commit/91522578cccdae0592c3c06ceda8a6a56a821a1f))
*   Display type information about function arguments ([fe2ec28d](https://github.com/gluon-lang/gluon/commit/fe2ec28d39b281b676b86cad95b0f35033062b46))
*   Fallback to returning information about the enclosing expression ([3a8e4c0b](https://github.com/gluon-lang/gluon/commit/3a8e4c0be7bef1b53a291fa897dab862002b8e9b))
*   Give more control over what data is returned for completions ([7d0bc359](https://github.com/gluon-lang/gluon/commit/7d0bc35961881955abfc9f68f065246ecb578a5b))
*   Constant fold binary expressions ([10b77ac3](https://github.com/gluon-lang/gluon/commit/10b77ac34218f469766170620f6f4543bdaaf07b))
*   Print the commit hash when passing --version to the gluon executable ([3a1e5969](https://github.com/gluon-lang/gluon/commit/3a1e5969c094f6a1a5587811a86254337cb77201))
*   Rewrite the parser to be Result based instead of continuation based ([488b6bdf](https://github.com/gluon-lang/gluon/commit/488b6bdf8000a06feede43f93c781a89adb214a5))
*   Add bytecode serialization and loading ([f5d6c752](https://github.com/gluon-lang/gluon/commit/f5d6c752f81d767851fbafeaea0a75f1a01e6463))
*   Make serde an optional dependency ([a17c0c75](https://github.com/gluon-lang/gluon/commit/a17c0c75418d5713e9d0240701ecdec639e5bb43))
* **base:**  Allow the width to be adjusted before displaying types ([2d1d3867](https://github.com/gluon-lang/gluon/commit/2d1d3867a7cbe314d581ed938c55f1a5cf01aa6d))
* **parser:**
  *  Allow projection on types in the parser ([b3aaabdf](https://github.com/gluon-lang/gluon/commit/b3aaabdf4661fde1bc03a42f8336a2d8412b602a))
  *  Let gluon files specify shebang ([d104deea](https://github.com/gluon-lang/gluon/commit/d104deeaa44a77cc8ea45297df97a76a6d410a85))
* **vm:**
  *  Allow generating a simple ffi binding for rust types ([31034b5a](https://github.com/gluon-lang/gluon/commit/31034b5a639781ef1e522d2750a7c154fcd10e5d))
  *  Add parse functions for floats and integers ([7e5f70d0](https://github.com/gluon-lang/gluon/commit/7e5f70d0177da7681c35d7d126d49ddeb8e52530))

#### Performance

* **vm:**  Avoid generating unnecessary catch-alls ([ebcdba96](https://github.com/gluon-lang/gluon/commit/ebcdba96751fc3a5706c69d061e7a4d9e5adbba6))



<a name="v.0.5.0"></a>
## v0.5.0 (2017-07-01)

Highlights for 0.5 include code formatting of gluon code and automatic marshalling between Rust
and Gluon through [serde][]. Formatting can be done either via the `gluon fmt` sub-command or with
directly in Visual Studio Code with the [language-server plugin][].

Type errors should now be formatted much better and have more precise types.

[serde]:https://serde.rs
[language-server plugin]:https://github.com/gluon-lang/gluon_language-server

#### Bug Fixes

*   Separate all errors with a newline ([86f159fd](https://github.com/gluon-lang/gluon/commit/86f159fd7099c04d74103b8561d6d0662029e81c))
* **check:**
  *  Indent types in error messages correctly ([13a7f52c](https://github.com/gluon-lang/gluon/commit/13a7f52c7a987febd64eab705f5ef6827bc855ac))
  *  Report clearer errors when aliases do not match ([2ea68654](https://github.com/gluon-lang/gluon/commit/2ea686547abcf64bc7553e85c7db0aba98d7fb7a))
  *  Don't leak inference variables out to type errors ([ef1d584b](https://github.com/gluon-lang/gluon/commit/ef1d584b478f93999e5fefd835fb8218701247b0), closes [#292](https://github.com/gluon-lang/gluon/issues/292))
* **parser:**  Give correct location information for unindentation errors ([30541c1e](https://github.com/gluon-lang/gluon/commit/30541c1eeb82b97823067c592e1fa7e0052146cc))
* **pretty:**  Always format empty records as unit types ([03f07f16](https://github.com/gluon-lang/gluon/commit/03f07f16453818cd3250b3bf1f2a5fa660117e4c))
* **vm:**
  *  Only allocate enough memory for a ValueArray when appending arrays ([abe7a4b2](https://github.com/gluon-lang/gluon/commit/abe7a4b2ac30d2bbcecf29762d500bf403731956))
  *  Fix the debug printing of GcStr and ValueArray ([5566b518](https://github.com/gluon-lang/gluon/commit/5566b5183e137cde97b4122f707dc049491ea40d))

#### Features

*   Add a fmt sub-command to the gluon executable ([b9c6ea6c](https://github.com/gluon-lang/gluon/commit/b9c6ea6c3cc0d532811f565d7ae509abf7a6eeb9))
*   Bump version of pretty ([29808fce](https://github.com/gluon-lang/gluon/commit/29808fce01d7e2e3a1fbc03aad18db8047280302))
* **base:**
  *  Display applied and function types better during multi line splits ([3fff91eb](https://github.com/gluon-lang/gluon/commit/3fff91eb14a7f113d36eab3908d66bd2c85eb86a))
  *  Add basic pretty printing of expressions ([68b3bb97](https://github.com/gluon-lang/gluon/commit/68b3bb975f24a7a5b480321ea60f087aa6803459))
* **check:**  Auto complete pattern matches ([712dc412](https://github.com/gluon-lang/gluon/commit/712dc4125ec1824d96d1c5e741a863c34bb766d7))
* **parser:**
  *  Allow partial parsing of alternatives when only the `|` exists ([cbe698f7](https://github.com/gluon-lang/gluon/commit/cbe698f768c1c4348ef5101855f805d015dea304))
  *  Allow partial parsing when patterns are missing ([e3285428](https://github.com/gluon-lang/gluon/commit/e32854284367531417466fab8e899ccf70d82af9))
  *  (Re-)add negative numbers to the language ([65dfc1ac](https://github.com/gluon-lang/gluon/commit/65dfc1ac8454750a13ce33f98e4adf177b68aca5))
* **vm:**
  *  Merge the Tag and Data variants of ValueRef ([ed7330d1](https://github.com/gluon-lang/gluon/commit/ed7330d1b318a406ade8993d526464d8e94c99e0))
  *  Add deserialization from gluon values ([6b98e29c](https://github.com/gluon-lang/gluon/commit/6b98e29c76abe30d2c9117de0475eed6d6a4dfe7))
  *  Allow automatic marshalling from Rust to gluon objects via serde ([8318e341](https://github.com/gluon-lang/gluon/commit/8318e34168848a31511b8c0ffce8a7f5c1009ee8))



<a name="v0.4.1"></a>
##  v0.4.1 (2017-05-23)


#### Features

*   Add the list function for simple Array to List conversion ([89019cef](https://github.com/gluon-lang/gluon/commit/89019cef90f167c46f15db9d43566b1ccb63549e), closes [#284](https://github.com/gluon-lang/gluon/issues/284))



<a name="v0.4.0"></a>
## v0.4.0 (2017-05-16)

Version 0.4.0 is a primarily a bug fix release with only a single significant feature as the upcoming features are all still WIP. 

#### Features

*   Name the the parser's tokens fit better in error messages ([33f733c8](https://github.com/gluon-lang/gluon/commit/33f733c88618092a545183114a56f1dcd5d9ec5e))
*   Use the async branch of hyper in the http example ([46f1dc39](https://github.com/gluon-lang/gluon/commit/46f1dc39313bec63a0027a2dceb8c434305568d1))
* **http:**  Add multiple routes for the http server example ([e93109d0](https://github.com/gluon-lang/gluon/commit/e93109d01c3f4b9e1c9c7147bdf7e87715f6c6b1))
* **repl:**  Allow binding variables in the repl for later use ([4f0dcf99](https://github.com/gluon-lang/gluon/commit/4f0dcf99b87910a869cd3f2a4aa5e61267a5cea2))

#### Bug Fixes

*   Display what tokens are expected when the parser fails ([6925c7b5](https://github.com/gluon-lang/gluon/commit/6925c7b53b6f896e747a8bbb4fc46a45e5c0c131), closes [#270](https://github.com/gluon-lang/gluon/issues/270))
*   Update the http server example to conform to a newer hyper version ([c841e4f3](https://github.com/gluon-lang/gluon/commit/c841e4f33f543ad2cfa23107da434236fae7f61e))
* **check:**
  *  When checking record constructors, include the type fields in the guess ([60d8cb0b](https://github.com/gluon-lang/gluon/commit/60d8cb0b3edd1546521c3ce56fc44d411477e629))
  *  Don't guess a record type when the field list is empty ([9db233a0](https://github.com/gluon-lang/gluon/commit/9db233a06dd712eabefdcbb67e07550718bdd998))
* **http:**  Move the handler creation of the http server to a file ([248474e6](https://github.com/gluon-lang/gluon/commit/248474e6a5c75e5f7697de71515823623b624a68))

#### Performance

*   Reuse an existing Kind::Type instance when creating a type variable ([81befe0c](https://github.com/gluon-lang/gluon/commit/81befe0cf07e8e1961132f18c01052a00b6306d1))
*   Add a kind cache as well to mirror the type cache ([f3c9efd2](https://github.com/gluon-lang/gluon/commit/f3c9efd287c8a43c985cbd0d2fac4731d6807faf))
*   Reuse the Arc pointers for builtin types ([ff3ab278](https://github.com/gluon-lang/gluon/commit/ff3ab2788b8cb8340d8d62f5825df1d2a2bd7890))



<a name="v0.3.0"></a>
## v0.3.0 (2017-02-01)

Version 0.3.0 improves the experience of writing gluon by a significant amount thanks to a few
different improvements. The main reason for this is the rewrite of gluon's parser to use [LALRPOP][]
which just started with the intent of making the parser easier to maintain but with [error recovery][]
added to LALRPOP the parser is now able to typecheck broken code which is used to drive code completion.

Another big addition to the usability of gluon is that an experimental debugger has been added to the
visual code plugin! This initial implementation provides breakpoints, pausing and variable inspection.

Lastly gluon has gotten support for asynchronous functions through tokio! It is now possible to write
Rust functions which return a `Future` and gluon will automatically suspend the running gluon program
and return a new future which drives the program until completion. As an example of this a [http server
built on hyper](https://github.com/gluon-lang/gluon/pull/226) is currently in the PR queue just waiting for a tokio based release of hyper.

[LALRPOP]:https://github.com/nikomatsakis/lalrpop
[error recovery]:https://github.com/nikomatsakis/lalrpop/blob/master/doc/tutorial.md#calculator6

#### Bug Fixes

*   Ensure that the gluon library can be built without any features ([347adea5](https://github.com/gluon-lang/gluon/commit/347adea5960538a33f2db6713fb3f8aac1c20c1e))
*   Print closures as `name: value` using debug information ([880e6006](https://github.com/gluon-lang/gluon/commit/880e6006735a3cfb54c7553401a60a9cef0694df))
*   Allow lambdas to appear on the right side of an infix expression ([1f587349](https://github.com/gluon-lang/gluon/commit/1f58734906328ace1cf0644e3345342b0edac9ae))
*   Avoid rebuilding the parser crate even if nothing has changed ([322e7ed2](https://github.com/gluon-lang/gluon/commit/322e7ed2ea872d093d7a1f7d1d86d92bd7ac579e))
*   Don't panic when compiling partially compiled constructors ([6fb552ea](https://github.com/gluon-lang/gluon/commit/6fb552ea51ae104c18e4ba48479911487170b995), closes [#202](https://github.com/gluon-lang/gluon/issues/202))
* **check:**
  *  Don't leak `Type::Ident` outside of aliased types ([9156a5e9](https://github.com/gluon-lang/gluon/commit/9156a5e9128347de14ee6f3cc32385b48abab475))
  *  Only mark the span of `let` and `type` expressions body ([717e08e9](https://github.com/gluon-lang/gluon/commit/717e08e9d0c4e2f672993c7f3511e051c7ec4b7d))
  *  Fill in the unified types of function arguments properly ([b5db5728](https://github.com/gluon-lang/gluon/commit/b5db5728f2f926b5586fc6ccc7605c7e2c2228af))
* **compiler:**
  *  Correctly close the debug variable information ([1cfa5862](https://github.com/gluon-lang/gluon/commit/1cfa5862b1da6647c248e1130c5aab856cb99573))
  *  Pop the correct amount of variables in the compiler ([99bf9343](https://github.com/gluon-lang/gluon/commit/99bf93437be2a6e37bf8edef38d76f843c1dff62))
* **completion:**  Don't pick the wrong types from unordered record patterns ([f283de18](https://github.com/gluon-lang/gluon/commit/f283de18247ca01216ea16711f40792bb8a30070))
* **parser:**
  *  Don't loop forever from inserting default blocks ([a2f18f33](https://github.com/gluon-lang/gluon/commit/a2f18f33e878d8a47189f3d32913db1268bb2a19))
  *  Recover from extra tokens before an `in` token ([4857fe95](https://github.com/gluon-lang/gluon/commit/4857fe958ccab3026abfcd386423b5fc7af9e147))
* **vm:**
  *  Allow hook functions to return asynchronous results ([52820e94](https://github.com/gluon-lang/gluon/commit/52820e947dea271c9ce0e073a040a6d245532294))
  *  Don't introduce an Unknown scope when calling functions ([f4f81fd7](https://github.com/gluon-lang/gluon/commit/f4f81fd705ceef3e55fa0b4e3ca3337f41b90f7f))
  *  Don't return an error for exiting to a locked scope ([81f6d956](https://github.com/gluon-lang/gluon/commit/81f6d95645e82acaae6b21fdcba24912dafa818e))
  *  Don't emit line information for macro expanded code ([4f056beb](https://github.com/gluon-lang/gluon/commit/4f056beb4d4b06e25d09cc261cb59333bda11851))
  *  Deep clone OpaqueValue when it is sent between disjoint threads ([ba7f316c](https://github.com/gluon-lang/gluon/commit/ba7f316cff17ae8d0f6457210272fb292d3ed844))
  *  Make get_global's type check act as a type signature check ([eee79952](https://github.com/gluon-lang/gluon/commit/eee799526d90cbc6caca2c02e2fc05f3ac168cb3))
  *  Implement Getable for Function<RootedThread, _> ([73f4feb0](https://github.com/gluon-lang/gluon/commit/73f4feb0debe8cb94ddbe67b56b897f8578d962a))

#### Performance

*   Allocate AppVec directly instead of using intermediate Vecs ([b0bc41f2](https://github.com/gluon-lang/gluon/commit/b0bc41f240141f579e93481a28f500b9b342da1b))
*   Use SmallVec in the Type::App variant ([a26c1062](https://github.com/gluon-lang/gluon/commit/a26c10629177172482e850a223d00d8ecfb4eec4))

#### Features

*   Make load_script return a future ([a8df68a5](https://github.com/gluon-lang/gluon/commit/a8df68a58263f86fc4b54e3389d490ce3ee62d85))
*   Add a future which can avoid creating an event loop for sync calls ([d2132fc8](https://github.com/gluon-lang/gluon/commit/d2132fc8890cee41d659cc07b9539a52a0fd5e82))
*   Implement explicit kinds on type alias parameters ([8a82cfdd](https://github.com/gluon-lang/gluon/commit/8a82cfdd83f3aacba7d8300485edc4f07ac053b0))
*   Allow querying the number of frames on the stack in the debug api ([a012274c](https://github.com/gluon-lang/gluon/commit/a012274c03ae35e1c10f06bc0f4f95458d5eafba))
*   Provide the index for each local through the debug interface ([6ba5b44f](https://github.com/gluon-lang/gluon/commit/6ba5b44f501c08089dd7a23f500544ff5d8eb360))
*   Add a function to query upvars from a Frame ([cf67386a](https://github.com/gluon-lang/gluon/commit/cf67386a62799db95ffcdb8af91ea6995c17156e))
*   Add a compiler option for controlling whether to emit debug information ([6c552806](https://github.com/gluon-lang/gluon/commit/6c552806f86bd3c91b57f390daa6badb008fe1c4))
*   Add an iterator over upvariable names ([a098c902](https://github.com/gluon-lang/gluon/commit/a098c9026e2ed8526ac78b9804b36413409f4624))
*   Allow the hook to yield and later resume execution ([2aea009f](https://github.com/gluon-lang/gluon/commit/2aea009f772a295b9ac2b87827711c7c464565b1))
*   Add variable name retrieval for the debug interface ([aa47e4dd](https://github.com/gluon-lang/gluon/commit/aa47e4dd262b73fe4a6679bd34d565efc0905be8))
*   Add an extra parameter to HookFn which can be queried for debug information ([01a041a9](https://github.com/gluon-lang/gluon/commit/01a041a90cd4787b0b1941372dcea07530897b8a))
*   Add flags to control when the hook function is called ([29230dbe](https://github.com/gluon-lang/gluon/commit/29230dbeb6df2338b59d7caa4069d2ea13445abb))
*   Allow the width to be specified in the value printer ([1481f3f4](https://github.com/gluon-lang/gluon/commit/1481f3f46031bf6d3b9ffdce8d78a6e0b6164308))
*   Allow the value printer to limit the depth of the printed value ([8d92cf08](https://github.com/gluon-lang/gluon/commit/8d92cf08d1be82b469150a78be239a595ff47296))
*   Rewrite parser using LALRPOP ([cc3d3267](https://github.com/gluon-lang/gluon/commit/cc3d3267770149189ebc0e4f22207bc88f733a99))
*   Add a macro for encoding gluon records into rust types ([1d5f67b3](https://github.com/gluon-lang/gluon/commit/1d5f67b3c920c47fd1bbf2700c77f28a11cb9d3f))
*   Add a macro for describing gluon record patterns ([e0151e2f](https://github.com/gluon-lang/gluon/commit/e0151e2f82e98e8a343d9346c2faeeccf853e143))
*   Visit and reparse all nested infix expressions ([0c531107](https://github.com/gluon-lang/gluon/commit/0c53110714fe21422668d6c15cf60464fdb98629))
* **parser:**  Return valid a valid AST after parsing an invalid expression ([1cdd0e31](https://github.com/gluon-lang/gluon/commit/1cdd0e31fd116c434dc42939aaa1dcb35406a471))
* **vm:**
  *  Make the compiler pipeline return futures for executing ([c0d355e2](https://github.com/gluon-lang/gluon/commit/c0d355e2149eae3e7ef0d41b112292e41018d9b5))
  *  Allow extern functions to return futures ([120f9d1d](https://github.com/gluon-lang/gluon/commit/120f9d1d170e8933654a412d5100813d065ddd8e))
  *  Add types to all variables in the debug info ([38674f1f](https://github.com/gluon-lang/gluon/commit/38674f1f202c313b49dbe16a3df18e17436b48b2))
  *  Add a pretty printer on vm values ([0288e0a4](https://github.com/gluon-lang/gluon/commit/0288e0a4a8fbe8aef3780f088e828220815ef6f5))
  *  Add a from_ut8 method for converting `Array Byte` into `String` ([a336a49f](https://github.com/gluon-lang/gluon/commit/a336a49fd506fc1d7fb9b48fce50020e68bb4669))
  *  Implement clone on OpaqueValue and Function ([b56549c4](https://github.com/gluon-lang/gluon/commit/b56549c47389e8c19dd5989e705005f97c7d21a0))



<a name="v0.2.0"></a>
## v0.2.0  (2016-09-25)

Version 0.2.0 consists of a few critical bug fixes, numerous usability improvements such as prettier printing of types and auto completion in the REPL as well as two additions to the language itself.

Row-polymorphic records are added to the type system (albeit in a slightly limited capacity) as well as type holes. More additions building on these features will be added in a backwards compatible way in upcoming versions.

In addition to the user visible changes listed here the internals have seen a lot of legacy cruft removed, in major part thanks to @brendanzab.

#### Features

*   Use InFile to display source information for parse errors ([7026d8a3](https://github.com/gluon-lang/gluon/commit/7026d8a374d780e9b0f27b9910bd229e6160b28d))
*   Use starts_with and ends_with from Rust instead of gluon ([5144ee29](https://github.com/gluon-lang/gluon/commit/5144ee295d423ca95f96a35b687906c603ea19fb))
*   Rename io.print to io.println and add io.print ([0a6b65bd](https://github.com/gluon-lang/gluon/commit/0a6b65bdd3e95dff737f6a846a9c2eafa1fd9581))
*   Implement unification of row polymorphic records ([df007c6e](https://github.com/gluon-lang/gluon/commit/df007c6e8337f582466b75e4a25c3e300a7093ee))
*   Improve readability of large types by splitting them onto multiple lines ([1c296ac9](https://github.com/gluon-lang/gluon/commit/1c296ac9841dba57f93defc416135d2bc1a8c90d))
*   Add holes to the type syntax, and use them when building the AST ([fb9bd82c](https://github.com/gluon-lang/gluon/commit/fb9bd82ce7792332e8a660e3f0ea05843d50f6d5))
*   Rename (*) to Type ([8a3e1945](https://github.com/gluon-lang/gluon/commit/8a3e194581d3c9eef70e94660c3edb89f3706629))
*   Repl UX improvements ([2ed0a35b](https://github.com/gluon-lang/gluon/commit/2ed0a35bd0e194ae9bd37b189c3f4bb59f6c6845))
* **base:**  Use quick-error for instantiate::Error ([96a8c631](https://github.com/gluon-lang/gluon/commit/96a8c63101ea2bfd02f2351eca4fa18cb80f8ef2))
* **check:**
  *  Attempt to generate variable starting with a unique letter ([f3c2e625](https://github.com/gluon-lang/gluon/commit/f3c2e625dda1a5779f4915898fb9219770a7a5db))
* **parser:**
  *  Use string slices in tokens ([e0b7d840](https://github.com/gluon-lang/gluon/commit/e0b7d840cdb9095bb52f39f5ab08ec5d5a68b851))
  *  Emit spans from the lexer instead of just locations ([e2a17a3a](https://github.com/gluon-lang/gluon/commit/e2a17a3a1e6cacf4cb9254c50bb16ae1f09aa577))
* **repl:**  Add completion to the repl ([ee4d0b60](https://github.com/gluon-lang/gluon/commit/ee4d0b60aa83f17e481ec96d048524b76b0b3645))
* **vm:**
  *  Implement field access of polymorphic records ([4696cedc](https://github.com/gluon-lang/gluon/commit/4696cedcc0a25e796361c010cddd8e8405e9d678))
  *  Allow the heap size on each thread to be limited ([f8a71f4c](https://github.com/gluon-lang/gluon/commit/f8a71f4cb79744c12fabb8c2edb0e199a37750c3))
  *  Return Result instead of Status in Pushable::push ([584c3590](https://github.com/gluon-lang/gluon/commit/584c35903f1af2856a09e5178d2cd01e21155aca))
  *  read GLUON_PATH from env var and add to new_vm (#79) ([e7254a40](https://github.com/gluon-lang/gluon/commit/(e7254a40f24d53fac6074b1189eda66032f7efc7)))

#### Bug Fixes

*   Don't gluon panic when writing only a colon (`:`) in the repl ([7864c449](https://github.com/gluon-lang/gluon/commit/7864c44912561dbdd218ce28bda5465fad1f81ad))
*   Only print a Stacktrace on panics ([c059bfd3](https://github.com/gluon-lang/gluon/commit/c059bfd33d8a0908019fc397c19e1682f4886d6e))
*   Surround operators with parens when pretty-printing ([7ccc6f22](https://github.com/gluon-lang/gluon/commit/7ccc6f229f48f0077bbb90f666cad137ebfab788), closes [#60](https://github.com/gluon-lang/gluon/issues/60))
*   Rename windows file separators characters ('\\') to '.' as well ([207bfc9a](https://github.com/gluon-lang/gluon/commit/207bfc9a658cf97aca40ff5eaff8c86e36d3474b))
*   Add a space before : when pretty printing types ([a9b160c3](https://github.com/gluon-lang/gluon/commit/a9b160c3725584702b14f76e44bbc63487024268))
*   Print ',' as separator between each type of a record ([d72d3e1b](https://github.com/gluon-lang/gluon/commit/d72d3e1b7c9d4d7313a89837d0ad184ad1cfe41c))
*   Don't return None from Source::location when byte is at end of file ([5aee09a5](https://github.com/gluon-lang/gluon/commit/5aee09a5518fbff972683644cd99ab07a5674016))
* **check:**
  *  Fail typechecking when records use a field more than once ([7bb8f0bd](https://github.com/gluon-lang/gluon/commit/7bb8f0bdfc7c25de7e3bf4f19e624bbaca784ac3))
  *  Handle unification with Type::Hole ([2912727f](https://github.com/gluon-lang/gluon/commit/2912727f496c11680a277ce7bc2323a4abb6a6ac))
  *  Detect recursive types for which unification do not terminate ([22b3c82e](https://github.com/gluon-lang/gluon/commit/22b3c82ee0955ebcfec4e2367696d28629b8c7a3))
* **completion:**
  *  Give completion for local variables when pointing to whitespace ([5c59a795](https://github.com/gluon-lang/gluon/commit/5c59a795f8558e5f1711a033f17142b29a001451))
* **repl:**
  *  Allow `:i` to be used on primitive types ([fe458488](https://github.com/gluon-lang/gluon/commit/fe458488ca336df0e604d1962ab4dcef089565a6))
  *  Include the prelude when using `:t` ([bb0f1347](https://github.com/gluon-lang/gluon/commit/bb0f1347f327c8d1e7327db26e374bb8d759a0eb))

#### Performance

*   Use a single mutex for both the stack and gc ([20fb0645](https://github.com/gluon-lang/gluon/commit/20fb0645fd681914157a848c69b7694aee9d88af))
*   use fnv instead of SipHasher for HashMaps. add type FnvMap (#106) ([4a64c68d](https://github.com/gluon-lang/gluon/commit/4a64c68d8d04a6788f1fea3d6f25471b873ee8e2))

* **check:**
  *  Avoid traversing the entire stack when generalizing ([29352bc3](https://github.com/gluon-lang/gluon/commit/29352bc38f211cb6427c6107f1b178310b0db84b))
  *  Avoid recreating new App instances in unroll_app unnecessarily ([ba4db236](https://github.com/gluon-lang/gluon/commit/ba4db236d793bb5e23ae2463512cef191827f7c9))

