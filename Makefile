# `lake build` replays the cached log of a module whose inputs did not change, and then does not
# write the Emela file again. `lake env lean` always runs the `#emit_emela` commands.
EXAMPLES := Examples/Base64Emit.lean Examples/TreeEmit.lean Examples/ListEmit.lean

.PHONY: gen test check

gen:
	lake build LeanEmela Examples.Base64 Examples.Tree Examples.List
	for f in $(EXAMPLES); do lake env lean $$f; done
	cd emela && emela fmt src/base64_model.emel src/tree_model.emel src/list_model.emel

test: gen
	cd emela && emela test .

check: test
	@git diff --exit-code -- emela/src || (echo "generated files are out of date"; exit 1)
