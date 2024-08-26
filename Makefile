all: ./phony/to_standalone_directory

./phony/dune_doc: ./coq/*.v
	cd coq; dune build @doc
	touch ./phony/dune_doc

./phony/inject_js: ./phony/dune_doc
	./build_scripts/inject_js.exe
	touch ./phony/inject_js

./phony/forester_build: ./phony/inject_js ./trees/*
	forester build
	touch ./phony/forester_build

./phony/to_standalone_directory: ./phony/forester_build
	cp -r ./output/. ../patrick-nicodemus.github.io
