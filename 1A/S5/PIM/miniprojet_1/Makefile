ifeq ($(OS),Windows_NT)
	BUILD_CLASSPATH="./src_java/;./binding/java;$$CLASSPATH"
	RUN_CLASSPATH="bin;$$CLASSPATH"
else
	BUILD_CLASSPATH="./src_java/:./binding/java:$$CLASSPATH"
	RUN_CLASSPATH="bin:$$CLASSPATH"
endif


all: gen_binding build_ada build_java run_java

gen_binding:
	ada2java -P ajis_hello.gpr src_ada/hello.ads -o binding/ada -c binding/java -L exo_2_lib -b com.adacore.example

build_ada:
	gprbuild -p -P binding/ada/exo_2_lib.gpr

build_java:
	CLASSPATH=$(BUILD_CLASSPATH) \
	javac src_java/com/adacore/example/Main.java -d bin

run_java:
	CLASSPATH=$(RUN_CLASSPATH) \
	PATH="binding/ada/lib:$$PATH" \
	java com.adacore.example.Main

