# Makefile

# The target
all: build

# Build the project using cargo
build:
	@cargo build

# Run the test_time executable using cargo
tests_time:
	@cargo run --bin test_time

# Run the test_arithm_time executable using cargo
tests_arithm_time:
	@cargo run --bin test_arithm_time

# Run the test_cycle executable using cargo
tests_cycle:
	@cargo run --bin test_cycle

# Run the test_arithm_cycle executable using cargo
tests_arithm_cycle:
	@cargo run --bin test_arithm_cycle

# Clean the build artifacts
clean:
	@cargo clean

# Help command of the Makefile
help:
	@echo "Usage:\n"
	@echo " make [all]:\t\t\t Build the library."
	@echo " make tests_time:\t\t Run the executable to have the comparison of executation time of the Full Scalar Multiplication."
	@echo " make tests_arithm_time:\t Run the executable to have the comparison of executation time of the Modular Multiplication."
	@echo " make tests_cycle:\t\t Run the executable to have the comparison of clock cycle number of the Full Scalar Multiplication."
	@echo " make tests_arithm_cycle:\t Run the executable to have the comparison of clock cycle number of the Modular Multiplication."
	@echo " make clean:\t\t\t Remove all files produced by the compilation."
	@echo " make help:\t\t\t Display the main targets of this Makefile."

.PHONY: all build tests_time tests_cycle clean help