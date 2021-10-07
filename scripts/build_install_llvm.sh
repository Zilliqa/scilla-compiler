# Fetch and build LLVM
llvm_commit="ea0e2ca1acb20781515c23850ec1ee7476909b2f"
llvm_src="${HOME}"/llvm-project-"${llvm_commit}"
llvm_build="${HOME}"/llvm_build

eval "$(opam env)"
mkdir -p "${llvm_build}"
wget -nv https://github.com/llvm/llvm-project/archive/"${llvm_commit}".tar.gz
tar -xzf ${llvm_commit}.tar.gz --directory="${HOME}"

cd "$llvm_build" || exit 1
cmake "${llvm_src}/llvm" -G "Ninja" -DCMAKE_BUILD_TYPE="Release" -DLLVM_ENABLE_ASSERTIONS=ON -DLLVM_TARGETS_TO_BUILD="host" -DLLVM_ENABLE_RTTI=ON -DLLVM_OCAML_INSTALL_PATH="$(opam var --safe --strict lib)"
ninja bindings/ocaml/install
