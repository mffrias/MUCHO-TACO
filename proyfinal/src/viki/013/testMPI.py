try:
    from mpi4py import MPI
    print("mpi4py is installed and can be imported.")
except ImportError:
    print("mpi4py is not installed or cannot be imported.")
