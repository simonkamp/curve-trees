use ark_dlog_gadget::error::Error as DivisorError;
use ark_serialize::SerializationError;
use ark_std::string::String;
use thiserror::Error;

pub type Result<T> = core::result::Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    /// Curve Tree height cannot be 0
    #[error("Curve Tree height cannot be 0")]
    HeightCantBe0,

    /// Child doesn't exist at the given index
    #[error("Child doesn't exist at index {0}")]
    ChildDoesntExistAtIndex(u64),

    /// Leaf doesn't exist at the given index
    #[error("Leaf doesn't exist at index {0}")]
    LeafDoesntExistAtIndex(u64),

    /// Leaf already exists at the given index
    #[error("Leaf already exists at index {0}")]
    LeafAlreadyExistAtIndex(u64),

    /// Leaf index is not expected
    #[error("Leaf index {0} is not expected, expected {1}")]
    LeafIndexNotAsExpected(u64, u64),

    /// Leaf index is not in the expected range
    #[error("Leaf index {1} is not in the expected range [0, {0})")]
    TreeWontSupportRequiredInsertions(u64, u64),

    /// Serialization error
    #[error("Serialization error: {0}")]
    SerializationError(SerializationError),

    /// Failed to generate point or scalar.
    #[error("Failed to generate point or scalar: {0}")]
    GenerationError(String),

    /// Bulletprof R1CS error
    #[error("Bulletproof R1CS error: {0}")]
    BulletproofR1CSError(#[from] bulletproofs::r1cs::R1CSError),

    /// Mismatched size.
    #[error("Mismatched size: {0} {1}")]
    MismatchedSize(usize, usize),

    /// The curve point cannot be 0.
    #[error("The curve point cannot be 0")]
    PointCantBeZero,

    /// The curve point cannot be negative of another.
    #[error("The curve point cannot be negative of another")]
    PointCantBeNegative,

    /// Mismatched commitment lengths
    #[error("Mismatched commitment lengths: expected {expected}, got {got}")]
    InconsistentCommitmentLengths { expected: usize, got: usize },

    /// Paths count must be greater than 0
    #[error("Paths count must be greater than 0")]
    NeedNonZeroNumberOfPaths,

    /// Number of selected indices must be greater than 0
    #[error("Number of selected indices must be greater than 0")]
    NeedNonZeroNumberOfIndices,

    /// Set size must be greater than 0
    #[error("Set size must be greater than 0")]
    NeedNonZeroSetSize,

    /// Malformed proof input
    #[error("Malformed proof input: {0}")]
    MalformedProofInput(String),

    /// Root type mismatch
    #[error("Root type mismatch: expected {expected}, got {got}")]
    RootTypeMismatch { expected: String, got: String },

    /// Mismatched x-coordinates of children
    #[error("Mismatched x-coordinates of children")]
    MismatchedXCoordsChildren,

    /// Invalid root type for path
    #[error("Invalid root type for path")]
    InvalidRootTypeForPath,

    /// Cannot prove for more indices than the maximum supported batch size
    #[error("Cannot prove for more indices than the maximum supported batch size: got {0}, expected at most {1}")]
    MoreIndicesThanSupportedBatchSize(u32, u32),

    /// Inconsistent number of indices across multi-paths
    #[error("Inconsistent number of indices across multi-paths")]
    InconsistentNumberOfIndices,

    /// DivisorError error
    #[error("Divisor error: {0}")]
    Divisor(DivisorError),
}

impl From<SerializationError> for Error {
    fn from(err: SerializationError) -> Self {
        Error::SerializationError(err)
    }
}

impl From<DivisorError> for Error {
    fn from(err: DivisorError) -> Self {
        Error::Divisor(err)
    }
}
