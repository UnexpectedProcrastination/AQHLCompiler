#pragma once


struct ArenaAllocatorBucket {
	ArenaAllocatorBucket *next;
	char *memory;
	u32 remaining;
};

ArenaAllocatorBucket *makeBucket(u32 size);

struct BucketedArenaAllocator {
	ArenaAllocatorBucket *first;
	ArenaAllocatorBucket *current;
	u32 bucketSize;

	BucketedArenaAllocator(u32 bucketSize) : bucketSize(bucketSize) {
		current = makeBucket(bucketSize);
		first = current;
	}

	void *allocate(u32 size);

	inline void free() {
		while (first) {
			ArenaAllocatorBucket *bucket = first;
			first = first->next;

			std::free(reinterpret_cast<char *>(bucket) - bucketSize);
		}
	}
};

