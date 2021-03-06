#pragma once

#include "Basic.h"

template <typename T, u32 smallSize>
class SmallArray {
public:
	T *storage = 0;
	u32 count = 0;
	u32 capacity = smallSize;

	T small[smallSize];


	void trim() {
		resize(count);
	}

	void resizeAndMaybeTrim(u32 newCapacity) {
		count = my_min(count, newCapacity);

		if (newCapacity <= smallSize) {
			if (count && storage) {
				memcpy(small, storage, count * sizeof(T));
				std::free(storage);

				storage = nullptr;
			}

			capacity = smallSize;

		}
		else {
			if (storage) {
				storage = static_cast<T *>(realloc(storage, newCapacity * sizeof(T)));
			}
			else {
				storage = static_cast<T *>(malloc(newCapacity * sizeof(T)));
				memcpy(storage, small, count * sizeof(T));
			}
		}
		capacity = newCapacity;
	}

	void resize(u32 newCapacity) {
		assert(count <= newCapacity);

		resizeAndMaybeTrim(newCapacity);
	}

	SmallArray() {
		resizeAndMaybeTrim(smallSize);
	}

	SmallArray(u32 capacity) {
		resizeAndMaybeTrim(capacity);
	}

	SmallArray(std::initializer_list<T> values) {
		count = static_cast<u32>(values.size());
		resizeAndMaybeTrim(count);

		memcpy(begin(), values.begin(), sizeof(T) * count);
	}

	

	template<typename Range, typename = std::enable_if_t<!std::is_integral<Range>::value>>
	explicit SmallArray(const Range& values) {
		count = static_cast<u32>(values.end() - values.begin());
		resizeAndMaybeTrim(count);

		memcpy(begin(), values.begin(), sizeof(T) * count);
	}

	u32 size() const {
		return count;
	}

	void add(const T &value) {
		if (count >= capacity) {
			resize(capacity * 2);
		}

		begin()[count++] = value;
	}

	const T &operator[] (u32 index) const {
		assert(index < count);
		return begin()[index];
	}

	T &operator[] (u32 index) {
		assert(index < count);
		return begin()[index];
	}

	T *begin() {
		if (storage) {
			return storage;
		}
		else {
			return small;
		}
	}

	T *end() {
		return begin() + count;
	}

	const T *begin() const {
		if (storage) {
			return storage;
		}
		else {
			return small;
		}
	}

	const T *end() const {
		return begin() + count;
	}

	void free() {
		std::free(storage);

		storage = nullptr;
		capacity = smallSize;
		count = 0;
	}

	bool unordered_remove(const T &value) {
		for (int i = 0; i < count; i++) {
			if (begin()[i] == value) {
				unordered_remove(index);

				return true;
			}
		}

		return false;
	}


	void unordered_remove(u32 index) {
		if (index != count - 1) {
			begin()[index] = begin()[count - 1];
		}

		--count;
	}

	void unordered_remove(T *location) {
		assert(location >= begin() && location < end());

		if (location != end() - 1) {
			*location = *(end() - 1);
		}

		--count;
	}

	void clear() {
		count = 0;
	}

	T *trySteal() {
		if (storage) {
			T *oldStorage = storage;

			storage = static_cast<T *>(malloc(capacity * sizeof(T)));
			count = 0;

			return oldStorage;
		}
		else {
			T *oldStorage = static_cast<T>(malloc(count * sizeof(T)));
			memcpy(oldStorage, small, count * sizeof(T));
			count = 0;


			return oldStorage;
		}
	}

	void reserve(u32 capacity) {
		if (this->capacity < capacity) {
			resizeAndMaybeTrim(capacity);
		}
	}

	void pop() {
		assert(count);
		unordered_remove(count - 1);
		// @Volatile: only works because we never automatically shrink
		return *end();
	}
};

template <typename T>
class Array {
public:
	T *storage = 0;
	u32 count = 0;
	u32 capacity = 0;


	void resizeAndMaybeTrim(u32 newCapacity) {
		storage = static_cast<T *>(realloc(storage, newCapacity * sizeof(T)));

		if (newCapacity < count) {
			count = newCapacity;
		}

		capacity = newCapacity;
	}

	void resize(u32 newCapacity) {
		assert(count <= newCapacity);

		resizeAndMaybeTrim(newCapacity);
	}

	void reserve(u32 capacity) {
		if (this->capacity < capacity) {
			resizeAndMaybeTrim(capacity);
		}
	}

	Array() {}

	Array(u32 capacity) {
		resizeAndMaybeTrim(capacity);
	}


	Array(std::initializer_list<T> values) {
		count = static_cast<u32>(values.size());
		resizeAndMaybeTrim(count);

		memcpy(storage, values.begin(), sizeof(T) * count);
	}

	template<typename Range, typename = std::enable_if_t<!std::is_integral<Range>::value>>
	explicit Array(const Range& values) {
		count = static_cast<u32>(values.end() - values.begin());
		resizeAndMaybeTrim(count);

		memcpy(begin(), values.begin(), sizeof(T) * count);
	}

	u32 size() const {
		return count;
	}

	T &add() {
		add(T{});

		return storage[count - 1];
	}

	void add(const T &value) {
		if (count >= capacity) {
			resize(my_max(count + 1, capacity * 2));
		}

		storage[count] = value;
		count++;
	}

	const T &operator[] (u32 index) const {
		assert(index < count);
		return storage[index];
	}

	T &operator[] (u32 index) {
		assert(index < count);
		return storage[index];
	}

	T *begin() const {
		return storage;
	}

	T *end() const {
		return storage + count;
	}

	void free() {
		std::free(storage);

		storage = nullptr;
		capacity = 0;
		count = 0;
	}

	bool unordered_remove(const T &value) {
		for (int i = 0; i < count; i++) {
			if (storage[i] == value) {
				unordered_remove(index);
				return true;
			}
		}

		return false;
	}

	void unordered_remove(u32 index) {
		if (index != count - 1) {
			storage[index] = storage[count - 1];
		}

		--count;
	}

	void unordered_remove(T *location) {
		assert(location >= begin() && location < end());

		if (location != end() - 1) {
			*location = *(end() - 1);
		}

		--count;
	}

	void clear() {
		count = 0;
	}

	T *trySteal() {
		T *oldStorage = storage;

		storage = static_cast<T *>(malloc(capacity * sizeof(T)));
		count = 0;

		return oldStorage;
	}

	T pop() {
		assert(count);
		unordered_remove(end() - 1);

		// @Volatile: only works because we never automatically shrink
		return *end();
	}
};