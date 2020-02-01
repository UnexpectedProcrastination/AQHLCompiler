#include "Basic.h"
#include "String.h"

String::String(const char *cString) {
	const char *s = cString;

	hash = 0;
	length = 0;
	u32 high;
	while (*s) {
		hash = (hash << 4) + *s;


		high = hash & 0xF0000000;

		if (high)
			hash ^= high >> 24;

		hash &= ~high;
		length++;
		s++;
	}

	characters = static_cast<char *>(malloc(length));
	memcpy(characters, cString, length);
}

String::String(const char *begin, const char *end) {
	assert(end >= begin);
	hash = 0;
	length = (u32)(end - begin);
	u32 high;

	characters = static_cast<char *>(malloc(length));

	for (u32 i = 0; i < length; i++) {
		characters[i] = begin[i];
		hash = (hash << 4) + begin[i];


		high = hash & 0xF0000000;

		if (high)
			hash ^= high >> 24;

		hash &= ~high;
	}
}

String::String(String_Hasher &hasher) {
	hash = hasher.hash;
	length = hasher.characters.size();
	characters = hasher.characters.trySteal();
}

bool String::operator==(const String &other) const {
	return length == other.length && hash == other.hash && !memcmp(characters, other.characters, length);
}

bool String::operator==(const String_Hasher &other) const {
	return length == other.characters.size() && hash == other.hash && !memcmp(characters, other.characters.storage, length);
}

std::ostream &operator<<(std::ostream &out, const String &str) {
	return out << std::string_view(str.characters, str.length);
}

void String_Hasher::append(char c) {
	characters.add(c);

	hash = (hash << 4) + c;

	u32 high = hash & 0xF0000000;

	if (high) {
		hash ^= high >> 24;
	}
	hash &= ~high;
}

bool String_Hasher::operator==(const String &other) const {
	return hash == other.hash && characters.size() == other.length && !memcmp(characters.storage, other.characters, other.length);
}

bool String_Hasher::operator==(const String_Hasher &other) const {
	return hash == other.hash && characters.size() == other.characters.size() && !memcmp(characters.storage, other.characters.storage, characters.size());
}
