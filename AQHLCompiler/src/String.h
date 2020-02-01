#pragma once

#include "Basic.h"
#include "Array.h"

struct String;

struct String_Hasher {
	Array<char> characters;
	u32 hash = 0;

	void append(char c);

	String_Hasher() : characters(128) {}

	bool operator==(const String &other) const;
	bool operator==(const String_Hasher &other) const;

	inline void free() { characters.free(); }
	inline void clear() { characters.clear(); hash = 0; }
};

struct String {
	u32 hash;
	u32 length;
	char *characters;

	String() : hash(0), length(0), characters(0) {};
	String(const char *cString);
	String(const char *begin, const char *end);
	String(String_Hasher &hasher);


	bool operator==(const String &other) const;
	bool operator==(const String_Hasher &other) const;

	inline void free() { std::free(characters); }
};

inline char *copyString(const char *s) {
	size_t len = strlen(s);

	char *ss = (char *) malloc(len + 1);

	assert(ss);
	strcpy_s(ss, len + 1, s);

	return ss;
}

std::ostream &operator<<(std::ostream &out, const String &str);

inline char *toCString(const String &s) {
	char *c = static_cast<char *>(malloc((size_t)s.length + 1));
	memcpy(c, s.characters, s.length);
	c[s.length] = 0;

	return c;
}

inline String copyString(const String &s) {
	String result;
	result.length = s.length;
	result.hash = s.hash;
	result.characters = static_cast<char *>(malloc(s.length));

	memcpy(result.characters, s.characters, s.length);

	return result;
}