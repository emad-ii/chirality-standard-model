import type { Metadata } from 'next';
import { Geist, Geist_Mono } from 'next/font/google';
import './globals.css';
import './exhibits.css';
import './physics.css';
import './themes.css';
import './reader-experience.css';
import './foundations.css';

const geistSans = Geist({
  variable: '--font-geist-sans',
  subsets: ['latin'],
});

const geistMono = Geist_Mono({
  variable: '--font-geist-mono',
  subsets: ['latin'],
});

export const metadata: Metadata = {
  title: 'From Chirality to the Standard Model — An Interactive Exploration',
  description:
    'Learn how symmetry becomes particle charges, how experiments test the Standard Model, and how a compact Lie-algebra classification leads to three net chiral families.',
  metadataBase: new URL('https://emad-ii.github.io/chirality-standard-model/'),
  alternates: {
    canonical: 'https://emad-ii.github.io/chirality-standard-model/',
  },
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html
      lang="en"
      className="dark"
      data-theme="dark"
      style={{ colorScheme: 'dark' }}
    >
      <body
        className={`${geistSans.variable} ${geistMono.variable} antialiased`}
      >
        {children}
      </body>
    </html>
  );
}
